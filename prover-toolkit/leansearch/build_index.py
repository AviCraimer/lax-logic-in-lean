#!/usr/bin/env python3
"""Build a LeanSearch-compatible index over the projects named in toolkit.json.

Declarations are extracted at **source level** — the statement as the author
wrote it, with its doc comment — rather than from Lean's elaborated
environment.  That is deliberate.  The failure this index exists to fix is a
model not knowing that `⋏` is an object-level constructor of `Form` and that
`Deriv Φ Γ _` is an inductively defined relation.  The surface syntax carries
exactly that information; an elaborated type would desugar the notation away
and lose it.

Notation declarations are indexed as first-class entries for the same reason:
`⊟` is meaningless to a model trained on Mathlib until it can look it up.

    python3 build_index.py -o index.jsonl
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract import strip_comments_for_scan, TOPLEVEL_RE  # noqa: E402

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+"
    r"([A-Za-z_À-￿][A-Za-z0-9_'!?.À-￿]*)"
)

NOTATION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:scoped\s+|local\s+)*"
    r"(notation|infixl|infixr|infix|prefix|postfix|macro_rules|syntax)\b"
)

DOC_OPEN = ("/--",)

SKIP_DIRS = {".lake", ".git", ".claude", "wip", "Archive", "archive"}


def iter_lean_files(root: Path, skip_extra: set[str]) -> list[Path]:
    out = []
    for p in root.rglob("*.lean"):
        parts = set(p.relative_to(root).parts)
        if parts & (SKIP_DIRS | skip_extra):
            continue
        out.append(p)
    return sorted(out)


def module_name(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def split_chunks(lines: list[str]) -> list[tuple[int, int]]:
    starts = [i for i, l in enumerate(lines) if l[:1].strip() and TOPLEVEL_RE.match(l)]
    return [
        (s, starts[k + 1] if k + 1 < len(starts) else len(lines))
        for k, s in enumerate(starts)
    ]


def find_sig_end(decl_text: str) -> int:
    """Index of the top-level `:=` (or `where`), else the whole text."""
    scan = strip_comments_for_scan(decl_text)
    depth = 0
    for i, c in enumerate(scan):
        if c in "([{⟨⦃«":
            depth += 1
        elif c in ")]}⟩⦄»":
            depth -= 1
        elif depth == 0 and scan.startswith(":=", i):
            return i
        elif depth == 0 and scan.startswith("\nwhere", i):
            return i
    return len(decl_text)


def harvest(root: Path, repo_label: str, skip_extra: set[str]) -> list[dict]:
    entries: list[dict] = []
    for path in iter_lean_files(root, skip_extra):
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        lines = text.splitlines(keepends=True)
        chunks = split_chunks(lines)
        mod = module_name(root, path)
        rel = str(path.relative_to(root))

        # namespace stack, so names can be reported fully qualified
        ns: list[str] = []
        ns_at_line: dict[int, list[str]] = {}
        for i, l in enumerate(lines):
            m = re.match(r"^namespace\s+([A-Za-z_][\w'.]*)", l)
            if m:
                ns.append(m.group(1))
            elif re.match(r"^end\s+[A-Za-z_][\w'.]*", l) and ns:
                ns.pop()
            ns_at_line[i] = list(ns)

        for ci, (s, e) in enumerate(chunks):
            # doc comment immediately above
            doc = ""
            if ci > 0:
                ps, pe = chunks[ci - 1]
                if pe == s and lines[ps].lstrip().startswith(DOC_OPEN):
                    raw = "".join(lines[ps:pe])
                    doc = re.sub(r"^\s*/--|-/\s*$", "", raw, flags=re.S).strip()

            head = lines[s]
            body = "".join(lines[s:e])

            m = DECL_RE.match(head)
            if m:
                kind, name = m.group(1), m.group(2)
                sig = body[: find_sig_end(body)].rstrip()
                sig = re.sub(r"\n\s*\n.*", "", sig, flags=re.S).strip()
                prefix = ".".join(ns_at_line.get(s, []))
                full = f"{prefix}.{name}" if prefix else name
                entries.append({
                    "name": full,
                    "short": name,
                    "kind": kind,
                    "signature": sig,
                    "docstring": doc,
                    "module": mod,
                    "repo": repo_label,
                    "file": rel,
                    "line": s + 1,
                })
                continue

            if NOTATION_RE.match(head):
                sig = body.strip().split("\n\n")[0].strip()
                entries.append({
                    "name": f"{mod} (notation)",
                    "short": "notation",
                    "kind": "notation",
                    "signature": sig,
                    "docstring": doc,
                    "module": mod,
                    "repo": repo_label,
                    "file": rel,
                    "line": s + 1,
                })
    return entries


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default=None,
                    help="toolkit.json (default: discovered upwards from cwd)")
    ap.add_argument("-o", "--out", type=Path, default=None)
    args = ap.parse_args()

    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from toolkit_config import find_config
    cfg = find_config(args.config)

    out = args.out or (Path(__file__).parent / "index.jsonl")
    entries: list[dict] = []
    skip = set(cfg.exclude)
    for root in cfg.index_roots:
        rp = Path(root["path"]).expanduser()
        if not rp.is_dir():
            print(f"warning: {rp} not found, skipping", file=sys.stderr)
            continue
        got = harvest(rp, root.get("label", rp.name), skip)
        print(f"{root.get('label', rp.name)}: {len(got)} declarations", file=sys.stderr)
        entries.extend(got)

    with out.open("w") as fh:
        for e in entries:
            fh.write(json.dumps(e) + "\n")
    kinds: dict[str, int] = {}
    for e in entries:
        kinds[e["kind"]] = kinds.get(e["kind"], 0) + 1
    print(f"\ntotal {len(entries)} -> {out}", file=sys.stderr)
    print("  " + ", ".join(f"{k}={v}" for k, v in
                           sorted(kinds.items(), key=lambda x: -x[1])), file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
