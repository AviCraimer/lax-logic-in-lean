#!/usr/bin/env python3
"""Build a prover benchmark from Lean 4 source files.

Each benchmark item is a *prefix-truncated* file: everything in the source file
up to and including the target theorem's statement, with the proof replaced by
`sorry`.  The model is asked to complete it.

Why prefix truncation rather than `import`-ing the module that contains the
lemma: importing the module makes the lemma itself available, so the model can
close the goal with `exact <original_name>` and, worse, a lemma tagged `@[simp]`
becomes provable by `simp` using itself.  Prefix truncation reproduces the exact
elaboration context the original author had, and nothing more.

Usage:
    python3 extract.py --config corpora/laxlogic.json -o corpora/items.jsonl
    python3 extract.py --config benchmarks/sources.json -o benchmarks/items.jsonl
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path

# Lines at column 0 that begin a new top-level construct, i.e. terminate the
# declaration currently being scanned.
TOPLEVEL_RE = re.compile(
    r"^(?:@\[|/--|/-!|/-|--|"
    r"theorem\b|lemma\b|def\b|abbrev\b|instance\b|structure\b|inductive\b|"
    r"example\b|namespace\b|end\b|open\b|variable\b|variables\b|section\b|"
    r"import\b|set_option\b|attribute\b|notation\b|scoped\b|macro\b|syntax\b|"
    r"deriving\b|mutual\b|partial\b|private\b|protected\b|noncomputable\b|"
    r"class\b|#|universe\b|local\b)"
)

DECL_RE = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)")

# Attribute / doc-comment lines that attach to the declaration below them.
ATTACH_RE = re.compile(r"^(?:@\[|/--|/-!)")


@dataclass
class Item:
    id: str
    repo: str
    file: str
    line: int              # 1-indexed line of the `theorem`/`lemma` keyword
    name: str
    prefix: str            # everything before the declaration
    statement: str         # the declaration header, up to but excluding `:=`
    ground_truth: str      # the original proof body (after `:=`)
    proof_lines: int
    has_simp_attr: bool
    group: str


def strip_comments_for_scan(text: str) -> str:
    """Blank out string literals and comments so bracket/`:=` scanning is safe.

    Characters are replaced one-for-one with spaces, so all offsets are
    preserved and can be used to index into the original text.
    """
    out = list(text)
    i, n = 0, len(text)
    depth = 0          # nesting depth of /- -/ block comments
    while i < n:
        two = text[i : i + 2]
        if depth > 0:
            if two == "-/":
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if two == "/-":
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if two == "/-":
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if two == "--":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if text[i] == '"':
            out[i] = " "
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    out[i] = " "
                    i += 1
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


OPENERS = "([{⟨⦃«"
CLOSERS = ")]}⟩⦄»"


def find_proof_separator(decl_text: str) -> int | None:
    """Index of the `:=` that separates statement from proof, or None.

    Scans at bracket depth 0.  Returns None for equation-compiler style
    declarations (`| pat => rhs`), which have no top-level `:=`.
    """
    scan = strip_comments_for_scan(decl_text)
    depth = 0
    i, n = 0, len(scan)
    while i < n:
        c = scan[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and scan.startswith(":=", i):
            return i
        i += 1
    return None


def split_top_level(lines: list[str]) -> list[tuple[int, int]]:
    """Partition the file into top-level chunks as (start, end) line indices."""
    starts: list[int] = []
    for idx, line in enumerate(lines):
        if line[:1].strip() and TOPLEVEL_RE.match(line):
            starts.append(idx)
    spans = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        spans.append((s, e))
    return spans


def extract_file(repo: Path, rel: str, group: str, max_proof_lines: int) -> tuple[list[Item], dict]:
    path = repo / rel
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    spans = split_top_level(lines)

    items: list[Item] = []
    skipped = {"no_separator": 0, "too_long": 0, "sorry_in_proof": 0}

    for si, (s, e) in enumerate(spans):
        m = DECL_RE.match(lines[s])
        if not m:
            continue
        name = m.group(1)

        # Absorb attribute / doc-comment chunks immediately above.
        decl_start = s
        j = si - 1
        while j >= 0:
            ps, pe = spans[j]
            if pe == decl_start and ATTACH_RE.match(lines[ps]):
                decl_start = ps
                j -= 1
            else:
                break

        # Trim trailing blank lines from the declaration body.
        end = e
        while end > s and not lines[end - 1].strip():
            end -= 1

        decl_text = "".join(lines[s:end])
        sep = find_proof_separator(decl_text)
        if sep is None:
            skipped["no_separator"] += 1
            continue

        statement = decl_text[:sep].rstrip()
        proof = decl_text[sep + 2 :].strip()
        if not proof:
            skipped["no_separator"] += 1
            continue
        if re.search(r"\bsorry\b|\badmit\b", proof):
            skipped["sorry_in_proof"] += 1
            continue

        n_proof_lines = len(proof.splitlines())
        if n_proof_lines > max_proof_lines:
            skipped["too_long"] += 1
            continue

        attrs = "".join(lines[decl_start:s])
        prefix = "".join(lines[:decl_start])

        items.append(
            Item(
                id=f"{rel}:{name}",
                repo=str(repo),
                file=rel,
                line=s + 1,
                name=name,
                prefix=prefix,
                statement=(attrs + statement).rstrip(),
                ground_truth=proof,
                proof_lines=n_proof_lines,
                has_simp_attr="@[simp" in attrs,
                group=group,
            )
        )

    return items, skipped


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", type=Path, required=True,
                    help="JSON: [{repo, file, group}, ...]")
    ap.add_argument("-o", "--out", type=Path, required=True)
    ap.add_argument("--max-proof-lines", type=int, default=15)
    args = ap.parse_args()

    sources = json.loads(args.config.read_text())
    all_items: list[Item] = []
    totals = {"no_separator": 0, "too_long": 0, "sorry_in_proof": 0}

    for src in sources:
        repo = Path(src["repo"])
        items, skipped = extract_file(
            repo, src["file"], src["group"], args.max_proof_lines
        )
        for k, v in skipped.items():
            totals[k] += v
        print(f"{src['file']}: {len(items)} items "
              f"(skipped {skipped})", file=sys.stderr)
        all_items.extend(items)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w") as fh:
        for it in all_items:
            fh.write(json.dumps(asdict(it)) + "\n")

    print(f"\ntotal: {len(all_items)} items -> {args.out}", file=sys.stderr)
    print(f"skipped overall: {totals}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
