#!/usr/bin/env python3
"""Verification of candidate Lean 4 proofs.

The checker is deliberately paranoid.  A prover harness that accepts a bad
proof produces a success rate that is not merely noisy but wrong, and every
downstream cost figure inherits the error.  Three things are enforced:

1. **The statement is ours.**  The model's proof body is spliced underneath the
   benchmark's verbatim statement, so a model that weakens the goal, adds a
   hypothesis, or proves a different lemma of the same name cannot score.
2. **No `sorry`.**  Checked via `#print axioms`, not by grepping the source:
   `sorryAx` in the axiom list is the definitive test, and it also catches a
   `sorry` reached through a helper lemma.
3. **No cheap escapes.**  `native_decide` (trusts the compiler, not the kernel)
   and any re-derivation of the target name are rejected.

Axioms are recorded for every success so the pinning discipline the repo uses
elsewhere carries over.
"""

from __future__ import annotations

import json
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

from extract import find_proof_separator

FENCE_RE = re.compile(r"```(?:lean4?|)\n(.*?)(?:```|\Z)", re.DOTALL)
AXIOM_RE = re.compile(r"depends on axioms:\s*\[(.*?)\]", re.DOTALL)
# Lean emits both `error:` and `error(lean.someCode):`.
ERROR_RE = re.compile(r"^.*?:\d+:\d+: error(?:\([^)]*\))?:", re.MULTILINE)

BANNED = ("native_decide", "sorry", "admit", "@[implemented_by")


@dataclass
class VerifyResult:
    ok: bool
    reason: str
    axioms: list[str] = field(default_factory=list)
    lean_stdout: str = ""
    lean_stderr: str = ""
    candidate: str = ""
    elapsed_s: float = 0.0


def extract_code_block(text: str) -> str | None:
    """Return the most plausible Lean code block from a model response."""
    blocks = FENCE_RE.findall(text)
    if blocks:
        # Prefer the longest block that mentions a declaration keyword.
        cands = [b for b in blocks if re.search(r"\b(theorem|lemma)\b", b)]
        return max(cands or blocks, key=len)
    # No fence: if the raw text looks like Lean, take it whole.
    if re.search(r"\b(theorem|lemma)\b", text):
        return text
    return None


def find_decl_start(block: str, name: str) -> int | None:
    """Index of the start of `theorem <name>` / `lemma <name>` in `block`."""
    pat = re.compile(
        rf"^[ \t]*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)?"
        rf"(?:theorem|lemma)\s+{re.escape(name)}\b",
        re.MULTILINE,
    )
    m = pat.search(block)
    return m.start() if m else None


def strip_trailing_attrs(head: str) -> str:
    """Drop doc comments and attributes hanging off the end of `head`.

    The benchmark's `statement` already carries the target's doc comment and
    attributes.  Whatever the model reproduced above the declaration must be
    removed, or the spliced file ends up with two doc comments in a row and
    fails to parse.
    """
    while True:
        stripped = head.rstrip()
        if stripped.endswith("-/"):
            for opener in ("/--", "/-!", "/-"):
                idx = stripped.rfind(opener)
                if idx != -1 and stripped.find("-/", idx) == len(stripped) - 2:
                    head = stripped[:idx]
                    break
            else:
                return head
            continue
        lines = stripped.splitlines()
        if lines and re.match(r"^\s*@\[[^\]]*\]\s*$", lines[-1]):
            head = "\n".join(lines[:-1])
            continue
        return head


def build_candidate(item: dict, response: str) -> tuple[str | None, str]:
    """Splice the model's proof body under the benchmark's own statement.

    Returns (candidate_source, reason).  `candidate_source` is None on failure.
    """
    block = extract_code_block(response)
    if block is None:
        return None, "no_code_block"

    start = find_decl_start(block, item["name"])
    if start is None:
        return None, "target_decl_absent"

    decl = block[start:]
    sep = find_proof_separator(decl)
    if sep is None:
        return None, "no_proof_separator"

    body = decl[sep + 2 :].strip()
    if not body:
        return None, "empty_proof"

    # Anything the model wrote before the target declaration: helper lemmas in
    # completion mode, or a reproduction of the file in whole-file mode.
    head = strip_trailing_attrs(block[:start])
    if re.search(r"^\s*import\b", head, re.MULTILINE):
        # Whole-file mode: the model reproduced the preamble, so trust its head
        # rather than prepending ours as well.
        preamble = head
    else:
        preamble = item["prefix"] + head

    candidate = f"{preamble.rstrip()}\n\n{item['statement']} :=\n  {body}\n"
    candidate += f"\n#print axioms {item['name']}\n"
    return candidate, "ok"


def verify(item: dict, response: str, repo: Path, timeout: int = 180) -> VerifyResult:
    candidate, reason = build_candidate(item, response)
    if candidate is None:
        return VerifyResult(ok=False, reason=reason)

    # Reject cheap escapes before paying for a Lean run.
    body_region = candidate[len(item["prefix"]) :] if candidate.startswith(item["prefix"]) else candidate
    for bad in BANNED:
        if bad in body_region:
            return VerifyResult(ok=False, reason=f"banned:{bad}", candidate=candidate)

    t0 = time.monotonic()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=repo, delete=False, encoding="utf-8"
    ) as fh:
        fh.write(candidate)
        tmp = Path(fh.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            cwd=repo,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        out, err, rc = proc.stdout, proc.stderr, proc.returncode
    except subprocess.TimeoutExpired:
        return VerifyResult(
            ok=False, reason="timeout", candidate=candidate,
            elapsed_s=time.monotonic() - t0,
        )
    finally:
        tmp.unlink(missing_ok=True)

    elapsed = time.monotonic() - t0
    combined = out + "\n" + err

    if ERROR_RE.search(combined) or rc != 0:
        return VerifyResult(
            ok=False, reason="lean_error", lean_stdout=out, lean_stderr=err,
            candidate=candidate, elapsed_s=elapsed,
        )

    m = AXIOM_RE.search(combined)
    if not m:
        if "does not depend on any axioms" in combined:
            axioms: list[str] = []
        else:
            return VerifyResult(
                ok=False, reason="no_axiom_report", lean_stdout=out,
                lean_stderr=err, candidate=candidate, elapsed_s=elapsed,
            )
    else:
        axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]

    if any("sorryAx" in a for a in axioms):
        return VerifyResult(
            ok=False, reason="sorry_ax", axioms=axioms, lean_stdout=out,
            lean_stderr=err, candidate=candidate, elapsed_s=elapsed,
        )

    return VerifyResult(
        ok=True, reason="ok", axioms=axioms, lean_stdout=out, lean_stderr=err,
        candidate=candidate, elapsed_s=elapsed,
    )


def self_test(items_path: Path, repo: Path, n: int = 8) -> None:
    """Sanity-check the verifier against ground truth.

    Every benchmark item's own proof must verify.  If it does not, the harness
    is broken, not the model, and any success rate it reports is meaningless.
    """
    import concurrent.futures as cf

    items = [json.loads(l) for l in items_path.read_text().splitlines() if l.strip()]
    sample = items[:n] if n else items

    def run(it):
        fake = f"```lean4\n{it['statement']} :=\n  {it['ground_truth']}\n```"
        return it, verify(it, fake, Path(it["repo"]))

    passed = failed = 0
    with cf.ThreadPoolExecutor(max_workers=8) as ex:
        for it, res in ex.map(run, sample):
            tag = "PASS" if res.ok else f"FAIL({res.reason})"
            if res.ok:
                passed += 1
            else:
                failed += 1
                print(f"  {tag} {it['id']}")
                print("   ", res.lean_stdout[:400].replace("\n", "\n    "))
            print(f"{tag:24s} {it['id']}  [{res.elapsed_s:.1f}s] axioms={res.axioms}")
    print(f"\nself-test: {passed} passed, {failed} failed, of {len(sample)}")


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("--items", type=Path, default=Path("benchmarks/items.jsonl"))
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("-n", type=int, default=8)
    a = ap.parse_args()
    self_test(a.items, a.repo, a.n)
