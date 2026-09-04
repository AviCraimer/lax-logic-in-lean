#!/usr/bin/env python3
"""Wrap ax-prover with an axiom-hygiene retry loop.

ax-prover's reviewer checks for `sorry` and cheating tactics. It does not check
which AXIOMS a proof pulls in, so it will happily accept a proof resting on
`Classical.choice` -- valid, but the wrong proof for a constructive
development. Three of eleven proofs in the first batch did exactly that.

This layer runs ax-prover, checks the axioms with `#print axioms`, and if the
proof exceeds the allowed set it restores the `sorry` and retries with an
explicit constraint injected into the file as a comment. The comment is the
injection point on purpose: ax-prover sends the file to the model, so no change
to ax-prover itself is needed, and the constraint names the actual offending
axioms rather than nagging in general terms.

    python3 constructive_prove.py path/to/Target.lean --rounds 3
"""
from __future__ import annotations

import argparse
import json
import re
import os
import subprocess
import sys
import time
from pathlib import Path

from toolkit_config import find_config

_CFG = find_config()
REPO = _CFG.repo

_ax = os.environ.get("AX_PROVER_HOME", "")
AX = Path(_ax).expanduser() if _ax else None
if AX is None or not (AX / ".venv" / "bin" / "ax-prover").exists():
    raise SystemExit(
        "set AX_PROVER_HOME to your ax-prover-base checkout, e.g.\n"
        "  export AX_PROVER_HOME=~/src/ax-prover-base")
# The gate compares a proof against the axioms of the proof it replaces and
# flags a STRICT SUPERSET -- a dependency the previous proof did not have.
#
# This is a change-detector, not a correctness standard. The baseline records
# what an existing proof happens to rest on, which is not necessarily what the
# statement requires: an axiom may enter incidentally through a library lemma
# rather than from any mathematical need. Treat a flag as "look at this",
# not as "this is wrong".
#
# Used when no ground truth exists (a genuinely new lemma): anything except
# `sorryAx` is accepted, with a warning, since there is nothing to compare to.
FALLBACK_NOTE = "no ground truth available - accepting any sorry-free proof"

BANNER = "-- === PROOF CONSTRAINT (added by constructive_prove.py) ==="


def decl_name(src: str) -> str | None:
    m = re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z_][\w'.]*)",
                   src, re.MULTILINE)
    return m[-1] if m else None


def axioms_of(path: Path, name: str) -> tuple[bool, list[str], str]:
    """(compiles_without_sorry, axioms, raw_output)"""
    tmp = REPO / "_axcheck_tmp.lean"
    tmp.write_text(path.read_text() + f"\n#print axioms {name}\n")
    try:
        p = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=REPO,
                           capture_output=True, text=True, timeout=600)
        out = p.stdout + p.stderr
    finally:
        tmp.unlink(missing_ok=True)
    if re.search(r":\d+:\d+: error:", out):
        return False, [], out
    m = re.search(r"depends on axioms:\s*\[(.*?)\]", out, re.DOTALL)
    axs = [a.strip() for a in m.group(1).split(",") if a.strip()] if m else []
    return ("sorryAx" not in axs), axs, out


def baseline_axioms(name: str) -> set[str] | None:
    """Axioms of the proof this one replaces, or None if there is no baseline.

    Computed from the benchmark's recorded ground truth, so it costs one Lean
    run and no judgement.
    """
    bench = Path(__file__).parent / "corpora" / "items.jsonl"
    if not bench.exists():
        # Derived data, gitignored. Silently falling back here would disable
        # the gate without saying so, which is worse than stopping.
        print(f"WARNING: {bench} missing - the axiom gate cannot find a "
              f"baseline.\n         Rebuild it with:\n"
              f"           python3 extract.py --config benchmarks/sources.json "
              f"-o benchmarks/items.jsonl", flush=True)
        return None
    for line in bench.read_text().splitlines():
        if not line.strip():
            continue
        it = json.loads(line)
        if it["name"] != name:
            continue
        tmp = REPO / "_baseline_tmp.lean"
        tmp.write_text(f"{it['prefix']}{it['statement']} :=\n  {it['ground_truth']}\n"
                       f"\n#print axioms {name}\n")
        try:
            p = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=REPO,
                               capture_output=True, text=True, timeout=600)
            out = p.stdout + p.stderr
        finally:
            tmp.unlink(missing_ok=True)
        if re.search(r":\d+:\d+: error:", out):
            return None
        m = re.search(r"depends on axioms:\s*\[(.*?)\]", out, re.DOTALL)
        return {a.strip() for a in m.group(1).split(",") if a.strip()} if m else set()
    return None


def constraint_block(offending: list[str], baseline: set[str]) -> str:
    named = ", ".join(f"`{a}`" for a in offending)
    base = ", ".join(f"`{a}`" for a in sorted(baseline)) or "no axioms at all"
    return f"""{BANNER}
-- The previous attempt was REJECTED. It compiled and contained no `sorry`, but
-- it depended on {named}, which the proof it replaces does NOT need.
-- The existing proof of this statement rests on {base}.
-- A correct proof here must not introduce a dependency beyond that. In
-- particular do not reach for `Classical.em`, `Classical.byContradiction`,
-- `by_contra`, or `by_cases` on a proposition with no `Decidable` instance,
-- unless the baseline already uses them. Where a case split is needed, obtain
-- it from a `Decidable` instance or from the inductive structure of the data.
-- Re-derive the proof within that limit.
-- === END CONSTRAINT ===
"""


def run_ax(path: Path, config: str) -> str:
    p = subprocess.run(
        [str(AX / ".venv/bin/ax-prover"), "--config", config, "prove",
         str(path.relative_to(REPO)), "--folder", str(REPO)],
        cwd=AX, capture_output=True, text=True, timeout=3600)
    return p.stdout + p.stderr


def log(msg: str) -> None:
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("target", type=Path)
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--config", default="configs/gpt5-local.yaml")
    a = ap.parse_args()

    path = (REPO / a.target) if not a.target.is_absolute() else a.target
    pristine = path.read_text()
    name = decl_name(pristine)
    if not name:
        print("could not find a theorem name"); return 2
    base = baseline_axioms(name)
    if base is None:
        log(f"target: {name}   {FALLBACK_NOTE}")
        allowed: set[str] = set()
        have_baseline = False
    else:
        log(f"target: {name}   baseline axioms (from ground truth): "
            f"{sorted(base) or 'none'}")
        allowed, have_baseline = base, True

    best = None
    for rnd in range(1, a.rounds + 1):
        log(f"--- round {rnd}: invoking ax-prover ---")
        out = run_ax(path, a.config)
        log("  ax-prover finished; checking axioms")
        ok, axs, _ = axioms_of(path, name)
        if not ok:
            log(f"  not proven (axioms={axs or 'n/a'})")
            path.write_text(pristine)
            continue
        extra = sorted(set(axs) - allowed) if have_baseline else []
        log(f"  proven; axioms = {axs or 'none'}")
        if not extra:
            why = ("matches the baseline" if have_baseline else FALLBACK_NOTE)
            log(f"  ACCEPTED — {why} (round {rnd})")
            return 0
        log(f"  REJECTED — axiom regression: {extra} beyond the baseline "
            f"{sorted(allowed) or 'none'}; retrying")
        best = path.read_text()          # keep it as a fallback
        path.write_text(constraint_block(extra, allowed) + pristine)

    if best:
        path.write_text(best)
        print(f"\nno constructive proof in {a.rounds} rounds; "
              f"kept the classical proof (FLAGGED, not accepted)")
        return 1
    path.write_text(pristine)
    print(f"\nno proof found in {a.rounds} rounds; restored `sorry`")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
