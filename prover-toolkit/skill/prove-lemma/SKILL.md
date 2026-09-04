---
name: prove-lemma
description: Prove a Lean 4 `sorry` using the agentic prover toolkit — runs ax-prover against a local corpus index, then verifies the result with an axiom-regression check. Use when asked to prove, close, or fill in a `sorry`, or to attempt an open lemma in a Lean development.
---

# prove-lemma

Attempt a Lean 4 goal with `ax-prover`, then **verify the result independently**.
The verification is the point: `ax-prover` checks that a proof compiles and
contains no `sorry`, but not which axioms it drags in. In testing, 3 of 11
accepted proofs pulled in `Classical.choice`.

## Before running

Check all three, and stop if any fails — a missing one produces results that
look plausible and mean nothing.

```bash
test -f toolkit.json && echo "config: ok"          # or set PROVER_TOOLKIT_CONFIG
curl -s localhost:8080/health                      # the corpus index
echo "${AX_PROVER_HOME:?set AX_PROVER_HOME to your ax-prover-base checkout}"
```

If the index is down:

```bash
python3 prover-toolkit/leansearch/build_index.py    # once, and after big edits
python3 prover-toolkit/leansearch/server.py --port 8080 &
```

## Running

For a lemma that already has a recorded ground-truth proof (i.e. it is in the
corpus, so the axiom baseline is known):

```bash
python3 prover-toolkit/constructive_prove.py path/to/File.lean --rounds 2
```

For a genuinely open goal there is no baseline, so the gate cannot regress
against anything. Run `ax-prover` directly and check the axioms yourself:

```bash
"$AX_PROVER_HOME/.venv/bin/ax-prover" --config configs/gpt5-local.yaml \
    prove path/to/File.lean:my_theorem --folder "$(pwd)"
```

## Verifying — do not skip

```lean
#print axioms my_theorem
```

- `sorryAx` present → **not a proof**. Report it as failed.
- Axioms beyond what the replaced proof needed → a regression. Report the
  specific extra axioms; do not quietly accept it.
- For an open goal, report the axioms plainly so the reader can judge.

## Reporting

Say what was proved, what it depends on, and what was *not* attempted. State
the cost. Never report "✓ Proven" from ax-prover's own output as if it were
verification — it is not.

## Cautions

- **It edits the target file on success.** Commit first, so `git diff` shows
  exactly what changed.
- Put experiments outside the `lakefile` globs so they cannot affect `lake build`.
- A failed attempt burns the full iteration budget, so failures cost several
  times more than successes. Roughly $0.28 per lemma with gpt-5 at 6 iterations.
- Success on lemmas with known proofs says nothing about open conjectures. Some
  goals are open because they are false.
