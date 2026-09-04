# prover-toolkit

A repository-independent toolkit for attempting Lean 4 goals with a language
model and **verifying the result properly**. Developed alongside
`lax-logic-in-lean` and published with it, but it depends on nothing in this
repository: point `toolkit.json` at any Lean project.

It is not a prover. The proving is done by
[ax-prover](https://github.com/Axiomatic-AI/ax-prover-base); this supplies the
parts that make its output trustworthy on a bespoke development.

## What it adds

**A corpus index.** ax-prover's `LeanSearch` tool searches *Mathlib*. For a
development with its own notation and inductive types that is the wrong corpus.
`leansearch/` serves the same API over your declarations — including **notation
as first-class entries**, because a model trained on Mathlib does not otherwise
know that `⋏` is a constructor of your formula type rather than Lean's
conjunction.

**An axiom gate.** ax-prover checks that a proof compiles and has no `sorry`.
It does not check axioms. `constructive_prove.py` compares against the axioms
of the proof being replaced and flags a **strict superset**, so a proof that
introduces a dependency the previous one did not have is surfaced rather than
silently accepted. Whether that baseline is the *right* standard is an open
question: it records what an existing proof happens to rest on, which is not
the same as what the statement requires.

**A paranoid checker.** `verify.py` splices the model's proof under the
benchmark's verbatim statement, so a weakened goal cannot score; catches
`sorry` via `#print axioms` rather than grep, so a `sorry` reached through a
helper is caught too; and rejects `native_decide`. It self-tests in both
directions — every ground-truth proof must replay, and six negative controls
must be rejected.

**A cost model.** `theorem_cost_model.py` reports cost per *verified theorem*
with Wilson intervals, not cost per token. The two disagree: in testing a model
costing 5× less per token proved 8% of attempts against another's 62%.

## Setup

```bash
export AX_PROVER_HOME=~/src/ax-prover-base       # your ax-prover checkout
python3 prover-toolkit/leansearch/build_index.py
python3 prover-toolkit/leansearch/server.py --port 8080 &
python3 prover-toolkit/extract.py --config prover-toolkit/corpora/laxlogic.json \
        -o prover-toolkit/corpora/items.jsonl
```

`toolkit.json` in the project root holds every path; nothing is hardcoded. See
the docstring in `toolkit_config.py`.

## A Claude Code skill

`skill/prove-lemma/` wraps the above. Install with:

```bash
cp -r prover-toolkit/skill/prove-lemma ~/.claude/skills/
```

## Known limitations

- **Mathlib cannot currently be used as a benchmark corpus.** Extraction works
  by prefix truncation — the file up to the target statement — which does not
  compose with Lean's new module system (`module` / `public import`). 99% of
  Mathlib now uses it; the 82 files that do not are tactic infrastructure with
  no usable theorems. Fixing this needs a different extraction strategy for
  library files, and is not done.
- The extractor mis-handles equation-compiler declarations (`| pat => rhs`)
  with no top-level `:=`, silently producing a malformed file. Validate that a
  generated file compiles with exactly one `sorry` before trusting it.
- The axiom gate has **no baseline for a genuinely open goal**, and falls back
  to accepting anything `sorry`-free. Check such proofs by hand.
- `corpora/items.jsonl` is derived data and not committed. If it is missing the
  gate warns and degrades; rebuild it with `extract.py`.

## What was measured

Small samples, one corpus, no controlled comparisons. Indicative only.

| setting | verified |
|---|---|
| one-shot, Goedel-Prover-V2-8B (local) | 6/46 |
| one-shot, gpt-4o-mini | 6/72 |
| one-shot, gpt-5 | 15/24 |
| agentic (ax-prover), gpt-5 | 12/13 |

Reasonably supported: general capability beat Lean-specific training; the
agentic loop beats one-shot on harder lemmas; ~97% of an agentic round is model
thinking, not Lean (6 s of 145 s).

**Not** established: whether the corpus index helps — it is *used*, but never
ablated; any ranking between models run on different lemmas; or anything
beyond this one development. One hypothesis was tested and **refuted**:
truncating the prompt context was *not* suppressing one-shot results.
