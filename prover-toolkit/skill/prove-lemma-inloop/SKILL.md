---
name: prove-lemma-inloop
description: Prove a Lean 4 `sorry` yourself, using the prover toolkit for corpus search, goal states, and axiom-checked verification. Use when asked to prove or close a `sorry` without spending on a hosted prover API, or when the goal needs judgement, repository context, or reading more than one file.
---

# prove-lemma-inloop

**You are the proposer.** The toolkit supplies retrieval, goal states, and
verification; the mathematics is yours.

This is the alternative to `prove-lemma`, which hands the goal to a hosted
model through `ax-prover`. Use this one when the goal needs context a fixed
prompt cannot carry — a proof pattern established elsewhere in the repository,
a definition three files away, an argument the docstring only gestures at — or
simply when you would rather not spend per attempt.

Neither route is better in general. The API route is unattended and can grind
through many lemmas; this one is free per attempt and can bring judgement.

## Setup

```bash
export PROVER_TOOLKIT_CONFIG=/path/to/toolkit.json
python3 prover-toolkit/leansearch/server.py &   # port comes from toolkit.json
```

## The loop

**1. Read the goal as Lean sees it** — not as you imagine it from the source.

```bash
python3 prover-toolkit/toolkit_cli.py goals path/to/File.lean
```

**2. Find what already exists.** Nearly every proof in a mature development has
a precedent. Search before inventing.

```bash
python3 prover-toolkit/toolkit_cli.py search "p-bisimulation variant" -n 8
```

Then read the precedent properly with `Read` — the index gives you signatures
and a location, not the argument. Also `grep` for the definitions the goal
mentions; understanding what `force`, `Rᵢ`, or `⋏` actually *are* prevents the
commonest failure, which is treating an object-level constructor as if it were
Lean's own connective.

**3. Write the proof.** Edit the file directly, replacing `sorry`.

**4. Check it.** This is not optional and not the same as "it compiled".

```bash
python3 prover-toolkit/toolkit_cli.py check path/to/File.lean my_theorem
```

Reports compile errors, whether `sorryAx` survives, and which axioms the proof
rests on. Pass `--baseline propext,Quot.sound` to be told about anything beyond
a set you expect.

**5. Iterate** on the reported errors, from step 1.

## Reporting

State what was proved, what it depends on, and what you did not attempt. Quote
the axioms. If you gave up, say so plainly and say where it broke — a partial
result with an honest boundary is worth more than a proof you have not checked.

## Cautions

- **Never leave a `sorry` you have not flagged.** `check` catches it via
  `sorryAx`; report it as a failure, not a proof.
- An open conjecture may be open because it is **false**. If the argument will
  not close, consider looking for a countermodel before assuming you are
  missing a trick.
- Commit before editing, so `git diff` shows exactly what you changed.
- The axiom report is a change-detector, not a verdict. An axiom can enter
  through a library lemma rather than from mathematical need.
