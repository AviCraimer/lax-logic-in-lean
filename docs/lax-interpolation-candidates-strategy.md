# Interpolation candidates — a strategy of last resort

> For the Lax Logic uniform-interpolation formalization (Lean 4).
> Point the coding agent here **if the current focused-calculus + polarity-phase-measure
> search does not yield a simple proof.** This is a methodological resource, not a
> recipe with guaranteed output. Read it alongside `lax-logic-interpolation-handoff.md`.

## One-line summary

Stop trying to construct *the* uniform interpolant directly. Instead, generalize to the
notion of an **interpolation candidate** — by analogy with Girard's reducibility
candidates for strong normalization of System F — and let the candidate conditions be
**discovered from the failing proof**, one closure clause per rule where the naive
induction won't close.

## Why the direct induction is (probably) doomed — the impredicativity

The propositional quantifier `∀p φ` ranges over propositions, *including possibly φ
itself*. This is exactly the impredicativity that defeats the naive strong-normalization
induction for System F, where `∀X.A` quantifies over types you are in the middle of
defining. Girard's fix was not to induct toward "the normalizing terms of a type" but
toward a **reducibility candidate**: a set of terms closed under certain conditions,
quantifying over *all* admissible candidates. The stronger, candidate-based hypothesis
survives the quantifier step precisely because it already speaks about every candidate.

**Hypothesis:** uniform interpolation for Lax Logic is unproved (despite attempts) not
because a lemma is missing but because the *natural induction hypothesis is too weak to
close*. The whole game is finding the strengthened statement that is simultaneously
provable and implies the target. The analogue of reducibility candidates is the natural
candidate for that strengthening. Call it an **interpolation candidate**.

## The method — reducibility candidates as an *algorithm*, not an inspiration

Girard's `CR1`–`CR3` are not guessed. They are exactly the conditions that make the
induction step go through **for each elimination rule** — one closure condition per way
you can *consume* a term. That is the reusable recipe:

> **Read the candidate's closure conditions off the rules of the calculus.**
> For each rule, ask: "what must an interpolation candidate be closed under so that this
> rule preserves candidacy?" Each rule contributes one closure clause.

Applied here: iterate over the **left rules** of the focused Lax calculus. Each left
rule (each way of *consuming* a formula on the left) yields one closure clause on the
candidate.

## Where polarity enters (this was the open question)

Polarity **sorts the closure conditions into two kinds**:

- **Asynchronous / invertible (negative) rules → unconditional closure clauses**
  ("the candidate must *always* be closed under this").
- **Synchronous / focused (positive) rules → guarded closure clauses**
  ("closed under this *provided* you are in focus").

So polarity is not decoration on the candidate notion — it is the thing that splits the
`CR`-style conditions into unconditional vs guarded. **This is a concrete, checkable
prediction:** when the closure clauses are extracted rule-by-rule, they should fall into
exactly these two families along the polarity boundary.

## Generalize over *what*? — the analogy map

| System F (strong normalization) | Lax Logic (uniform interpolation) |
|---|---|
| quantifier over **types** `∀X.A` | quantifier over **propositions** `∀p φ` |
| candidate attached to a **type** | candidate attached to a **proposition** |
| generalize over **terms** inhabiting the type | generalize over **proofs / proof-states / focused strategies** |
| `CR1`–`CR3` closure conditions | closure clauses read off the left rules (sorted by polarity) |

**Best current guess:** an interpolation candidate = a **set of focused strategies
(equivalently proof-states) closed under the phase operations, indexed by proposition**.
Positive/negative strategies are the "term" analogue in the focused world. The extremal
definable such candidate is the interpolant.

Caveat, stated plainly: this **cannot be fully stated until the focused calculus is
pinned down**, because the closure clauses *literally are* the rules. No rules, no
clauses. So the calculus must be fixed first (see step 1 of the programme in the handoff
doc).

## The discipline — let the proof build the candidate

This is the heart of it, and it matches the spirit of the whole project ("you start to
prove, but you don't know exactly what you're proving; in the course of the proof, as you
meet each rule, you find the constraint that satisfies it"):

1. **Attempt the completeness / interpolation induction directly** (structural
   focalization style — one structural induction, à la Simmons).
2. **At each rule where the induction will not close, do not patch locally and do not
   spin on hypothesis-testing.** Instead, read off *what the step wished it had
   available*. Made formal, that wish **is the next closure clause** of the candidate.
3. **Accumulate the clauses.** The interpolation-candidate notion **assembles itself as
   the residue of the failed naive induction** — one clause per sticking point. The
   candidate is *discovered*, not designed, and it is discovered exactly at the points
   where the plain induction breaks.
4. Terminate when either (a) the induction closes with the accumulated candidate —
   you have the theorem — or (b) a sticking point demands a clause that is provably
   *unsatisfiable* — you have an impossibility result. **Both are papers.**

## Operational note for the agent (important)

The failure mode to avoid: the agent gets **bogged down in testing hypotheses and does
not progress the proof**. The instruction is the opposite:

- **Drive the proof forward rule-by-rule.** Treat each non-closing step as a *source of a
  closure condition*, not as a bug to be locally hacked or a hypothesis to be
  exhaustively tested.
- Maintain an explicit, growing list: **"Candidate closure conditions discovered so
  far"**, each tagged with (i) the rule that forced it and (ii) its polarity (->
  unconditional or guarded).
- **Cheap early test / triangulation:** run this against the *adversarial case first* —
  the specific single-variable formula that broke Rosalie's calculus, and the derivation
  where contraction had to be tracked. Check whether the accumulating candidate conditions
  account for exactly the re-use that the contraction-tracking was bookkeeping. If the
  contraction-count turns out to *be* a guarded (positive-phase) closure condition, that
  is strong evidence the whole reframing is right — and it makes the "same obstruction
  twice" claim (decision procedure vs interpolation) precise.

## Honest status

Whether this converges or stalls is genuinely unknown — this is at the research edge and
may not work. But it converts a vague "we need a clever trick" into a **disciplined
search with a stopping condition**: listen to the step, each break names a closure
condition, and either the candidate closes the induction or it exhibits the obstruction.
Either outcome is a result.
