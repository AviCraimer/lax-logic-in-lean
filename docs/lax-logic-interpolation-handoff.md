# Lax Logic — Uniform Interpolation: context handoff

> Purpose: brief a coding agent (Claude Code / Cursor / etc.) on the current state of
> the uniform-interpolation work so it can pick up without the original chat thread.
> Drop this in the repo (root, or wherever `CLAUDE.md` points). All references below
> should be **independently verified** — some were surfaced by an LLM and may be
> mis-cited.

## The goal

Prove **uniform interpolation for propositional Lax Logic** (Lax = the
Fairtlough–Mendler modality `◯`, "lax"/"slack"), formalized in **Lean 4**.

- Working in a small fragment: **propositional, single propositional variable**.
- The single-variable case is intended as the **base case of an induction on the
  number of propositional variables**.
- Gut belief: uniform interpolation is **true** for this logic. If it turns out
  false, an impossibility result is publishable either way.

## Where it's stuck (the technical state)

1. A **published calculus** (call it Rosalie's calculus) was intended to be
   *contraction-free* and sound+complete. Lean-checking revealed it is **not
   complete** — there is a specific single-variable formula the standard published
   calculi prove but hers cannot. This traces to the **contraction question**.

2. The calculus was **patched into a complete, provably-terminating decision
   procedure in Lean** — but only by **tracking uses of contraction**. So we have
   termination/decidability, but via proof-dependent bookkeeping.

3. **Conjecture:** there is *no* contraction-free calculus for propositional Lax
   Logic. (Hard even to state precisely.)

4. Both the **syntactic** and **semantic** routes hit what appears to be the *same*
   combinatorial wall. (An LLM claimed they're "the same obstruction"; treat with
   suspicion unless a translation both ways is exhibited — but see the reframing
   below, which now makes the sameness plausible.)

## The core diagnosis (this is the key idea)

The contraction-usage tracking is **proof-dependent** — exactly what uniform
interpolation forbids, because the interpolant must be reconstructable from the
**sequent alone**, not from the particular proof. So *the terminating decision
procedure and the interpolation obstruction are the same fact seen twice.* That is
why the two routes collide at the same wall.

**Strategic pivot to test:** recast the contraction-usage tracking as a
**polarity-phase metric** in a **focused, polarised** version of the calculus.
Polarity is fixed by the *formula*, not by the derivation — so a polarity-phase
measure is **proof-independent**, hence interpolation-friendly. Contraction becomes
*structural, bounded re-entry* with a well-founded (multiset / lexicographic)
measure. Because the Lax modality is a **box-then-diamond composite** (`∀∃`), it may
give **two smaller pieces to descend on** rather than one stubborn whole.

Why Rosalie didn't just use Dyckhoff: Dyckhoff's contraction-free calculus is
tailored to intuitionistic **implication-left**. A Dyckhoff-style *refined rule for
the Lax modality* may **not yet exist** — which is where the novelty could sit.

## Why "induct on a proof" is not actually forbidden (resolving a standing confusion)

- It is **false** that a uniform interpolant cannot be built from a proof. Pitts'
  classic construction inducts on a terminating proof-search.
- The real constraint is only that the **output be invariant across proofs** —
  a function of the sequent (really of the antecedent alone), up to equivalence.
- **Canonicity/determinism discharges this for free.** If the focused proof is unique
  up to inessential permutation, "the proof" *is* a function of the sequent, so
  inducting on the proof = inducting on the sequent. **Buying determinism/canonicity
  of the proof system is the whole game.**

## The real monster (most recent refinement)

A proof is a proof of the **whole sequent** (antecedent *and* consequent), and in a
single-conclusion calculus the **left** rules you may fire depend on the **consequent**.
But a uniform interpolant for the antecedent must be built **without seeing the
consequent** — it must work for every right-hand side at once.

For Lax specifically: the **modal left rule only fires when the goal on the right is
itself modal** (you can strip `◯` off `◯q` on the left only in service of proving some
`◯p` on the right). This **goal-dependent left rule** is the crux — the antecedent's
left-behaviour is not independent of the consequent, which is exactly the entanglement
uniform interpolation must break.

The mechanism that tames it: the **propositional quantifiers** `∀p φ` / `∃p φ`.
- `∀p φ`: strongest p-free consequence *below* φ (best p-free approximation from below).
- `∃p φ`: weakest p-free formula φ *entails* (best p-free approximation from above);
  this is the **p-free consequence of the antecedent** — the left-hand summary,
  quantifying over all goals uniformly.

The single-variable base case is where you must prove these extremal p-free
approximants **exist as formulas** in the calculus (there's a large array of
variable-free candidate interpolants in this case; the task is existence + extremality).

## The contraction tension, concretely

To use `◯q` on the left without losing information you'd want to **retain** `◯p` on the
left after stripping — i.e. duplicate the sequent going backwards. That is **contraction
by the back door**, and it destroys the terminating/analytic proof search that uniform
interpolation needs. Contraction-free demands you **abandon** the premise; not losing
information demands you **keep** it. Squaring this circle = the whole problem. The
polarity-phase reframing above is the proposed way through: bound the re-use with a
metric rather than abolishing it.

## Suggested 3-step programme (for Matthew + Michael)

1. **Port the calculus to polarised, focused form** — use the Twelf "lax logic"
   construction as a template (it translates Fairtlough–Mendler Lax Logic into
   polarised Pfenning–Davies precisely to make completeness of *focused* Lax Logic
   clearer; does cut-admissibility in the target).
2. **Prove the focused system sound + complete** vs the fixed calculus by
   **structural focalization** (Simmons) — one structural induction, no invertibility
   lemmas, mechanically verifiable (ideal for Lean).
3. **Define the interpolant by recursion on focusing phases**, reading the
   contraction-count off as a polarity-phase measure.

## References (VERIFY INDEPENDENTLY)

1. **Pfenning & Davies (2001), "A Judgmental Reconstruction of Modal Logic"**,
   Math. Structures in Comp. Sci. 11(4):511–540.
   Judgmental presentation of Lax Logic; lax modality expressible via box+diamond;
   ties to Moggi's monadic metalanguage (→ realizability/belief flavour).
   `cs.cmu.edu/~fp/papers/mscs00.pdf`
2. **Twelf wiki, "Lax logic"** (`twelf.org/wiki/lax-logic/`; `lax-logic.elf` in the
   standardml/twelf GitHub). Translates Fairtlough–Mendler into polarised
   Pfenning–Davies for completeness of *focused* Lax Logic; cut-admissibility in
   target. Directly relevant to the contraction/completeness problem.
3. **Simmons, "Structural Focalization"** — `cs.cmu.edu/~rjsimmon/drafts/focus.pdf`.
   Soundness+completeness of a focused system by *one* structural induction
   (Pfenning cut-elim style), mechanically verifiable. **Most actionable: check
   whether this induction style/metric ports to the Lax fragment as the missing
   induction fuel.**
4. **Liang & Miller, LJF** ("Focusing and Polarization in Intuitionistic Logic",
   CSL 2007) and **Dale Miller**, "Focusing and Polarization in Linear,
   Intuitionistic, and Classical Logics". Arbitrary polarity on atoms tunes forward
   vs backward chaining — the syntactic/semantic duality as a tunable parameter.
5. Background: **Dyckhoff's contraction-free calculus** for intuitionistic logic
   (the model for refined, well-founded-measure rules — but tailored to implication,
   not the Lax modality).

## Related paper in flight

"Belief in Lax Logic" — blends a realizability interpretation with belief semantics.
Two orders: intuitionistic partial order + a Lax sub-relation. `Bp` true at `u` iff for
all `v ≥ u` there is a Lax step from `v` to a world where `p` holds (`∀∃`, box-then-
diamond; collapses to double-negation in the weakest case). Realizer = uniform
procedure across futures; non-confluence forces genuine computational content.
Intro rule = monadic unit/`val` (boxing, invertible → asynchronous/negative); left
rule = `bind` (consuming a belief, synchronous/positive); the Lax left rule only fires
when the goal is itself modal. Mapping to focusing: intuitionistic order ↔
async/invertible/box; Lax sub-relation ↔ sync/focused/diamond.

## Human next step (non-code)

Draft email to Rosalie exists (warm, out-of-the-blue, one concrete formula her
calculus can't prove but the standard ones can, framed as "did we mis-formalise?",
**no mention of any AI/model** — the Lean work stands on its own). Not yet sent.
