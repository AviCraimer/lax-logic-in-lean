# Uniform interpolation for PLL: what was tried, and where it stands

*Written 2026-07-12, at the point the proof effort was paused. Aimed at
a reader who knows proof theory but has not been following this
repository's day-to-day work. All claims below are cross-checked
against the Lean source; "PROVED" means machine-checked by Lean with
no `sorry` (Lean's marker for an unproved gap left in a proof); "file"
citations are relative to this repository.*

## Background, in one paragraph

The repository mechanises Fairtlough–Mendler Propositional Lax Logic
(PLL) in Lean 4. Iemhoff's published sequent calculus G4iLL for PLL
(a Dyckhoff-style contraction-free calculus) was found to be
**incomplete** for PLL: a valid sequent needs one of its hypotheses
used twice, on opposite sides of a step that opens a "possibly" (◯)
modality, and G4iLL's rule for that step only ever consumes the
hypothesis once. A repaired calculus, complete for PLL with cut and
contraction both admissible, was then built by changing three of
Iemhoff's rules so that each *keeps* a formula in a premise that her
version discarded. Uniform interpolation (existence of quantifiers
∃p/∀p eliminating an atom p from a formula, in the strongest/weakest
sense of Pitts) was then attempted over the repaired calculus. That
attempt is essentially complete — every part of the argument is
machine-checked except one lemma, described below, which remains
unproved despite an extensive search for a counterexample. Separately,
Iemhoff's own quantifier tables were checked against her own
(incomplete) calculus, to see whether her uniform-interpolation
argument is at least locally correct; two flaws were found.

## Terms used below (defined once, used throughout)

- **Recursion-depth bound** (`fuel` in the code): a natural number
  capping how many times a quantifier's defining recursion may unfold.
  Needed because one of the recursive clauses does not shrink any
  syntactic measure on its own.
- **Revisit-counter** (`budget`/`b` in the code): a separate counter,
  distinct from the recursion-depth bound above, limiting how many
  times the recursion may pass through a ◯-step that leaves the
  context unchanged (a "same-context" step). Growth of the context
  is paid for separately (next item), so only genuinely unproductive
  revisits consume this counter.
- **Missing-formula count** (`defect` in the code): given a fixed
  finite pool of formulas expected to be relevant to a proof (closed
  under taking subformulas and a couple of standard rule-shapes), the
  number of them not yet present in the current context. This strictly
  decreases whenever a step actually grows the context, and is the
  quantity that makes context-growing steps terminate.
- **Box-commitment point**: a point in a proof where a ◯ must be
  introduced on the right before an inner sub-argument can be
  finished, so that sub-argument's conclusion is a bare value rather
  than the proof's real, fixed target formula.
- **Test-algebra collection**: the exhaustive set of finite Heyting
  algebras (up to size 6) equipped with every possible "necessity"
  operation (a nucleus) that could interpret ◯ soundly — 34
  (algebra, nucleus) pairs in total. Checking a candidate law against
  every valuation on every pair is a semantic countermodel search:
  any failure is a genuine countermodel; passing everywhere is strong
  (but not conclusive) evidence of truth.
- **Background hypothesis**: a fact already available in the
  surrounding context that a step may draw on without it being one of
  its stated premises.

## Table A — modifications of Iemhoff's G4iLL tried

| Calculus | What it is | Complete for PLL? | Cut admissible? | Decidable / terminating proof search? | Machine-checked where |
|---|---|---|---|---|---|
| **G4iLL as published** (`G4`) | Dyckhoff's contraction-free calculus for intuitionistic logic, plus four rules for ◯, transcribed verbatim from Iemhoff (arXiv:2209.08976, Fig. 2.2–2.3); every left rule, including both ◯-implication rules, consumes its principal formula. | **No.** REFUTED: a sequent derivable in the (cut-admitting) G3 calculus needs a hypothesis used twice across a ◯-opening; G4iLL's rule for that shape only keeps the hypothesis once, so the sequent is underivable there (both directions machine-checked by `decide`). | **No.** REFUTED outright (`cut_not_admissible`). Contraction fails too (`contraction_not_admissible`). | Yes, for G4-derivability itself (not for PLL): every rule's premises are strictly lighter in a Dershowitz–Manna multiset order, so plain backward search terminates with no extra device. This decides membership in G4iLL, which is a proper sub-relation of PLL-derivability. | `LaxLogic/PLLG4.lean`, `LaxLogic/PLLG4Gap.lean`, `LaxLogic/PLLDecide.lean` |
| **First repair, one retention** (`G4p`) | A single change to Iemhoff's rule for a boxed implication that opens a box: its first premise now *keeps* the implication instead of discarding it. | Not settled as a standalone question: the previously-missing sequent becomes derivable, but full completeness for this calculus alone was never finished. | Not established. Writing out the admissibility proof exposed an unresolved circular obligation between cut and a needed self-absorption property (a step could not be shown to terminate). | No: explicitly not terminating by the original measure any more (the kept implication can leave a premise no lighter than its conclusion); no separate termination argument was built for this calculus. | `LaxLogic/PLLG4P.lean` + `PLLG4PInv/PLLG4PAdm/PLLG4PStr.lean` (exchange, weakening, inversion, generalised identity all proved; cut/contraction/completeness not attempted here) |
| **Full repair, three retentions together** (`G4h`/`G4c`, called "G4iLL″") | Three changes to Iemhoff's rules, each keeping a formula that her version discarded: the box-opening rule keeps its box (this is exactly G3's rule for ◯ on the left); the box-opening ◯-implication rule keeps both the box *and* the implication; the non-opening ◯-implication rule keeps its whole premise context too. A step-count ("height") is carried alongside each sequent so structural properties can be proved by induction on it. | **Yes, proved.** `G4c = SC = LaxND` = term-inhabitation, unconditionally (`completeness`). | **Yes, proved outright and unconditionally** (`G4c.cut`); the one hypothesis the proof needed (a self-absorption property) is itself proved with no assumptions, so nothing is left conditional. Contraction is also proved, cut-free (`G4c.contract`). | Not directly in this (list-context) form; decidability is obtained via the reformulation below. | `LaxLogic/PLLG4H.lean`, `PLLG4HInv/HAdm/HStr/HCtr/HCut/HComp.lean`. Axiom audit: `[propext, Quot.sound]` (choice-free since the 2026-07-17 hygiene pass), no `sorry`. |
| **Height-indexed, set-based variant** (`G4sh`/`G4s`) | The same three-retention calculus restated with contexts as finite sets rather than lists, made fully cumulative (every rule only ever adds formulas, never removes any); proved to derive exactly the sequents `G4c` does. | **Yes** (inherited via the proved equivalence with `G4c`). | Inherited via the same equivalence, not reproved as a rule of this calculus in its own right. Nothing to contract (cumulative contexts have nothing to remove). | **Yes, proved.** Bounding the space of formulas that can ever appear (by a weight cap and a fixed atom alphabet) plus a "have we seen this sequent before" bookkeeping device gives a backward search that is sound, complete, and terminating — F&M's Theorem 2.8. The search is total but can be exponential; the sequent separating G4iLL from PLL above has an astronomically large search space and is not run directly. | `LaxLogic/PLLG4Set.lean`, `PLLG4Space.lean`, `PLLG4Dec.lean` |
| **The ◯-free fragment** (any calculus above, restricted to formulas that never mention ◯) | Not a separate calculus — PLL restricted to ◯-free formulas coincides with ordinary intuitionistic propositional logic, and no ◯-rule is ever exercised. | Yes (inherited trivially). | Yes (inherited trivially). | Yes (inherited trivially). | Relevant because the one open lemma in Table B/C below (`cascade_low_pos_box`) is specifically about formulas that mention ◯: on this fragment the corresponding case is proved unconditionally (`cascade_low_pos_boxfree`, `cascade_main_bf`), so uniform interpolation for ordinary intuitionistic propositional logic already comes out of this work with no gap. |

## Table B — quantifier-definition attempts, by calculus

| Attempt | Definition idea | Calculus used | What is PROVED | What FAILED or is OPEN | Verdict |
|---|---|---|---|---|---|
| **1. First attempt** | The standard (Pitts-style) recipe for ∃p (strongest p-free consequence) and ∀p (weakest p-free antecedent for a goal), written by direct analogy with the textbook clause tables, without yet adapting the clauses to the fact that the repaired calculus's rules retain material. | The repaired calculus (`G4c`/`G4s`) | p-freeness; the two "one-line" interpolation properties (Γ ⊢ ∃pΓ, and its ∀-side counterpart); monotonicity under the recursion-depth bound. | The fourth (adequacy) property. A direct kernel-checked test produced counterexamples: the ∀-quantifier applied to a simple sequent collapsed to the bare goal formula instead of the true weakest antecedent, and the ∃-quantifier trivialised to "true" on some contexts. Diagnosis: the ∀-clauses never referred back to the ∃-quantifier at all, although the intended recursion is a *mutual* one; some reflection-style clauses were missing; and there was no clause at all letting a ◯-shaped hypothesis be used when the goal itself is ◯-shaped. | **REFUTED** (counterexample; superseded in place — no separate file survives, rewritten directly into the file below) |
| **2. Second (corrected) attempt** | The mutual recursion corrected to match the repaired calculus's rules exactly, including a clause — for a boxed hypothesis paired with an implication out of a box — that is genuinely self-referential: unfolding it once more reproduces the very same context and goal it is defining. Because nothing shrinks across that one clause, the definition cannot be phrased as an ordinary structural recursion; it is given a recursion-depth bound instead, and a separate argument is needed to show results about it do not depend on exactly how large that bound was. | The repaired calculus (`G4c`/`G4s`), same rules as attempt 1 | The full four-property adequacy pair, for a derivation of step-count n, at any recursion-depth bound greater than n (`inter_adequate`, `LaxLogic/PLLG4UIAdq.lean`, no `sorry`); a context-set congruence property and a fixed-point law for ◯ (`◯((α∨◯(α∧β))∧β) ⊣⊢ ◯(α∧β)`, pure monad multiplication, no Löb-style axiom needed), both unconditional (`LaxLogic/PLLG4UIStab.lean`). | Eliminating the recursion-depth bound itself, so as to get a single formula computable from the context alone (a genuine *uniform* interpolant). This needs two "the bound can be raised or lowered by one with no change of content" properties; one has a clean proof, the other runs into a self-repeating demand at contexts the recursion revisits without growing them — the argument reproduces, one level down, exactly the demand it started from. Three separate proof strategies were tried and all reproduce the same obstruction (`docs/ui-endgame.md`) — a mechanised instance of essentially the same phenomenon that breaks Iemhoff's own termination argument once the calculus is repaired. | **ABANDONED** (superseded; adequacy proved outright, but the recursion-depth bound could not be eliminated by any of the direct stabilization strategies tried, so the definition was replaced) |
| **3. Current (truncated) definition** | Redefined a third time so the recursion-depth bound becomes unnecessary in principle: (a) clauses that would just reproduce the sequent already being defined are dropped, having first been shown formally redundant, not merely omitted; (b) every remaining same-context reference is indexed by the revisit-counter (see Terms, above) instead, decreasing by one each time, while context growth is paid for out of the missing-formula count instead; (c) the one truly self-referential clause is replaced by a one-step unfolding into the *other* possible outcomes at that point, justified by the fixed-point law proved in attempt 2. With these three changes the recursion has an honest decreasing measure, and its value is uniform (computable from the context alone) by construction — no recursion-depth bound appears in the final answer at all. | The repaired calculus (`G4c`/`G4s`), same rules as attempts 1–2 | The full four-property adequacy pair re-run against the new clauses (`wip/adequacy.lean`, no `sorry` in that file); side lemmas showing the answer does not depend on the (now-vestigial) recursion-depth bound or on which sufficiently-large finite formula-pool was chosen (`wip/indiff.lean`, `wip/spaceindiff.lean`, both unconditional); a packaging layer producing one closed formula per quantifier and checking all four of Pitts's conditions plus two standard factorization laws (`wip/packaging.lean`, `wip/final.lean`); on the ◯-free fragment, everything closes with no residue at all (full uniform interpolation for ordinary intuitionistic logic, unconditionally). | One single lemma: informally, "a value computed with the revisit-counter one higher can always be brought down to the value at one lower, given that the corresponding ∃-quantifier fact already holds at the lower level" — proved for every case **except** where the goal formula (or the relevant formula-pool) involves ◯ (`cascade_low_pos_box`, `wip/absorb_base.lean`, the sole `sorry` in the entire development; see Table C). | **OPEN** (searched extensively — see Table C; file: `wip/absorb_base.lean`) |
| **4. Iemhoff's own tables, over her own calculus** (task #13) | No new definition: Iemhoff's own §6.3–6.6 clause tables, transcribed verbatim and checked against the published figures, evaluated over her own calculus exactly as printed (no retention anywhere), asking a narrower question than completeness: is her uniform-interpolation *argument* at least locally correct for her own notion of derivability? | Iemhoff's original, unrepaired G4iLL (`G4`) | p-freeness, outright. The "one-line" interpolation properties for every rule family **except** one conjunct (below). Of the fourth (adequacy) property: both axiom cases, all four right-hand rules, and the box-opening rule on either side **when the goal is not itself the thing under a box**. A genuinely new admissible rule was found and proved along the way: a "consumed-form" modus ponens against a context implication (from `Δ ⊢ X` and `Y, Δ ⊢ C`, conclude `X→Y, Δ ⊢ C`) — the *retained* form of this is G3's usual left-implication rule and it is **not** admissible here (it would prove too much); the consumed form is, and is exactly the tool her own proof needs. | **Flaw 1** (a hidden reliance on an inference her own calculus lacks): her proof of the "one-line" property for the rule handling `(A⊃B)⊃D` on the left implicitly composes two derivations through cut — but G4iLL does not admit cut, so this step is not actually available to her; the standard (Pitts/UIML) clause for the same rule uses a differently-shaped, *guarded* premise that **is** provable without cut. Her choice of the unguarded shape, not the rule itself, is the avoidable shortcoming. **Flaw 2** (an outright case-mismatch in the text, independent of the completeness gap): in her adequacy proof (Lemma 7), for the case where a hypothesis's box is opened while the tracked goal sits on the *other* side of the sequent, she states the target sequent that must be reached, then in fact derives the target sequent of a *different* case, and declares this "what we had to show." It is not: the step actually required is not an instance of any of her rules, and no disjunct of her own ∀-quantifier anticipates a boxed hypothesis on that side. The repair used elsewhere in this project for exactly this situation (attempt 3's self-referential clause) recurs at the identical sequent, so it could not be expressed inside her terminating recursion at all — table blindness and calculus incompleteness turn out to be two faces of the same underlying failure. | **REFUTED** for "her printed argument is correct as it stands" (two located, machine-confirmed problems) — while p-freeness, most rule families, and the right-rule/Γ-side cases of adequacy are separately **PROVED**; file: `wip/g4ill_ui.lean` |

## Table C — candidate auxiliary laws tested this week, en route to the missing lemma

**The missing lemma itself**, displayed (E@k(Γ) abbreviates the
∃-quantifier at revisit-level k on context Γ; A@k(Γ,g) abbreviates the
∀-quantifier at revisit-level k, context Γ, goal g; both also carry a
recursion-depth bound, suppressed here as pure bookkeeping):

    E@(b+1)(Γ)  and  A@(b+1)(Γ,g)  and  1 ≤ missing-formula-count(Γ)
    and  b past a fixed threshold computable from the formula-pool alone
    ⟹  A@b(Γ,g)

In words: raising the revisit-counter by one, on either quantifier,
never changes the value of the ∀-quantifier for a fixed goal — provided
the context is not already saturated (at least one expected formula is
still missing) and the counter has already climbed past a threshold
that depends only on the fixed formula-pool, not on the context.

**Verdict: OPEN.** Searched across three separate rounds this week
(`wip/refute3.lean`, plus predecessor probes): the full test-algebra
collection (34 algebra/nucleus pairs, exhaustive over Heyting algebras
up to size 6), roughly 454 configurations checked at or above the
lemma's own threshold, of which about 45 were genuinely semantically
evaluated across the whole test-algebra collection (on the order of
9,800 individual valuations, all consistent with the lemma), the rest
either trivially true by construction or resolved directly by the
verified decision procedure. Zero counterexamples found. Where the two
sides of the lemma were comparable at all, they came out **exactly
equal**, not merely one bounding the other — i.e. the evidence says the
lemma is not just true but has no slack in it, which is consistent with
it being genuinely hard to prove by the methods tried so far rather
than false. (The 454 figure is as logged in the working session record;
it was not independently re-tallied line-by-line for this note.)

Auxiliary laws adjudicated on the same test-algebra collection this
week, aimed at finding either a proof route or a counterexample:

| Law | Statement (plain terms) | Verdict |
|---|---|---|
| **Z1** — the bare law below its own threshold | The missing lemma's conclusion, tested at *every* counter value ≥ 0, not just above the proper threshold. | **REFUTED (witness)** at exactly one structural point: counter value 0 with a ◯-shaped goal, where the ∀-quantifier's table is definitionally empty there (an empty disjunction). **True at every other value tested** (counter ≥ 1, across missing-formula counts 1 and 2, and formula-pools with 1, 2, or 4 relevant intermediate goals) — i.e. the real semantic threshold looks like a flat "≥ 1", not the more generous count-dependent one the current proof strategy uses. |
| **Z2a** — re-guard a box-commitment point one level down, unaided | Inside a box-commitment point, strengthen a guard from level c to level c−1 with no outside help. | **REFUTED (witness)**: fails exactly where the ∃-quantifier's value genuinely has not yet settled between the two levels (witness: a 3-element chain algebra, a specific fixed-point map, at counter value 1). |
| **Z2b** — the same, but using an already-available background fact | The same re-guarding, given the surrounding context's own higher-level ∃-quantifier fact as a background hypothesis. | **PROVED, as an actual inference rule** (not merely checked): see `box_remap`/`box_reguard` below. |
| **Z3 / Z7** — the two box-commitment points restated directly | The two places a proof actually gets stuck (having to commit to a ◯-shaped conclusion before an inner argument finishes), stated as one-step laws rather than built up from parts. | **PROVED (no counterexample, with room to spare)** — confirms that isolating the missing lemma this way is faithful to the real obstruction, not an artefact of how the problem was split up. |
| **Z5** — growing the context by one genuinely new formula | A background fact at level c+1 on a context Γ, together with the same background fact at level c on Γ plus one new formula, together equal (not just imply) the level-(c+1) fact on the grown context. | **OPEN (no counterexample)** — held as an exact equality everywhere tested, including the one case where a closely related law (Z8, below) fails. Proving it would remove one of the four places the argument gets stuck without needing to rebuild the whole proof; the sharpest identified target for follow-up work. |
| **Z6** — sanity check on Z1 | Z1's law, with an extra copy of the target-level guard added on the left (redundant, if the guard family is monotone under the surrounding context). | **REFUTED (witness)**, at exactly the same point as Z1, with the same witness — confirms, as predicted, that the extra guard supplies no information not already available. |
| **Z8** — the mirror question on the ∃-side | Does the ∃-quantifier only grow as the revisit-counter increases, with no threshold at all? | **REFUTED (witness)**: a genuine counterexample at counter value 1, in a configuration where the ∃-quantifier has not yet settled; true again from counter value 2 onward in that same configuration. This independently rules out the most obvious two-step proof strategy (prove the ∃-side grows, prove the ∀-side falls, combine): the ∃-side half is simply false below counter value 2. |

**Two new inference rules proved this week** (`wip/absorb_base.lean`,
`box_remap` and `box_reguard`; Δ is the surrounding context, E/E′/Z/Z′
are formulas, "◯(X ⇒ Y)" is the boxed-guarded-implication shape used
throughout the quantifier tables):

    Δ ⊢ ◯(E ⇒ Z)      E′, Δ ⊢ E      Z, E′, Δ ⊢ Z′
    -----------------------------------------------  (box_remap)
                  Δ ⊢ ◯(E′ ⇒ Z′)

In words: given a boxed guarded value, a way to derive the old guard
from a new one (using the whole surrounding context), and a way to map
the opened value plus the new guard to a new value, one may replace
both the guard and the value inside the box at once. This pins down
exactly what a box-commitment point *can* carry across: every
formula-shaped resource in the surrounding context, but nothing
belonging to the bookkeeping that tracks which goals have already been
visited (that bookkeeping concludes the proof's fixed outer target,
which is strictly weaker than the single boxed disjunct a
box-commitment point must produce, and cannot be threaded through).

    Δ ⊢ ◯(E ⇒ Z)      E′, Δ ⊢ E
    -----------------------------  (box_reguard, = box_remap with Z′ := Z, identity map)
              Δ ⊢ ◯(E′ ⇒ Z)

In words: the special case of the above where only the guard changes
and the value inside the box is left alone — re-guarding a
box-commitment point one level down is always sound, provided the
weaker guard is derivable from the stronger one using the surrounding
context (never by trying to strengthen the guard from *inside* the
box, which Z2a above shows is unsound in general).

## Closing section — the two direct questions

**(i) Do the ∃p/∀p definitions need revising, or is the missing piece
a lemma about the current ones?** The current (third-attempt, truncated)
definitions have passed every soundness, base-property, and adequacy
test run against them, and the one remaining gap is not a
counterexample to the definitions but an unproved lemma *about* how
they behave as the revisit-counter grows — a lemma an extensive
semantic search (Table C) has failed to refute at every point that
actually falls inside its stated range. On the evidence collected so
far, no revision to the ∃p/∀p clauses is indicated. This is evidence,
not a proof of the negative: the lemma itself remains open, and a
revision cannot be ruled out if some future proof attempt of it fails
for a structural reason rather than running out of effort.

**(ii) Can the working ∃p be kept while only ∀p is modified?** The two
quantifiers are defined by one mutual recursion: each one's clauses
call the other at smaller measures. Consequently, if ∀p's clauses were
changed, the entire supporting argument — soundness, the adequacy
pair, monotonicity, all of it — would need to be re-proved for *both*
quantifiers together, even if not one character of ∃p's own defining
clauses changed. So: the text of ∃p could be kept verbatim, but none
of the proofs *about* it could simply be carried over unchanged if
∀p's definition changed; textual retention, yes — proof reuse, no.

---
*Sources: `HANDOFF.md`; module docstrings of `LaxLogic/PLLG4Gap.lean`,
`PLLG4.lean`, `PLLG4P.lean`, `PLLG4H.lean`, `PLLG4HCut.lean`,
`PLLG4HComp.lean`, `PLLG4Set.lean`, `PLLG4Space.lean`, `PLLG4Dec.lean`,
`PLLG4UI.lean`, `PLLG4UIAdq.lean`, `PLLG4UIStab.lean`,
`PLLG4UITrunc.lean`; `wip/absorb_base.lean`, `wip/adequacy.lean`,
`wip/packaging.lean`, `wip/final.lean`, `wip/g4ill_ui.lean`,
`wip/refute3.lean`, `wip/refute4.lean`; `docs/ui-endgame.md`;
`docs/g4p-ladder.md`; and the working session's own status log. No git
history was consulted in preparing this note.*
