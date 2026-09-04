# A map of the calculi

This development contains six or seven distinct proof systems for propositional
lax logic, several of them named after their originators and several of them
repairs or extensions of one another. Confusing them is easy and has happened
more than once. This page says, for each: what it is, whose it is, where it
lives, what is proved about it here, and what depends on it.

Read the second table first if you only want to know **which system a given
result is really about**.

---

## The systems

### `LaxND` — natural deduction, the reference system

* **File**: `LaxLogic/PLLNDCore.lean` ("a slime-free core ND system for PLL,
  with conservativity over IPL"), with the formula type in
  `LaxLogic/PLLFormula.lean`.
* **Whose**: standard; the axioms are Fairtlough and Mendler's `◯R`, `◯M`, `◯F`
  (Inf. Comput. 137(1), 1997, p. 5).
* **Status here**: this is the reference notion of provability.
  `Deriv Γ φ := Nonempty (LaxND Γ φ)` is what "PLL proves" means throughout the
  repository. When a paper-level claim is stated, it is stated in these terms.

### `SC` (F&M's GPLL) — the cut-free sequent calculus

* **File**: `LaxLogic/PLLSequent.lean` ("a cut-free sequent calculus for PLL,
  and cut elimination, F&M Theorem 2.6").
* **Whose**: Fairtlough and Mendler, 1997, Figure 2. Iemhoff calls it GPLL.
  It has explicit contraction.
* **Status here**: cut elimination is mechanised, and with it the subformula
  property, the **disjunction property** (`disjunction_property`, F&M Lemma
  2.7(i)) and the admissible inverse of necessitation.
* **Depended on by**: the visibility proofs (`wip/visible.lean`) — the Harrop
  argument is an induction on cut-free `SC` derivations, and the fact that a
  boxed hypothesis can never help produce a disjunction is a feature of this
  calculus's `laxL` rule, whose conclusion succedent must itself be boxed.

### `G3iLL`, `G4iLL` — Iemhoff's calculi

* **Whose**: Rosalie Iemhoff, "Proof Theory for Lax Logic" (arXiv:2209.08976;
  published as a chapter, 2024). `G3iLL` is `G3ip` plus F&M's `R◯`/`L◯`;
  `G4iLL` is the contraction-free, terminating refinement.
* **Status here**: **`G4iLL` is machine-checked INCOMPLETE for PLL**, and
  contraction is not admissible in it — `LaxLogic/PLLG4Gap.lean`. The witness is
  `◯((◯p→r)→◯p), ◯p→r ⇒ r`, derivable in `SC` and rejected by the verified
  `G4` decider; with two copies of `◯p→r` it *is* derivable, which is how
  contraction fails. The shape is Howe's (MSCS 2001, §5), so his conjecture that
  lax logic admits no contraction-free calculus survives its claimed refutation.
* **Consequence, recorded 2026-07-08**: Iemhoff's uniform-interpolation theorem
  for PLL (her Thm 6 / 8.4) routes through her Cor. 8.1, whose adequacy needs
  `G4iLL ≡ PLL`. Craig interpolation is unaffected, its proof using `G3iLL`
  only. This is why the repository builds its own repaired calculus rather than
  importing hers.

### `G4h` / `G4c` — the repaired calculus, and the one everything runs on

* **File**: `LaxLogic/PLLG4H.lean` ("G4iLL″, height-indexed"). `G4h n Γ C` is
  the height-indexed relation; `G4c Γ C := ∃ n, G4h n Γ C` (`PLLG4H.lean:97`).
* **Whose**: ours, repairing `G4iLL`. Revisions 2 and 3: `laxL` is `G3`'s `L◯`;
  `L◯→″` and `R◯→″` keep the full context in premise 1, following the `G3`
  `L⊃` discipline. That discipline is required rather than stylistic — the
  contraction of a doubled `◯φ→ψ` fired by consuming `R◯→` is semantically
  unfixable.
* **Status here**: unconditional and sorry-free — cut (`G4c.cut`), full
  contraction cut-free (`G4c.contract`), completeness (`completeness`,
  `PLLG4HComp.lean:99`) and the equivalences `equiv_sc`, `equiv_nd`, `equiv_tm`.
  So **`G4iLL″ = SC = LaxND = Tm`**: a complete cut-free calculus for PLL with
  all structural rules admissible.
* **Depended on by**: essentially everything computational. The proof terms and
  searcher (`PLLG4Term.lean`, including `G4cTm.find`), the decider
  (`PLLG4Dec.lean`, F&M Theorem 2.8), the countermodel emitter
  (`PLLCountermodelEmit.lean`), the interpolant tables `itpE`/`itpA`
  (`PLLG4UITrunc.lean`) and hence the entire uniform-interpolation tower and the
  nine-round cascade campaign in `wip/`.

### `DerivU` — PCLL, the confluent extension

* **File**: `LaxLogic/PLLConfluentComplete.lean` ("completeness of
  PLL + `◯(A∨B) ⊃ (◯A∨◯B)` for confluent constraint models"); namespace
  `ConfluentU`.
* **Whose**: the axiom and its frame condition are F&M's — Theorem 4.7, second
  bullet, p. 16, and **"mutually confluent" is their term**, matching
  `PLLFrames.MutuallyConfluent` character for character. The mechanisation is
  ours.
* **Status here**: sound and complete for mutually confluent constraint models;
  `force_somehow_iff_of_confluent` (the collapse of the `∀∃` clause to `∃`) is
  also theirs, p. 16.

### `DerivUNoFall` — PCLL plus `¬◯⊥`, the infallible extension

* **File**: `LaxLogic/PLLNoFall.lean`.
* **Whose**: **the completeness result is F&M's** — Theorem 4.7, first bullet,
  p. 16: "PLL + ¬◯*false* is sound and complete for the class of constraint
  models with F = ∅", proved there by the same route (discard the unreachable
  fallible triple from the canonical model).
* **Status here**: `derivUNoFall_iff_infallible_valid`, plus results that are
  ours: `varfree_dichotomy` (the variable-free fragment collapses to `{⊥, ⊤}`;
  the proof uses the axiom exactly once, in the `◯` case, and never uses
  distribution, so it applies verbatim to PLL + `¬◯⊥`), and `exUI` / `allUI`
  (uniform interpolation into the variable-free fragment, trivial once that
  fragment is two elements — the ≥ 2-variable problem is deliberately not
  asserted).
* **Naming caveat, flagged 2026-08-07**: the theorem name says
  "infallible_valid" but the model class is *mutually confluent **and***
  infallible, which is strictly smaller than F&M's `F = ∅` class — on the plain
  `F = ∅` class distribution genuinely fails. F&M state their two bullets
  separately and never the conjunction; ours is a routine merge of their two
  specialisations. The name should be corrected.

### The term calculus and reduction

Not a logic, but frequently confused with one. `LaxLogic/PLLG4Term.lean` gives
proof terms for `G4c` and the searcher. Separately,
`LaxLogic/PLLReducibility.lean` and `LaxLogic/PLLTopTop.lean` concern the
*proof-term* calculus of `LaxND` and its reduction: strong normalisation of the
full interleaved reduction (β for every connective plus `let`-assoc) via
Lindley–Stark `⊤⊤`-lifting. That is a result about terms, not about derivability.

---

## Which system is a given result really about?

| result | system | file |
|---|---|---|
| "PLL proves φ" | `LaxND` (`Deriv`) | `PLLNDCore.lean` |
| cut elimination, disjunction property | `SC` | `PLLSequent.lean` |
| decidability (F&M Thm 2.8) | `G4c` | `PLLG4Dec.lean` |
| countermodels, `checkB` certificates | `G4c` + constraint models | `PLLCountermodelEmit.lean` |
| the interpolant tables `itpE` / `itpA` | `G4c` | `PLLG4UITrunc.lean` |
| the uniform-interpolation tower and the cascade campaign | `G4c` | `wip/absorb_base.lean` and successors |
| join-primality / visibility proofs | `SC` (Harrop induction) | `wip/visible.lean` |
| the `◯`-depth hierarchy | `LaxND` + constraint models | `wip/depth*.lean` |
| distribution, confluence | `DerivU` | `PLLConfluentComplete.lean` |
| infallible collapse | `DerivUNoFall` | `PLLNoFall.lean` |
| strong normalisation | proof terms of `LaxND` | `PLLTopTop.lean` |

---

## Provenance summary

Ours: the `G4iLL` incompleteness counterexample; the repaired calculus `G4c`
with its cut, contraction, completeness and equivalences; the decider; the
variable-free collapse under `¬◯⊥`; and everything about the structure of the
closed fragment RN(◯,{}) — the Rieger–Nishimura ladder embedded by `p ↦ ◯⊥`,
the families, the gap antichain, the descending chain with no floor, the
visibility proofs, and the strict `◯`-depth hierarchy. None of that appears in
F&M 1997, which contains no "Rieger", no "variable-free", no "closed fragment"
and no interpolation at all.

Theirs: the axioms and both sequent presentations; cut elimination; the
constraint-model semantics with fallible worlds and the `∀∃` clause for `◯`
(our forcing definition reproduces theirs field for field); soundness and
completeness; mutual confluence as the frame condition for distribution and its
completeness theorem; and the infallible completeness theorem. Their stated open
problems all concern Circuit-PLL expressibility — none concern the closed
fragment, interpolation, linearity or complexity.
