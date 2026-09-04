import wip.towerkit
import wip.postui
import wip.coverfail
import wip.mixedfail
import wip.paramfork

/-!
# `towerpin` — the audit half of the tower-vs-ladder experiment

Two things are pinned here, both sorry-free:

**§1  The transcriptions are the originals.**  `wip/towerkit.lean` re-declares
the battery formulas because an executable root cannot import
`wip/postui.lean` (its closure reaches `wip.rnc_probe`, which declares a
root-level `main`).  This module is an ordinary library module, so it *can*
import both, and checks every transcription by `rfl`.

**§2  The verdict transfers upward in the budget.**  The tower's packaged
quantifiers run at budget `kcap (pieceClosure φ) + 1` — `339` for `φ★`,
`579` for `φ♣`/`φ♠` — and the table's *output* grows by about an order of
magnitude per budget step, so the prescribed budget denotes a formula far
too large to write down, let alone search.  What makes the experiment
conclusive anyway is `itp_budget_mono_le`
(`LaxLogic/PLLG4UITrunc.lean`:1907, axiom-clean): on the ∃-side a larger
budget gives a *stronger* formula, on the ∀-side a *weaker* one.  So a
certified `T b ⊢ v` at a small budget `b` propagates to every budget above
it, the prescribed one included (`eTower_test_up`), and dually on the ∀-side
(`aTower_test_up`).

The converse direction (`v ⊢ T b`) is free at *every* budget from
`itp_sound` plus minimality of the semantic value — except that
`IsPostInterp`'s minimality clause is stated for `atomFree` formulas while
`itp_pfree` only delivers p-freeness, so it is recorded here as
`eTower_free_of_atomFree`, with atom-freeness as an explicit hypothesis.
(For every row of the battery the probe `towertest` computes the tower's
answer and it is visibly variable-free; the general lemma
"`atoms (itpE p S f b Γ) ⊆ atoms S ∪ atoms Γ`" is not in the library.)
-/

open PLLFormula PLLND PLLND.RNEmbed PLLND.SemUI
open PLLND.LaxInfinite (atomFree)

namespace TowerPin

/-! ## §1  The transcriptions are the originals -/

theorem nt_eq : TowerKit.nt = PLLND.RNEmbed.nt := rfl
theorem exLadder_eq : TowerKit.exLadder = PLLND.RNEmbed.exLadder := rfl
theorem phiMix_eq : TowerKit.phiMix = PLLND.RNEmbed.phiMix := rfl
theorem wemP_eq : TowerKit.wemP = PLLND.RNEmbed.wemP := rfl
theorem phiStar_eq : TowerKit.phiStar = PLLND.RNEmbed.phiStar := rfl
theorem phiDia_eq : TowerKit.phiDia = PLLND.RNEmbed.phiDia := rfl
theorem phiClub_eq : TowerKit.phiClub = PLLND.RNEmbed.phiClub := rfl
theorem psiClub_eq : TowerKit.psiClub = PLLND.RNEmbed.psiClub := rfl
theorem phiSpade_eq : TowerKit.phiSpade = PLLND.RNEmbed.phiSpade := rfl

/-! ## §2  Upward transfer of a low-budget verdict

Everything below is stated for the raw tables `itpE`/`itpA` at a fixed
space and fuel, so nothing here has to *evaluate* a table. -/

/-- **∃-side upward transfer.**  A derivation of `itpE … b Γ ⊢ ψ` at one
budget gives one at every larger budget: the larger budget's value is the
stronger formula (`itp_budget_mono_le`). -/
theorem itpE_test_up (p : String) (S : Finset PLLFormula) (f : Nat)
    {b b' : Nat} (hb : b ≤ b') (Γ : List PLLFormula) {ψ : PLLFormula}
    (h : G4c [itpE p S f b Γ] ψ) : G4c [itpE p S f b' Γ] ψ :=
  G4c.cut ((itp_budget_mono_le p S hb f).1 Γ)
    ((h.weaken (itpE p S f b' Γ)).perm (List.Perm.swap _ _ _))

/-- **∀-side upward transfer.**  A derivation of `ψ ⊢ itpA … b Γ C` at one
budget gives one at every larger budget: the larger budget's value is the
weaker formula. -/
theorem itpA_test_up (p : String) (S : Finset PLLFormula) (f : Nat)
    {b b' : Nat} (hb : b ≤ b') (Γ : List PLLFormula) (C : PLLFormula)
    {ψ : PLLFormula} (h : G4c [ψ] (itpA p S f b Γ C)) :
    G4c [ψ] (itpA p S f b' Γ C) :=
  G4c.cut h ((((itp_budget_mono_le p S hb f).2 Γ C).weaken ψ).perm
    (List.Perm.swap _ _ _))

/-- The same, for `TowerKit.eTower` (the packaged instantiation: space
`pieceClosure φ`, context `[φ]`, prescribed fuel). -/
theorem eTower_test_up {φ ψ : PLLFormula} {b b' : Nat} (hb : b ≤ b')
    (h : G4c [TowerKit.eTower φ b] ψ) : G4c [TowerKit.eTower φ b'] ψ :=
  itpE_test_up pv (TowerKit.pieceClosure φ) (TowerKit.eFuel φ) hb [φ] h

/-- The same, for `TowerKit.aTower`. -/
theorem aTower_test_up {C ψ : PLLFormula} {b b' : Nat} (hb : b ≤ b')
    (h : G4c [ψ] (TowerKit.aTower C b)) : G4c [ψ] (TowerKit.aTower C b') :=
  itpA_test_up pv (TowerKit.pieceClosure C) (TowerKit.aFuel C) hb [] C h

/-! ### The free directions

`itp_sound` gives `Γ ⊢ itpE … Γ` and `itpA … Γ C ⊢ C` at every fuel and
budget, with no side conditions; `G4c.equiv_nd` moves between the
calculus and natural deduction, which is where the ladder's `Deriv` lives. -/

/-- **∀-side, free**: the tower's ∀-answer is always an antecedent of `C`,
hence (being p-free — modulo `atomFree`, see the module docstring) always
below the pre-interpolant. -/
theorem aTower_sound (C : PLLFormula) (b : Nat) :
    Deriv [TowerKit.aTower C b] C := by
  refine G4c.equiv_nd.mp (G4c.iff_set.mpr ?_)
  have h := (itp_sound pv (TowerKit.pieceClosure C) (TowerKit.aFuel C)).2
    b [] C
  simpa [TowerKit.aTower] using h

/-- **∃-side, free**: `φ ⊢ ∃-answer`, at every budget. -/
theorem eTower_sound (φ : PLLFormula) (b : Nat) :
    Deriv [φ] (TowerKit.eTower φ b) :=
  G4c.equiv_nd.mp (G4c.iff_set.mpr
    ((itp_sound pv (TowerKit.pieceClosure φ) (TowerKit.eFuel φ)).1 b [φ]))

/-- **∃-side minimality, free given atom-freeness**: the pinned value `v` of
`∃p.φ` proves the tower's answer at *every* budget. -/
theorem eTower_free_of_atomFree {φ v : PLLFormula} (hv : IsPostInterp φ v)
    (b : Nat) (ha : atomFree (TowerKit.eTower φ b) = true) :
    Deriv [v] (TowerKit.eTower φ b) :=
  hv.2.2 _ ha (eTower_sound φ b)

/-- **∀-side maximality, free given atom-freeness**: the tower's ∀-answer
proves the pinned value `w` of `∀p.C`, at *every* budget. -/
theorem aTower_free_of_atomFree {C w : PLLFormula} (hw : IsPreInterp C w)
    (b : Nat) (ha : atomFree (TowerKit.aTower C b) = true) :
    Deriv [TowerKit.aTower C b] w :=
  hw.2.2 _ ha (aTower_sound C b)

/-! ### The packaged conclusion

Combining: one certified search at a small budget settles the row at
**every** budget from there up — in particular at the prescribed
`kcap (pieceClosure φ) + 1`. -/

/-- **∃-row settled at every budget above `b`.**  Hypotheses: the pinned
semantic value `v`; a certificate `T b ⊢ v` at the small budget `b`;
atom-freeness of the tower's answer at the target budget `b'`. -/
theorem eRow_settled {φ v : PLLFormula} (hv : IsPostInterp φ v) {b b' : Nat}
    (hb : b ≤ b') (ha : atomFree (TowerKit.eTower φ b') = true)
    (htest : G4c [TowerKit.eTower φ b] v) :
    Interd (TowerKit.eTower φ b') v :=
  ⟨G4c.equiv_nd.mp (eTower_test_up hb htest),
    eTower_free_of_atomFree hv b' ha⟩

/-- **∀-row settled at every budget above `b`.** -/
theorem aRow_settled {C w : PLLFormula} (hw : IsPreInterp C w) {b b' : Nat}
    (hb : b ≤ b') (ha : atomFree (TowerKit.aTower C b') = true)
    (htest : G4c [w] (TowerKit.aTower C b)) :
    Interd (TowerKit.aTower C b') w :=
  ⟨aTower_free_of_atomFree hw b' ha,
    G4c.equiv_nd.mp (aTower_test_up hb htest)⟩

/-! ## §3  Axiom audits

None of §1–§2 touches `wip/absorb_base.lean`: `itp_budget_mono_le`,
`itp_sound` and `itp_pfree` all live in the axiom-clean
`LaxLogic/PLLG4UITrunc.lean`, and the calculus bridge `G4c.equiv_nd` is
unconditional (`LaxLogic/PLLG4HComp.lean`).  So the transfer apparatus is
independent of the tower's single open lemma `cascade_low_pos_box`. -/

/-- info: 'TowerPin.eRow_settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eRow_settled

/-- info: 'TowerPin.aRow_settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aRow_settled

/-- info: 'TowerPin.phiStar_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms phiStar_eq

end TowerPin
