import wip.towerpin
import wip.nfcorrect
import wip.phispade

/-!
# `towercircle` — the `nf`-mediated tower verdicts, at kernel grade

`wip/towertest.lean` reads most of its verdicts off `nf`-normalised tower
outputs: the raw tables are 10–100× larger than their normal forms
(`88 202 → 391` nodes for `φ♠` at `b = 1`), so the search is only feasible
after normalisation.  Until now that made those rows *probe-level* claims:
the search certificate concerned `nf T`, and nothing in the library said
what `nf T` had to do with `T`.

`wip/nfcorrect.lean` closes that: `nf_interd : ∀ φ, Interd φ (nf φ)`,
axiom-clean.  This module cuts it into the tower's row lemmas, so an
`nf`-level certificate settles the raw-table row, and records the `φ♠`
circle.

## §1  `nf`-mediated rows

`TowerPin.eRow_settled` / `aRow_settled` take a certificate about the raw
table.  The `_nf` and `_nfIter` variants below take one about the normal
form and cut through `nf_interd`; they are otherwise identical, the same
`itp_budget_mono_le` transfer to the prescribed budget included.

## §2  The `φ♠` circle

`§53` proved `postInterp_phiSpade : IsPostInterp φ♠ ψ♣` with
`ψ♣ = ¬¬◯⊥ ⊃ ◯⊥`; `§54` computed the tower's `b = 1` answer `T♠1`.  The
circle closes iff `Interd T♠1 ψ♣`.  Two facts are recorded:

* the **a-priori** direction `ψ♣ ⊢ T♠b`, at *every* budget, from
  `itp_sound` and the minimality clause of `IsPostInterp` — modulo the
  `atomFree` side condition that `IsPostInterp` carries and `itp_pfree`
  does not supply (see `wip/towerpin.lean`'s module docstring, and §3
  below);
* the **composite** `spade_circle`, which turns the two search
  certificates on `nf T♠1` into `Interd T♠1 ψ♣` with no side condition at
  all — the normalisation is now free, and `ψ♣`'s own atom-freeness is
  not needed either because the certificate supplies both directions.

## §3  The remaining gap

`atomFree (itpE p S f b Γ)` is still hypothetical.  What the library has
is `itp_pfree` (`p ∉ atoms`); what is wanted is the containment
`atoms (itpE p S f b Γ) ⊆ atomsL Γ`, whose induction mirrors `itp_pfree`
clause for clause (≈500 lines) — see the closing remarks.  `spade_circle`
is stated so as not to need it.
-/

open PLLFormula PLLND PLLND.RNEmbed PLLND.SemUI PLLND.Search
open PLLND.LaxInfinite (atomFree)

namespace TowerCircle

/-! ## §1  Rows settled from an `nf`-level certificate -/

/-- **∃-row settled from a certificate about the normal form.**  Same
statement as `TowerPin.eRow_settled`, except that the search certificate
concerns `nf (eTower φ b)` — the object the probe actually decides. -/
theorem eRow_settled_nf {φ v : PLLFormula} (hv : IsPostInterp φ v) {b b' : Nat}
    (hb : b ≤ b') (ha : atomFree (TowerKit.eTower φ b') = true)
    (htest : G4c [nf (TowerKit.eTower φ b)] v) :
    Interd (TowerKit.eTower φ b') v :=
  TowerPin.eRow_settled hv hb ha (g4c_of_nf htest)

/-- **∀-row settled from a certificate about the normal form.** -/
theorem aRow_settled_nf {C w : PLLFormula} (hw : IsPreInterp C w) {b b' : Nat}
    (hb : b ≤ b') (ha : atomFree (TowerKit.aTower C b') = true)
    (htest : G4c [w] (nf (TowerKit.aTower C b))) :
    Interd (TowerKit.aTower C b') w :=
  TowerPin.aRow_settled hw hb ha (g4c_to_nf htest)

/-- The same, for a certificate about the `n`-fold iterate — the form
`wip/towertest.lean`'s `nfStar` produces (it reports its `n`). -/
theorem eRow_settled_nfIter {φ v : PLLFormula} (hv : IsPostInterp φ v)
    {b b' n : Nat} (hb : b ≤ b')
    (ha : atomFree (TowerKit.eTower φ b') = true)
    (htest : G4c [nfIter n (TowerKit.eTower φ b)] v) :
    Interd (TowerKit.eTower φ b') v :=
  TowerPin.eRow_settled hv hb ha (g4c_of_nfIter htest)

/-- The same, `n`-fold, on the ∀-side. -/
theorem aRow_settled_nfIter {C w : PLLFormula} (hw : IsPreInterp C w)
    {b b' n : Nat} (hb : b ≤ b')
    (ha : atomFree (TowerKit.aTower C b') = true)
    (htest : G4c [w] (nfIter n (TowerKit.aTower C b))) :
    Interd (TowerKit.aTower C b') w :=
  TowerPin.aRow_settled hw hb ha (g4c_to_nfIter htest)

/-! ## §2  The `φ♠` circle -/

/-- **A priori, at every budget**: `ψ♣ ⊢ T♠b`.  `φ♠ ⊢ T♠b` is `itp_sound`,
`T♠b` is variable-free by hypothesis, and `ψ♣` is the *least* variable-free
consequence of `φ♠` (`postInterp_phiSpade`, §53).  This is the direction the
probe does not have to find — the search on it is a cross-check. -/
theorem psiClub_to_eTower_phiSpade (b : Nat)
    (ha : atomFree (TowerKit.eTower phiSpade b) = true) :
    Deriv [psiClub] (TowerKit.eTower phiSpade b) :=
  TowerPin.eTower_free_of_atomFree postInterp_phiSpade b ha

/-- **The circle, from the two `nf`-level certificates.**  No side
condition: `nf_interd` supplies the normalisation step in both directions,
and both directions are certificates, so `atomFree` never enters. -/
theorem spade_circle {b : Nat}
    (hfwd : G4c [nf (TowerKit.eTower phiSpade b)] psiClub)
    (hbwd : G4c [psiClub] (nf (TowerKit.eTower phiSpade b))) :
    Interd (TowerKit.eTower phiSpade b) psiClub :=
  ⟨G4c.equiv_nd.mp (g4c_of_nf hfwd), G4c.equiv_nd.mp (g4c_to_nf hbwd)⟩

/-- The same from the `n`-fold iterate. -/
theorem spade_circle_nfIter {b n : Nat}
    (hfwd : G4c [nfIter n (TowerKit.eTower phiSpade b)] psiClub)
    (hbwd : G4c [psiClub] (nfIter n (TowerKit.eTower phiSpade b))) :
    Interd (TowerKit.eTower phiSpade b) psiClub :=
  ⟨G4c.equiv_nd.mp (g4c_of_nfIter hfwd), G4c.equiv_nd.mp (g4c_to_nfIter hbwd)⟩

/-- **One direction suffices, given atom-freeness.**  If the *forward*
certificate `nf T♠b ⊢ ψ♣` is found, the backward direction is the a-priori
one, so the circle closes; and by `itp_budget_mono_le` it closes at every
budget above `b` — the prescribed one (`579` for `φ♠`) included. -/
theorem spade_circle_up {b b' : Nat} (hb : b ≤ b')
    (ha : atomFree (TowerKit.eTower phiSpade b') = true)
    (hfwd : G4c [nf (TowerKit.eTower phiSpade b)] psiClub) :
    Interd (TowerKit.eTower phiSpade b') psiClub :=
  eRow_settled_nf postInterp_phiSpade hb ha hfwd

/-! ## §3  Axiom audits -/

/-- info: 'TowerCircle.eRow_settled_nf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eRow_settled_nf

/-- info: 'TowerCircle.aRow_settled_nf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aRow_settled_nf

/-- info: 'TowerCircle.spade_circle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spade_circle

/-- info: 'TowerCircle.psiClub_to_eTower_phiSpade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms psiClub_to_eTower_phiSpade

/-- info: 'TowerCircle.spade_circle_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spade_circle_up

end TowerCircle
