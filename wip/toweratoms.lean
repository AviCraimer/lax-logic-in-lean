import wip.towercircle

/-!
# `toweratoms` — the `atomFree` side condition, reduced to one containment

`TowerPin.eRow_settled` / `aRow_settled` and `TowerCircle`'s `_nf` variants
all carry the hypothesis `atomFree (eTower φ b') = true`.  The library
supplies `itp_pfree` (`p ∉ atoms (itpE p S f b Γ)`) but not the
containment `atoms (itpE p S f b Γ) ⊆ atoms Γ`, so the hypothesis stays
explicit (`§54` follow-up (c)).

This module makes the gap exactly one named statement, and discharges
everything on either side of it:

* `atomFree_iff` — the bridge between the `Bool` predicate `atomFree`
  (`LaxLogic/PLLLaxInfinite.lean`) and the `Finset String` of `atoms`
  (`LaxLogic/PLLG4Space.lean`), which the library also lacked;
* `ItpAtomsBounded` — the containment, in the pointwise form the induction
  will produce: an atom absent from every hypothesis is absent from the
  table's output;
* `atomFree_eTower_of_bounded` — the reduction: `ItpAtomsBounded` plus
  `itp_pfree` gives `atomFree (eTower φ b)` for every `φ` whose only atom
  is `p`, hence discharges the hypothesis of every ∃-row of the battery;
  `atomFree_aTower_of_bounded` likewise on the ∀-side;
* `phiSpade_atoms`, `spade_circle_of_bounded` — the instance at `φ♠`: the
  circle closes from `ItpAtomsBounded` and the *forward* search
  certificate alone.

`ItpAtomsBounded` is **OPEN** here — stated, not proved.  It is not a
`sorry`: nothing below claims it, everything below is an implication with
it as an explicit hypothesis.  Its proof is the induction that mirrors
`itp_pfree` (`LaxLogic/PLLG4UITrunc.lean`:1961, ≈500 lines) clause for
clause: the only clauses that put an atom into the output are the `prop q`
filter-map and the `.ifThen (.prop q) B` rule (and, on the ∀-side, the
`prop q` goal), and in each the atom comes from a member of `Γ` resp. `C`;
every other clause is structural, and the recursive calls only ever extend
`Γ` by *subformulas* of its members, so the hypothesis is preserved.
-/

open PLLFormula PLLND PLLND.RNEmbed PLLND.SemUI PLLND.Search
open PLLND.LaxInfinite (atomFree)

namespace TowerAtoms

/-! ## §1  `atomFree` is emptiness of `atoms` -/

/-- The two ways the library says "variable-free" agree. -/
theorem atomFree_iff : ∀ φ : PLLFormula, atomFree φ = true ↔ ∀ x, x ∉ φ.atoms
  | .prop a => by
      constructor
      · intro h; exact absurd h (by simp [atomFree])
      · intro h; exact absurd (h a (by simp [PLLFormula.atoms])) (by simp)
  | .falsePLL => by simp [atomFree, PLLFormula.atoms]
  | .and A B => by
      rw [atomFree, Bool.and_eq_true, atomFree_iff A, atomFree_iff B]
      constructor
      · rintro ⟨hA, hB⟩ x hx
        rcases PLLFormula.mem_atoms_and.mp hx with h | h
        · exact hA x h
        · exact hB x h
      · intro h
        exact ⟨fun x hx => h x (PLLFormula.mem_atoms_and.mpr (Or.inl hx)),
          fun x hx => h x (PLLFormula.mem_atoms_and.mpr (Or.inr hx))⟩
  | .or A B => by
      rw [atomFree, Bool.and_eq_true, atomFree_iff A, atomFree_iff B]
      constructor
      · rintro ⟨hA, hB⟩ x hx
        rcases PLLFormula.mem_atoms_or.mp hx with h | h
        · exact hA x h
        · exact hB x h
      · intro h
        exact ⟨fun x hx => h x (PLLFormula.mem_atoms_or.mpr (Or.inl hx)),
          fun x hx => h x (PLLFormula.mem_atoms_or.mpr (Or.inr hx))⟩
  | .ifThen A B => by
      rw [atomFree, Bool.and_eq_true, atomFree_iff A, atomFree_iff B]
      constructor
      · rintro ⟨hA, hB⟩ x hx
        rcases PLLFormula.mem_atoms_ifThen.mp hx with h | h
        · exact hA x h
        · exact hB x h
      · intro h
        exact ⟨fun x hx => h x (PLLFormula.mem_atoms_ifThen.mpr (Or.inl hx)),
          fun x hx => h x (PLLFormula.mem_atoms_ifThen.mpr (Or.inr hx))⟩
  | .somehow A => by
      rw [atomFree, atomFree_iff A]
      constructor
      · intro h x hx; exact h x (by rwa [PLLFormula.atoms_somehow] at hx)
      · intro h x hx; exact h x (by rwa [PLLFormula.atoms_somehow])

/-! ## §2  The open containment -/

/-- **OPEN** (`§54` follow-up (c)).  The truncated quantifier tables
introduce no atoms of their own: an atom absent from every hypothesis is
absent from the output, at every space, fuel and budget.  (`S` is used by
`itpE`/`itpA` only in membership *tests* — it never contributes a formula
— which is why it does not appear in the hypothesis.) -/
def ItpAtomsBounded : Prop :=
  (∀ (p : String) (S : Finset PLLFormula) (f b : Nat) (Γ : List PLLFormula)
      (x : String), (∀ F ∈ Γ, x ∉ F.atoms) → x ∉ (itpE p S f b Γ).atoms) ∧
  (∀ (p : String) (S : Finset PLLFormula) (f b : Nat) (Γ : List PLLFormula)
      (C : PLLFormula) (x : String), (∀ F ∈ Γ, x ∉ F.atoms) → x ∉ C.atoms →
      x ∉ (itpA p S f b Γ C).atoms)

/-! ## §3  The reduction -/

/-- **The ∃-side hypothesis, discharged.**  For a subject whose only atom
is the eliminated `p`, `ItpAtomsBounded` kills every other atom and
`itp_pfree` kills `p`. -/
theorem atomFree_eTower_of_bounded (H : ItpAtomsBounded) {φ : PLLFormula}
    (hφ : ∀ x, x ≠ pv → x ∉ φ.atoms) (b : Nat) :
    atomFree (TowerKit.eTower φ b) = true := by
  refine (atomFree_iff _).mpr fun x hx => ?_
  by_cases hxp : x = pv
  · subst hxp
    exact (itp_pfree pv (TowerKit.pieceClosure φ) (TowerKit.eFuel φ)).1 b [φ] hx
  · refine H.1 pv (TowerKit.pieceClosure φ) (TowerKit.eFuel φ) b [φ] x ?_ hx
    intro F hF
    rw [List.mem_singleton] at hF
    subst hF
    exact hφ x hxp

/-- **The ∀-side hypothesis, discharged.** -/
theorem atomFree_aTower_of_bounded (H : ItpAtomsBounded) {C : PLLFormula}
    (hC : ∀ x, x ≠ pv → x ∉ C.atoms) (b : Nat) :
    atomFree (TowerKit.aTower C b) = true := by
  refine (atomFree_iff _).mpr fun x hx => ?_
  by_cases hxp : x = pv
  · subst hxp
    exact (itp_pfree pv (TowerKit.pieceClosure C) (TowerKit.aFuel C)).2 b [] C hx
  · exact H.2 pv (TowerKit.pieceClosure C) (TowerKit.aFuel C) b [] C x
      (by intro F hF; cases hF) (hC x hxp) hx

/-! ## §4  The instance at `φ♠` -/

/-- `φ♠`'s only atom is `p`. -/
theorem phiSpade_atoms : ∀ x, x ≠ pv → x ∉ phiSpade.atoms := by
  intro x hx h
  simp only [phiSpade, nt, oBot] at h
  simp only [PLLFormula.atoms_ifThen, PLLFormula.atoms_or,
    PLLFormula.atoms_and, PLLFormula.atoms_somehow, PLLFormula.atoms_false,
    PLLFormula.atoms_prop, Finset.union_empty, Finset.empty_union,
    Finset.union_self, Finset.mem_singleton] at h
  exact hx h

/-- **The `φ♠` circle, from the forward certificate alone.**  Given
`ItpAtomsBounded`, the backward direction is a priori (`§53`'s
`postInterp_phiSpade` plus `itp_sound`), so a single certified search
`nf T♠b ⊢ ψ♣` closes the circle — and `itp_budget_mono_le` carries it to
every budget above `b`, the prescribed `579` included. -/
theorem spade_circle_of_bounded (H : ItpAtomsBounded) {b b' : Nat} (hb : b ≤ b')
    (hfwd : G4c [nf (TowerKit.eTower phiSpade b)] psiClub) :
    Interd (TowerKit.eTower phiSpade b') psiClub :=
  TowerCircle.spade_circle_up hb
    (atomFree_eTower_of_bounded H phiSpade_atoms b') hfwd

/-! ## §5  Axiom audits -/

/-- info: 'TowerAtoms.atomFree_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms atomFree_iff

/-- info: 'TowerAtoms.phiSpade_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiSpade_atoms

/-- info: 'TowerAtoms.atomFree_eTower_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms atomFree_eTower_of_bounded

/-- info: 'TowerAtoms.spade_circle_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spade_circle_of_bounded

end TowerAtoms
