import wip.boxSndTight
import wip.cascadeBox

/-!
# The three pair-floor interfaces, reduced by goal shape

`wip/cascadeBox.lean` proves the ◯-involving low-budget descent (`cascade_box`)
modulo four open interfaces.  Three of them — `GammaPairFloorA`,
`GammaPairFloorBox`, `JumpPairFloor` — are the *same* branch shape at target budget
`1` with three different first components, and `wip/boxSndTight.lean` closes all
three at two goal shapes:

* an **unboxed atom** goal `q ≠ p` (`floorAny_atom`: neither ambient nor first
  component is used);
* a **boxed atom** goal `◯q`, `q ≠ p` (`floorBox_of_grownAmb` plus the interface's
  own way of firing the ambient).

A fourth shape is vacuous: a `∨`-shaped goal is excluded by `g ∈ S` over a `∨`-free
space.

This file turns that into a machine-checked reduction **against the interfaces as
`wip/cascadeBox.lean` states them**.  Each theorem says: the interface follows from
its own restriction to the goal shapes the atom machinery does not reach.  So the
residue of the three floor interfaces is exactly

    g = prop p ,  ⊥ ,  C₁ ∧ C₂ ,  C₁ ⊃ C₂ ,  ◯(prop p) ,  ◯D with D not an atom

over a `∨`-free space — nothing else.  Nothing here is a `sorry`, and nothing here
touches `wip/cascadeBox.lean`'s stub section, so the audits below are
`sorryAx`-free even though the imported file has stubs.
-/

open PLLFormula

namespace PLLND
namespace FloorGoals

open BoxSndTight

/-- The goal shapes the atom machinery reaches: an atom `≠ p`, or a boxed atom
`≠ p`.  A residue hypothesis is the interface with these two excluded. -/
def NotAtomic (p : String) (g : PLLFormula) : Prop :=
  (∀ q : String, q ≠ p → g ≠ prop q) ∧
  (∀ q : String, q ≠ p → g ≠ (prop q).somehow)

/-- `GammaPairFloorBox` restricted to the non-atomic goal shapes. -/
def GammaBoxFloorResidue (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl : Nat) (Γ : List PLLFormula) (A B g : PLLFormula)
    (Δ : List PLLFormula),
    NotAtomic p g →
    F + 1 ≤ fl →
    A.somehow.ifThen B ∈ Γ → A.somehow.ifThen B ∈ S →
    B ∈ S → B ∉ Γ → g ∈ S → (∀ X ∈ Γ, X ∈ S) →
    (∀ (Γ' : List PLLFormula) (g' : PLLFormula) (Δ' : List PLLFormula),
      defect S Γ' < defect S Γ → g' ∈ S → (∀ X ∈ Γ', X ∈ S) →
      G4c Δ' (itpE p S fl 2 Γ') →
      G4c Δ' (itpA p S (F + 1) 2 Γ' g') →
      G4c Δ' (itpA p S fl 1 Γ' g')) →
    G4c Δ (itpE p S (fl + 1) 2 Γ) →
    G4c Δ (((itpE p S (F + 1) 1 Γ).ifThen
      (itpA p S (F + 1) 1 Γ A.somehow)).somehow) →
    G4c Δ (itpA p S (F + 1) 2 (B :: Γ) g) →
    G4c Δ (orAll (itpAoth p S fl 1 Γ g))

/-- `GammaPairFloorA` restricted to the non-atomic goal shapes. -/
def GammaAFloorResidue (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl : Nat) (Γ : List PLLFormula) (A B g : PLLFormula)
    (Δ : List PLLFormula),
    NotAtomic p g →
    F + 1 ≤ fl →
    A.somehow.ifThen B ∈ Γ → A.somehow.ifThen B ∈ S →
    B ∈ S → B ∉ Γ → g ∈ S → (∀ X ∈ Γ, X ∈ S) →
    (∀ (Γ' : List PLLFormula) (g' : PLLFormula) (Δ' : List PLLFormula),
      defect S Γ' < defect S Γ → g' ∈ S → (∀ X ∈ Γ', X ∈ S) →
      G4c Δ' (itpE p S fl 2 Γ') →
      G4c Δ' (itpA p S (F + 1) 2 Γ' g') →
      G4c Δ' (itpA p S fl 1 Γ' g')) →
    G4c Δ (itpE p S (fl + 1) 2 Γ) →
    G4c Δ (itpA p S (F + 1) 1 Γ A) →
    G4c Δ (itpA p S (F + 1) 2 (B :: Γ) g) →
    G4c Δ (orAll (itpAoth p S fl 1 Γ g))

/-- `JumpPairFloor` restricted to the non-atomic goal shapes. -/
def JumpFloorResidue (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl : Nat) (Γ : List PLLFormula) (A B D g : PLLFormula)
    (Δ : List PLLFormula),
    NotAtomic p g →
    F + 1 ≤ fl →
    (A.ifThen B).ifThen D ∈ Γ → (A.ifThen B).ifThen D ∈ S →
    B.ifThen D ∈ Γ → D ∈ S → D ∉ Γ → g ∈ S → (∀ X ∈ Γ, X ∈ S) →
    (∀ (Γ' : List PLLFormula) (g' : PLLFormula) (Δ' : List PLLFormula),
      defect S Γ' < defect S Γ → g' ∈ S → (∀ X ∈ Γ', X ∈ S) →
      G4c Δ' (itpE p S fl 2 Γ') →
      G4c Δ' (itpA p S (F + 1) 2 Γ' g') →
      G4c Δ' (itpA p S fl 1 Γ' g')) →
    G4c Δ (itpE p S (fl + 1) 2 Γ) →
    G4c Δ ((itpE p S (F + 1) 1 Γ).ifThen
      (itpA p S (F + 1) 1 Γ (A.ifThen B))) →
    G4c Δ (itpA p S (F + 1) 2 (D :: Γ) g) →
    G4c Δ (orAll (itpAoth p S fl 1 Γ g))

/-! ## The goal-shape dispatch

Six constructors.  `or` is vacuous over a `∨`-free space (`g ∈ S`); `prop q` splits
on `q = p` and `somehow D` on whether `D` is an atom `≠ p`; everything else goes to
the residue. -/

/-- Dispatch skeleton: given the two atomic cases and the residue, cover `g`. -/
private theorem dispatch (p : String) {S : Finset PLLFormula}
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {g : PLLFormula} (hgS : g ∈ S)
    {C : Prop}
    (hatom : ∀ q : String, q ≠ p → g = prop q → C)
    (hbox : ∀ q : String, q ≠ p → g = (prop q).somehow → C)
    (hres : NotAtomic p g → C) : C := by
  cases hg : g with
  | prop q' =>
      by_cases hqp : q' = p
      · subst hqp
        refine hres ⟨?_, ?_⟩
        · intro q hq hcontra
          apply hq
          have h : (prop q' : PLLFormula) = prop q := hg ▸ hcontra
          injection h with h'
          exact h'.symm
        · intro q _ hcontra
          exact absurd (hg ▸ hcontra) (by simp)
      · exact hatom q' hqp hg
  | falsePLL =>
      exact hres ⟨fun q _ h => absurd (hg ▸ h) (by simp),
        fun q _ h => absurd (hg ▸ h) (by simp)⟩
  | and C₁ C₂ =>
      exact hres ⟨fun q _ h => absurd (hg ▸ h) (by simp),
        fun q _ h => absurd (hg ▸ h) (by simp)⟩
  | ifThen C₁ C₂ =>
      exact hres ⟨fun q _ h => absurd (hg ▸ h) (by simp),
        fun q _ h => absurd (hg ▸ h) (by simp)⟩
  | or C₁ C₂ => exact absurd (hg ▸ hgS) (hOr C₁ C₂)
  | somehow D =>
      cases hD : D with
      | prop q' =>
          by_cases hqp : q' = p
          · subst hqp
            refine hres ⟨fun q _ h => absurd (hg ▸ h) (by simp), ?_⟩
            intro q hq hcontra
            apply hq
            have h : ((prop q' : PLLFormula)).somehow = (prop q).somehow := by
              have h0 := hg ▸ hcontra
              rw [hD] at h0
              exact h0
            injection h with h1
            injection h1 with h2
            exact h2.symm
          · exact hbox q' hqp (by rw [hg, hD])
      | falsePLL =>
          exact hres ⟨fun q _ h => absurd (hg ▸ h) (by simp),
            fun q _ h => absurd (by rw [hD] at hg; exact hg ▸ h) (by simp)⟩
      | and _ _ =>
          exact hres ⟨fun q _ h => absurd (hg ▸ h) (by simp),
            fun q _ h => absurd (by rw [hD] at hg; exact hg ▸ h) (by simp)⟩
      | or _ _ =>
          exact hres ⟨fun q _ h => absurd (hg ▸ h) (by simp),
            fun q _ h => absurd (by rw [hD] at hg; exact hg ▸ h) (by simp)⟩
      | ifThen _ _ =>
          exact hres ⟨fun q _ h => absurd (hg ▸ h) (by simp),
            fun q _ h => absurd (by rw [hD] at hg; exact hg ▸ h) (by simp)⟩
      | somehow _ =>
          exact hres ⟨fun q _ h => absurd (hg ▸ h) (by simp),
            fun q _ h => absurd (by rw [hD] at hg; exact hg ▸ h) (by simp)⟩

/-- **`GammaPairFloorBox` reduces to its non-atomic goal shapes.** -/
theorem gammaPairFloorBox_of_residue (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (hres : GammaBoxFloorResidue p S) : GammaPairFloorBox p S := by
  intro F fl Γ A B g Δ hF hmem hS hBS hB hgS hΓS hrec hamb hbox hsnd
  refine dispatch p hOr hgS ?_ ?_ ?_
  · rintro q hq rfl
    exact floorAny_atom p S hOr hq hBS hΓS hsnd
  · rintro q hq rfl
    exact gammaPairFloorBox_boxedAtom p S hOr hq hsome F fl Γ A B Δ hF hmem hS
      hBS hB hΓS hamb hbox hsnd
  · intro hna
    exact hres F fl Γ A B g Δ hna hF hmem hS hBS hB hgS hΓS hrec hamb hbox hsnd

/-- **`GammaPairFloorA` reduces to its non-atomic goal shapes.** -/
theorem gammaPairFloorA_of_residue (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (hres : GammaAFloorResidue p S) : GammaPairFloorA p S := by
  intro F fl Γ A B g Δ hF hmem hS hBS hB hgS hΓS hrec hamb hval hsnd
  refine dispatch p hOr hgS ?_ ?_ ?_
  · rintro q hq rfl
    exact floorAny_atom p S hOr hq hBS hΓS hsnd
  · rintro q hq rfl
    exact gammaPairFloorA_boxedAtom p S hOr hq hsome F fl Γ A B Δ hF hmem hS
      hBS hB hΓS hamb hval hsnd
  · intro hna
    exact hres F fl Γ A B g Δ hna hF hmem hS hBS hB hgS hΓS hrec hamb hval hsnd

/-- **`JumpPairFloor` reduces to its non-atomic goal shapes.** -/
theorem jumpPairFloor_of_residue (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (hres : JumpFloorResidue p S) : JumpPairFloor p S := by
  intro F fl Γ A B D g Δ hF hmem hS hBD hDS hD hgS hΓS hrec hamb hfst hsnd
  refine dispatch p hOr hgS ?_ ?_ ?_
  · rintro q hq rfl
    exact floorAny_atom p S hOr hq hDS hΓS hsnd
  · rintro q hq rfl
    exact jumpPairFloor_boxedAtom p S hOr hq hsome F fl Γ A B D Δ hF hmem hS
      hBD hDS hD hΓS hamb hfst hsnd
  · intro hna
    exact hres F fl Γ A B D g Δ hna hF hmem hS hBD hDS hD hgS hΓS hrec hamb
      hfst hsnd

end FloorGoals
end PLLND

/-! ### Axiom audit — `sorryAx`-free despite importing a file with stubs -/

/--
info: 'PLLND.FloorGoals.gammaPairFloorBox_of_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FloorGoals.gammaPairFloorBox_of_residue

/--
info: 'PLLND.FloorGoals.gammaPairFloorA_of_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FloorGoals.gammaPairFloorA_of_residue

/--
info: 'PLLND.FloorGoals.jumpPairFloor_of_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FloorGoals.jumpPairFloor_of_residue
