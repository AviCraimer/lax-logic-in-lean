import LaxLogic.PLLG4
import LaxLogic.PLLFinsetKit

/-!
# Termination A: the finite formula space

Backward `G4iLL″` search cannot terminate by a decreasing rule measure
(the lax rules retain, the Dyckhoff rules consume, and an erased
implication can re-enter as a piece of a split conjunction).  It
terminates by **finiteness of the reachable space**: every formula
appearing in any premise of any rule has weight bounded by the
conclusion's formulas and atoms among theirs — retained material
trivially, opened boxes and premise goals as subformulas, and the
Dyckhoff pieces because the curried transforms *strictly decrease*
weight (the `∧ = +2` convention's purpose).

This file: the atom set of a formula, the space predicate
`InSpace W as φ` (weight ≤ `W`, atoms ⊆ `as`, decidable), a concrete
`Finset` enumeration `enum as W` with `InSpace.mem_enum` embedding the
space into it (one direction is all the pigeonhole needs), and the
component/piece stability lemmas the sequent-level argument will
consume.

**Axiom hygiene.** `atoms` and `enum` are built on the choice-free
combinators of `PLLFinsetKit.lean` (`finUnion`, `finImage`,
`finPairMap`), so they and everything downstream of them audit
`[propext, Quot.sound]`.  The `atoms_and`/`atoms_or`/`atoms_ifThen`
simp lemmas keep their Mathlib-`∪` statements for the interpolation
files, and are therefore the only choice-tainted *statements* here; the
clean chain uses the `mem_atoms_*` forms instead.
-/

namespace PLLFormula

open PLLND (finUnion finImage finPairMap mem_finUnion mem_finImage
  mem_finPairMap subAntisymm)

/-- The atoms occurring in a formula. -/
def atoms : PLLFormula → Finset String
  | prop a => {a}
  | falsePLL => ∅
  | and A B => finUnion A.atoms B.atoms
  | or A B => finUnion A.atoms B.atoms
  | ifThen A B => finUnion A.atoms B.atoms
  | somehow A => A.atoms

/-! ### Membership forms (choice-free) -/

@[simp] theorem mem_atoms_and {A B : PLLFormula} {x : String} :
    x ∈ (A.and B).atoms ↔ x ∈ A.atoms ∨ x ∈ B.atoms := mem_finUnion

@[simp] theorem mem_atoms_or {A B : PLLFormula} {x : String} :
    x ∈ (A.or B).atoms ↔ x ∈ A.atoms ∨ x ∈ B.atoms := mem_finUnion

@[simp] theorem mem_atoms_ifThen {A B : PLLFormula} {x : String} :
    x ∈ (A.ifThen B).atoms ↔ x ∈ A.atoms ∨ x ∈ B.atoms := mem_finUnion

/-! ### Equational forms (statements mention Mathlib `∪`; kept for the
interpolation files, whose audit is not choice-critical) -/

@[simp] theorem atoms_prop {a : String} : (prop a).atoms = {a} := rfl
@[simp] theorem atoms_false : (falsePLL).atoms = ∅ := rfl
@[simp] theorem atoms_and {A B : PLLFormula} :
    (A.and B).atoms = A.atoms ∪ B.atoms :=
  subAntisymm
    (fun x hx => Finset.mem_union.mpr (mem_finUnion.mp hx))
    (fun x hx => mem_finUnion.mpr (Finset.mem_union.mp hx))
@[simp] theorem atoms_or {A B : PLLFormula} :
    (A.or B).atoms = A.atoms ∪ B.atoms :=
  subAntisymm
    (fun x hx => Finset.mem_union.mpr (mem_finUnion.mp hx))
    (fun x hx => mem_finUnion.mpr (Finset.mem_union.mp hx))
@[simp] theorem atoms_ifThen {A B : PLLFormula} :
    (A.ifThen B).atoms = A.atoms ∪ B.atoms :=
  subAntisymm
    (fun x hx => Finset.mem_union.mpr (mem_finUnion.mp hx))
    (fun x hx => mem_finUnion.mpr (Finset.mem_union.mp hx))
@[simp] theorem atoms_somehow {A : PLLFormula} :
    (A.somehow).atoms = A.atoms := rfl

/-- The weight-bounded space over a finite atom alphabet. -/
def InSpace (W : Nat) (as : Finset String) (φ : PLLFormula) : Prop :=
  φ.weight ≤ W ∧ φ.atoms ⊆ as

instance (W : Nat) (as : Finset String) (φ : PLLFormula) :
    Decidable (InSpace W as φ) := by
  unfold InSpace; infer_instance

namespace InSpace

variable {W : Nat} {as : Finset String} {A B D : PLLFormula}

/-! ### Subformula components stay in the space -/

theorem and_left (h : InSpace W as (A.and B)) : InSpace W as A :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (mem_atoms_and.mpr (.inl hx))⟩

theorem and_right (h : InSpace W as (A.and B)) : InSpace W as B :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (mem_atoms_and.mpr (.inr hx))⟩

theorem or_left (h : InSpace W as (A.or B)) : InSpace W as A :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (mem_atoms_or.mpr (.inl hx))⟩

theorem or_right (h : InSpace W as (A.or B)) : InSpace W as B :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (mem_atoms_or.mpr (.inr hx))⟩

theorem imp_left (h : InSpace W as (A.ifThen B)) : InSpace W as A :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (mem_atoms_ifThen.mpr (.inl hx))⟩

theorem imp_right (h : InSpace W as (A.ifThen B)) : InSpace W as B :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (mem_atoms_ifThen.mpr (.inr hx))⟩

theorem box (h : InSpace W as A.somehow) : InSpace W as A :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (by rw [atoms_somehow]; exact hx)⟩

/-! ### The Dyckhoff pieces stay in the space (weights strictly drop) -/

theorem impAnd_piece (h : InSpace W as ((A.and B).ifThen D)) :
    InSpace W as (A.ifThen (B.ifThen D)) := by
  obtain ⟨hw, ha⟩ := h
  simp only [weight] at hw
  refine ⟨by simp only [weight]; omega, fun x hx => ha ?_⟩
  rcases mem_atoms_ifThen.mp hx with hA | hBD
  · exact mem_atoms_ifThen.mpr (.inl (mem_atoms_and.mpr (.inl hA)))
  · rcases mem_atoms_ifThen.mp hBD with hB | hD
    · exact mem_atoms_ifThen.mpr (.inl (mem_atoms_and.mpr (.inr hB)))
    · exact mem_atoms_ifThen.mpr (.inr hD)

theorem impOr_piece₁ (h : InSpace W as ((A.or B).ifThen D)) :
    InSpace W as (A.ifThen D) := by
  obtain ⟨hw, ha⟩ := h
  simp only [weight] at hw
  have := weight_pos B
  refine ⟨by simp only [weight]; omega, fun x hx => ha ?_⟩
  rcases mem_atoms_ifThen.mp hx with hA | hD
  · exact mem_atoms_ifThen.mpr (.inl (mem_atoms_or.mpr (.inl hA)))
  · exact mem_atoms_ifThen.mpr (.inr hD)

theorem impOr_piece₂ (h : InSpace W as ((A.or B).ifThen D)) :
    InSpace W as (B.ifThen D) := by
  obtain ⟨hw, ha⟩ := h
  simp only [weight] at hw
  have := weight_pos A
  refine ⟨by simp only [weight]; omega, fun x hx => ha ?_⟩
  rcases mem_atoms_ifThen.mp hx with hB | hD
  · exact mem_atoms_ifThen.mpr (.inl (mem_atoms_or.mpr (.inr hB)))
  · exact mem_atoms_ifThen.mpr (.inr hD)

theorem impImp_piece (h : InSpace W as ((A.ifThen B).ifThen D)) :
    InSpace W as (B.ifThen D) := by
  obtain ⟨hw, ha⟩ := h
  simp only [weight] at hw
  have := weight_pos A
  refine ⟨by simp only [weight]; omega, fun x hx => ha ?_⟩
  rcases mem_atoms_ifThen.mp hx with hB | hD
  · exact mem_atoms_ifThen.mpr (.inl (mem_atoms_ifThen.mpr (.inr hB)))
  · exact mem_atoms_ifThen.mpr (.inr hD)

end InSpace

/-! ### A concrete finite enumeration containing the space -/

/-- All formulas built in at most `W` weight over alphabet `as` land in
this finite set (`InSpace.mem_enum`); the converse is not needed. -/
def enum (as : Finset String) : Nat → Finset PLLFormula
  | 0 => ∅
  | W + 1 =>
      (finUnion (finUnion (finUnion (finUnion (finUnion
        (finImage prop as) {falsePLL})
        (finPairMap (fun A B => A.and B) (enum as W) (enum as W)))
        (finPairMap (fun A B => A.or B) (enum as W) (enum as W)))
        (finPairMap (fun A B => A.ifThen B) (enum as W) (enum as W)))
        (finImage somehow (enum as W))).filter (fun φ => φ.weight ≤ W + 1)

theorem InSpace.mem_enum : ∀ (W : Nat) {as : Finset String} {φ : PLLFormula},
    InSpace W as φ → φ ∈ enum as W := by
  intro W
  induction W with
  | zero =>
      intro as φ h
      exact absurd h.1 (by have := weight_pos φ; omega)
  | succ W ih =>
      intro as φ h
      obtain ⟨hw, ha⟩ := h
      simp only [enum]
      refine Finset.mem_filter.mpr ⟨mem_finUnion.mpr ?_, hw⟩
      cases φ with
      | prop a =>
          have haa : a ∈ as := ha (by rw [atoms_prop]; exact Finset.mem_singleton_self a)
          exact .inl (mem_finUnion.mpr (.inl (mem_finUnion.mpr (.inl
            (mem_finUnion.mpr (.inl (mem_finUnion.mpr (.inl
              (mem_finImage.mpr ⟨a, haa, rfl⟩)))))))))
      | falsePLL =>
          exact .inl (mem_finUnion.mpr (.inl (mem_finUnion.mpr (.inl
            (mem_finUnion.mpr (.inl (mem_finUnion.mpr (.inr
              (Finset.mem_singleton_self _)))))))))
      | and A B =>
          simp only [weight] at hw
          have hA := ih (as := as) (φ := A)
            ⟨by omega, fun x hx => ha (mem_atoms_and.mpr (.inl hx))⟩
          have hB := ih (as := as) (φ := B)
            ⟨by omega, fun x hx => ha (mem_atoms_and.mpr (.inr hx))⟩
          exact .inl (mem_finUnion.mpr (.inl (mem_finUnion.mpr (.inl
            (mem_finUnion.mpr (.inr (mem_finPairMap.mpr ⟨A, hA, B, hB, rfl⟩)))))))
      | or A B =>
          simp only [weight] at hw
          have hA := ih (as := as) (φ := A)
            ⟨by omega, fun x hx => ha (mem_atoms_or.mpr (.inl hx))⟩
          have hB := ih (as := as) (φ := B)
            ⟨by omega, fun x hx => ha (mem_atoms_or.mpr (.inr hx))⟩
          exact .inl (mem_finUnion.mpr (.inl (mem_finUnion.mpr (.inr
            (mem_finPairMap.mpr ⟨A, hA, B, hB, rfl⟩)))))
      | ifThen A B =>
          simp only [weight] at hw
          have hA := ih (as := as) (φ := A)
            ⟨by omega, fun x hx => ha (mem_atoms_ifThen.mpr (.inl hx))⟩
          have hB := ih (as := as) (φ := B)
            ⟨by omega, fun x hx => ha (mem_atoms_ifThen.mpr (.inr hx))⟩
          exact .inl (mem_finUnion.mpr (.inr
            (mem_finPairMap.mpr ⟨A, hA, B, hB, rfl⟩)))
      | somehow A =>
          simp only [weight] at hw
          have hA := ih (as := as) (φ := A)
            ⟨by omega, fun x hx => ha (show x ∈ A.atoms from hx)⟩
          exact .inr (mem_finImage.mpr ⟨A, hA, rfl⟩)

end PLLFormula
