import wip.witOut
import wip.rankedM
import wip.rnEmbed

/-!
# The witness-form semantic quantifiers over confluent models

Branch `ui-confluence`.  The spec layer the witness-form pipeline
feeds: `IsSemExW`/`IsSemAllW` are the semantic ∃p/∀p specifications of
`PLLSemUI.lean` with two changes forced by the route —

* the model quantifier ranges over MUTUALLY CONFLUENT bases only (the
  completeness class of PCLL = PLL + distribution, `DerivU`), and
* p-variants are `PBisimWit` (witness-form) links, the notion the
  amalgamation actually delivers and `force_iff_of_witOut` actually
  transfers along.

Proved here, all sorry-free:

* `semExW_rhs_hered`: the ∃-side right-hand predicate is hereditary
  along `Rᵢ` — the spec is coherent (its RHS is a legitimate
  "proposition" of the intuitionistic semantics).  The fallible escape
  is absorbed by the IDENTITY witness link on the base itself.
* `isSemExW_unique` / `isSemAllW_unique`: spec-satisfiers are unique
  up to PCLL-interderivability, via `derivU_iff_confluent_valid` —
  the point of restricting the quantifier to the confluent class.
* `pOnly_V_eq_F`: under the corrected one-variable purity, every atom
  off `p` has truth set EXACTLY `F` — so p-free formulas over `POnly`
  models are pointwise the variable-free formulas with dead atoms read
  as `⊥`.  (The bridge for re-aiming the residue boundary theorem at
  the ranked link.)

What still separates `restricted_amalgamation_oneVar_ranked` from
`IsSemExW` for a concrete interpolant candidate: the candidate itself
(the rank-bounded join `⋁{D variable-free, crank ≤ rslope(2|cl|+1) |
D ⊢ φ}` of the cross-route experiment) and the two halves of the
biconditional — the soundness half consumes `force_iff_of_witOut`
(PROVED), the completeness half consumes the amalgamation (PROVED
modulo `MwitResidue`) at a root pair agreeing on the join's rank.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU
open RNEmbed

variable {p : String}

/-- **Witness-form semantic ∃p** over confluent bases: `ψ` is p-free
and forced exactly at the worlds having a witness-form p-variant
forcing `φ`. -/
def IsSemExW (p : String) (φ ψ : PLLFormula) : Prop :=
  p ∉ ψ.atoms ∧
  ∀ (M : ConstraintModel), MutuallyConfluent M → ∀ (w : M.W),
    (M.force w ψ ↔
      ∃ (N : ConstraintModel) (C : PBisimWit p M N) (w' : N.W),
        C.Z w w' ∧ N.force w' φ)

/-- **Witness-form semantic ∀p** over confluent bases. -/
def IsSemAllW (p : String) (φ ψ : PLLFormula) : Prop :=
  p ∉ ψ.atoms ∧
  ∀ (M : ConstraintModel), MutuallyConfluent M → ∀ (w : M.W),
    (M.force w ψ ↔
      ∀ v, M.Ri w v →
        ∀ (N : ConstraintModel) (C : PBisimWit p M N) (v' : N.W),
          C.Z v v' → N.force v' φ)

/-- **Coherence of the ∃-spec**: its right-hand side is hereditary
along `Rᵢ`.  An `iforth` answer moves the variant world up; the
fallible escape is absorbed by the identity witness link on the base
itself (a fallible world forces `φ` outright). -/
theorem semExW_rhs_hered {φ : PLLFormula} {M : ConstraintModel}
    {w v : M.W} (hwv : M.Ri w v)
    (h : ∃ (N : ConstraintModel) (C : PBisimWit p M N) (w' : N.W),
      C.Z w w' ∧ N.force w' φ) :
    ∃ (N : ConstraintModel) (C : PBisimWit p M N) (v' : N.W),
      C.Z v v' ∧ N.force v' φ := by
  obtain ⟨N, C, w', hZ, hφ⟩ := h
  rcases C.iforth hZ hwv with ⟨v', hv', hZv⟩ | hF
  · exact ⟨N, C, v', hZv, N.force_hered hv' hφ⟩
  · exact ⟨M, (ABisim.id (fun a => a ≠ p) M).toWitOut, v, rfl,
      M.force_of_fallible hF⟩

/-- Spec-satisfiers of ∃p are unique up to PCLL-interderivability —
the reward for restricting the base class to the confluent models,
where `DerivU` is complete. -/
theorem isSemExW_unique {φ ψ₁ ψ₂ : PLLFormula}
    (h1 : IsSemExW p φ ψ₁) (h2 : IsSemExW p φ ψ₂) : InterdU ψ₁ ψ₂ := by
  constructor
  · rw [derivU_iff_confluent_valid]
    intro C hc w hΓ
    exact (h2.2 C hc w).mpr ((h1.2 C hc w).mp (hΓ ψ₁ (by simp)))
  · rw [derivU_iff_confluent_valid]
    intro C hc w hΓ
    exact (h1.2 C hc w).mpr ((h2.2 C hc w).mp (hΓ ψ₂ (by simp)))

/-- Spec-satisfiers of ∀p are unique up to PCLL-interderivability. -/
theorem isSemAllW_unique {φ ψ₁ ψ₂ : PLLFormula}
    (h1 : IsSemAllW p φ ψ₁) (h2 : IsSemAllW p φ ψ₂) : InterdU ψ₁ ψ₂ := by
  constructor
  · rw [derivU_iff_confluent_valid]
    intro C hc w hΓ
    exact (h2.2 C hc w).mpr ((h1.2 C hc w).mp (hΓ ψ₁ (by simp)))
  · rw [derivU_iff_confluent_valid]
    intro C hc w hΓ
    exact (h1.2 C hc w).mpr ((h2.2 C hc w).mp (hΓ ψ₂ (by simp)))

/-- Under the corrected one-variable purity, every atom off `p` has
truth set exactly `F`: `POnly` gives one inclusion, `full_F` the
other.  P-free formulas over `POnly` models are therefore pointwise
variable-free formulas with dead atoms read as `⊥`. -/
theorem pOnly_V_eq_F {C : ConstraintModel} (h : POnly p C)
    {a : String} (ha : a ≠ p) : C.V a = C.F := by
  ext w
  exact ⟨fun hv => h a ha w hv, fun hf => C.full_F hf⟩

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.semExW_rhs_hered' does not depend on any axioms
-/
#guard_msgs in
#print axioms semExW_rhs_hered

/--
info: 'PLLND.SemUI.isSemExW_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isSemExW_unique

/--
info: 'PLLND.SemUI.isSemAllW_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isSemAllW_unique

/--
info: 'PLLND.SemUI.pOnly_V_eq_F' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms pOnly_V_eq_F

end SemUI
end PLLND
