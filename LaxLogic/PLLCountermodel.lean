import LaxLogic.PLLFiniteModel

/-!
# Countermodels for non-theorems of PLL — the extractor specification

A PLL formula fails to be provable **exactly** when a *finite* constraint model
refutes it at a world.  This is the contrapositive of the finite model property
(F&M Theorem 4.6, `finite_model_property`), and it is the semantic guarantee that
any "failed proof search ⟹ countermodel" procedure must meet.

**Route B bridge.**  The finite refuting model this yields is the seed for the
realisability completeness of `docs/route-b-model.md` §6: equip its worlds with a
suitable evidence assignment and one obtains a realisability model in which `φ`
is unrealised.

**On computability.**  The guarantee here is *existence*: the initial refuting
model comes, inside `completeness`, from the Zorn/Lindenbaum canonical model, so
it is classical.  A *computable* extractor — a function `φ ↦ Option (finite
model)` that runs — requires either **emitting the saturated branch** of the
terminating decision procedure (`decidablePLL`, `PLLG4Dec.lean`), which is the
genuine "from failed search" route, or a **decidable enumeration** over the
filtration space (`PLLFiniteModel.filtration`).  That constructive upgrade is a
separate development; this file pins the specification it must satisfy.
-/

open PLLFormula

namespace PLLND

/-- **Countermodel specification.**  `φ` is *not* a PLL theorem iff some finite
constraint model refutes it at a world.  (Contrapositive of the finite model
property.) -/
theorem not_provable_iff_exists_finite_countermodel {φ : PLLFormula} :
    ¬ Nonempty (LaxND [] φ) ↔
      ∃ C : ConstraintModel, Finite C.W ∧ ∃ w : C.W, ¬ C.force w φ := by
  constructor
  · intro hnp
    by_contra hnc
    apply hnp
    apply finite_model_property.mpr
    intro C hfin w
    by_contra hf
    exact hnc ⟨C, hfin, w, hf⟩
  · rintro ⟨C, _hfin, w, hw⟩ ⟨p⟩
    exact hw (soundness_valid p C w)

/-- The refuting world does force the (empty) hypotheses vacuously — recorded so
the statement reads as a genuine countermodel to the sequent `⊢ φ`. -/
theorem not_provable_iff_exists_finite_countermodel' {φ : PLLFormula} :
    ¬ Nonempty (LaxND [] φ) ↔
      ∃ C : ConstraintModel, Finite C.W ∧ ∃ w : C.W,
        (∀ ψ ∈ ([] : List PLLFormula), C.force w ψ) ∧ ¬ C.force w φ := by
  rw [not_provable_iff_exists_finite_countermodel]
  refine exists_congr fun C => and_congr_right fun _ => exists_congr fun w => ?_
  exact ⟨fun h => ⟨by simp, h⟩, fun h => h.2⟩

end PLLND

#print axioms PLLND.not_provable_iff_exists_finite_countermodel
#print axioms PLLND.not_provable_iff_exists_finite_countermodel'
