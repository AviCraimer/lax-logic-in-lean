import LaxLogic.PLLKripke

/-! # Newly minted claims, for exercising the toolkit

Five statements about `ConstraintModel.force` that are true but not proved
anywhere in the development. Graded from trivial to needing two frame
properties at once. Nothing here is used elsewhere; the file exists to test
the prove-lemma-inloop workflow on goals of sensible difficulty.
-/

namespace PLLND
namespace ConstraintModel

open PLLFormula

variable (C : ConstraintModel)

/-- (1) Every world forces `⊤` (`⊥ ⊃ ⊥`). -/
theorem force_truePLL (w : C.W) : C.force w truePLL :=
  fun _ _ h => h

/-- (2) Conjunction is commutative under forcing. -/
theorem force_and_comm {w : C.W} {φ ψ : PLLFormula} :
    C.force w (.and φ ψ) ↔ C.force w (.and ψ φ) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- (3) `φ` implies `◯φ`: the unit of the lax modality, semantically. -/
theorem force_somehow_of_force {w : C.W} {φ : PLLFormula}
    (h : C.force w φ) : C.force w (.somehow φ) :=
  fun v hv => ⟨v, C.refl_m v, C.force_hered hv h⟩

/-- (4) Implication composes at a world. -/
theorem force_imp_trans {w : C.W} {φ ψ χ : PLLFormula}
    (h₁ : C.force w (.ifThen φ ψ)) (h₂ : C.force w (.ifThen ψ χ)) :
    C.force w (.ifThen φ χ) :=
  fun v hv hφ => h₂ v hv (h₁ v hv hφ)

/-- (5) `◯` is idempotent downwards: `◯◯φ` forces `◯φ`. -/
theorem force_somehow_idem {w : C.W} {φ : PLLFormula}
    (h : C.force w (.somehow (.somehow φ))) : C.force w (.somehow φ) := by
  intro v hv
  obtain ⟨u, hvu, hu⟩ := h v hv
  obtain ⟨t, hut, ht⟩ := hu u (C.refl_i u)
  exact ⟨t, C.trans_m hvu hut, ht⟩

end ConstraintModel
end PLLND
