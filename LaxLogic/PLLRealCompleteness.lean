import LaxLogic.PLLEvidence
import LaxLogic.PLLFinComp

/-!
# Completeness of PLL for presented-strategy realisability

The composition of the two halves of the programme:

* `emitter_completeness` (`PLLFinComp.lean`) — every underivable sequent
  has a finite countermodel as verified checker data, by the Zorn-free
  canonical model;
* `realP_refutes_sequent_tbl` (`PLLEvidence.lean`) — every checked
  countermodel, decorated with token evidence over the explicit table
  algebra, is a `⊩ᵖ`-refutation: hypotheses realised, conclusion
  unrealisable.

`realP_countermodel_of_underivable` chains them; together with soundness
and the adequacy/fullness bridge it sharpens to the biconditional
`derivable_iff_no_realP_refutation`: a sequent is derivable exactly when
no token-decorated checked finite model realisability-refutes it.

Every quantifier here ranges over concrete objects — finite models as
printable data, evidence with one token per atom, realisers in an explicit
algebra of finite lookup tables — and the countermodel construction is the
iterated *decided* extension of `PLLFinComp.lean`: no Zorn.  After the
2026-07-18 choice-scrub of the decidability infrastructure the audit is
**`[propext, Quot.sound]`** — no `Classical.choice` anywhere in the
chain, as the guards below check.
-/

open PLLFormula

namespace PLLND
namespace BeliefReal

open FinComp

/-- The canonical atom token in the table algebra. -/
private def tok₀ : String → Tbl := fun _ => Tbl.base 0

/-- **Realisability countermodels for underivable sequents**: if `Γ ⊢ C`
is underivable, some finite checked model, decorated with token evidence
over the table algebra, realises every hypothesis at its refuting world
while `C` is unrealisable there. -/
theorem realP_countermodel_of_underivable {Γ : List PLLFormula}
    {C : PLLFormula} (h : ¬ Nonempty (LaxND Γ C)) :
    ∃ (M : FinCM) (w : Nat) (hwf : M.WellFormed) (hlt : w < M.n),
      (∀ ψ ∈ Γ, ∃ x,
        x ⊩ᵖ[tokenEvidence tblPca M hwf tok₀, tblκ, ⟨w, hlt⟩] ψ) ∧
      ¬ ∃ x, x ⊩ᵖ[tokenEvidence tblPca M hwf tok₀, tblκ, ⟨w, hlt⟩] C := by
  obtain ⟨M, w, hcheck⟩ := emitter_completeness h
  obtain ⟨hwf, hlt, hΓ, hC⟩ := realP_refutes_sequent_tbl hcheck
  exact ⟨M, w, hwf, hlt, hΓ, hC⟩

/-- **Completeness of PLL for `⊩ᵖ`-realisability**: a sequent is derivable
exactly when no token-decorated checked finite model realisability-refutes
it.  Forward: soundness plus adequacy and fullness — a derivable
conclusion is forced wherever its realised hypotheses are, hence realised
by its fullness witness.  Backward: the countermodel construction above;
the case decision is by the mechanised decision procedure, not excluded
middle. -/
theorem derivable_iff_no_realP_refutation {Γ : List PLLFormula}
    {C : PLLFormula} :
    Nonempty (LaxND Γ C) ↔
      ¬ ∃ (M : FinCM) (w : Nat) (hwf : M.WellFormed) (hlt : w < M.n),
        (∀ ψ ∈ Γ, ∃ x,
          x ⊩ᵖ[tokenEvidence tblPca M hwf tok₀, tblκ, ⟨w, hlt⟩] ψ) ∧
        ¬ ∃ x, x ⊩ᵖ[tokenEvidence tblPca M hwf tok₀, tblκ, ⟨w, hlt⟩] C := by
  constructor
  · rintro ⟨p⟩ ⟨M, w, hwf, hlt, hΓ, hC⟩
    have hforced : ∀ ψ ∈ Γ, (M.toModel hwf).force ⟨w, hlt⟩ ψ := by
      intro ψ hψ
      obtain ⟨x, hx⟩ := hΓ ψ hψ
      exact (realP_adequate_and_full (P := tblPca) hwf tok₀ tblκ
        tbl_htab tbl_htabP ψ).1 ⟨w, hlt⟩ x hx
    have hCforced := soundness p (M.toModel hwf) ⟨w, hlt⟩ hforced
    obtain ⟨wit, hwit⟩ := (realP_adequate_and_full (P := tblPca) hwf tok₀
      tblκ tbl_htab tbl_htabP C).2
    exact hC ⟨wit ⟨w, hlt⟩, hwit ⟨w, hlt⟩ hCforced⟩
  · intro h
    cases (decidable_of_iff _ curry_howard :
        Decidable (Nonempty (LaxND Γ C))) with
    | isTrue hy => exact hy
    | isFalse hn => exact absurd (realP_countermodel_of_underivable hn) h

end BeliefReal
end PLLND

/--
info: 'PLLND.BeliefReal.realP_countermodel_of_underivable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.realP_countermodel_of_underivable

/--
info: 'PLLND.BeliefReal.derivable_iff_no_realP_refutation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.derivable_iff_no_realP_refutation
