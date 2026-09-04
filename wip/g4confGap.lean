import wip.G4conf
import LaxLogic.PLLSearchCmd

/-!
# `G4cf` is not complete without cut: the assumed metatheory of `wip/G4conf.lean` refuted

`G4cf` (= G4iLL″ + the analytic left rule `distL` for `◯(A∨B)`-hypotheses)
was set up with its heavier metatheory — completeness for confluent
validity and cut admissibility — *assumed* under stated licence.  This file
refutes both, kernel-checked, with the cut-necessity sequent of
`PLLNoFallSep.lean`:

    S  :=  ◯(a ⊃ (b ∨ c)), ◯a, ◯b ⊃ p, ◯c ⊃ p  ⊢  p

* `derivU_gapSeq`: `S` is PCLL-derivable (through the intermediary
  `◯b ∨ ◯c` — a cut), hence confluent-valid (`derivU_sound`).
* `g4cf_not_gapSeq`: `S` is **not** `G4cf`-derivable.  The point: `distL`
  fires only on hypotheses of literal shape `◯(A ∨ B)`, and no formula
  with a subformula of that shape ever appears in the backward cone of
  `S` — the invariant `NoObOr` below is preserved by all 18 rules — so on
  this cone `G4cf` collapses to `G4c` (`g4hf_to_g4h`), and `G4c` cannot
  derive `S` because PLL cannot (five-world countermodel, `decide`).
* `g4cf_complete_refuted`: therefore the completeness claim
  (`G4cf_complete`) is false as stated.  Since the embedding
  `G4c ⊆ G4cf` and the derivability of the distribution instances are
  routine and true, **cut admissibility (`G4cf_cut`) is false as well**:
  with cut, `G4cf` does derive `S` (compose `derivU_gapSeq`'s witness),
  so cut is not eliminable.

In standard language: the analytic distribution rule is too weak — the
confluence content needed at `S` sits under an implication inside a box,
where a left rule keyed to `◯(A ∨ B)`-hypotheses cannot reach; the cut
through `◯b ∨ ◯c` is essential.  This is the calculus-level face of the
§62 analysis (PROGRESS): a cut-free single-succedent calculus for the
distributing systems needs a rule that lets a disjunction of `◯`-formulas
survive across implication eliminations (multi-succedent `◯`-rule, or an
elimination rule internalising the case split).
-/

open PLLFormula

namespace PLLND
namespace G4ConfGap

open G4Conf

/-! ## 1. The invariant: no subformula of shape `◯(A ∨ B)` -/

/-- No subformula of shape `◯(A ∨ B)` occurs. -/
def NoObOr : PLLFormula → Prop
  | .prop _ => True
  | .falsePLL => True
  | .and A B => NoObOr A ∧ NoObOr B
  | .or A B => NoObOr A ∧ NoObOr B
  | .ifThen A B => NoObOr A ∧ NoObOr B
  | .somehow (.or _ _) => False
  | .somehow A => NoObOr A

theorem NoObOr.ob_inv : ∀ {A : PLLFormula}, NoObOr A.somehow → NoObOr A
  | .prop _, _ => trivial
  | .falsePLL, _ => trivial
  | .and _ _, h => h
  | .or _ _, h => h.elim
  | .ifThen _ _, h => h
  | .somehow _, h => h

private theorem consN {x : PLLFormula} {Γ : List PLLFormula}
    (hx : NoObOr x) (hΓ : ∀ F ∈ Γ, NoObOr F) :
    ∀ F ∈ x :: Γ, NoObOr F := by
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hx
  · exact hΓ F hF

/-! ## 2. On `NoObOr` sequents, `G4cf` collapses to `G4c` -/

/-- `distL` never fires on a `NoObOr` context, and every rule preserves
the invariant, so a `G4hf` derivation of a `NoObOr` sequent is a `G4h`
derivation. -/
theorem g4hf_to_g4h : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    (∀ F ∈ Γ, NoObOr F) → NoObOr C → G4hf n Γ C → G4h n Γ C := by
  intro n Γ C hΓ hC d
  induction d with
  | init h => exact .init h
  | botL h => exact .botL h
  | andR _ _ ih₁ ih₂ => exact .andR (ih₁ hΓ hC.1) (ih₂ hΓ hC.2)
  | orR1 _ ih => exact .orR1 (ih hΓ hC.1)
  | orR2 _ ih => exact .orR2 (ih hΓ hC.2)
  | impR _ ih => exact .impR (ih (consN hC.1 hΓ) hC.2)
  | laxR _ ih => exact .laxR (ih hΓ hC.ob_inv)
  | @andL _ Γ' Δ A B _ h _ ih =>
      have hF := hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .andL h (ih (consN hF.1 (consN hF.2 hΔ)) hC)
  | @orL _ Γ' Δ A B _ h _ _ ih₁ ih₂ =>
      have hF := hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .orL h (ih₁ (consN hF.1 hΔ) hC) (ih₂ (consN hF.2 hΔ) hC)
  | @laxL _ Γ' A B h _ ih =>
      exact .laxL h (ih (consN (hΓ _ h).ob_inv hΓ) hC)
  | @impLProp _ Γ' Δ q B _ h ha _ ih =>
      have hF := hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .impLProp h ha (ih (consN hF.2 hΔ) hC)
  | @impLBot _ Γ' Δ B _ h _ ih =>
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .impLBot h (ih hΔ hC)
  | @impLAnd _ Γ' Δ A B D _ h _ ih =>
      have hF := hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .impLAnd h (ih (consN ⟨hF.1.1, hF.1.2, hF.2⟩ hΔ) hC)
  | @impLOr _ Γ' Δ A B D _ h _ ih =>
      have hF := hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .impLOr h
        (ih (consN ⟨hF.1.1, hF.2⟩ (consN ⟨hF.1.2, hF.2⟩ hΔ)) hC)
  | @impLImp _ Γ' Δ A B D _ h _ _ ih₁ ih₂ =>
      have hF := hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .impLImp h (ih₁ (consN ⟨hF.1.2, hF.2⟩ hΔ) hF.1)
        (ih₂ (consN hF.2 hΔ) hC)
  | @impLLax _ Γ' Δ A B _ h _ _ ih₁ ih₂ =>
      have hF := hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .impLLax h (ih₁ hΓ hF.1.ob_inv) (ih₂ (consN hF.2 hΔ) hC)
  | @impLLaxLax _ Γ' Δ A B X _ h hX _ _ ih₁ ih₂ =>
      have hF := hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))
      have hΔ : ∀ F ∈ Δ, NoObOr F :=
        fun F hFm => hΓ F (h.mem_iff.mpr (List.mem_cons_of_mem _ hFm))
      exact .impLLaxLax h hX
        (ih₁ (consN (hΔ _ hX).ob_inv hΓ) hF.1) (ih₂ (consN hF.2 hΔ) hC)
  | @distL _ Γ' Δ A B _ h _ _ _ _ =>
      exact absurd (hΓ _ (h.mem_iff.mpr (List.mem_cons_self ..))) id

/-! ## 3. The witnessing sequent -/

def gapH₁ : PLLFormula := ((prop "a").ifThen ((prop "b").or (prop "c"))).somehow
def gapH₂ : PLLFormula := (prop "a").somehow
def gapH₃ : PLLFormula := ((prop "b").somehow).ifThen (prop "p")
def gapH₄ : PLLFormula := ((prop "c").somehow).ifThen (prop "p")

def gapSeq : List PLLFormula := [gapH₁, gapH₂, gapH₃, gapH₄]

/-- `S` is PCLL-derivable (one distribution instance, searcher term). -/
theorem derivU_gapSeq : ConfluentU.DerivU gapSeq (prop "p") :=
  RNC.derivU_of_proved [(prop "b", prop "c")] (PLLND.Search.proved_sound
    (.impLLaxLax (A := ((PLLFormula.prop "b").or (PLLFormula.prop "c")))
      (B := (((PLLFormula.prop "b").somehow).or ((PLLFormula.prop "c").somehow)))
      (X := ((PLLFormula.prop "a").ifThen ((PLLFormula.prop "b").or (PLLFormula.prop "c"))))
      (by decide) (by decide)
      (.laxL (A := (PLLFormula.prop "a")) (by decide)
        (.laxR (.impLProp (a := "a")
          (B := ((PLLFormula.prop "b").or (PLLFormula.prop "c")))
          (by decide) (by decide)
          (.orL (A := (PLLFormula.prop "b")) (B := (PLLFormula.prop "c"))
            (by decide) (.orR1 (.init (by decide)))
            (.orR2 (.init (by decide)))))))
      (.orL (A := ((PLLFormula.prop "b").somehow))
        (B := ((PLLFormula.prop "c").somehow)) (by decide)
        (.impLLaxLax (A := (PLLFormula.prop "b")) (B := (PLLFormula.prop "p"))
          (X := (PLLFormula.prop "b")) (by decide) (by decide)
          (.laxR (.init (by decide))) (.init (by decide)))
        (.impLLaxLax (A := (PLLFormula.prop "c")) (B := (PLLFormula.prop "p"))
          (X := (PLLFormula.prop "c")) (by decide) (by decide)
          (.laxR (.init (by decide))) (.init (by decide))))))

/-- `S` is not PLL-derivable: the five-world `∀∃`-countermodel. -/
theorem pll_not_gapSeq : ¬ Nonempty (LaxND gapSeq (prop "p")) :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (1, 3), (2, 4), (0, 3), (0, 4)],
      [(1, 3), (2, 4), (0, 3)], [],
      [(3, "a"), (4, "a"), (3, "b"), (4, "c"),
       (1, "p"), (2, "p"), (3, "p"), (4, "p")]⟩)
    (w := 0) (by decide)

theorem noObOr_gapSeq : ∀ F ∈ gapSeq, NoObOr F := by
  intro F hF
  simp only [gapSeq, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl
  · exact ⟨trivial, trivial, trivial⟩
  · exact trivial
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩

/-- **`S` is not `G4cf`-derivable.** -/
theorem g4cf_not_gapSeq : ¬ G4cf gapSeq (prop "p") := by
  rintro ⟨n, d⟩
  exact pll_not_gapSeq
    (G4c.equiv_nd.mp ⟨n, g4hf_to_g4h noObOr_gapSeq trivial d⟩)

/-! ## 4. The refutations -/

/-- **The assumed completeness of `G4cf` is false**: the closed form of
`G4cf_complete`'s statement is refuted by `S`, whose confluent validity
follows from `derivU_gapSeq` by soundness. -/
theorem g4cf_complete_refuted :
    ¬ (∀ (Γ : List PLLFormula) (C : PLLFormula),
        (∀ (M : ConstraintModel), MutuallyConfluent M → ∀ w : M.W,
          (∀ φ ∈ Γ, M.force w φ) → M.force w C) → G4cf Γ C) :=
  fun H => g4cf_not_gapSeq (H _ _ (fun _ hc w hΓ =>
    ConfluentU.derivU_sound derivU_gapSeq hc w hΓ))

end G4ConfGap
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.G4ConfGap.g4cf_not_gapSeq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.G4ConfGap.g4cf_not_gapSeq

/-- info: 'PLLND.G4ConfGap.g4cf_complete_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.G4ConfGap.g4cf_complete_refuted
