import LaxLogic.PLLNDCore

/-!
# Kripke constraint models for PLL, and soundness

Following Fairtlough & Mendler, *Propositional Lax Logic*, Information and
Computation 137(1), 1997 — Definitions 3.1 (constraint model), 3.2 (validity)
and Theorem 3.3 (soundness), over the slime-free system `PLLND.LaxND` of
`PLLNDCore.lean`.

A constraint model is `(W, Rₘ, Rᵢ, V, F)`: two preorders with `Rₘ ⊆ Rᵢ`, a
hereditary set `F` of *fallible* worlds at which `⊥` (and hence everything)
holds, and a hereditary valuation that is *full* on `F`.  The lax modality is
interpreted by the ∀∃ clause

  `w ⊨ ◯N  iff  ∀ v. w Rᵢ v → ∃ u. v Rₘ u ∧ u ⊨ N`,

which gives `◯` its mixed possibility/necessity flavour.

Everything here is `Prop`-valued: no casts, no transport.
-/

open PLLFormula

namespace PLLND

/-- Fairtlough–Mendler constraint model (Definition 3.1). -/
structure ConstraintModel where
  W : Type
  /-- intuitionistic accessibility -/
  Ri : W → W → Prop
  /-- modal (constraint) accessibility -/
  Rm : W → W → Prop
  /-- fallible worlds -/
  F : Set W
  /-- valuation on propositional constants -/
  V : String → Set W
  refl_i : ∀ w, Ri w w
  trans_i : ∀ {w v u}, Ri w v → Ri v u → Ri w u
  refl_m : ∀ w, Rm w w
  trans_m : ∀ {w v u}, Rm w v → Rm v u → Rm w u
  /-- the ◯-frame is a subrelation of the ⊃-frame -/
  sub_mi : ∀ {w v}, Rm w v → Ri w v
  hered_F : ∀ {w v}, Ri w v → w ∈ F → v ∈ F
  hered_V : ∀ {a : String} {w v}, Ri w v → w ∈ V a → v ∈ V a
  /-- `V` is full on `F`: fallible worlds validate every atom -/
  full_F : ∀ {a : String} {w}, w ∈ F → w ∈ V a

namespace ConstraintModel

/-- Forcing (Definition 3.2).  `⊥` holds exactly at fallible worlds. -/
def force (C : ConstraintModel) : C.W → PLLFormula → Prop
  | w, .prop a     => w ∈ C.V a
  | w, .falsePLL   => w ∈ C.F
  | w, .and φ ψ    => C.force w φ ∧ C.force w ψ
  | w, .or φ ψ     => C.force w φ ∨ C.force w ψ
  | w, .ifThen φ ψ => ∀ v, C.Ri w v → C.force v φ → C.force v ψ
  | w, .somehow φ  => ∀ v, C.Ri w v → ∃ u, C.Rm v u ∧ C.force u φ

/-- Validity is hereditary along `Rᵢ` (and hence along `Rₘ ⊆ Rᵢ`). -/
theorem force_hered (C : ConstraintModel) {φ : PLLFormula} :
    ∀ {w v : C.W}, C.Ri w v → C.force w φ → C.force v φ := by
  induction φ with
  | prop a => exact fun h hw => C.hered_V h hw
  | falsePLL => exact fun h hw => C.hered_F h hw
  | and φ ψ ihφ ihψ => exact fun h hw => ⟨ihφ h hw.1, ihψ h hw.2⟩
  | or φ ψ ihφ ihψ =>
      exact fun h hw => hw.elim (fun x => .inl (ihφ h x)) (fun x => .inr (ihψ h x))
  | ifThen φ ψ ihφ ihψ =>
      exact fun h hw u hvu hu => hw u (C.trans_i h hvu) hu
  | somehow φ ih =>
      exact fun h hw u hvu => hw u (C.trans_i h hvu)

/-- Fallible worlds validate every formula. -/
theorem force_of_fallible (C : ConstraintModel) {φ : PLLFormula} :
    ∀ {w : C.W}, w ∈ C.F → C.force w φ := by
  induction φ with
  | prop a => exact fun hw => C.full_F hw
  | falsePLL => exact fun hw => hw
  | and φ ψ ihφ ihψ => exact fun hw => ⟨ihφ hw, ihψ hw⟩
  | or φ ψ ihφ _ => exact fun hw => .inl (ihφ hw)
  | ifThen φ ψ _ ihψ =>
      exact fun hw v hv _ => ihψ (C.hered_F hv hw)
  | somehow φ ih =>
      exact fun hw v hv => ⟨v, C.refl_m v, ih (C.hered_F hv hw)⟩

end ConstraintModel

/-- Semantic consequence over a (list) context: at every world of every
constraint model where all hypotheses hold, the conclusion holds. -/
def Consequence (Γ : List PLLFormula) (φ : PLLFormula) : Prop :=
  ∀ (C : ConstraintModel) (w : C.W), (∀ ψ ∈ Γ, C.force w ψ) → C.force w φ

infix:60 " ⊨- " => Consequence

/-- **Soundness** (Theorem 3.3), in sequent form. -/
theorem soundness {Γ : List PLLFormula} {φ : PLLFormula}
    (p : LaxND Γ φ) : Γ ⊨- φ := by
  induction p with
  | @iden Γ φ h =>
      exact fun C w hΓ => hΓ φ h
  | @falsoElim Γ φ _ ih =>
      exact fun C w hΓ => C.force_of_fallible (ih C w hΓ)
  | @impIntro Γ φ ψ _ ih =>
      intro C w hΓ v hwv hv
      exact ih C v (fun χ hχ => by
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact hv
        · exact C.force_hered hwv (hΓ χ hχ))
  | @impElim Γ φ ψ _ _ ih₁ ih₂ =>
      exact fun C w hΓ => ih₁ C w hΓ w (C.refl_i w) (ih₂ C w hΓ)
  | @andIntro Γ φ ψ _ _ ih₁ ih₂ =>
      exact fun C w hΓ => ⟨ih₁ C w hΓ, ih₂ C w hΓ⟩
  | @andElim1 Γ φ ψ _ ih => exact fun C w hΓ => (ih C w hΓ).1
  | @andElim2 Γ φ ψ _ ih => exact fun C w hΓ => (ih C w hΓ).2
  | @orIntro1 Γ φ ψ _ ih => exact fun C w hΓ => .inl (ih C w hΓ)
  | @orIntro2 Γ φ ψ _ ih => exact fun C w hΓ => .inr (ih C w hΓ)
  | @orElim Γ φ ψ χ _ _ _ ih₀ ih₁ ih₂ =>
      intro C w hΓ
      rcases ih₀ C w hΓ with hφ | hψ
      · exact ih₁ C w (fun χ' hχ' => by
          rcases List.mem_cons.mp hχ' with rfl | hχ'
          · exact hφ
          · exact hΓ χ' hχ')
      · exact ih₂ C w (fun χ' hχ' => by
          rcases List.mem_cons.mp hχ' with rfl | hχ'
          · exact hψ
          · exact hΓ χ' hχ')
  | @laxIntro Γ φ _ ih =>
      intro C w hΓ v hwv
      exact ⟨v, C.refl_m v, C.force_hered hwv (ih C w hΓ)⟩
  | @laxElim Γ φ ψ _ _ ih₁ ih₂ =>
      intro C w hΓ v hwv
      obtain ⟨u, hvu, hu⟩ := ih₁ C w hΓ v hwv
      have hwu : C.Ri w u := C.trans_i hwv (C.sub_mi hvu)
      have hu' : ∀ χ ∈ φ :: Γ, C.force u χ := fun χ hχ => by
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact hu
        · exact C.force_hered hwu (hΓ χ hχ)
      obtain ⟨t, hut, ht⟩ := ih₂ C u hu' u (C.refl_i u)
      exact ⟨t, C.trans_m hvu hut, ht⟩

/-- Soundness for the empty context: derivable formulas are valid. -/
theorem soundness_valid {φ : PLLFormula} (p : LaxND [] φ) :
    ∀ (C : ConstraintModel) (w : C.W), C.force w φ :=
  fun C w => soundness p C w (by simp)

end PLLND
