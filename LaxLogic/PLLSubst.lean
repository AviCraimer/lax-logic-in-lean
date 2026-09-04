import LaxLogic.PLLTerms

/-!
# The substitution algebra (σ-calculus equations)

The composition laws for renaming and substitution of PLL proof terms —
the simp set that every normalisation argument consumes.  All statements
are *pointwise* in the renaming/substitution argument (no function
extensionality on the `∀ {φ}`-shaped maps), and every proof is a structural
induction whose binder cases reduce to a two-case analysis of a lifted
variable.  No casts, as ever: all indices are `φ :: Γ` or variables.
-/

open PLLFormula

namespace PLLND

/-! ### Congruence -/

theorem Tm.rename_congr : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) {ρ ρ' : Ren Γ Δ},
    (∀ {ψ : PLLFormula} (v : Var Γ ψ), ρ v = ρ' v) →
    t.rename ρ = t.rename ρ'
  | _, _, _, .var v, _, _, h => by simp [Tm.rename, h v]
  | _, _, _, .abort φ t, _, _, h => by
      simp [Tm.rename, t.rename_congr h]
  | _, _, _, .lam t, ρ, ρ', h => by
      simp only [Tm.rename]
      congr 1
      refine t.rename_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w => simp [Ren.lift, h w]
  | _, _, _, .app t s, _, _, h => by
      simp [Tm.rename, t.rename_congr h, s.rename_congr h]
  | _, _, _, .pair t s, _, _, h => by
      simp [Tm.rename, t.rename_congr h, s.rename_congr h]
  | _, _, _, .fst t, _, _, h => by simp [Tm.rename, t.rename_congr h]
  | _, _, _, .snd t, _, _, h => by simp [Tm.rename, t.rename_congr h]
  | _, _, _, .inl t, _, _, h => by simp [Tm.rename, t.rename_congr h]
  | _, _, _, .inr t, _, _, h => by simp [Tm.rename, t.rename_congr h]
  | _, _, _, .case t u₁ u₂, ρ, ρ', h => by
      simp only [Tm.rename]
      rw [t.rename_congr h]
      congr 1
      · exact u₁.rename_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => simp [Ren.lift, h w])
      · exact u₂.rename_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => simp [Ren.lift, h w])
  | _, _, _, .val t, _, _, h => by simp [Tm.rename, t.rename_congr h]
  | _, _, _, .bind t u, ρ, ρ', h => by
      simp only [Tm.rename]
      rw [t.rename_congr h]
      congr 1
      refine u.rename_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w => simp [Ren.lift, h w]

theorem Tm.subst_congr : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) {σ σ' : Sub Γ Δ},
    (∀ {ψ : PLLFormula} (v : Var Γ ψ), σ v = σ' v) →
    t.subst σ = t.subst σ'
  | _, _, _, .var v, _, _, h => by simp [Tm.subst, h v]
  | _, _, _, .abort φ t, _, _, h => by simp [Tm.subst, t.subst_congr h]
  | _, _, _, .lam t, σ, σ', h => by
      simp only [Tm.subst]
      congr 1
      refine t.subst_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w => simp [Sub.lift, h w]
  | _, _, _, .app t s, _, _, h => by
      simp [Tm.subst, t.subst_congr h, s.subst_congr h]
  | _, _, _, .pair t s, _, _, h => by
      simp [Tm.subst, t.subst_congr h, s.subst_congr h]
  | _, _, _, .fst t, _, _, h => by simp [Tm.subst, t.subst_congr h]
  | _, _, _, .snd t, _, _, h => by simp [Tm.subst, t.subst_congr h]
  | _, _, _, .inl t, _, _, h => by simp [Tm.subst, t.subst_congr h]
  | _, _, _, .inr t, _, _, h => by simp [Tm.subst, t.subst_congr h]
  | _, _, _, .case t u₁ u₂, σ, σ', h => by
      simp only [Tm.subst]
      rw [t.subst_congr h]
      congr 1
      · exact u₁.subst_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => simp [Sub.lift, h w])
      · exact u₂.subst_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => simp [Sub.lift, h w])
  | _, _, _, .val t, _, _, h => by simp [Tm.subst, t.subst_congr h]
  | _, _, _, .bind t u, σ, σ', h => by
      simp only [Tm.subst]
      rw [t.subst_congr h]
      congr 1
      refine u.subst_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w => simp [Sub.lift, h w]

/-! ### Composition laws -/

theorem Tm.rename_rename : ∀ {Γ Δ Θ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) (ρ : Ren Γ Δ) (ρ' : Ren Δ Θ),
    (t.rename ρ).rename ρ' = t.rename (fun v => ρ' (ρ v))
  | _, _, _, _, .var v, ρ, ρ' => rfl
  | _, _, _, _, .abort φ t, ρ, ρ' => by
      simp [Tm.rename, t.rename_rename]
  | _, _, _, _, .lam t, ρ, ρ' => by
      simp only [Tm.rename]
      rw [t.rename_rename]
      congr 1
      refine t.rename_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w => rfl
  | _, _, _, _, .app t s, ρ, ρ' => by
      simp [Tm.rename, t.rename_rename, s.rename_rename]
  | _, _, _, _, .pair t s, ρ, ρ' => by
      simp [Tm.rename, t.rename_rename, s.rename_rename]
  | _, _, _, _, .fst t, ρ, ρ' => by simp [Tm.rename, t.rename_rename]
  | _, _, _, _, .snd t, ρ, ρ' => by simp [Tm.rename, t.rename_rename]
  | _, _, _, _, .inl t, ρ, ρ' => by simp [Tm.rename, t.rename_rename]
  | _, _, _, _, .inr t, ρ, ρ' => by simp [Tm.rename, t.rename_rename]
  | _, _, _, _, .case t u₁ u₂, ρ, ρ' => by
      simp only [Tm.rename]
      rw [t.rename_rename, u₁.rename_rename, u₂.rename_rename]
      congr 1
      · exact u₁.rename_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => rfl)
      · exact u₂.rename_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => rfl)
  | _, _, _, _, .val t, ρ, ρ' => by simp [Tm.rename, t.rename_rename]
  | _, _, _, _, .bind t u, ρ, ρ' => by
      simp only [Tm.rename]
      rw [t.rename_rename, u.rename_rename]
      congr 1
      refine u.rename_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w => rfl

theorem Tm.subst_rename : ∀ {Γ Δ Θ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) (ρ : Ren Γ Δ) (σ : Sub Δ Θ),
    (t.rename ρ).subst σ = t.subst (fun v => σ (ρ v))
  | _, _, _, _, .var v, ρ, σ => rfl
  | _, _, _, _, .abort φ t, ρ, σ => by
      simp [Tm.rename, Tm.subst, t.subst_rename]
  | _, _, _, _, .lam t, ρ, σ => by
      simp only [Tm.rename, Tm.subst]
      rw [t.subst_rename]
      congr 1
      refine t.subst_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w => rfl
  | _, _, _, _, .app t s, ρ, σ => by
      simp [Tm.rename, Tm.subst, t.subst_rename, s.subst_rename]
  | _, _, _, _, .pair t s, ρ, σ => by
      simp [Tm.rename, Tm.subst, t.subst_rename, s.subst_rename]
  | _, _, _, _, .fst t, ρ, σ => by simp [Tm.rename, Tm.subst, t.subst_rename]
  | _, _, _, _, .snd t, ρ, σ => by simp [Tm.rename, Tm.subst, t.subst_rename]
  | _, _, _, _, .inl t, ρ, σ => by simp [Tm.rename, Tm.subst, t.subst_rename]
  | _, _, _, _, .inr t, ρ, σ => by simp [Tm.rename, Tm.subst, t.subst_rename]
  | _, _, _, _, .case t u₁ u₂, ρ, σ => by
      simp only [Tm.rename, Tm.subst]
      rw [t.subst_rename, u₁.subst_rename, u₂.subst_rename]
      congr 1
      · exact u₁.subst_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => rfl)
      · exact u₂.subst_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => rfl)
  | _, _, _, _, .val t, ρ, σ => by simp [Tm.rename, Tm.subst, t.subst_rename]
  | _, _, _, _, .bind t u, ρ, σ => by
      simp only [Tm.rename, Tm.subst]
      rw [t.subst_rename, u.subst_rename]
      congr 1
      refine u.subst_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w => rfl

theorem Tm.rename_subst : ∀ {Γ Δ Θ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) (σ : Sub Γ Δ) (ρ : Ren Δ Θ),
    (t.subst σ).rename ρ = t.subst (fun v => (σ v).rename ρ)
  | _, _, _, _, .var v, σ, ρ => rfl
  | _, _, _, _, .abort φ t, σ, ρ => by
      simp [Tm.rename, Tm.subst, t.rename_subst]
  | _, _, _, _, .lam t, σ, ρ => by
      simp only [Tm.rename, Tm.subst]
      rw [t.rename_subst]
      congr 1
      refine t.subst_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w =>
          show ((σ w).weaken).rename ρ.lift = ((σ w).rename ρ).weaken
          simp only [Tm.weaken]
          rw [Tm.rename_rename, Tm.rename_rename]
          exact (σ w).rename_congr (fun v => rfl)
  | _, _, _, _, .app t s, σ, ρ => by
      simp [Tm.rename, Tm.subst, t.rename_subst, s.rename_subst]
  | _, _, _, _, .pair t s, σ, ρ => by
      simp [Tm.rename, Tm.subst, t.rename_subst, s.rename_subst]
  | _, _, _, _, .fst t, σ, ρ => by simp [Tm.rename, Tm.subst, t.rename_subst]
  | _, _, _, _, .snd t, σ, ρ => by simp [Tm.rename, Tm.subst, t.rename_subst]
  | _, _, _, _, .inl t, σ, ρ => by simp [Tm.rename, Tm.subst, t.rename_subst]
  | _, _, _, _, .inr t, σ, ρ => by simp [Tm.rename, Tm.subst, t.rename_subst]
  | _, _, _, _, .case t u₁ u₂, σ, ρ => by
      simp only [Tm.rename, Tm.subst]
      rw [t.rename_subst, u₁.rename_subst, u₂.rename_subst]
      congr 1
      · refine u₁.subst_congr ?_
        intro ψ v
        cases v with
        | here => rfl
        | there w =>
            show ((σ w).weaken).rename ρ.lift = ((σ w).rename ρ).weaken
            simp only [Tm.weaken]
            rw [Tm.rename_rename, Tm.rename_rename]
            exact (σ w).rename_congr (fun v => rfl)
      · refine u₂.subst_congr ?_
        intro ψ v
        cases v with
        | here => rfl
        | there w =>
            show ((σ w).weaken).rename ρ.lift = ((σ w).rename ρ).weaken
            simp only [Tm.weaken]
            rw [Tm.rename_rename, Tm.rename_rename]
            exact (σ w).rename_congr (fun v => rfl)
  | _, _, _, _, .val t, σ, ρ => by simp [Tm.rename, Tm.subst, t.rename_subst]
  | _, _, _, _, .bind t u, σ, ρ => by
      simp only [Tm.rename, Tm.subst]
      rw [t.rename_subst, u.rename_subst]
      congr 1
      refine u.subst_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w =>
          show ((σ w).weaken).rename ρ.lift = ((σ w).rename ρ).weaken
          simp only [Tm.weaken]
          rw [Tm.rename_rename, Tm.rename_rename]
          exact (σ w).rename_congr (fun v => rfl)

theorem Tm.subst_subst : ∀ {Γ Δ Θ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) (σ : Sub Γ Δ) (τ : Sub Δ Θ),
    (t.subst σ).subst τ = t.subst (fun v => (σ v).subst τ)
  | _, _, _, _, .var v, σ, τ => rfl
  | _, _, _, _, .abort φ t, σ, τ => by
      simp [Tm.subst, t.subst_subst]
  | _, _, _, _, .lam t, σ, τ => by
      simp only [Tm.subst]
      rw [t.subst_subst]
      congr 1
      refine t.subst_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w =>
          show ((σ w).weaken).subst τ.lift = ((σ w).subst τ).weaken
          simp only [Tm.weaken]
          rw [Tm.subst_rename, Tm.rename_subst]
          exact (σ w).subst_congr (fun v => rfl)
  | _, _, _, _, .app t s, σ, τ => by
      simp [Tm.subst, t.subst_subst, s.subst_subst]
  | _, _, _, _, .pair t s, σ, τ => by
      simp [Tm.subst, t.subst_subst, s.subst_subst]
  | _, _, _, _, .fst t, σ, τ => by simp [Tm.subst, t.subst_subst]
  | _, _, _, _, .snd t, σ, τ => by simp [Tm.subst, t.subst_subst]
  | _, _, _, _, .inl t, σ, τ => by simp [Tm.subst, t.subst_subst]
  | _, _, _, _, .inr t, σ, τ => by simp [Tm.subst, t.subst_subst]
  | _, _, _, _, .case t u₁ u₂, σ, τ => by
      simp only [Tm.subst]
      rw [t.subst_subst, u₁.subst_subst, u₂.subst_subst]
      congr 1
      · refine u₁.subst_congr ?_
        intro ψ v
        cases v with
        | here => rfl
        | there w =>
            show ((σ w).weaken).subst τ.lift = ((σ w).subst τ).weaken
            simp only [Tm.weaken]
            rw [Tm.subst_rename, Tm.rename_subst]
            exact (σ w).subst_congr (fun v => rfl)
      · refine u₂.subst_congr ?_
        intro ψ v
        cases v with
        | here => rfl
        | there w =>
            show ((σ w).weaken).subst τ.lift = ((σ w).subst τ).weaken
            simp only [Tm.weaken]
            rw [Tm.subst_rename, Tm.rename_subst]
            exact (σ w).subst_congr (fun v => rfl)
  | _, _, _, _, .val t, σ, τ => by simp [Tm.subst, t.subst_subst]
  | _, _, _, _, .bind t u, σ, τ => by
      simp only [Tm.subst]
      rw [t.subst_subst, u.subst_subst]
      congr 1
      refine u.subst_congr ?_
      intro ψ v
      cases v with
      | here => rfl
      | there w =>
          show ((σ w).weaken).subst τ.lift = ((σ w).subst τ).weaken
          simp only [Tm.weaken]
          rw [Tm.subst_rename, Tm.rename_subst]
          exact (σ w).subst_congr (fun v => rfl)

/-! ### Identity and the single-substitution laws -/

theorem Tm.subst_ids : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ), t.subst Sub.ids = t
  | _, _, .var v => rfl
  | _, _, .abort φ t => by simp [Tm.subst, t.subst_ids]
  | _, _, .lam t => by
      simp only [Tm.subst]
      congr 1
      rw [show t.subst Sub.ids.lift = t.subst Sub.ids from
        t.subst_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => rfl), t.subst_ids]
  | _, _, .app t s => by simp [Tm.subst, t.subst_ids, s.subst_ids]
  | _, _, .pair t s => by simp [Tm.subst, t.subst_ids, s.subst_ids]
  | _, _, .fst t => by simp [Tm.subst, t.subst_ids]
  | _, _, .snd t => by simp [Tm.subst, t.subst_ids]
  | _, _, .inl t => by simp [Tm.subst, t.subst_ids]
  | _, _, .inr t => by simp [Tm.subst, t.subst_ids]
  | _, _, .case t u₁ u₂ => by
      simp only [Tm.subst]
      rw [t.subst_ids]
      congr 1
      · rw [show u₁.subst Sub.ids.lift = u₁.subst Sub.ids from
          u₁.subst_congr (fun {ψ} v => by
            cases v with
            | here => rfl
            | there w => rfl), u₁.subst_ids]
      · rw [show u₂.subst Sub.ids.lift = u₂.subst Sub.ids from
          u₂.subst_congr (fun {ψ} v => by
            cases v with
            | here => rfl
            | there w => rfl), u₂.subst_ids]
  | _, _, .val t => by simp [Tm.subst, t.subst_ids]
  | _, _, .bind t u => by
      simp only [Tm.subst]
      rw [t.subst_ids]
      congr 1
      rw [show u.subst Sub.ids.lift = u.subst Sub.ids from
        u.subst_congr (fun {ψ} v => by
          cases v with
          | here => rfl
          | there w => rfl), u.subst_ids]

/-- Weakening then substituting for the introduced variable is the
identity. -/
theorem Tm.weaken_subst1 {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm Γ φ) (s : Tm Γ ψ) : (t.weaken).subst1 s = t := by
  simp only [Tm.weaken, Tm.subst1]
  rw [Tm.subst_rename]
  exact (t.subst_congr (fun v => rfl)).trans t.subst_ids

/-- The key β-law: substituting under a lifted substitution. -/
theorem Tm.subst_lift_subst1 {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm (φ :: Γ) ψ) (σ : Sub Γ Δ) (s : Tm Δ φ) :
    (t.subst σ.lift).subst1 s = t.subst (Sub.cons s σ) := by
  simp only [Tm.subst1]
  rw [Tm.subst_subst]
  refine t.subst_congr ?_
  intro χ v
  cases v with
  | here => rfl
  | there w =>
      show ((σ w).weaken).subst (Sub.cons s Sub.ids) = σ w
      simp only [Tm.weaken]
      rw [Tm.subst_rename]
      exact ((σ w).subst_congr (fun v => rfl)).trans (σ w).subst_ids

/-- Renaming commutes with single substitution. -/
theorem Tm.rename_lift_subst1 {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm (φ :: Γ) ψ) (ρ : Ren Γ Δ) (s : Tm Δ φ) :
    (t.rename ρ.lift).subst1 s = t.subst (Sub.cons s (fun v => .var (ρ v))) := by
  simp only [Tm.subst1]
  rw [Tm.subst_rename]
  refine t.subst_congr ?_
  intro χ v
  cases v with
  | here => rfl
  | there w => rfl

end PLLND
