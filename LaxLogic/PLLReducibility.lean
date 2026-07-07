import LaxLogic.PLLStrongNorm
import LaxLogic.PLLTactics

/-!
# Strong normalisation of β-reduction (Kripke–Tait reducibility)

This file proves **strong normalisation of the β-fragment** `RStep` of the
PLL proof-term reduction: all of `Step` except `let`-assoc — function,
projection and case β, `let`-β (`bind (val s) u ⟶ u[s]`), and the full
congruence closure.  Together with `assoc_sn` (termination of the assoc
fragment alone, `PLLStrongNorm.lean`) this covers both halves of the
reduction; termination of their *interleaving* — full `Step` — is the
remaining Lindley–Stark ⊤⊤-lifting theorem and is discussed at the end of
the file.

The proof is Tait's reducibility method, arranged for intrinsic syntax:

* `Red φ t` is defined by recursion on the *formula*: Kripke function
  spaces at `⊃` (quantifying over renamings, since `lam`-bodies live in
  extended contexts), elimination clauses at `∧`, and *value clauses* at
  `∨` and `◯` (`t ⟶* val w` implies `Red w`, etc.) — the latter are sound
  here precisely because `RStep` has no assoc rule to restructure `bind`s;
* strong normalisation is conjoined into every clause, so CR1 is free;
* CR2 (closure under reduction), CR3 (neutral terms with reducible reducts
  are reducible) and renaming-stability are proved by induction on the
  formula; renaming-stability of the value clauses rests on the *reflection*
  of reduction under renaming, proved by a constructor-inversion grind;
* one closure lemma per construct, and the fundamental theorem
  (`fundamental`): reducibility-respecting substitutions send every term to
  a reducible one.  `beta_sn : ∀ t, RSN t` follows at the identity
  substitution.
-/

open PLLFormula

namespace PLLND

/-! ### The β-fragment -/

/-- The β-fragment of `Step`: everything except `bindAssoc`. -/
inductive RStep : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Tm Γ φ → Tm Γ φ → Prop
  | beta {Γ : List PLLFormula} {φ ψ : PLLFormula} (t : Tm (φ :: Γ) ψ) (s : Tm Γ φ) :
      RStep (.app (.lam t) s) (t.subst1 s)
  | fstPair {Γ : List PLLFormula} {φ ψ : PLLFormula} (t : Tm Γ φ) (s : Tm Γ ψ) :
      RStep (.fst (.pair t s)) t
  | sndPair {Γ : List PLLFormula} {φ ψ : PLLFormula} (t : Tm Γ φ) (s : Tm Γ ψ) :
      RStep (.snd (.pair t s)) s
  | caseInl {Γ : List PLLFormula} {φ ψ χ : PLLFormula} (s : Tm Γ φ)
      (u₁ : Tm (φ :: Γ) χ) (u₂ : Tm (ψ :: Γ) χ) :
      RStep (.case (.inl s) u₁ u₂) (u₁.subst1 s)
  | caseInr {Γ : List PLLFormula} {φ ψ χ : PLLFormula} (s : Tm Γ ψ)
      (u₁ : Tm (φ :: Γ) χ) (u₂ : Tm (ψ :: Γ) χ) :
      RStep (.case (.inr s) u₁ u₂) (u₂.subst1 s)
  | bindVal {Γ : List PLLFormula} {φ ψ : PLLFormula} (s : Tm Γ φ)
      (t : Tm (φ :: Γ) (somehow ψ)) :
      RStep (.bind (.val s) t) (t.subst1 s)
  | abortCong {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ .falsePLL} :
      RStep t t' → RStep (.abort φ t) (.abort φ t')
  | lamCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm (φ :: Γ) ψ} :
      RStep t t' → RStep (.lam t) (.lam t')
  | appCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t t' : Tm Γ (φ.ifThen ψ)} {s : Tm Γ φ} :
      RStep t t' → RStep (.app t s) (.app t' s)
  | appCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t : Tm Γ (φ.ifThen ψ)} {s s' : Tm Γ φ} :
      RStep s s' → RStep (.app t s) (.app t s')
  | pairCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t t' : Tm Γ φ} {s : Tm Γ ψ} :
      RStep t t' → RStep (.pair t s) (.pair t' s)
  | pairCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t : Tm Γ φ} {s s' : Tm Γ ψ} :
      RStep s s' → RStep (.pair t s) (.pair t s')
  | fstCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ (φ.and ψ)} :
      RStep t t' → RStep (.fst t) (.fst t')
  | sndCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ (φ.and ψ)} :
      RStep t t' → RStep (.snd t) (.snd t')
  | inlCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ φ} :
      RStep t t' → RStep (.inl (ψ := ψ) t) (.inl t')
  | inrCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ ψ} :
      RStep t t' → RStep (.inr (φ := φ) t) (.inr t')
  | caseCong₀ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t t' : Tm Γ (φ.or ψ)}
      {u₁ : Tm (φ :: Γ) χ} {u₂ : Tm (ψ :: Γ) χ} :
      RStep t t' → RStep (.case t u₁ u₂) (.case t' u₁ u₂)
  | caseCong₁ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t : Tm Γ (φ.or ψ)}
      {u₁ u₁' : Tm (φ :: Γ) χ} {u₂ : Tm (ψ :: Γ) χ} :
      RStep u₁ u₁' → RStep (.case t u₁ u₂) (.case t u₁' u₂)
  | caseCong₂ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t : Tm Γ (φ.or ψ)}
      {u₁ : Tm (φ :: Γ) χ} {u₂ u₂' : Tm (ψ :: Γ) χ} :
      RStep u₂ u₂' → RStep (.case t u₁ u₂) (.case t u₁ u₂')
  | valCong {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ φ} :
      RStep t t' → RStep (.val t) (.val t')
  | bindCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t t' : Tm Γ (somehow φ)} {u : Tm (φ :: Γ) (somehow ψ)} :
      RStep t t' → RStep (.bind t u) (.bind t' u)
  | bindCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t : Tm Γ (somehow φ)} {u u' : Tm (φ :: Γ) (somehow ψ)} :
      RStep u u' → RStep (.bind t u) (.bind t u')

/-- Every β-step is a step. -/
theorem RStep.toStep : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ}, RStep t t' → Step t t' := by
  intro Γ φ t t' h
  induction h <;> mirror

/-- Strong normalisation for the β-fragment. -/
def RSN {Γ : List PLLFormula} {φ : PLLFormula} (t : Tm Γ φ) : Prop :=
  Acc (fun a b : Tm Γ φ => RStep b a) t

theorem RSN.step {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ φ}
    (h : RSN t) (hs : RStep t t') : RSN t' :=
  h.inv hs

/-- Reflexive-transitive closure of `RStep`. -/
inductive RSteps {Γ : List PLLFormula} {φ : PLLFormula} :
    Tm Γ φ → Tm Γ φ → Prop
  | refl (t : Tm Γ φ) : RSteps t t
  | head {t t' t'' : Tm Γ φ} : RStep t t' → RSteps t' t'' → RSteps t t''

/-! ### SN congruence lemmas

Each is `Acc.of_inversion(₂)` at the step-inversion fact for one
constructor: a step of the compound is a step of a component. -/

theorem RSN.abort {Γ : List PLLFormula} (φ : PLLFormula) {t : Tm Γ .falsePLL}
    (h : RSN t) : RSN (Tm.abort φ t) :=
  Acc.of_inversion (f := Tm.abort φ)
    (fun hy => by cases hy with | abortCong h' => exact ⟨_, rfl, h'⟩) h

theorem RSN.lam {Γ : List PLLFormula} {φ ψ : PLLFormula} {b : Tm (φ :: Γ) ψ}
    (h : RSN b) : RSN (Tm.lam b) :=
  Acc.of_inversion (f := Tm.lam)
    (fun hy => by cases hy with | lamCong h' => exact ⟨_, rfl, h'⟩) h

theorem RSN.inl {Γ : List PLLFormula} {φ ψ : PLLFormula} {a : Tm Γ φ}
    (h : RSN a) : RSN (Tm.inl (ψ := ψ) a) :=
  Acc.of_inversion (f := Tm.inl (ψ := ψ))
    (fun hy => by cases hy with | inlCong h' => exact ⟨_, rfl, h'⟩) h

theorem RSN.inr {Γ : List PLLFormula} {φ ψ : PLLFormula} {a : Tm Γ ψ}
    (h : RSN a) : RSN (Tm.inr (φ := φ) a) :=
  Acc.of_inversion (f := Tm.inr (φ := φ))
    (fun hy => by cases hy with | inrCong h' => exact ⟨_, rfl, h'⟩) h

theorem RSN.val {Γ : List PLLFormula} {φ : PLLFormula} {a : Tm Γ φ}
    (h : RSN a) : RSN (Tm.val a) :=
  Acc.of_inversion (f := Tm.val)
    (fun hy => by cases hy with | valCong h' => exact ⟨_, rfl, h'⟩) h

theorem RSN.pair {Γ : List PLLFormula} {φ ψ : PLLFormula}
    {a : Tm Γ φ} {b : Tm Γ ψ} (ha : RSN a) (hb : RSN b) :
    RSN (Tm.pair a b) :=
  Acc.of_inversion₂ (f := Tm.pair)
    (fun hy => by
      cases hy with
      | pairCong₁ h' => exact .inl ⟨_, rfl, h'⟩
      | pairCong₂ h' => exact .inr ⟨_, rfl, h'⟩) ha hb

/-! ### The identity renaming -/

theorem Tm.rename_id : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ), t.rename (fun {_} v => v) = t
  | _, _, .var v => rfl
  | _, _, .abort φ t => by simp [Tm.rename, t.rename_id]
  | _, _, .lam t => by
      simp only [Tm.rename]
      rw [show t.rename (Ren.lift fun {_} v => v) = t.rename (fun {_} v => v)
        from t.rename_congr (by lift_cases), t.rename_id]
  | _, _, .app t s => by simp [Tm.rename, t.rename_id, s.rename_id]
  | _, _, .pair t s => by simp [Tm.rename, t.rename_id, s.rename_id]
  | _, _, .fst t => by simp [Tm.rename, t.rename_id]
  | _, _, .snd t => by simp [Tm.rename, t.rename_id]
  | _, _, .inl t => by simp [Tm.rename, t.rename_id]
  | _, _, .inr t => by simp [Tm.rename, t.rename_id]
  | _, _, .case t u₁ u₂ => by
      simp only [Tm.rename]
      rw [t.rename_id]
      congr 1
      · rw [show u₁.rename (Ren.lift fun {_} v => v) = u₁.rename (fun {_} v => v)
          from u₁.rename_congr (by lift_cases), u₁.rename_id]
      · rw [show u₂.rename (Ren.lift fun {_} v => v) = u₂.rename (fun {_} v => v)
          from u₂.rename_congr (by lift_cases), u₂.rename_id]
  | _, _, .val t => by simp [Tm.rename, t.rename_id]
  | _, _, .bind t u => by
      simp only [Tm.rename]
      rw [t.rename_id]
      congr 1
      rw [show u.rename (Ren.lift fun {_} v => v) = u.rename (fun {_} v => v)
        from u.rename_congr (by lift_cases), u.rename_id]

/-! ### Reduction versus renaming and substitution -/

/-- `subst1` after a lifted renaming. -/
theorem Tm.subst1_rename {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm (φ :: Γ) ψ) (s : Tm Γ φ) (ρ : Ren Γ Δ) :
    (t.subst1 s).rename ρ = (t.rename ρ.lift).subst1 (s.rename ρ) := by
  simp only [Tm.subst1]
  rw [Tm.rename_subst, Tm.subst_rename]
  exact t.subst_congr (by lift_cases)

/-- `subst1` after a lifted substitution (restatement of
`subst_lift_subst1` in the direction reduction needs). -/
theorem Tm.subst1_subst {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm (φ :: Γ) ψ) (s : Tm Γ φ) (σ : Sub Γ Δ) :
    (t.subst1 s).subst σ = (t.subst σ.lift).subst1 (s.subst σ) := by
  rw [Tm.subst_lift_subst1]
  simp only [Tm.subst1]
  rw [Tm.subst_subst]
  exact t.subst_congr (by lift_cases)

/-- β-steps are preserved by renaming. -/
theorem RStep.rename : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (ρ : Ren Γ Δ),
    RStep t t' → RStep (t.rename ρ) (t'.rename ρ) := by
  intro Γ Δ φ t t' ρ h
  induction h generalizing Δ <;> (try rw [Tm.subst1_rename]) <;> mirror

/-- β-steps are preserved by substitution. -/
theorem RStep.subst : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (σ : Sub Γ Δ),
    RStep t t' → RStep (t.subst σ) (t'.subst σ) := by
  intro Γ Δ φ t t' σ h
  induction h generalizing Δ <;> (try rw [Tm.subst1_subst]) <;> mirror

/-- SN transfers along renaming (any reduction of the term embeds into a
reduction of its renaming). -/
theorem RSN.of_rename {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} (ρ : Ren Γ Δ) (h : RSN (t.rename ρ)) : RSN t := by
  have := InvImage.accessible (f := fun t : Tm Γ φ => t.rename ρ) h
  refine Subrelation.accessible ?_ this
  intro a b hab
  exact RStep.rename ρ hab

/-! ### Constructor inversion under renaming -/

theorem Tm.rename_eq_lam {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    {t : Tm Γ (φ.ifThen ψ)} {ρ : Ren Γ Δ} {b : Tm (φ :: Δ) ψ}
    (h : t.rename ρ = .lam b) :
    ∃ b₀ : Tm (φ :: Γ) ψ, t = .lam b₀ ∧ b = b₀.rename ρ.lift := by
  cases t <;> simp [Tm.rename] at h
  case lam b₀ => exact ⟨b₀, rfl, h.symm⟩

theorem Tm.rename_eq_pair {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    {t : Tm Γ (φ.and ψ)} {ρ : Ren Γ Δ} {a : Tm Δ φ} {b : Tm Δ ψ}
    (h : t.rename ρ = .pair a b) :
    ∃ (a₀ : Tm Γ φ) (b₀ : Tm Γ ψ),
      t = .pair a₀ b₀ ∧ a = a₀.rename ρ ∧ b = b₀.rename ρ := by
  cases t <;> simp [Tm.rename] at h
  case pair a₀ b₀ => exact ⟨a₀, b₀, rfl, h.1.symm, h.2.symm⟩

theorem Tm.rename_eq_inl {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    {t : Tm Γ (φ.or ψ)} {ρ : Ren Γ Δ} {a : Tm Δ φ}
    (h : t.rename ρ = .inl a) :
    ∃ a₀ : Tm Γ φ, t = .inl a₀ ∧ a = a₀.rename ρ := by
  cases t <;> simp [Tm.rename] at h
  case inl a₀ => exact ⟨a₀, rfl, h.symm⟩

theorem Tm.rename_eq_inr {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    {t : Tm Γ (φ.or ψ)} {ρ : Ren Γ Δ} {a : Tm Δ ψ}
    (h : t.rename ρ = .inr a) :
    ∃ a₀ : Tm Γ ψ, t = .inr a₀ ∧ a = a₀.rename ρ := by
  cases t <;> simp [Tm.rename] at h
  case inr a₀ => exact ⟨a₀, rfl, h.symm⟩

theorem Tm.rename_eq_val {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ (somehow φ)} {ρ : Ren Γ Δ} {a : Tm Δ φ}
    (h : t.rename ρ = .val a) :
    ∃ a₀ : Tm Γ φ, t = .val a₀ ∧ a = a₀.rename ρ := by
  cases t <;> simp [Tm.rename] at h
  case val a₀ => exact ⟨a₀, rfl, h.symm⟩

/-- **Reflection of β-reduction under renaming**: every step of a renamed
term is the renaming of a step. -/
theorem RStep.rename_reflect : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ), ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) {y : Tm Δ φ},
    RStep (t.rename ρ) y → ∃ t' : Tm Γ φ, RStep t t' ∧ y = t'.rename ρ := by
  intro Γ φ t
  induction t with
  | var v =>
      intro Δ ρ y h
      cases h
  | abort φ t iht =>
      intro Δ ρ y h
      cases h with
      | abortCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨.abort φ t', .abortCong hs, rfl⟩
  | lam t iht =>
      intro Δ ρ y h
      cases h with
      | lamCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ.lift h'
          exact ⟨.lam t', .lamCong hs, rfl⟩
  | app t s iht ihs =>
      intro Δ ρ y h
      cases t
      case lam b₀ =>
          cases h with
          | beta _ _ => exact ⟨b₀.subst1 s, .beta b₀ s, (Tm.subst1_rename ..).symm⟩
          | appCong₁ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .appCong₁ hs, rfl⟩
          | appCong₂ h' =>
              obtain ⟨s', hs, rfl⟩ := ihs ρ h'
              exact ⟨_, .appCong₂ hs, rfl⟩
      all_goals
        cases h with
        | appCong₁ h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .appCong₁ hs, rfl⟩
        | appCong₂ h' =>
            obtain ⟨s', hs, rfl⟩ := ihs ρ h'
            exact ⟨_, .appCong₂ hs, rfl⟩
  | pair t s iht ihs =>
      intro Δ ρ y h
      cases h with
      | pairCong₁ h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨_, .pairCong₁ hs, rfl⟩
      | pairCong₂ h' =>
          obtain ⟨s', hs, rfl⟩ := ihs ρ h'
          exact ⟨_, .pairCong₂ hs, rfl⟩
  | fst t iht =>
      intro Δ ρ y h
      cases t
      case pair a₀ b₀ =>
          cases h with
          | fstPair _ _ => exact ⟨a₀, .fstPair a₀ b₀, rfl⟩
          | fstCong h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .fstCong hs, rfl⟩
      all_goals
        cases h with
        | fstCong h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .fstCong hs, rfl⟩
  | snd t iht =>
      intro Δ ρ y h
      cases t
      case pair a₀ b₀ =>
          cases h with
          | sndPair _ _ => exact ⟨b₀, .sndPair a₀ b₀, rfl⟩
          | sndCong h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .sndCong hs, rfl⟩
      all_goals
        cases h with
        | sndCong h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .sndCong hs, rfl⟩
  | inl t iht =>
      intro Δ ρ y h
      cases h with
      | inlCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨_, .inlCong hs, rfl⟩
  | inr t iht =>
      intro Δ ρ y h
      cases h with
      | inrCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨_, .inrCong hs, rfl⟩
  | case t u₁ u₂ iht ih₁ ih₂ =>
      intro Δ ρ y h
      cases t
      case inl a₀ =>
          cases h with
          | caseInl _ _ _ =>
              exact ⟨u₁.subst1 a₀, .caseInl a₀ u₁ u₂, (Tm.subst1_rename ..).symm⟩
          | caseCong₀ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .caseCong₀ hs, rfl⟩
          | caseCong₁ h' =>
              obtain ⟨u₁', hs, rfl⟩ := ih₁ ρ.lift h'
              exact ⟨_, .caseCong₁ hs, rfl⟩
          | caseCong₂ h' =>
              obtain ⟨u₂', hs, rfl⟩ := ih₂ ρ.lift h'
              exact ⟨_, .caseCong₂ hs, rfl⟩
      case inr a₀ =>
          cases h with
          | caseInr _ _ _ =>
              exact ⟨u₂.subst1 a₀, .caseInr a₀ u₁ u₂, (Tm.subst1_rename ..).symm⟩
          | caseCong₀ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .caseCong₀ hs, rfl⟩
          | caseCong₁ h' =>
              obtain ⟨u₁', hs, rfl⟩ := ih₁ ρ.lift h'
              exact ⟨_, .caseCong₁ hs, rfl⟩
          | caseCong₂ h' =>
              obtain ⟨u₂', hs, rfl⟩ := ih₂ ρ.lift h'
              exact ⟨_, .caseCong₂ hs, rfl⟩
      all_goals
        cases h with
        | caseCong₀ h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .caseCong₀ hs, rfl⟩
        | caseCong₁ h' =>
            obtain ⟨u₁', hs, rfl⟩ := ih₁ ρ.lift h'
            exact ⟨_, .caseCong₁ hs, rfl⟩
        | caseCong₂ h' =>
            obtain ⟨u₂', hs, rfl⟩ := ih₂ ρ.lift h'
            exact ⟨_, .caseCong₂ hs, rfl⟩
  | val t iht =>
      intro Δ ρ y h
      cases h with
      | valCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨_, .valCong hs, rfl⟩
  | bind t u iht ihu =>
      intro Δ ρ y h
      cases t
      case val a₀ =>
          cases h with
          | bindVal _ _ =>
              exact ⟨u.subst1 a₀, .bindVal a₀ u, (Tm.subst1_rename ..).symm⟩
          | bindCong₁ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .bindCong₁ hs, rfl⟩
          | bindCong₂ h' =>
              obtain ⟨u', hs, rfl⟩ := ihu ρ.lift h'
              exact ⟨_, .bindCong₂ hs, rfl⟩
      all_goals
        cases h with
        | bindCong₁ h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .bindCong₁ hs, rfl⟩
        | bindCong₂ h' =>
            obtain ⟨u', hs, rfl⟩ := ihu ρ.lift h'
            exact ⟨_, .bindCong₂ hs, rfl⟩

/-- Multi-step reflection under renaming. -/
theorem RSteps.rename_reflect {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} {ρ : Ren Γ Δ} {z : Tm Δ φ}
    (h : RSteps (t.rename ρ) z) :
    ∃ t₀ : Tm Γ φ, RSteps t t₀ ∧ z = t₀.rename ρ := by
  generalize hx : t.rename ρ = x at h
  induction h generalizing t with
  | refl _ => exact ⟨t, .refl t, hx.symm⟩
  | head hs _ ih =>
      subst hx
      obtain ⟨t', hst, rfl⟩ := RStep.rename_reflect _ ρ hs
      obtain ⟨t₀, hsteps, rfl⟩ := ih rfl
      exact ⟨t₀, .head hst hsteps, rfl⟩

/-! ### Reducibility -/

/-- Non-introduction (neutral) terms. -/
def Neut : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → Prop
  | _, _, .lam _ => False
  | _, _, .pair _ _ => False
  | _, _, .inl _ => False
  | _, _, .inr _ => False
  | _, _, .val _ => False
  | _, _, _ => True

theorem Neut.rename : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} (ρ : Ren Γ Δ), Neut t → Neut (t.rename ρ) := by
  intro Γ Δ φ t ρ h
  cases t <;> first | exact h.elim | trivial

/-- SN transfers forwards along renaming, by reflection. -/
theorem RSN.rename {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} (ρ : Ren Γ Δ) (h : RSN t) : RSN (t.rename ρ) :=
  Acc.of_inversion (f := fun t : Tm Γ φ => t.rename ρ)
    (fun hy => by
      obtain ⟨t', hs, heq⟩ := RStep.rename_reflect _ ρ hy
      exact ⟨t', heq, hs⟩) h

/-- **The reducibility predicate**, by recursion on the formula.
Strong normalisation is conjoined into every clause. -/
def Red : (φ : PLLFormula) → ∀ {Γ : List PLLFormula}, Tm Γ φ → Prop
  | .prop _, _, t => RSN t
  | .falsePLL, _, t => RSN t
  | .ifThen A B, Γ, t => RSN t ∧
      ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) (s : Tm Δ A),
        Red A s → Red B (.app (t.rename ρ) s)
  | .and A B, _, t => RSN t ∧ Red A (.fst t) ∧ Red B (.snd t)
  | .or A B, _, t => RSN t ∧
      (∀ {w}, RSteps t (.inl w) → Red A w) ∧
      (∀ {w}, RSteps t (.inr w) → Red B w)
  | .somehow A, _, t => RSN t ∧ ∀ {w}, RSteps t (.val w) → Red A w

/-- CR1: reducible terms are strongly normalising (free, by construction). -/
theorem Red.sn : ∀ {φ : PLLFormula} {Γ : List PLLFormula} {t : Tm Γ φ},
    Red φ t → RSN t := by
  intro φ
  cases φ <;> intro Γ t h
  · exact h
  · exact h
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

/-- CR2: reducibility is closed under reduction. -/
theorem Red.step {φ : PLLFormula} : ∀ {Γ : List PLLFormula}
    {t t' : Tm Γ φ}, Red φ t → RStep t t' → Red φ t' := by
  induction φ with
  | prop a => exact fun h hs => RSN.step h hs
  | falsePLL => exact fun h hs => RSN.step h hs
  | ifThen A B ihA ihB =>
      intro Γ t t' h hs
      refine ⟨h.1.step hs, ?_⟩
      intro Δ ρ s hsred
      exact ihB (h.2 ρ s hsred) (.appCong₁ (hs.rename ρ))
  | and A B ihA ihB =>
      intro Γ t t' h hs
      exact ⟨h.1.step hs, ihA h.2.1 (.fstCong hs), ihB h.2.2 (.sndCong hs)⟩
  | or A B ihA ihB =>
      intro Γ t t' h hs
      exact ⟨h.1.step hs,
        fun hst => h.2.1 (.head hs hst),
        fun hst => h.2.2 (.head hs hst)⟩
  | somehow A ihA =>
      intro Γ t t' h hs
      exact ⟨h.1.step hs, fun hst => h.2 (.head hs hst)⟩

/-- CR2, many steps. -/
theorem Red.steps {φ : PLLFormula} {Γ : List PLLFormula}
    {t t' : Tm Γ φ} (h : Red φ t) (hs : RSteps t t') : Red φ t' := by
  induction hs with
  | refl _ => exact h
  | head h₁ hrest ih =>
      exact ih (Red.step h h₁)

/-- Reducibility is stable under renaming. -/
theorem Red.rename {φ : PLLFormula} : ∀ {Γ Δ : List PLLFormula}
    (ρ : Ren Γ Δ) {t : Tm Γ φ}, Red φ t → Red φ (t.rename ρ) := by
  induction φ with
  | prop a =>
      intro Γ Δ ρ t h
      exact RSN.rename ρ h
  | falsePLL =>
      intro Γ Δ ρ t h
      exact RSN.rename ρ h
  | ifThen A B ihA ihB =>
      intro Γ Δ ρ t h
      refine ⟨h.1.rename ρ, ?_⟩
      intro Δ' ρ' s hs
      rw [Tm.rename_rename]
      exact h.2 (fun v => ρ' (ρ v)) s hs
  | and A B ihA ihB =>
      intro Γ Δ ρ t h
      exact ⟨h.1.rename ρ, ihA ρ h.2.1, ihB ρ h.2.2⟩
  | or A B ihA ihB =>
      intro Γ Δ ρ t h
      refine ⟨h.1.rename ρ, ?_, ?_⟩
      · intro w hst
        obtain ⟨t₀, hsteps, heq⟩ := RSteps.rename_reflect hst
        obtain ⟨w₀, rfl, rfl⟩ := Tm.rename_eq_inl heq.symm
        exact ihA ρ (h.2.1 hsteps)
      · intro w hst
        obtain ⟨t₀, hsteps, heq⟩ := RSteps.rename_reflect hst
        obtain ⟨w₀, rfl, rfl⟩ := Tm.rename_eq_inr heq.symm
        exact ihB ρ (h.2.2 hsteps)
  | somehow A ihA =>
      intro Γ Δ ρ t h
      refine ⟨h.1.rename ρ, ?_⟩
      intro w hst
      obtain ⟨t₀, hsteps, heq⟩ := RSteps.rename_reflect hst
      obtain ⟨w₀, rfl, rfl⟩ := Tm.rename_eq_val heq.symm
      exact ihA ρ (h.2 hsteps)

/-- CR3: a neutral term whose one-step reducts are all reducible is
reducible. -/
theorem Red.cr3 {φ : PLLFormula} : ∀ {Γ : List PLLFormula} {t : Tm Γ φ},
    Neut t → (∀ t', RStep t t' → Red φ t') → Red φ t := by
  induction φ with
  | prop a =>
      intro Γ t _ hred
      exact .intro _ (fun y hy => hred y hy)
  | falsePLL =>
      intro Γ t _ hred
      exact .intro _ (fun y hy => hred y hy)
  | ifThen A B ihA ihB =>
      intro Γ t hneut hred
      refine ⟨.intro _ (fun y hy => (hred y hy).sn), ?_⟩
      intro Δ ρ s hs
      have hsn : RSN s := hs.sn
      revert hs
      induction hsn with
      | intro s hacc ihs =>
          intro hs
          refine ihB trivial ?_
          intro y hy
          generalize hX : t.rename ρ = X at hy
          cases hy with
          | beta b s' =>
              obtain ⟨b₀, hb₀, _⟩ := Tm.rename_eq_lam hX
              subst hb₀
              exact hneut.elim
          | appCong₁ h' =>
              subst hX
              obtain ⟨t'', hs'', rfl⟩ := RStep.rename_reflect t ρ h'
              exact (hred t'' hs'').2 ρ s hs
          | appCong₂ h' =>
              subst hX
              exact ihs _ h' (Red.step hs h')
  | and A B ihA ihB =>
      intro Γ t hneut hred
      refine ⟨.intro _ (fun y hy => (hred y hy).sn), ?_, ?_⟩
      · refine ihA trivial ?_
        intro y hy
        cases hy with
        | fstPair a b => exact hneut.elim
        | fstCong h' => exact (hred _ h').2.1
      · refine ihB trivial ?_
        intro y hy
        cases hy with
        | sndPair a b => exact hneut.elim
        | sndCong h' => exact (hred _ h').2.2
  | or A B ihA ihB =>
      intro Γ t hneut hred
      refine ⟨.intro _ (fun y hy => (hred y hy).sn), ?_, ?_⟩
      · intro w hst
        cases hst with
        | refl _ => exact hneut.elim
        | head h₁ hrest => exact (hred _ h₁).2.1 hrest
      · intro w hst
        cases hst with
        | refl _ => exact hneut.elim
        | head h₁ hrest => exact (hred _ h₁).2.2 hrest
  | somehow A ihA =>
      intro Γ t hneut hred
      refine ⟨.intro _ (fun y hy => (hred y hy).sn), ?_⟩
      intro w hst
      cases hst with
      | refl _ => exact hneut.elim
      | head h₁ hrest => exact (hred _ h₁).2 hrest

/-- Variables are reducible. -/
theorem Red.var {φ : PLLFormula} {Γ : List PLLFormula} (v : Var Γ φ) :
    Red φ (.var v) :=
  Red.cr3 trivial (fun _ hy => by cases hy)

/-! ### Closure lemmas -/

/-- Substitution by variables is renaming. -/
theorem Tm.subst_var : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) (ρ : Ren Γ Δ), t.subst (fun {_} v => .var (ρ v)) = t.rename ρ
  | _, _, _, .var v, ρ => rfl
  | _, _, _, .abort φ t, ρ => by simp [Tm.subst, Tm.rename, t.subst_var]
  | _, _, _, .lam t, ρ => by
      simp only [Tm.subst, Tm.rename]
      rw [show t.subst (Sub.lift fun {_} v => .var (ρ v))
          = t.subst (fun {_} v => .var (ρ.lift v)) from
        t.subst_congr (by lift_cases), t.subst_var]
  | _, _, _, .app t s, ρ => by
      simp [Tm.subst, Tm.rename, t.subst_var, s.subst_var]
  | _, _, _, .pair t s, ρ => by
      simp [Tm.subst, Tm.rename, t.subst_var, s.subst_var]
  | _, _, _, .fst t, ρ => by simp [Tm.subst, Tm.rename, t.subst_var]
  | _, _, _, .snd t, ρ => by simp [Tm.subst, Tm.rename, t.subst_var]
  | _, _, _, .inl t, ρ => by simp [Tm.subst, Tm.rename, t.subst_var]
  | _, _, _, .inr t, ρ => by simp [Tm.subst, Tm.rename, t.subst_var]
  | _, _, _, .case t u₁ u₂, ρ => by
      simp only [Tm.subst, Tm.rename]
      rw [t.subst_var]
      congr 1
      · rw [show u₁.subst (Sub.lift fun {_} v => .var (ρ v))
            = u₁.subst (fun {_} v => .var (ρ.lift v)) from
          u₁.subst_congr (by lift_cases), u₁.subst_var]
      · rw [show u₂.subst (Sub.lift fun {_} v => .var (ρ v))
            = u₂.subst (fun {_} v => .var (ρ.lift v)) from
          u₂.subst_congr (by lift_cases), u₂.subst_var]
  | _, _, _, .val t, ρ => by simp [Tm.subst, Tm.rename, t.subst_var]
  | _, _, _, .bind t u, ρ => by
      simp only [Tm.subst, Tm.rename]
      rw [t.subst_var]
      congr 1
      rw [show u.subst (Sub.lift fun {_} v => .var (ρ v))
          = u.subst (fun {_} v => .var (ρ.lift v)) from
        u.subst_congr (by lift_cases), u.subst_var]

/-- The key β-equation for the `lam` case of the fundamental theorem. -/
theorem subst_lift_rename_subst1 {Γ Δ Δ' : List PLLFormula}
    {A B : PLLFormula} (b : Tm (A :: Γ) B) (σ : Sub Γ Δ) (ρ : Ren Δ Δ')
    (s : Tm Δ' A) :
    ((b.subst σ.lift).rename ρ.lift).subst1 s
      = b.subst (Sub.cons s (fun {χ} v => (σ v).rename ρ)) := by
  simp only [Tm.subst1]
  rw [Tm.rename_subst, Tm.subst_subst]
  refine b.subst_congr ?_
  intro χ v
  cases v with
  | here => rfl
  | there w =>
      show (((σ w).weaken).rename ρ.lift).subst (Sub.cons s Sub.ids)
        = (σ w).rename ρ
      simp only [Tm.weaken]
      rw [Tm.rename_rename, Tm.subst_rename]
      exact ((σ w).subst_congr (fun v => rfl)).trans ((σ w).subst_var ρ)

/-- Abort terms over SN scrutinees are reducible. -/
theorem red_abort {Γ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ .falsePLL} (h : RSN t) : Red φ (.abort φ t) :=
  Acc.selfInduction (P := fun t => Red φ (Tm.abort φ t)) h fun t _ ih =>
    Red.cr3 trivial fun y hy => by
      cases hy with
      | abortCong h' => exact ih _ h'

/-- β-expansion for application. -/
theorem red_beta_exp {Γ : List PLLFormula} {A B : PLLFormula}
    {b : Tm (A :: Γ) B} (hbsn : RSN b) {s : Tm Γ A} (hs : Red A s)
    (H : ∀ s' : Tm Γ A, Red A s' → Red B (b.subst1 s')) :
    Red B (.app (.lam b) s) := by
  refine Acc.pairInduction (P := fun b s =>
      Red A s → (∀ s', Red A s' → Red B (b.subst1 s')) →
      Red B (.app (.lam b) s)) hbsn hs.sn ?_ hs H
  intro b s _ _ ihb ihs hs H
  refine Red.cr3 trivial fun y hy => ?_
  cases hy with
  | beta _ _ => exact H s hs
  | appCong₁ h' =>
      cases h' with
      | lamCong h'' =>
          exact ihb _ h'' hs
            (fun s' hs' => (H s' hs').step (RStep.subst _ h''))
  | appCong₂ h' => exact ihs _ h' (hs.step h') H

/-- Abstractions with reducible instances are reducible. -/
theorem red_lam {Γ : List PLLFormula} {A B : PLLFormula} {b : Tm (A :: Γ) B}
    (hbsn : RSN b)
    (H : ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) (s : Tm Δ A),
      Red A s → Red B ((b.rename ρ.lift).subst1 s)) :
    Red (A.ifThen B) (.lam b) :=
  ⟨hbsn.lam, fun ρ _s hs =>
    red_beta_exp (hbsn.rename ρ.lift) hs (fun s' hs' => H ρ s' hs')⟩

/-- Pairs of reducibles are reducible. -/
theorem red_pair {Γ : List PLLFormula} {A B : PLLFormula}
    {a : Tm Γ A} {b : Tm Γ B} (ha : Red A a) (hb : Red B b) :
    Red (A.and B) (.pair a b) := by
  refine Acc.pairInduction (P := fun a b =>
      Red A a → Red B b → Red (A.and B) (.pair a b)) ha.sn hb.sn ?_ ha hb
  intro a b _ _ iha ihb ha hb
  refine ⟨RSN.pair ha.sn hb.sn, ?_, ?_⟩
  · refine Red.cr3 trivial fun y hy => ?_
    cases hy with
    | fstPair _ _ => exact ha
    | fstCong h' =>
        cases h' with
        | pairCong₁ h'' => exact (iha _ h'' (ha.step h'') hb).2.1
        | pairCong₂ h'' => exact (ihb _ h'' ha (hb.step h'')).2.1
  · refine Red.cr3 trivial fun y hy => ?_
    cases hy with
    | sndPair _ _ => exact hb
    | sndCong h' =>
        cases h' with
        | pairCong₁ h'' => exact (iha _ h'' (ha.step h'') hb).2.2
        | pairCong₂ h'' => exact (ihb _ h'' ha (hb.step h'')).2.2

/-- Reduction sequences from `inl` stay `inl`. -/
theorem rsteps_inl : ∀ {Γ : List PLLFormula} {A B : PLLFormula}
    {x z : Tm Γ (A.or B)}, RSteps x z →
    ∀ {a : Tm Γ A}, x = .inl a → ∃ a', z = .inl a' ∧ RSteps a a' := by
  intro Γ A B x z h
  induction h with
  | refl t =>
      intro a hx
      exact ⟨a, hx, .refl a⟩
  | head h₁ hrest ih =>
      intro a hx
      subst hx
      cases h₁ with
      | inlCong h' =>
          obtain ⟨a', rfl, hsteps⟩ := ih rfl
          exact ⟨a', rfl, .head h' hsteps⟩

/-- Reduction sequences from `inr` stay `inr`. -/
theorem rsteps_inr : ∀ {Γ : List PLLFormula} {A B : PLLFormula}
    {x z : Tm Γ (A.or B)}, RSteps x z →
    ∀ {a : Tm Γ B}, x = .inr a → ∃ a', z = .inr a' ∧ RSteps a a' := by
  intro Γ A B x z h
  induction h with
  | refl t =>
      intro a hx
      exact ⟨a, hx, .refl a⟩
  | head h₁ hrest ih =>
      intro a hx
      subst hx
      cases h₁ with
      | inrCong h' =>
          obtain ⟨a', rfl, hsteps⟩ := ih rfl
          exact ⟨a', rfl, .head h' hsteps⟩

/-- Reduction sequences from `val` stay `val`. -/
theorem rsteps_val : ∀ {Γ : List PLLFormula} {A : PLLFormula}
    {x z : Tm Γ (somehow A)}, RSteps x z →
    ∀ {a : Tm Γ A}, x = .val a → ∃ a', z = .val a' ∧ RSteps a a' := by
  intro Γ A x z h
  induction h with
  | refl t =>
      intro a hx
      exact ⟨a, hx, .refl a⟩
  | head h₁ hrest ih =>
      intro a hx
      subst hx
      cases h₁ with
      | valCong h' =>
          obtain ⟨a', rfl, hsteps⟩ := ih rfl
          exact ⟨a', rfl, .head h' hsteps⟩

/-- Left injections of reducibles are reducible. -/
theorem red_inl {Γ : List PLLFormula} {A B : PLLFormula} {a : Tm Γ A}
    (ha : Red A a) : Red (A.or B) (.inl a) :=
  ⟨RSN.inl ha.sn,
   fun hst => by
     obtain ⟨a', heq, hsteps⟩ := rsteps_inl hst rfl
     cases heq
     exact ha.steps hsteps,
   fun hst => by
     obtain ⟨a', heq, _⟩ := rsteps_inl hst rfl
     exact Tm.noConfusion heq⟩

/-- Right injections of reducibles are reducible. -/
theorem red_inr {Γ : List PLLFormula} {A B : PLLFormula} {a : Tm Γ B}
    (ha : Red B a) : Red (A.or B) (.inr a) :=
  ⟨RSN.inr ha.sn,
   fun hst => by
     obtain ⟨a', heq, _⟩ := rsteps_inr hst rfl
     exact Tm.noConfusion heq,
   fun hst => by
     obtain ⟨a', heq, hsteps⟩ := rsteps_inr hst rfl
     cases heq
     exact ha.steps hsteps⟩

/-- `val`s of reducibles are reducible. -/
theorem red_val {Γ : List PLLFormula} {A : PLLFormula} {a : Tm Γ A}
    (ha : Red A a) : Red (somehow A) (.val a) :=
  ⟨RSN.val ha.sn,
   fun hst => by
     obtain ⟨a', heq, hsteps⟩ := rsteps_val hst rfl
     cases heq
     exact ha.steps hsteps⟩

/-- Case analysis over reducibles with reducible branches is reducible. -/
theorem red_case {Γ : List PLLFormula} {A B χ : PLLFormula}
    {t : Tm Γ (A.or B)} {u₁ : Tm (A :: Γ) χ} {u₂ : Tm (B :: Γ) χ}
    (h1sn : RSN u₁) (h2sn : RSN u₂) (ht : Red (A.or B) t)
    (H₁ : ∀ s : Tm Γ A, Red A s → Red χ (u₁.subst1 s))
    (H₂ : ∀ s : Tm Γ B, Red B s → Red χ (u₂.subst1 s)) :
    Red χ (.case t u₁ u₂) := by
  refine Acc.tripleInduction (P := fun t u₁ u₂ =>
      Red (A.or B) t → (∀ s, Red A s → Red χ (u₁.subst1 s)) →
      (∀ s, Red B s → Red χ (u₂.subst1 s)) → Red χ (.case t u₁ u₂))
    ht.sn h1sn h2sn ?_ ht H₁ H₂
  intro t u₁ u₂ _ _ _ iht ih1 ih2 ht H₁ H₂
  refine Red.cr3 trivial fun y hy => ?_
  cases hy with
  | caseInl s _ _ => exact H₁ s (ht.2.1 (.refl _))
  | caseInr s _ _ => exact H₂ s (ht.2.2 (.refl _))
  | caseCong₀ h' => exact iht _ h' (ht.step h') H₁ H₂
  | caseCong₁ h' =>
      exact ih1 _ h' ht (fun s hs => (H₁ s hs).step (RStep.subst _ h')) H₂
  | caseCong₂ h' =>
      exact ih2 _ h' ht H₁ (fun s hs => (H₂ s hs).step (RStep.subst _ h'))

/-- Value analysis of reduction sequences from a `bind` (no assoc rule in
the β-fragment, so a `bind` reaches a `val` only through `let`-β). -/
theorem rsteps_bind_val : ∀ {Γ : List PLLFormula} {A B : PLLFormula}
    {x z : Tm Γ (somehow B)}, RSteps x z →
    ∀ {t : Tm Γ (somehow A)} {u : Tm (A :: Γ) (somehow B)}, x = .bind t u →
    Red (somehow A) t →
    (∀ s : Tm Γ A, Red A s → Red (somehow B) (u.subst1 s)) →
    ∀ {w : Tm Γ B}, z = .val w → Red B w := by
  intro Γ A B x z h
  induction h with
  | refl t =>
      intro t' u hx ht H w hz
      subst hx
      exact Tm.noConfusion hz
  | head h₁ hrest ih =>
      intro t' u hx ht H w hz
      subst hx
      cases h₁ with
      | bindVal s _ =>
          subst hz
          exact (H s (ht.2 (.refl _))).2 hrest
      | bindCong₁ h' =>
          exact ih rfl (Red.step ht h') H hz
      | bindCong₂ h' =>
          exact ih rfl ht
            (fun s hs => Red.step (H s hs) (RStep.subst _ h')) hz

/-- Binds of reducibles with reducible bodies are reducible. -/
theorem red_bind {Γ : List PLLFormula} {A B : PLLFormula}
    {t : Tm Γ (somehow A)} {u : Tm (A :: Γ) (somehow B)}
    (husn : RSN u) (ht : Red (somehow A) t)
    (H : ∀ s : Tm Γ A, Red A s → Red (somehow B) (u.subst1 s)) :
    Red (somehow B) (.bind t u) := by
  refine Acc.pairInduction (P := fun t u =>
      Red (somehow A) t → (∀ s, Red A s → Red (somehow B) (u.subst1 s)) →
      Red (somehow B) (.bind t u)) ht.sn husn ?_ ht H
  intro t u _ _ iht ihu ht H
  refine ⟨.intro _ fun y hy => ?_, fun hst => rsteps_bind_val hst rfl ht H rfl⟩
  cases hy with
  | bindVal s _ => exact (H s (ht.2 (.refl _))).sn
  | bindCong₁ h' => exact (iht _ h' (ht.step h') H).sn
  | bindCong₂ h' =>
      exact (ihu _ h' ht (fun s hs => (H s hs).step (RStep.subst _ h'))).sn

/-! ### The fundamental theorem and strong normalisation -/

/-- Reducibility-respecting substitutions. -/
def RedS {Γ Δ : List PLLFormula} (σ : Sub Γ Δ) : Prop :=
  ∀ {φ : PLLFormula} (v : Var Γ φ), Red φ (σ v)

theorem RedS.ids {Γ : List PLLFormula} : RedS (Sub.ids (Γ := Γ)) :=
  fun v => Red.var v

theorem RedS.cons {Γ Δ : List PLLFormula} {A : PLLFormula}
    {s : Tm Δ A} {σ : Sub Γ Δ} (hs : Red A s) (hσ : RedS σ) :
    RedS (Sub.cons s σ) := by
  intro φ v
  cases v with
  | here => exact hs
  | there w => exact hσ w

theorem RedS.rename {Γ Δ Δ' : List PLLFormula} {σ : Sub Γ Δ}
    (ρ : Ren Δ Δ') (hσ : RedS σ) :
    RedS (fun {χ} v => (σ v).rename ρ) :=
  fun v => Red.rename ρ (hσ v)

theorem RedS.lift {Γ Δ : List PLLFormula} {A : PLLFormula} {σ : Sub Γ Δ}
    (hσ : RedS σ) : RedS (Sub.lift (ψ := A) σ) := by
  intro φ v
  cases v with
  | here => exact Red.var .here
  | there w => exact Red.rename (fun v => .there v) (hσ w)

/-- **The fundamental theorem of the logical relation**: substituting
reducibles into any term yields a reducible term. -/
theorem fundamental : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) {Δ : List PLLFormula} (σ : Sub Γ Δ),
    RedS σ → Red φ (t.subst σ) := by
  intro Γ φ t
  induction t with
  | var v =>
      intro Δ σ hσ
      exact hσ v
  | abort φ t ih =>
      intro Δ σ hσ
      exact red_abort (Red.sn (ih σ hσ))
  | lam b ihb =>
      intro Δ σ hσ
      refine red_lam (Red.sn (ihb σ.lift (RedS.lift hσ))) ?_
      intro Δ' ρ s hs
      rw [subst_lift_rename_subst1]
      exact ihb (Sub.cons s (fun {χ} v => (σ v).rename ρ))
        (RedS.cons hs (RedS.rename ρ hσ))
  | app t s iht ihs =>
      intro Δ σ hσ
      have h := (iht σ hσ).2 (fun {χ} v => v) (s.subst σ) (ihs σ hσ)
      rwa [Tm.rename_id] at h
  | pair t s iht ihs =>
      intro Δ σ hσ
      exact red_pair (iht σ hσ) (ihs σ hσ)
  | fst t ih =>
      intro Δ σ hσ
      exact (ih σ hσ).2.1
  | snd t ih =>
      intro Δ σ hσ
      exact (ih σ hσ).2.2
  | inl t ih =>
      intro Δ σ hσ
      exact red_inl (ih σ hσ)
  | inr t ih =>
      intro Δ σ hσ
      exact red_inr (ih σ hσ)
  | case t u₁ u₂ iht ih1 ih2 =>
      intro Δ σ hσ
      refine red_case (Red.sn (ih1 σ.lift (RedS.lift hσ)))
        (Red.sn (ih2 σ.lift (RedS.lift hσ))) (iht σ hσ) ?_ ?_
      · intro s hs
        rw [Tm.subst_lift_subst1]
        exact ih1 (Sub.cons s σ) (RedS.cons hs hσ)
      · intro s hs
        rw [Tm.subst_lift_subst1]
        exact ih2 (Sub.cons s σ) (RedS.cons hs hσ)
  | val t ih =>
      intro Δ σ hσ
      exact red_val (ih σ hσ)
  | bind t u iht ihu =>
      intro Δ σ hσ
      refine red_bind (Red.sn (ihu σ.lift (RedS.lift hσ))) (iht σ hσ) ?_
      intro s hs
      rw [Tm.subst_lift_subst1]
      exact ihu (Sub.cons s σ) (RedS.cons hs hσ)

/-- **Strong normalisation of β-reduction** for the PLL proof-term
calculus: every term is strongly normalising for `RStep`. -/
theorem beta_sn {Γ : List PLLFormula} {φ : PLLFormula} (t : Tm Γ φ) :
    RSN t := by
  have h := fundamental t Sub.ids RedS.ids
  rw [Tm.subst_ids] at h
  exact Red.sn h

/-- Every step is a β-step or an assoc-step: `RStep` and `AStep` exactly
partition `Step`. -/
theorem step_split : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ}, Step t t' → RStep t t' ∨ AStep t t' := by
  intro Γ φ t t' h
  induction h <;>
    first
    | (refine .inl ?_; mirror)
    | (refine .inr ?_; mirror)
    | (cases ‹_ ∨ _› with
        | inl h => refine .inl ?_; mirror
        | inr h => refine .inr ?_; mirror)

/-! ### Why the two halves do not combine: machine-checked counterexamples

`beta_sn` and `assoc_sn` do not compose to strong normalisation of full
`Step`, and the obstruction is genuine: each fragment creates redexes of
the other.

*Assoc creates β*: `let y ⇐ (let x ⇐ z in val x) in val y` is β-normal —
its `val x` sits in *body* position, the right-unit shape, which is not a
redex — but one reassociation moves it into *scrutinee* position, creating
a `let`-β redex.

*β creates assoc*: `(λf. let x ⇐ f in val x) (let x ⇐ z in val x)` is
assoc-normal, but the β step substitutes a `bind` into scrutinee position —
and its reduct is exactly the first counterexample, so the two creation
directions chain into a β/assoc ping-pong.

These examples also close the generic modular-termination route
(Bachmair–Dershowitz/Geser quasi-commutation, which combines `SN(R)` and
`SN(A)` into `SN(R ∪ A)` given `A;R ⊆ R;(R∪A)*` or its mirror): the first
performs `assoc;β` from a term admitting *no* β-step, the second `β;assoc`
from a term admitting *no* assoc-step, so neither inclusion can hold.  A
semantic method is forced. -/

section Counterexamples

private abbrev CA := PLLFormula.prop "A"

/-- `let y ⇐ (let x ⇐ z in val x) in val y`, over `z : ◯A`. -/
private abbrev ce₁ : Tm [somehow CA] (somehow CA) :=
  .bind (.bind (.var .here) (.val (.var .here))) (.val (.var .here))

/-- The result of reassociating `ce₁`:
`let x ⇐ z in (let y ⇐ val x in val y)`. -/
private abbrev ce₁assoc : Tm [somehow CA] (somehow CA) :=
  .bind (.var .here) (.bind (.val (.var .here)) (.val (.var .here)))

/-- `ce₁` is β-normal: no β-step applies anywhere in it. -/
example : ∀ y, ¬ RStep ce₁ y := by
  intro y h
  cases h with
  | bindCong₁ h1 =>
      cases h1 with
      | bindCong₁ h2 => cases h2
      | bindCong₂ h2 => cases h2 with | valCong h3 => cases h3
  | bindCong₂ h1 =>
      cases h1 with
      | valCong h2 => cases h2

/-- One assoc step applies to `ce₁` … -/
example : AStep ce₁ ce₁assoc := .bindAssoc _ _ _

/-- … and its result contains a freshly created `let`-β redex. -/
example : RStep ce₁assoc (.bind (.var .here) (.val (.var .here))) :=
  .bindCong₂ (.bindVal _ _)

/-- `(λf. let x ⇐ f in val x) (let x ⇐ z in val x)`, over `z : ◯A`. -/
private abbrev ce₂ : Tm [somehow CA] (somehow CA) :=
  .app (.lam (.bind (.var .here) (.val (.var .here))))
    (.bind (.var .here) (.val (.var .here)))

/-- `ce₂` is assoc-normal: no assoc step applies anywhere in it. -/
example : ∀ y, ¬ AStep ce₂ y := by
  intro y h
  cases h with
  | appCong₁ h1 =>
      cases h1 with
      | lamCong h2 =>
          cases h2 with
          | bindCong₁ h3 => cases h3
          | bindCong₂ h3 => cases h3 with | valCong h4 => cases h4
  | appCong₂ h1 =>
      cases h1 with
      | bindCong₁ h2 => cases h2
      | bindCong₂ h2 => cases h2 with | valCong h3 => cases h3

/-- One β step on `ce₂` creates an assoc redex — indeed it reduces `ce₂`
to `ce₁` exactly, closing the ping-pong. -/
example : RStep ce₂ ce₁ := .beta _ _

end Counterexamples

/-!
### Status of full strong normalisation

With `beta_sn` (this file) and `assoc_sn` (`PLLStrongNorm.lean`), both
halves of `Step` — as partitioned by `step_split` — are strongly
normalising in isolation.  Termination of their *interleaving* (`SNt t` for
every `t`) does not follow compositionally: the counterexamples above show
each fragment creates redexes of the other, killing both orientations of
quasi-commutation, and no simple size or count measure survives both
phases (β duplicates arbitrary subterms through substitution, and the
β-redexes created by assoc have unbounded scrutinees, which the subsequent
`let`-β duplicates in turn).  Note also that even a measure for the
*phased* strategy "β to completion; assoc to completion; repeat" would
only prove that one strategy normalises — a weak-normalisation statement
already available via cut elimination — not strong normalisation over all
interleavings.  The standard route is Lindley–Stark
⊤⊤-lifting: reinterpret `Red (◯A)` by quantification over reducible
*continuation stacks* `K` (`SN (K[t])` for all `K ⊥⊥ A`), where the
principal lemma's assoc case is handled by an induction on stack length
inside a measure on `SN (K[val s])`.  The value-style interpretation used
here is exactly the `K = []` shadow of that semantics; upgrading it is the
one remaining normalisation theorem.
-/

end PLLND
