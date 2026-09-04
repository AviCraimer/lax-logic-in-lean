import LaxLogic.PLLSubst
import LaxLogic.PLLSequent

/-!
# Normal forms, progress, and weak normalisation via cut elimination

β-normal forms for the PLL proof-term calculus, as a mutual grammar of
*normal* (`Nf`) and *neutral* (`Ne`) terms.  Design points:

* `case` and `abort` with neutral scrutinee are *neutral* — they can be
  eliminated further and are stuck (there are no commuting conversions in
  `Step`);
* `bind` is **not** neutral: `bind (bind s t) u` is a `let`-assoc redex even
  when the inner `bind` is stuck, so normal `bind`-chains are forced to be
  right-nested with non-`bind`, non-`val` scrutinees — exactly the
  assoc-normal forms of the computational metalanguage.

Results:

* `Nf`/`Ne` are closed under renaming and under substitution of neutral
  terms for variables (`Nf.subst_ne`) — the engine of the sequent
  translation;
* normal terms are stuck (`not_step_of_nf`) and stuck terms are normal
  (`nf_or_step`, progress) — so `Nf` is exactly normality for `Step`;
* **weak normalisation via cut elimination**: every cut-free sequent proof
  denotes a normal proof term (`nf_of_SCh`), hence every inhabited sequent
  has a normal inhabitant (`normal_form_exists`).  Note the harvested
  normal form is produced by cut elimination, not by reducing the given
  term — the `t ⟶* nf t` refinement is what strong normalisation will add.
-/

open PLLFormula

namespace PLLND

mutual
  /-- Neutral terms: eliminations blocked on a variable. -/
  inductive Ne : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → Prop
    | var {Γ : List PLLFormula} {φ : PLLFormula} (v : Var Γ φ) :
        Ne (.var v)
    | app {Γ : List PLLFormula} {φ ψ : PLLFormula}
        {t : Tm Γ (φ.ifThen ψ)} {s : Tm Γ φ} :
        Ne t → Nf s → Ne (.app t s)
    | fst {Γ : List PLLFormula} {φ ψ : PLLFormula} {t : Tm Γ (φ.and ψ)} :
        Ne t → Ne (.fst t)
    | snd {Γ : List PLLFormula} {φ ψ : PLLFormula} {t : Tm Γ (φ.and ψ)} :
        Ne t → Ne (.snd t)
    | abort {Γ : List PLLFormula} (φ : PLLFormula) {t : Tm Γ .falsePLL} :
        Ne t → Ne (.abort φ t)
    | case {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t : Tm Γ (φ.or ψ)}
        {u₁ : Tm (φ :: Γ) χ} {u₂ : Tm (ψ :: Γ) χ} :
        Ne t → Nf u₁ → Nf u₂ → Ne (.case t u₁ u₂)

  /-- β-normal (and assoc-normal) terms. -/
  inductive Nf : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → Prop
    | ne {Γ : List PLLFormula} {φ : PLLFormula} {t : Tm Γ φ} :
        Ne t → Nf t
    | lam {Γ : List PLLFormula} {φ ψ : PLLFormula} {t : Tm (φ :: Γ) ψ} :
        Nf t → Nf (.lam t)
    | pair {Γ : List PLLFormula} {φ ψ : PLLFormula}
        {t : Tm Γ φ} {s : Tm Γ ψ} :
        Nf t → Nf s → Nf (.pair t s)
    | inl {Γ : List PLLFormula} {φ ψ : PLLFormula} {t : Tm Γ φ} :
        Nf t → Nf (.inl (ψ := ψ) t)
    | inr {Γ : List PLLFormula} {φ ψ : PLLFormula} {t : Tm Γ ψ} :
        Nf t → Nf (.inr (φ := φ) t)
    | val {Γ : List PLLFormula} {φ : PLLFormula} {t : Tm Γ φ} :
        Nf t → Nf (.val t)
    | bind {Γ : List PLLFormula} {φ ψ : PLLFormula}
        {t : Tm Γ (somehow φ)} {u : Tm (φ :: Γ) (somehow ψ)} :
        Ne t → Nf u → Nf (.bind t u)
end

/-! ### Stability under renaming -/

mutual
  theorem Ne.rename : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
      {t : Tm Γ φ} (ρ : Ren Γ Δ), Ne t → Ne (t.rename ρ)
    | _, _, _, _, ρ, .var v => .var (ρ v)
    | _, _, _, _, ρ, .app hn hf => .app (hn.rename ρ) (hf.rename ρ)
    | _, _, _, _, ρ, .fst hn => .fst (hn.rename ρ)
    | _, _, _, _, ρ, .snd hn => .snd (hn.rename ρ)
    | _, _, _, _, ρ, .abort φ hn => .abort φ (hn.rename ρ)
    | _, _, _, _, ρ, .case hn h₁ h₂ =>
        .case (hn.rename ρ) (h₁.rename ρ.lift) (h₂.rename ρ.lift)

  theorem Nf.rename : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
      {t : Tm Γ φ} (ρ : Ren Γ Δ), Nf t → Nf (t.rename ρ)
    | _, _, _, _, ρ, .ne hn => .ne (hn.rename ρ)
    | _, _, _, _, ρ, .lam hf => .lam (hf.rename ρ.lift)
    | _, _, _, _, ρ, .pair h₁ h₂ => .pair (h₁.rename ρ) (h₂.rename ρ)
    | _, _, _, _, ρ, .inl hf => .inl (hf.rename ρ)
    | _, _, _, _, ρ, .inr hf => .inr (hf.rename ρ)
    | _, _, _, _, ρ, .val hf => .val (hf.rename ρ)
    | _, _, _, _, ρ, .bind hn hf => .bind (hn.rename ρ) (hf.rename ρ.lift)
end

/-! ### Stability under neutral substitution -/

/-- A substitution is *neutral* when every image is neutral. -/
def Sub.Neutral {Γ Δ : List PLLFormula} (σ : Sub Γ Δ) : Prop :=
  ∀ {φ : PLLFormula} (v : Var Γ φ), Ne (σ v)

theorem Sub.Neutral.app {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {σ : Sub Γ Δ} (hσ : Sub.Neutral σ) (v : Var Γ φ) : Ne (σ v) := hσ v

theorem Sub.Neutral.lift {Γ Δ : List PLLFormula} {ψ : PLLFormula}
    {σ : Sub Γ Δ} (hσ : Sub.Neutral σ) :
    Sub.Neutral (Sub.lift (ψ := ψ) σ) := by
  intro φ v
  cases v with
  | here => exact .var .here
  | there w => exact (hσ w).rename _

mutual
  theorem Ne.subst_ne : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
      {t : Tm Γ φ} {σ : Sub Γ Δ}, σ.Neutral → Ne t → Ne (t.subst σ)
    | _, _, _, _, _, hσ, .var v => hσ v
    | _, _, _, _, _, hσ, .app hn hf => .app (hn.subst_ne hσ) (hf.subst_ne hσ)
    | _, _, _, _, _, hσ, .fst hn => .fst (hn.subst_ne hσ)
    | _, _, _, _, _, hσ, .snd hn => .snd (hn.subst_ne hσ)
    | _, _, _, _, _, hσ, .abort φ hn => .abort φ (hn.subst_ne hσ)
    | _, _, _, _, _, hσ, .case hn h₁ h₂ =>
        .case (hn.subst_ne hσ) (h₁.subst_ne hσ.lift) (h₂.subst_ne hσ.lift)

  theorem Nf.subst_ne : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
      {t : Tm Γ φ} {σ : Sub Γ Δ}, σ.Neutral → Nf t → Nf (t.subst σ)
    | _, _, _, _, _, hσ, .ne hn => .ne (hn.subst_ne hσ)
    | _, _, _, _, _, hσ, .lam hf => .lam (hf.subst_ne hσ.lift)
    | _, _, _, _, _, hσ, .pair h₁ h₂ =>
        .pair (h₁.subst_ne hσ) (h₂.subst_ne hσ)
    | _, _, _, _, _, hσ, .inl hf => .inl (hf.subst_ne hσ)
    | _, _, _, _, _, hσ, .inr hf => .inr (hf.subst_ne hσ)
    | _, _, _, _, _, hσ, .val hf => .val (hf.subst_ne hσ)
    | _, _, _, _, _, hσ, .bind hn hf =>
        .bind (hn.subst_ne hσ) (hf.subst_ne hσ.lift)
end

/-- The identity substitution is neutral. -/
theorem Sub.Neutral.ids {Γ : List PLLFormula} :
    Sub.Neutral (Sub.ids (Γ := Γ)) := fun v => Ne.var v

/-- Extending a neutral substitution with a neutral term. -/
theorem Sub.Neutral.cons {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {s : Tm Δ φ} {σ : Sub Γ Δ} (hs : Ne s) (hσ : Sub.Neutral σ) :
    Sub.Neutral (Sub.cons s σ) := by
  intro ψ v
  cases v with
  | here => exact hs
  | there w => exact hσ w

/-! ### Normal terms are exactly the stuck terms -/

/-- Normal terms do not reduce. -/
theorem not_step_of_nf : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ}, Step t t' → Nf t → False := by
  intro Γ φ t t' h
  induction h with
  | beta t s =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | app h _ => cases h
  | fstPair t s =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | fst h => cases h
  | sndPair t s =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | snd h => cases h
  | caseInl s u₁ u₂ =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | case h _ _ => cases h
  | caseInr s u₁ u₂ =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | case h _ _ => cases h
  | bindVal s t =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | bind hn _ => cases hn
  | bindAssoc s t u =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | bind hn _ => cases hn
  | abortCong _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | abort _ hn' => exact ih (.ne hn')
  | lamCong _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | lam hf => exact ih hf
  | appCong₁ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | app hn' _ => exact ih (.ne hn')
  | appCong₂ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | app _ hf => exact ih hf
  | pairCong₁ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | pair h₁ _ => exact ih h₁
  | pairCong₂ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | pair _ h₂ => exact ih h₂
  | fstCong _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | fst hn' => exact ih (.ne hn')
  | sndCong _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | snd hn' => exact ih (.ne hn')
  | inlCong _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | inl hf => exact ih hf
  | inrCong _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | inr hf => exact ih hf
  | caseCong₀ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | case hn' _ _ => exact ih (.ne hn')
  | caseCong₁ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | case _ h₁ _ => exact ih h₁
  | caseCong₂ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn with | case _ _ h₂ => exact ih h₂
  | valCong _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | val hf => exact ih hf
  | bindCong₁ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | bind hn _ => exact ih (.ne hn)
  | bindCong₂ _ ih =>
      intro hnf
      cases hnf with
      | ne hn => cases hn
      | bind _ hf => exact ih hf

/-- **Progress**: every term is normal or takes a step.  Together with
`not_step_of_nf`, `Nf` characterises normality for `Step`. -/
theorem nf_or_step : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ), Nf t ∨ ∃ t', Step t t' := by
  intro Γ φ t
  induction t with
  | var v => exact .inl (.ne (.var v))
  | abort φ t ih =>
      rcases ih with hf | ⟨t', h⟩
      · cases hf with
        | ne hn => exact .inl (.ne (.abort φ hn))
      · exact .inr ⟨_, .abortCong h⟩
  | lam t ih =>
      rcases ih with hf | ⟨t', h⟩
      · exact .inl (.lam hf)
      · exact .inr ⟨_, .lamCong h⟩
  | app t s iht ihs =>
      rcases iht with hf | ⟨t', h⟩
      · cases hf with
        | ne hn =>
            rcases ihs with hs | ⟨s', h⟩
            · exact .inl (.ne (.app hn hs))
            · exact .inr ⟨_, .appCong₂ h⟩
        | lam hf => exact .inr ⟨_, .beta _ _⟩
      · exact .inr ⟨_, .appCong₁ h⟩
  | pair t s iht ihs =>
      rcases iht with hf | ⟨t', h⟩
      · rcases ihs with hs | ⟨s', h⟩
        · exact .inl (.pair hf hs)
        · exact .inr ⟨_, .pairCong₂ h⟩
      · exact .inr ⟨_, .pairCong₁ h⟩
  | fst t ih =>
      rcases ih with hf | ⟨t', h⟩
      · cases hf with
        | ne hn => exact .inl (.ne (.fst hn))
        | pair h₁ h₂ => exact .inr ⟨_, .fstPair _ _⟩
      · exact .inr ⟨_, .fstCong h⟩
  | snd t ih =>
      rcases ih with hf | ⟨t', h⟩
      · cases hf with
        | ne hn => exact .inl (.ne (.snd hn))
        | pair h₁ h₂ => exact .inr ⟨_, .sndPair _ _⟩
      · exact .inr ⟨_, .sndCong h⟩
  | inl t ih =>
      rcases ih with hf | ⟨t', h⟩
      · exact .inl (.inl hf)
      · exact .inr ⟨_, .inlCong h⟩
  | inr t ih =>
      rcases ih with hf | ⟨t', h⟩
      · exact .inl (.inr hf)
      · exact .inr ⟨_, .inrCong h⟩
  | case t u₁ u₂ iht ih₁ ih₂ =>
      rcases iht with hf | ⟨t', h⟩
      · cases hf with
        | ne hn =>
            rcases ih₁ with h₁ | ⟨u₁', h⟩
            · rcases ih₂ with h₂ | ⟨u₂', h⟩
              · exact .inl (.ne (.case hn h₁ h₂))
              · exact .inr ⟨_, .caseCong₂ h⟩
            · exact .inr ⟨_, .caseCong₁ h⟩
        | inl hf => exact .inr ⟨_, .caseInl _ _ _⟩
        | inr hf => exact .inr ⟨_, .caseInr _ _ _⟩
      · exact .inr ⟨_, .caseCong₀ h⟩
  | val t ih =>
      rcases ih with hf | ⟨t', h⟩
      · exact .inl (.val hf)
      · exact .inr ⟨_, .valCong h⟩
  | bind t u iht ihu =>
      rcases iht with hf | ⟨t', h⟩
      · cases hf with
        | ne hn =>
            rcases ihu with hu | ⟨u', h⟩
            · exact .inl (.bind hn hu)
            · exact .inr ⟨_, .bindCong₂ h⟩
        | val hf => exact .inr ⟨_, .bindVal _ _⟩
        | bind hn hf => exact .inr ⟨_, .bindAssoc _ _ _⟩
      · exact .inr ⟨_, .bindCong₁ h⟩

/-! ### Weak normalisation via cut elimination -/

/-- **Every cut-free sequent proof denotes a normal proof term.**  The
translation realises left rules by substituting neutral eliminations for
variables (`Nf.subst_ne`); `laxL` becomes a right-nested `bind` on a
variable — an assoc-normal form. -/
theorem nf_of_SCh : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    SCh n Γ C → ∃ t : Tm Γ C, Nf t := by
  intro n Γ C d
  induction d with
  | init h =>
      obtain ⟨v⟩ := exists_var h
      exact ⟨.var v, .ne (.var v)⟩
  | @botL _ _ C h =>
      obtain ⟨v⟩ := exists_var h
      exact ⟨.abort C (.var v), .ne (.abort C (.var v))⟩
  | andR _ _ ih₁ ih₂ =>
      obtain ⟨t, ht⟩ := ih₁
      obtain ⟨s, hs⟩ := ih₂
      exact ⟨.pair t s, .pair ht hs⟩
  | @andL _ _ A B _ h _ ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨v⟩ := exists_var h
      refine ⟨u.subst (Sub.cons (.fst (.var v))
        (Sub.cons (.snd (.var v)) Sub.ids)), ?_⟩
      exact hu.subst_ne
        (Sub.Neutral.cons (.fst (.var v))
          (Sub.Neutral.cons (.snd (.var v)) Sub.Neutral.ids))
  | orR1 _ ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨.inl t, .inl ht⟩
  | orR2 _ ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨.inr t, .inr ht⟩
  | orL h _ _ ih₁ ih₂ =>
      obtain ⟨u₁, h₁⟩ := ih₁
      obtain ⟨u₂, h₂⟩ := ih₂
      obtain ⟨v⟩ := exists_var h
      exact ⟨.case (.var v) u₁ u₂, .ne (.case (.var v) h₁ h₂)⟩
  | impR _ ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨.lam t, .lam ht⟩
  | impL h _ _ ih₁ ih₂ =>
      obtain ⟨s, hs⟩ := ih₁
      obtain ⟨u, hu⟩ := ih₂
      obtain ⟨v⟩ := exists_var h
      refine ⟨u.subst1 (.app (.var v) s), ?_⟩
      exact hu.subst_ne (Sub.Neutral.cons (.app (.var v) hs) Sub.Neutral.ids)
  | laxR _ ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨.val t, .val ht⟩
  | laxL h _ ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨v⟩ := exists_var h
      exact ⟨.bind (.var v) u, .bind (.var v) hu⟩

/-- **Weak normalisation** (via cut elimination): every inhabited sequent
has a normal inhabitant.  (The normal form is harvested from the cut-free
sequent proof; relating it to the input term by reduction is what strong
normalisation adds.) -/
theorem normal_form_exists {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) : ∃ t' : Tm Γ φ, Nf t' := by
  obtain ⟨n, d⟩ := ND_to_SC t.toND
  exact nf_of_SCh d

end PLLND
