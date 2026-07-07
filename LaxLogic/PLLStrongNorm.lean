import LaxLogic.PLLNormal
import LaxLogic.PLLTactics

/-!
# Towards strong normalisation: assoc termination and a certified reducer

Two of the three ingredients of the strong-normalisation story, mechanised:

1. **The `let`-assoc fragment terminates** (`assoc_sn`): the reassociation
   rule `bind (bind s t) u ⟶ bind s (bind t u↑)` strictly decreases the
   weight `w(bind t u) = 2·w(t) + w(u) + 1` (renaming-invariant), and the
   congruence closure inherits the decrease.  This is the part of `Step`
   that β-methods do not see.

2. **A computable one-step reducer** `Tm.step?`, returning a certified step
   (`Option {t' // Step t t'}`), with `step?_none`: if it returns `none`
   the term is normal.  Iterating it gives the executable, fueled
   normaliser `Tm.reduceFuel`, sound by construction (`reduceFuel_sound`):
   whatever it returns is reachable by reduction, and if it reports normal,
   the result *is* normal.

The missing third ingredient is termination of the full relation — strong
normalisation proper — which needs a Tait-style reducibility interpretation
(Kripke-indexed, because branches of `case`/`bind` live in extended
contexts) with Lindley–Stark ⊤⊤-lifting to absorb `let`-assoc.  With
`SNt t` in hand, `reduceFuel` upgrades to a total normaliser by
well-founded recursion.  Everything below is cast-free and `sorry`-free;
the ⊤⊤ development is left as the explicitly scoped next step.
-/

open PLLFormula

namespace PLLND

/-! ### Termination of the assoc fragment -/

/-- Weight: `bind` counts its scrutinee twice. -/
def Tm.weight : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → Nat
  | _, _, .var _ => 1
  | _, _, .abort _ t => t.weight + 1
  | _, _, .lam t => t.weight + 1
  | _, _, .app t s => t.weight + s.weight + 1
  | _, _, .pair t s => t.weight + s.weight + 1
  | _, _, .fst t => t.weight + 1
  | _, _, .snd t => t.weight + 1
  | _, _, .inl t => t.weight + 1
  | _, _, .inr t => t.weight + 1
  | _, _, .case t u₁ u₂ => t.weight + u₁.weight + u₂.weight + 1
  | _, _, .val t => t.weight + 1
  | _, _, .bind t u => 2 * t.weight + u.weight + 1

/-- Weight is invariant under renaming. -/
theorem Tm.weight_rename : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) (ρ : Ren Γ Δ), (t.rename ρ).weight = t.weight
  | _, _, _, .var _, ρ => rfl
  | _, _, _, .abort _ t, ρ => by simp [Tm.rename, Tm.weight, t.weight_rename]
  | _, _, _, .lam t, ρ => by simp [Tm.rename, Tm.weight, t.weight_rename]
  | _, _, _, .app t s, ρ => by
      simp [Tm.rename, Tm.weight, t.weight_rename, s.weight_rename]
  | _, _, _, .pair t s, ρ => by
      simp [Tm.rename, Tm.weight, t.weight_rename, s.weight_rename]
  | _, _, _, .fst t, ρ => by simp [Tm.rename, Tm.weight, t.weight_rename]
  | _, _, _, .snd t, ρ => by simp [Tm.rename, Tm.weight, t.weight_rename]
  | _, _, _, .inl t, ρ => by simp [Tm.rename, Tm.weight, t.weight_rename]
  | _, _, _, .inr t, ρ => by simp [Tm.rename, Tm.weight, t.weight_rename]
  | _, _, _, .case t u₁ u₂, ρ => by
      simp [Tm.rename, Tm.weight, t.weight_rename, u₁.weight_rename,
        u₂.weight_rename]
  | _, _, _, .val t, ρ => by simp [Tm.rename, Tm.weight, t.weight_rename]
  | _, _, _, .bind t u, ρ => by
      simp [Tm.rename, Tm.weight, t.weight_rename, u.weight_rename]

/-- The assoc fragment of `Step`: the reassociation redex and its
congruence closure. -/
inductive AStep : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Tm Γ φ → Tm Γ φ → Prop
  | bindAssoc {Γ : List PLLFormula} {φ ψ χ : PLLFormula}
      (s : Tm Γ (somehow φ)) (t : Tm (φ :: Γ) (somehow ψ))
      (u : Tm (ψ :: Γ) (somehow χ)) :
      AStep (.bind (.bind s t) u) (.bind s (.bind t (u.rename Ren.skip1)))
  | abortCong {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ .falsePLL} :
      AStep t t' → AStep (.abort φ t) (.abort φ t')
  | lamCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm (φ :: Γ) ψ} :
      AStep t t' → AStep (.lam t) (.lam t')
  | appCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t t' : Tm Γ (φ.ifThen ψ)} {s : Tm Γ φ} :
      AStep t t' → AStep (.app t s) (.app t' s)
  | appCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t : Tm Γ (φ.ifThen ψ)} {s s' : Tm Γ φ} :
      AStep s s' → AStep (.app t s) (.app t s')
  | pairCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t t' : Tm Γ φ} {s : Tm Γ ψ} :
      AStep t t' → AStep (.pair t s) (.pair t' s)
  | pairCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t : Tm Γ φ} {s s' : Tm Γ ψ} :
      AStep s s' → AStep (.pair t s) (.pair t s')
  | fstCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ (φ.and ψ)} :
      AStep t t' → AStep (.fst t) (.fst t')
  | sndCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ (φ.and ψ)} :
      AStep t t' → AStep (.snd t) (.snd t')
  | inlCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ φ} :
      AStep t t' → AStep (.inl (ψ := ψ) t) (.inl t')
  | inrCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ ψ} :
      AStep t t' → AStep (.inr (φ := φ) t) (.inr t')
  | caseCong₀ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t t' : Tm Γ (φ.or ψ)}
      {u₁ : Tm (φ :: Γ) χ} {u₂ : Tm (ψ :: Γ) χ} :
      AStep t t' → AStep (.case t u₁ u₂) (.case t' u₁ u₂)
  | caseCong₁ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t : Tm Γ (φ.or ψ)}
      {u₁ u₁' : Tm (φ :: Γ) χ} {u₂ : Tm (ψ :: Γ) χ} :
      AStep u₁ u₁' → AStep (.case t u₁ u₂) (.case t u₁' u₂)
  | caseCong₂ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t : Tm Γ (φ.or ψ)}
      {u₁ : Tm (φ :: Γ) χ} {u₂ u₂' : Tm (ψ :: Γ) χ} :
      AStep u₂ u₂' → AStep (.case t u₁ u₂) (.case t u₁ u₂')
  | valCong {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ φ} :
      AStep t t' → AStep (.val t) (.val t')
  | bindCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t t' : Tm Γ (somehow φ)} {u : Tm (φ :: Γ) (somehow ψ)} :
      AStep t t' → AStep (.bind t u) (.bind t' u)
  | bindCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula}
      {t : Tm Γ (somehow φ)} {u u' : Tm (φ :: Γ) (somehow ψ)} :
      AStep u u' → AStep (.bind t u) (.bind t u')

/-- Every assoc step is a step. -/
theorem AStep.toStep : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ}, AStep t t' → Step t t' := by
  intro Γ φ t t' h
  induction h <;> mirror

/-- Assoc steps strictly decrease the weight. -/
theorem AStep.weight_lt : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ}, AStep t t' → t'.weight < t.weight := by
  intro Γ φ t t' h
  induction h <;> simp only [Tm.weight, Tm.weight_rename] <;> omega

/-- **The assoc fragment is strongly normalising.** -/
theorem assoc_sn {Γ : List PLLFormula} {φ : PLLFormula} (t : Tm Γ φ) :
    Acc (fun a b : Tm Γ φ => AStep b a) t := by
  have h : Subrelation (fun a b : Tm Γ φ => AStep b a)
      (InvImage (· < ·) Tm.weight) := fun h => h.weight_lt
  exact (Subrelation.wf h (InvImage.wf Tm.weight Nat.lt_wfRel.wf)).apply t

/-! ### A certified, computable one-step reducer -/

/-- Head-redex dispatch for applications. -/
def Tm.appRedex? : ∀ {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm Γ (φ.ifThen ψ)) (s : Tm Γ φ), Option {t' : Tm Γ ψ // Step (.app t s) t'}
  | _, _, _, .lam t, s => some ⟨t.subst1 s, .beta t s⟩
  | _, _, _, _, _ => none

/-- Head-redex dispatch for first projections. -/
def Tm.fstRedex? : ∀ {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm Γ (φ.and ψ)), Option {t' : Tm Γ φ // Step (.fst t) t'}
  | _, _, _, .pair t s => some ⟨t, .fstPair t s⟩
  | _, _, _, _ => none

/-- Head-redex dispatch for second projections. -/
def Tm.sndRedex? : ∀ {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm Γ (φ.and ψ)), Option {t' : Tm Γ ψ // Step (.snd t) t'}
  | _, _, _, .pair t s => some ⟨s, .sndPair t s⟩
  | _, _, _, _ => none

/-- Head-redex dispatch for case analyses. -/
def Tm.caseRedex? : ∀ {Γ : List PLLFormula} {φ ψ χ : PLLFormula}
    (t : Tm Γ (φ.or ψ)) (u₁ : Tm (φ :: Γ) χ) (u₂ : Tm (ψ :: Γ) χ),
    Option {t' : Tm Γ χ // Step (.case t u₁ u₂) t'}
  | _, _, _, _, .inl s, u₁, u₂ => some ⟨u₁.subst1 s, .caseInl s u₁ u₂⟩
  | _, _, _, _, .inr s, u₁, u₂ => some ⟨u₂.subst1 s, .caseInr s u₁ u₂⟩
  | _, _, _, _, _, _, _ => none

/-- Head-redex dispatch for binds (`let`-β and `let`-assoc). -/
def Tm.bindRedex? : ∀ {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm Γ (somehow φ)) (u : Tm (φ :: Γ) (somehow ψ)),
    Option {t' : Tm Γ (somehow ψ) // Step (.bind t u) t'}
  | _, _, _, .val s, u => some ⟨u.subst1 s, .bindVal s u⟩
  | _, _, _, .bind s t, u =>
      some ⟨.bind s (.bind t (u.rename Ren.skip1)), .bindAssoc s t u⟩
  | _, _, _, _, _ => none

/-- Certified one-step reduction: congruences (innermost subterms first),
then head-redex dispatch.  Returns a proof-carrying step or `none`. -/
def Tm.step? : ∀ {Γ : List PLLFormula} {φ : PLLFormula} (t : Tm Γ φ),
    Option {t' : Tm Γ φ // Step t t'}
  | _, _, .var _ => none
  | _, _, .abort φ t =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.abort φ t', .abortCong h⟩
      | none => none
  | _, _, .lam t =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.lam t', .lamCong h⟩
      | none => none
  | _, _, .app t s =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.app t' s, .appCong₁ h⟩
      | none =>
          match s.step? with
          | some ⟨s', h⟩ => some ⟨.app t s', .appCong₂ h⟩
          | none => t.appRedex? s
  | _, _, .pair t s =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.pair t' s, .pairCong₁ h⟩
      | none =>
          match s.step? with
          | some ⟨s', h⟩ => some ⟨.pair t s', .pairCong₂ h⟩
          | none => none
  | _, _, .fst t =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.fst t', .fstCong h⟩
      | none => t.fstRedex?
  | _, _, .snd t =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.snd t', .sndCong h⟩
      | none => t.sndRedex?
  | _, _, .inl t =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.inl t', .inlCong h⟩
      | none => none
  | _, _, .inr t =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.inr t', .inrCong h⟩
      | none => none
  | _, _, .case t u₁ u₂ =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.case t' u₁ u₂, .caseCong₀ h⟩
      | none =>
          match u₁.step? with
          | some ⟨u₁', h⟩ => some ⟨.case t u₁' u₂, .caseCong₁ h⟩
          | none =>
              match u₂.step? with
              | some ⟨u₂', h⟩ => some ⟨.case t u₁ u₂', .caseCong₂ h⟩
              | none => t.caseRedex? u₁ u₂
  | _, _, .val t =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.val t', .valCong h⟩
      | none => none
  | _, _, .bind t u =>
      match t.step? with
      | some ⟨t', h⟩ => some ⟨.bind t' u, .bindCong₁ h⟩
      | none =>
          match u.step? with
          | some ⟨u', h⟩ => some ⟨.bind t u', .bindCong₂ h⟩
          | none => t.bindRedex? u

/-- If the reducer finds no step, the term is normal. -/
theorem Tm.step?_none : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ}, t.step? = none → Nf t := by
  intro Γ φ t
  induction t with
  | var v => intro _; exact .ne (.var v)
  | abort φ t ih =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none =>
          cases ih ht with
          | ne hn => exact .ne (.abort φ hn)
  | lam t ih =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none => exact .lam (ih ht)
  | app t s iht ihs =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none =>
          rw [ht] at h
          cases hs : s.step? with
          | some p => rw [hs] at h; cases h
          | none =>
              rw [hs] at h
              cases iht ht with
              | ne hn => exact .ne (.app hn (ihs hs))
              | lam hf => simp [Tm.appRedex?] at h
  | pair t s iht ihs =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none =>
          rw [ht] at h
          cases hs : s.step? with
          | some p => rw [hs] at h; cases h
          | none => exact .pair (iht ht) (ihs hs)
  | fst t ih =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none =>
          rw [ht] at h
          cases ih ht with
          | ne hn => exact .ne (.fst hn)
          | pair h₁ h₂ => simp [Tm.fstRedex?] at h
  | snd t ih =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none =>
          rw [ht] at h
          cases ih ht with
          | ne hn => exact .ne (.snd hn)
          | pair h₁ h₂ => simp [Tm.sndRedex?] at h
  | inl t ih =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none => exact .inl (ih ht)
  | inr t ih =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none => exact .inr (ih ht)
  | case t u₁ u₂ iht ih₁ ih₂ =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none =>
          rw [ht] at h
          cases h₁ : u₁.step? with
          | some p => rw [h₁] at h; cases h
          | none =>
              rw [h₁] at h
              cases h₂ : u₂.step? with
              | some p => rw [h₂] at h; cases h
              | none =>
                  rw [h₂] at h
                  cases iht ht with
                  | ne hn => exact .ne (.case hn (ih₁ h₁) (ih₂ h₂))
                  | inl hf => simp [Tm.caseRedex?] at h
                  | inr hf => simp [Tm.caseRedex?] at h
  | val t ih =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none => exact .val (ih ht)
  | bind t u iht ihu =>
      intro h
      simp only [Tm.step?] at h
      cases ht : t.step? with
      | some p => rw [ht] at h; cases h
      | none =>
          rw [ht] at h
          cases hu : u.step? with
          | some p => rw [hu] at h; cases h
          | none =>
              rw [hu] at h
              cases iht ht with
              | ne hn => exact .bind hn (ihu hu)
              | val hf => simp [Tm.bindRedex?] at h
              | bind hn hf => simp [Tm.bindRedex?] at h

/-- The fueled normaliser: iterate `step?`.  Returns the final term and
whether it certified normality (`true` = ran to a stuck term). -/
def Tm.reduceFuel : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Nat → Tm Γ φ → Tm Γ φ × Bool
  | _, _, 0, t => (t, false)
  | _, _, fuel + 1, t =>
      match t.step? with
      | some ⟨t', _⟩ => t'.reduceFuel fuel
      | none => (t, true)

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps {Γ : List PLLFormula} {φ : PLLFormula} :
    Tm Γ φ → Tm Γ φ → Prop
  | refl (t : Tm Γ φ) : Steps t t
  | head {t t' t'' : Tm Γ φ} : Step t t' → Steps t' t'' → Steps t t''

/-- **Soundness of the fueled normaliser**: the result is reachable by
reduction, and when it reports `true` the result is normal. -/
theorem Tm.reduceFuel_sound : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (fuel : Nat) (t : Tm Γ φ),
    Steps t (t.reduceFuel fuel).1 ∧
      ((t.reduceFuel fuel).2 = true → Nf (t.reduceFuel fuel).1)
  | _, _, 0, t => ⟨.refl t, by simp [Tm.reduceFuel]⟩
  | Γ, φ, fuel + 1, t => by
      simp only [Tm.reduceFuel]
      cases hs : t.step? with
      | some p =>
          obtain ⟨hsteps, hnf⟩ := Tm.reduceFuel_sound fuel p.1
          exact ⟨.head p.2 hsteps, hnf⟩
      | none =>
          exact ⟨.refl t, fun _ => Tm.step?_none hs⟩

end PLLND
