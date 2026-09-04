import LaxLogic.PLLReducibility
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Strong normalisation of the full reduction (Lindley–Stark ⊤⊤-lifting)

This file proves **strong normalisation of the full one-step reduction
`Step`** — β for every connective *and* `let`-assoc, interleaved freely —
for the PLL proof-term calculus: `SNt t` for every `t : Tm Γ φ`.

`PLLReducibility.lean` ends with machine-checked counterexamples showing
that `beta_sn` and `assoc_sn` do not compose: each fragment creates redexes
of the other (both orientations of Bachmair–Dershowitz quasi-commutation
fail), so a semantic method over the *full* relation is forced.  The method
is Lindley–Stark ⊤⊤-lifting (TLCA 2005), the biorthogonal upgrade of the
value-style `◯`-clause used for the β-fragment:

* a **continuation stack** `K : Kont Γ A B` is a list of `bind`-bodies;
  `K.plug t` wraps `t` in scrutinee position, innermost frame first;
* `K` is **reducible** (`KRed A K`, membership in `SRed A ⊤`) when
  `K[val s]` is SN for every reducible `s` — in any renaming extension;
* `SRed (◯A) t` holds when `K[t ρ]` is SN for every reducible stack `K`
  (membership in `SRed A ⊤⊤`).  The β-fragment's value clause is exactly
  the `K = []` shadow of this definition.

The mathematical heart is the **principal lemma**
`SN s → SN (K[u[s]]) → SN (K[bind (val s) u])`, whose assoc-interface case
produces a reduct with the *same* underlying SN witness but a *shorter*
stack; bare `Acc`-induction cannot recurse on an equal argument, so the
induction is over the lexicographic measure
`(Acc.rank of K[u[s]], |K|, Acc.rank of s)` using mathlib's ordinal rank
of accessibility (`Mathlib.SetTheory.Ordinal.Rank`).

Everything else is the Kripke–Tait skeleton of `PLLReducibility.lean`
re-run over `Step`: the reducibility candidates change only at `◯`, and
`bind` is no longer neutral (its scrutinee position participates in assoc),
matching the normal-form grammar of `PLLNormal.lean`.

On paper, the method including sums is Lindley–Stark's own: TLCA 2005
§4.1 treats λml with sums, case restricted to computation-typed branches,
via sum continuations, and the unrestricted case construct is handled by
frame stacks in Lindley's PhD thesis (Edinburgh, 2005, §3.5) — which also
proves confluence and decidability of convertibility for λml.  Strong
normalisation for λml itself predates the method: Benton–Bierman–de Paiva
(JFP 1998) obtained it by translation into a λ-calculus with sums plus
Prawitz's permutation-conversion result, and Lindley–Stark's §5.1 surveys
the other translation-based proofs.  The only prior *mechanisation* of
⊤⊤-lifting we know of is Doczkal–Schwinghammer (Isabelle/HOL-Nominal,
LFMTP 2009; AFP entry `Lam-ml-Normalization`), for the core calculus
without sums; the present file appears to be the first mechanisation with
sums, the first in Lean, and the first over intrinsically-typed syntax.
(Two differences from the published system, both making our relation
smaller: `Step` has no η-rules and no case commuting conversions — it is
β together with `let`-assoc, exactly.)
-/

open PLLFormula

namespace PLLND

/-! ### SN for the full relation: basic kit

`SNt` is defined in `PLLTerms.lean`.  The congruence lemmas are
`Acc.of_inversion` at the evident step inversions, as in the β-fragment.
-/

theorem SNt.step {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ φ}
    (h : SNt t) (hs : Step t t') : SNt t' :=
  h.inv hs

theorem SNt.steps {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ φ}
    (hs : Steps t t') : SNt t → SNt t' := by
  induction hs with
  | refl _ => exact id
  | head h1 _ ih => exact fun h => ih (h.inv h1)

theorem SNt.abort {Γ : List PLLFormula} (φ : PLLFormula) {t : Tm Γ .falsePLL}
    (h : SNt t) : SNt (Tm.abort φ t) :=
  Acc.of_inversion (f := Tm.abort φ)
    (fun hy => by cases hy with | abortCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.lam {Γ : List PLLFormula} {φ ψ : PLLFormula} {b : Tm (φ :: Γ) ψ}
    (h : SNt b) : SNt (Tm.lam b) :=
  Acc.of_inversion (f := Tm.lam)
    (fun hy => by cases hy with | lamCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.inl {Γ : List PLLFormula} {φ ψ : PLLFormula} {a : Tm Γ φ}
    (h : SNt a) : SNt (Tm.inl (ψ := ψ) a) :=
  Acc.of_inversion (f := Tm.inl (ψ := ψ))
    (fun hy => by cases hy with | inlCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.inr {Γ : List PLLFormula} {φ ψ : PLLFormula} {a : Tm Γ ψ}
    (h : SNt a) : SNt (Tm.inr (φ := φ) a) :=
  Acc.of_inversion (f := Tm.inr (φ := φ))
    (fun hy => by cases hy with | inrCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.val {Γ : List PLLFormula} {φ : PLLFormula} {a : Tm Γ φ}
    (h : SNt a) : SNt (Tm.val a) :=
  Acc.of_inversion (f := Tm.val)
    (fun hy => by cases hy with | valCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.pair {Γ : List PLLFormula} {φ ψ : PLLFormula}
    {a : Tm Γ φ} {b : Tm Γ ψ} (ha : SNt a) (hb : SNt b) :
    SNt (Tm.pair a b) :=
  Acc.of_inversion₂ (f := Tm.pair)
    (fun hy => by
      cases hy with
      | pairCong₁ h' => exact .inl ⟨_, rfl, h'⟩
      | pairCong₂ h' => exact .inr ⟨_, rfl, h'⟩) ha hb

/-! ### Multi-step utilities -/

theorem Steps.trans {Γ : List PLLFormula} {φ : PLLFormula}
    {a b c : Tm Γ φ} (h₁ : Steps a b) (h₂ : Steps b c) : Steps a c := by
  induction h₁ with
  | refl _ => exact h₂
  | head h _ ih => exact .head h (ih h₂)

/-- Congruence closure of `Steps` under any step-preserving map. -/
theorem Steps.cong {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    {f : Tm Γ φ → Tm Δ ψ}
    (hf : ∀ {x y : Tm Γ φ}, Step x y → Step (f x) (f y))
    {a b : Tm Γ φ} (h : Steps a b) : Steps (f a) (f b) := by
  induction h with
  | refl _ => exact .refl _
  | head h1 _ ih => exact .head (hf h1) ih

/-! ### Full steps versus renaming and substitution

The β-cases are as in the β-fragment; the new assoc case needs the two
σ-algebra facts below (how `skip1` commutes with a lifted renaming or
substitution).
-/

theorem Tm.rename_lift_skip1 {Γ Δ : List PLLFormula} {A ψ χ : PLLFormula}
    (u : Tm (ψ :: Γ) χ) (ρ : Ren Γ Δ) :
    (u.rename (Ren.lift ρ)).rename (Ren.skip1 (φ := A))
      = (u.rename Ren.skip1).rename (Ren.lift (Ren.lift ρ)) := by
  rw [Tm.rename_rename, Tm.rename_rename]
  exact u.rename_congr (by lift_cases)

theorem Tm.subst_lift_skip1 {Γ Δ : List PLLFormula} {A ψ χ : PLLFormula}
    (u : Tm (ψ :: Γ) χ) (σ : Sub Γ Δ) :
    (u.rename (Ren.skip1 (φ := A))).subst (Sub.lift (Sub.lift σ))
      = (u.subst (Sub.lift σ)).rename Ren.skip1 := by
  rw [Tm.subst_rename, Tm.rename_subst]
  refine u.subst_congr ?_
  intro χ v
  cases v with
  | here => rfl
  | there w =>
      show ((σ w).weaken).weaken = ((σ w).weaken).rename Ren.skip1
      simp only [Tm.weaken]
      rw [Tm.rename_rename, Tm.rename_rename]
      exact (σ w).rename_congr (fun v => rfl)

/-- Full steps are preserved by renaming. -/
theorem Step.rename : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (ρ : Ren Γ Δ),
    Step t t' → Step (t.rename ρ) (t'.rename ρ) := by
  intro Γ Δ φ t t' ρ h
  induction h generalizing Δ <;>
    (try rw [Tm.subst1_rename]) <;>
    (try (simp only [Tm.rename]; rw [← Tm.rename_lift_skip1])) <;>
    mirror

/-- Full steps are preserved by substitution. -/
theorem Step.subst : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (σ : Sub Γ Δ),
    Step t t' → Step (t.subst σ) (t'.subst σ) := by
  intro Γ Δ φ t t' σ h
  induction h generalizing Δ <;>
    (try rw [Tm.subst1_subst]) <;>
    (try (simp only [Tm.subst]; rw [Tm.subst_lift_skip1])) <;>
    mirror

theorem Steps.rename {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (ρ : Ren Γ Δ) {a b : Tm Γ φ} (h : Steps a b) :
    Steps (a.rename ρ) (b.rename ρ) :=
  Steps.cong (fun hs => Step.rename ρ hs) h

/-- **Reflection of full reduction under renaming**: every step of a
renamed term is the renaming of a step.  As for the β-fragment, but the
`bind` case now splits its scrutinee three ways (`val` / `bind` / other)
to expose the `let`-β and `let`-assoc head redexes. -/
theorem Step.rename_reflect : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ), ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) {y : Tm Δ φ},
    Step (t.rename ρ) y → ∃ t' : Tm Γ φ, Step t t' ∧ y = t'.rename ρ := by
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
      case bind s₀ t₀ =>
          cases h with
          | bindAssoc _ _ _ =>
              refine ⟨.bind s₀ (.bind t₀ (u.rename Ren.skip1)),
                .bindAssoc s₀ t₀ u, ?_⟩
              simp only [Tm.rename]
              rw [Tm.rename_lift_skip1]
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
theorem Steps.rename_reflect {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} {ρ : Ren Γ Δ} {z : Tm Δ φ}
    (h : Steps (t.rename ρ) z) :
    ∃ t₀ : Tm Γ φ, Steps t t₀ ∧ z = t₀.rename ρ := by
  generalize hx : t.rename ρ = x at h
  induction h generalizing t with
  | refl _ => exact ⟨t, .refl t, hx.symm⟩
  | head hs _ ih =>
      subst hx
      obtain ⟨t', hst, rfl⟩ := Step.rename_reflect _ ρ hs
      obtain ⟨t₀, hsteps, rfl⟩ := ih rfl
      exact ⟨t₀, .head hst hsteps, rfl⟩

/-- SN transfers forwards along renaming, by reflection. -/
theorem SNt.rename {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} (ρ : Ren Γ Δ) (h : SNt t) : SNt (t.rename ρ) :=
  Acc.of_inversion (f := fun t : Tm Γ φ => t.rename ρ)
    (fun hy => by
      obtain ⟨t', hs, heq⟩ := Step.rename_reflect _ ρ hy
      exact ⟨t', heq, hs⟩) h

/-! ### Pointwise multi-step substitution

A step in the substituend becomes finitely many steps (one per occurrence)
in the substituted term.
-/

/-- Pointwise multi-step relation between substitutions. -/
def SubSteps {Γ Δ : List PLLFormula} (σ τ : Sub Γ Δ) : Prop :=
  ∀ {ψ : PLLFormula} (v : Var Γ ψ), Steps (σ v) (τ v)

theorem SubSteps.lift {Γ Δ : List PLLFormula} {A : PLLFormula}
    {σ τ : Sub Γ Δ} (h : SubSteps σ τ) :
    SubSteps (Sub.lift (ψ := A) σ) (Sub.lift τ) := by
  intro ψ v
  cases v with
  | here => exact .refl _
  | there w => exact Steps.rename (fun v => .there v) (h w)

theorem Tm.subst_steps : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) {σ τ : Sub Γ Δ}, SubSteps σ τ →
    Steps (t.subst σ) (t.subst τ)
  | _, _, _, .var v, _, _, h => h v
  | _, _, _, .abort φ t, _, _, h =>
      Steps.cong (fun hs => .abortCong hs) (t.subst_steps h)
  | _, _, _, .lam t, _, _, h =>
      Steps.cong (fun hs => .lamCong hs) (t.subst_steps h.lift)
  | _, _, _, .app t s, _, _, h =>
      (Steps.cong (fun hs => .appCong₁ hs) (t.subst_steps h)).trans
        (Steps.cong (fun hs => .appCong₂ hs) (s.subst_steps h))
  | _, _, _, .pair t s, _, _, h =>
      (Steps.cong (fun hs => .pairCong₁ hs) (t.subst_steps h)).trans
        (Steps.cong (fun hs => .pairCong₂ hs) (s.subst_steps h))
  | _, _, _, .fst t, _, _, h =>
      Steps.cong (fun hs => .fstCong hs) (t.subst_steps h)
  | _, _, _, .snd t, _, _, h =>
      Steps.cong (fun hs => .sndCong hs) (t.subst_steps h)
  | _, _, _, .inl t, _, _, h =>
      Steps.cong (fun hs => .inlCong hs) (t.subst_steps h)
  | _, _, _, .inr t, _, _, h =>
      Steps.cong (fun hs => .inrCong hs) (t.subst_steps h)
  | _, _, _, .case t u₁ u₂, _, _, h =>
      ((Steps.cong (fun hs => .caseCong₀ hs) (t.subst_steps h)).trans
        (Steps.cong (fun hs => .caseCong₁ hs) (u₁.subst_steps h.lift))).trans
        (Steps.cong (fun hs => .caseCong₂ hs) (u₂.subst_steps h.lift))
  | _, _, _, .val t, _, _, h =>
      Steps.cong (fun hs => .valCong hs) (t.subst_steps h)
  | _, _, _, .bind t u, _, _, h =>
      (Steps.cong (fun hs => .bindCong₁ hs) (t.subst_steps h)).trans
        (Steps.cong (fun hs => .bindCong₂ hs) (u.subst_steps h.lift))

/-- A step in the substituted value becomes multi-steps of the instance. -/
theorem Tm.subst1_steps_arg {Γ : List PLLFormula} {A φ : PLLFormula}
    (u : Tm (A :: Γ) φ) {s s' : Tm Γ A} (h : Step s s') :
    Steps (u.subst1 s) (u.subst1 s') := by
  refine u.subst_steps ?_
  intro ψ v
  cases v with
  | here => exact .head h (.refl _)
  | there w => exact .refl _

/-! ### Ordinal rank bookkeeping

`Acc.rank` is proof-irrelevant (any two `Acc` proofs of the same element
are equal), so ranks are effectively attached to terms; the two lemmas
below package the strict and non-strict decreases the principal lemma
needs.
-/

theorem rank_lt_of_step {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (h : SNt t) (h' : SNt t') (hs : Step t t') :
    Acc.rank h' < Acc.rank h := by
  rw [Subsingleton.elim h' (h.inv hs)]
  exact Acc.rank_lt_of_rel h hs

theorem rank_le_of_steps {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (hs : Steps t t') :
    ∀ (h : SNt t) (h' : SNt t'), Acc.rank h' ≤ Acc.rank h := by
  induction hs with
  | refl _ =>
      intro h h'
      rw [Subsingleton.elim h' h]
  | head h1 _ ih =>
      intro h h'
      exact (ih (h.inv h1) h').trans (le_of_lt (Acc.rank_lt_of_rel h h1))

/-! ### The lexicographic triple -/

/-- The measure order for the principal lemma:
`(rank of K[u[s]], stack size, rank of s)`, lexicographically. -/
def Lex₃ : Ordinal × ℕ × Ordinal → Ordinal × ℕ × Ordinal → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem lex₃_wf : WellFounded Lex₃ :=
  Ordinal.lt_wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Ordinal.lt_wf)

theorem lex₃_of_lt {o₁ o₁' : Ordinal} {n n' : ℕ} {o₂ o₂' : Ordinal}
    (h : o₁' < o₁) : Lex₃ (o₁', n', o₂') (o₁, n, o₂) :=
  .left _ _ h

theorem lex₃_of_le_lt {o₁ o₁' : Ordinal} {n n' : ℕ} {o₂ o₂' : Ordinal}
    (h1 : o₁' ≤ o₁) (h2 : n' < n) : Lex₃ (o₁', n', o₂') (o₁, n, o₂) := by
  rcases lt_or_eq_of_le h1 with h | rfl
  · exact .left _ _ h
  · exact .right _ (.left _ _ h2)

theorem lex₃_of_le_eq_lt {o₁ o₁' : Ordinal} {n n' : ℕ} {o₂ o₂' : Ordinal}
    (h1 : o₁' ≤ o₁) (h2 : n' = n) (h3 : o₂' < o₂) :
    Lex₃ (o₁', n', o₂') (o₁, n, o₂) := by
  subst h2
  rcases lt_or_eq_of_le h1 with h | rfl
  · exact .left _ _ h
  · exact .right _ (.right _ h3)

theorem rank_eq_of_eq {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (heq : t = t') (h : SNt t) (h' : SNt t') :
    Acc.rank h = Acc.rank h' := by
  cases heq
  rw [Subsingleton.elim h h']

/-! ### Continuation stacks

`Kont Γ C A` is a stack of `bind`-bodies awaiting a scrutinee of type
`◯A` and producing a term of type `◯C`.  The *result* type `C` is a
parameter and the *hole* type `A` is the index — `nil`'s index is then a
bare variable (the `Eq.refl` shape), so matches iota-reduce and the
plugging equations below hold definitionally.  (The first draft indexed
both ends and `nil : Kont Γ A A` repeated an index — green slime, in this
project of all places.)
-/

/-- Continuation stacks with result type `◯C` and hole type `◯A`. -/
inductive Kont (Γ : List PLLFormula) (C : PLLFormula) : PLLFormula → Type
  | nil : Kont Γ C C
  | cons {A B : PLLFormula} (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B) :
      Kont Γ C A

namespace Kont

/-- Plugging, innermost frame first: `(cons u K).plug t = K.plug (bind t u)`.
The parameters `Γ, C` stay out of the match columns so that the equations
hold by iota-reduction. -/
def plug {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ {A : PLLFormula}, Kont Γ C A → Tm Γ (somehow A) → Tm Γ (somehow C)
  | _, .nil, t => t
  | _, .cons u K, t => plug K (.bind t u)

/-- Number of frames. -/
def size {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ {A : PLLFormula}, Kont Γ C A → ℕ
  | _, .nil => 0
  | _, .cons _ K => size K + 1

/-- Framewise renaming (under the binder). -/
def rename {Γ Δ : List PLLFormula} {C : PLLFormula} (ρ : Ren Γ Δ) :
    ∀ {A : PLLFormula}, Kont Γ C A → Kont Δ C A
  | _, .nil => .nil
  | _, .cons u K => .cons (u.rename ρ.lift) (rename ρ K)

theorem rename_id {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ {A : PLLFormula} (K : Kont Γ C A), K.rename (fun {_} v => v) = K
  | _, .nil => rfl
  | _, .cons u K => by
      show Kont.cons (u.rename (Ren.lift fun {_} v => v))
        (K.rename fun {_} v => v) = _
      rw [show u.rename (Ren.lift fun {_} v => v) = u from
        (u.rename_congr (by lift_cases)).trans u.rename_id, rename_id K]

theorem rename_rename {Γ Δ Θ : List PLLFormula} {C : PLLFormula}
    (ρ : Ren Γ Δ) (ρ' : Ren Δ Θ) :
    ∀ {A : PLLFormula} (K : Kont Γ C A),
    (K.rename ρ).rename ρ' = K.rename (fun v => ρ' (ρ v))
  | _, .nil => rfl
  | _, .cons u K => by
      show Kont.cons ((u.rename ρ.lift).rename ρ'.lift) ((K.rename ρ).rename ρ')
        = Kont.cons (u.rename (Ren.lift fun v => ρ' (ρ v))) (K.rename _)
      rw [Tm.rename_rename, rename_rename ρ ρ' K,
        show u.rename (fun v => Ren.lift ρ' (Ren.lift ρ v))
            = u.rename (Ren.lift fun v => ρ' (ρ v)) from
          u.rename_congr (by lift_cases)]

/-- Scrutinee steps lift through the stack. -/
theorem plug_step {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ {A : PLLFormula} (K : Kont Γ C A) {t t' : Tm Γ (somehow A)},
    Step t t' → Step (K.plug t) (K.plug t')
  | _, .nil, _, _, h => h
  | _, .cons u K, _, _, h => plug_step K (.bindCong₁ h)

theorem plug_steps {Γ : List PLLFormula} {C A : PLLFormula}
    (K : Kont Γ C A) {t t' : Tm Γ (somehow A)}
    (h : Steps t t') : Steps (K.plug t) (K.plug t') :=
  Steps.cong (fun hs => K.plug_step hs) h

end Kont

/-- One-step reduction of a stack: the innermost frame steps, a deeper
part steps, or two adjacent frames merge by `let`-assoc. -/
inductive KStep : ∀ {Γ : List PLLFormula} {C A : PLLFormula},
    Kont Γ C A → Kont Γ C A → Prop
  | frame {Γ : List PLLFormula} {C A B : PLLFormula}
      {u u' : Tm (A :: Γ) (somehow B)} {K : Kont Γ C B} :
      Step u u' → KStep (.cons u K) (.cons u' K)
  | tail {Γ : List PLLFormula} {C A B : PLLFormula}
      {u : Tm (A :: Γ) (somehow B)} {K K' : Kont Γ C B} :
      KStep K K' → KStep (.cons u K) (.cons u K')
  | assocK {Γ : List PLLFormula} {C A B₁ B₂ : PLLFormula}
      (u₁ : Tm (A :: Γ) (somehow B₁)) (u₂ : Tm (B₁ :: Γ) (somehow B₂))
      (K : Kont Γ C B₂) :
      KStep (.cons u₁ (.cons u₂ K)) (.cons (.bind u₁ (u₂.rename Ren.skip1)) K)

/-- Stack steps are steps of any plugged term. -/
theorem KStep.plug_step : ∀ {Γ : List PLLFormula} {C A : PLLFormula}
    {K K' : Kont Γ C A}, KStep K K' →
    ∀ (t : Tm Γ (somehow A)), Step (K.plug t) (K'.plug t) := by
  intro Γ C A K K' h
  induction h with
  | frame h' => exact fun t => Kont.plug_step _ (.bindCong₂ h')
  | tail _ ih => exact fun t => ih (.bind t _)
  | assocK u₁ u₂ K => exact fun t => Kont.plug_step K (.bindAssoc t u₁ u₂)

/-- Stack steps are preserved by renaming. -/
theorem KStep.rename : ∀ {Γ Δ : List PLLFormula} {C A : PLLFormula}
    (ρ : Ren Γ Δ) {K K' : Kont Γ C A},
    KStep K K' → KStep (K.rename ρ) (K'.rename ρ) := by
  intro Γ Δ C A ρ K K' h
  induction h with
  | frame h' => exact .frame (Step.rename ρ.lift h')
  | tail _ ih => exact .tail ih
  | assocK u₁ u₂ K =>
      show KStep _ (Kont.cons ((Tm.bind u₁ (u₂.rename Ren.skip1)).rename ρ.lift)
        (K.rename ρ))
      simp only [Tm.rename]
      rw [← Tm.rename_lift_skip1]
      exact .assocK (u₁.rename ρ.lift) (u₂.rename ρ.lift) (K.rename ρ)

/-- **Classification of the steps of a plugged term**, for an arbitrary
scrutinee `X`: either `X` steps, or the stack steps, or `X`'s head
constructor meets the innermost frame (`let`-β or `let`-assoc at the
interface).  This is `cut_aux`'s `leftCommute` in continuation clothing;
the scrutinee is kept general precisely so the lemma can be reused for
neutral, `val`- and `bind`-headed `X` alike. -/
theorem plug_step_cases : ∀ {Γ : List PLLFormula} {C A : PLLFormula}
    (K : Kont Γ C A) (X : Tm Γ (somehow A)) {y : Tm Γ (somehow C)},
    Step (K.plug X) y →
    (∃ X', Step X X' ∧ y = K.plug X') ∨
    (∃ K', KStep K K' ∧ y = K'.plug X) ∨
    (∃ (s₀ : Tm Γ A) (B : PLLFormula) (u₀ : Tm (A :: Γ) (somehow B))
        (K₀ : Kont Γ C B), X = .val s₀ ∧ K = .cons u₀ K₀ ∧
        y = K₀.plug (u₀.subst1 s₀)) ∨
    (∃ (A₀ : PLLFormula) (t₀ : Tm Γ (somehow A₀))
        (t₁ : Tm (A₀ :: Γ) (somehow A)) (B : PLLFormula)
        (u₀ : Tm (A :: Γ) (somehow B)) (K₀ : Kont Γ C B),
        X = .bind t₀ t₁ ∧ K = .cons u₀ K₀ ∧
        y = K₀.plug (.bind t₀ (.bind t₁ (u₀.rename Ren.skip1)))) := by
  intro Γ C A K
  induction K with
  | nil =>
      intro X y h
      exact .inl ⟨y, h, rfl⟩
  | cons u₀ K₀ ih =>
      intro X y h
      rcases ih (.bind X u₀) h with
        ⟨Z', hZ, rfl⟩ | ⟨K', hK, rfl⟩ | ⟨s₀, B', w, K₁, hXeq, hKeq, rfl⟩ |
        ⟨A₀, t₀, t₁, B', w, K₁, hXeq, hKeq, rfl⟩
      · cases hZ with
        | bindVal s _ =>
            exact .inr (.inr (.inl ⟨s, _, u₀, K₀, rfl, rfl, rfl⟩))
        | bindAssoc s t _ =>
            exact .inr (.inr (.inr ⟨_, s, t, _, u₀, K₀, rfl, rfl, rfl⟩))
        | bindCong₁ h' =>
            exact .inl ⟨_, h', rfl⟩
        | bindCong₂ h' =>
            exact .inr (.inl ⟨.cons _ K₀, .frame h', rfl⟩)
      · exact .inr (.inl ⟨.cons u₀ K', .tail hK, rfl⟩)
      · cases hXeq
      · cases hXeq
        subst hKeq
        exact .inr (.inl ⟨_, .assocK u₀ w K₁, rfl⟩)

/-! ### The interface σ-lemma and the principal lemma -/

/-- Renaming by `skip1` and then substituting under a lifted `cons`
collapses to the identity: the merged frame of an interface assoc, once
the `let`-β fires, is the original frame. -/
theorem Tm.rename_skip1_subst_lift {Γ : List PLLFormula} {A B χ : PLLFormula}
    (u₀ : Tm (B :: Γ) χ) (s : Tm Γ A) :
    (u₀.rename (Ren.skip1 (φ := A))).subst (Sub.lift (Sub.cons s Sub.ids)) = u₀ := by
  rw [Tm.subst_rename]
  exact (u₀.subst_congr (by lift_cases)).trans u₀.subst_ids

/-- Instantiating a merged frame is binding the instance against the
original frame. -/
theorem bind_subst1_merge {Γ : List PLLFormula} {A B C : PLLFormula}
    (u : Tm (A :: Γ) (somehow B)) (u₀ : Tm (B :: Γ) (somehow C)) (s : Tm Γ A) :
    (Tm.bind u (u₀.rename Ren.skip1)).subst1 s = Tm.bind (u.subst1 s) u₀ := by
  show Tm.bind (u.subst (Sub.cons s Sub.ids))
      ((u₀.rename Ren.skip1).subst (Sub.lift (Sub.cons s Sub.ids))) = _
  rw [Tm.rename_skip1_subst_lift]
  exact rfl

/-- **The principal lemma** (Lindley–Stark): a `let`-β redex in a stack
context is SN as soon as its contractum-in-context and its value part are.
Induction over `(rank (K.plug (u[s])), K.size, rank s)`: the
interface-assoc reduct keeps the first component — the underlying term is
literally unchanged — and shortens the stack, which is exactly the case
bare `Acc`-induction cannot handle and ordinal rank can. -/
theorem principal : ∀ {Γ : List PLLFormula} {A B C : PLLFormula}
    (s : Tm Γ A) (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B),
    SNt s → SNt (K.plug (u.subst1 s)) →
    SNt (K.plug (.bind (.val s) u)) := by
  suffices H : ∀ (μ : Ordinal × ℕ × Ordinal) {Γ A B C}
      (s : Tm Γ A) (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B)
      (hs : SNt s) (hKu : SNt (K.plug (u.subst1 s))),
      μ = (Acc.rank hKu, K.size, Acc.rank hs) →
      SNt (K.plug (.bind (.val s) u)) by
    intro Γ A B C s u K hs hKu
    exact H _ s u K hs hKu rfl
  intro μ
  induction μ using lex₃_wf.induction with
  | _ μ IH =>
    intro Γ A B C s u K hs hKu hμ
    subst hμ
    refine Acc.intro _ fun y hy => ?_
    rcases plug_step_cases K _ hy with
      ⟨X', hX, rfl⟩ | ⟨K', hK, rfl⟩ | ⟨s₀, B', u₀, K₀, hXeq, hKeq, rfl⟩ |
      ⟨A₀, t₀, t₁, B', u₀, K₀, hXeq, hKeq, rfl⟩
    · -- the redex part stepped
      cases hX with
      | bindVal _ _ =>
          exact hKu
      | bindCong₁ h' =>
          cases h' with
          | valCong h'' =>
              have hs' := hs.step h''
              have hsteps := Kont.plug_steps K (u.subst1_steps_arg h'')
              have hKu' := SNt.steps hsteps hKu
              exact IH _ (lex₃_of_le_eq_lt (rank_le_of_steps hsteps hKu hKu')
                rfl (rank_lt_of_step hs hs' h'')) _ u K hs' hKu' rfl
      | bindCong₂ h' =>
          have hstep := Kont.plug_step K (Step.subst (Sub.cons s Sub.ids) h')
          have hKu' := hKu.step hstep
          exact IH _ (lex₃_of_lt (rank_lt_of_step hKu hKu' hstep)) s _ K hs hKu' rfl
    · -- the stack stepped
      have hstep := KStep.plug_step hK (u.subst1 s)
      have hKu' := hKu.step hstep
      exact IH _ (lex₃_of_lt (rank_lt_of_step hKu hKu' hstep)) s u K' hs hKu' rfl
    · -- X = val s₀: impossible, X is a bind
      cases hXeq
    · -- interface assoc: same contractum, shorter stack
      cases hXeq
      subst hKeq
      have heq : K₀.plug ((Tm.bind u (u₀.rename Ren.skip1)).subst1 s)
          = K₀.plug (Tm.bind (u.subst1 s) u₀) :=
        congrArg _ (bind_subst1_merge u u₀ s)
      have hKu' : SNt (K₀.plug ((Tm.bind u (u₀.rename Ren.skip1)).subst1 s)) :=
        heq ▸ hKu
      exact IH _ (lex₃_of_le_lt (rank_eq_of_eq heq hKu' hKu).le
        (Nat.lt_succ_self _)) s _ K₀ hs hKu' rfl

/-! ### Neutrality for the full reduction -/

/-- Neutral terms for the full reduction: non-introduction terms that are
also not `bind`s — a `bind` in scrutinee position participates in
`let`-assoc, so a `bind`-headed plug can head-step without either part
stepping (this matches `PLLNormal.lean`, where `bind` is not `Ne`). -/
def SNeut : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → Prop
  | _, _, .lam _ => False
  | _, _, .pair _ _ => False
  | _, _, .inl _ => False
  | _, _, .inr _ => False
  | _, _, .val _ => False
  | _, _, .bind _ _ => False
  | _, _, _ => True

theorem SNeut.rename {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} (ρ : Ren Γ Δ) (h : SNeut t) : SNeut (t.rename ρ) := by
  cases t <;> first | exact h.elim | trivial

/-! ### The ⊤⊤ reducibility candidates -/

/-- Reducibility of a continuation stack relative to a predicate on values:
the `(-)^⊤` operation with SN as its pole.  All plugs of `val`s of
`P`-terms, in every renaming extension, are SN. -/
def KRedP {Γ : List PLLFormula} {C A : PLLFormula}
    (P : ∀ {Δ : List PLLFormula}, Tm Δ A → Prop) (K : Kont Γ C A) : Prop :=
  ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) (s : Tm Δ A),
    P s → SNt ((K.rename ρ).plug (.val s))

/-- **The reducibility predicate** for the full reduction, by recursion on
the formula.  Only the `◯`-clause differs from the β-fragment
(`PLLReducibility.lean`): the value clause is upgraded to Lindley–Stark
biorthogonality — `t` is reducible at `◯A` when every reducible stack
consumes (every renaming of) it into an SN term. -/
def SRed : (φ : PLLFormula) → ∀ {Γ : List PLLFormula}, Tm Γ φ → Prop
  | .prop _, _, t => SNt t
  | .falsePLL, _, t => SNt t
  | .ifThen A B, Γ, t => SNt t ∧
      ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) (s : Tm Δ A),
        SRed A s → SRed B (.app (t.rename ρ) s)
  | .and A B, _, t => SNt t ∧ SRed A (.fst t) ∧ SRed B (.snd t)
  | .or A B, _, t => SNt t ∧
      (∀ {w}, Steps t (.inl w) → SRed A w) ∧
      (∀ {w}, Steps t (.inr w) → SRed B w)
  | .somehow A, Γ, t => SNt t ∧
      ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) {C : PLLFormula}
        (K : Kont Δ C A), KRedP (SRed A) K → SNt (K.plug (t.rename ρ))

/-- Stack reducibility at a formula: `K ∈ (SRed A)^⊤`. -/
abbrev KRed (A : PLLFormula) {Γ : List PLLFormula} {C : PLLFormula}
    (K : Kont Γ C A) : Prop :=
  KRedP (SRed A) K

theorem KRedP.rename {Γ Δ : List PLLFormula} {C A : PLLFormula}
    {P : ∀ {Δ' : List PLLFormula}, Tm Δ' A → Prop} {K : Kont Γ C A}
    (hK : KRedP P K) (ρ : Ren Γ Δ) : KRedP P (K.rename ρ) := by
  intro Δ' ρ' s hs
  rw [Kont.rename_rename]
  exact hK (fun v => ρ' (ρ v)) s hs

theorem KRedP.step {Γ : List PLLFormula} {C A : PLLFormula}
    {P : ∀ {Δ' : List PLLFormula}, Tm Δ' A → Prop} {K K' : Kont Γ C A}
    (hK : KRedP P K) (h : KStep K K') : KRedP P K' := by
  intro Δ ρ s hs
  exact (hK ρ s hs).step (KStep.plug_step (KStep.rename ρ h) _)

/-- CR1: reducible terms are strongly normalising (free, by construction). -/
theorem SRed.sn : ∀ {φ : PLLFormula} {Γ : List PLLFormula} {t : Tm Γ φ},
    SRed φ t → SNt t := by
  intro φ
  cases φ <;> intro Γ t h
  · exact h
  · exact h
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

/-- The `◯`-clause at the identity renaming. -/
theorem SRed.plugSN {Γ : List PLLFormula} {A C : PLLFormula}
    {t : Tm Γ (somehow A)} (ht : SRed (somehow A) t)
    {K : Kont Γ C A} (hK : KRedP (SRed A) K) : SNt (K.plug t) := by
  have h := ht.2 (fun {_} v => v) K hK
  rwa [Tm.rename_id] at h

/-- CR2: reducibility is closed under reduction. -/
theorem SRed.step {φ : PLLFormula} : ∀ {Γ : List PLLFormula}
    {t t' : Tm Γ φ}, SRed φ t → Step t t' → SRed φ t' := by
  induction φ with
  | prop a => exact fun h hs => SNt.step h hs
  | falsePLL => exact fun h hs => SNt.step h hs
  | ifThen A B ihA ihB =>
      intro Γ t t' h hs
      refine ⟨h.1.step hs, ?_⟩
      intro Δ ρ s hsred
      exact ihB (h.2 ρ s hsred) (.appCong₁ (Step.rename ρ hs))
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
      refine ⟨h.1.step hs, ?_⟩
      intro Δ ρ C K hK
      exact (h.2 ρ K hK).step (Kont.plug_step K (Step.rename ρ hs))

/-- CR2, many steps. -/
theorem SRed.steps {φ : PLLFormula} {Γ : List PLLFormula}
    {t t' : Tm Γ φ} (h : SRed φ t) (hs : Steps t t') : SRed φ t' := by
  induction hs with
  | refl _ => exact h
  | head h₁ _ ih => exact ih (h.step h₁)

/-- Reducibility is stable under renaming. -/
theorem SRed.rename {φ : PLLFormula} : ∀ {Γ Δ : List PLLFormula}
    (ρ : Ren Γ Δ) {t : Tm Γ φ}, SRed φ t → SRed φ (t.rename ρ) := by
  induction φ with
  | prop a =>
      intro Γ Δ ρ t h
      exact SNt.rename ρ h
  | falsePLL =>
      intro Γ Δ ρ t h
      exact SNt.rename ρ h
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
        obtain ⟨t₀, hsteps, heq⟩ := Steps.rename_reflect hst
        obtain ⟨w₀, rfl, rfl⟩ := Tm.rename_eq_inl heq.symm
        exact ihA ρ (h.2.1 hsteps)
      · intro w hst
        obtain ⟨t₀, hsteps, heq⟩ := Steps.rename_reflect hst
        obtain ⟨w₀, rfl, rfl⟩ := Tm.rename_eq_inr heq.symm
        exact ihB ρ (h.2.2 hsteps)
  | somehow A ihA =>
      intro Γ Δ ρ t h
      refine ⟨h.1.rename ρ, ?_⟩
      intro Δ' ρ' C K hK
      rw [Tm.rename_rename]
      exact h.2 (fun v => ρ' (ρ v)) K hK

/-- SN of a neutral plug (the `◯`-case of CR3).  `t` is neutral — in
particular neither `val` nor `bind` — so no interface redex forms; the
induction is on the SN of a canonical witness for the stack, namely the
weakened stack plugged with a reducible variable. -/
theorem sn_plug_neut {Γ : List PLLFormula} {C A : PLLFormula}
    (hvar : SRed A (Tm.var (Var.here (Γ := Γ) (φ := A))))
    {t : Tm Γ (somehow A)} (hne : SNeut t)
    (hred : ∀ t', Step t t' → SRed (somehow A) t')
    {K : Kont Γ C A} (hK : KRedP (SRed A) K) : SNt (K.plug t) := by
  have hmt : SNt ((K.rename (fun v => .there v)).plug (.val (.var .here))) :=
    hK _ _ hvar
  refine Acc.selfInduction (P := fun mt => ∀ K : Kont Γ C A,
      KRedP (SRed A) K →
      mt = (K.rename (fun v => .there v)).plug (.val (.var .here)) →
      SNt (K.plug t)) hmt ?_ K hK rfl
  intro mt _ ihmt K hK hmteq
  refine Acc.intro _ fun y hy => ?_
  rcases plug_step_cases K t hy with
    ⟨t', ht', rfl⟩ | ⟨K', hK', rfl⟩ | ⟨s₀, B', u₀, K₀, hXeq, _, rfl⟩ |
    ⟨A₀, t₀, t₁, B', u₀, K₀, hXeq, _, rfl⟩
  · exact (hred t' ht').plugSN hK
  · subst hmteq
    exact ihmt _ (KStep.plug_step (KStep.rename _ hK') _) K' (hK.step hK') rfl
  · subst hXeq
    exact hne.elim
  · subst hXeq
    exact hne.elim

/-- CR3: a neutral term whose one-step reducts are all reducible is
reducible. -/
theorem SRed.cr3 : ∀ {φ : PLLFormula} {Γ : List PLLFormula} {t : Tm Γ φ},
    SNeut t → (∀ t', Step t t' → SRed φ t') → SRed φ t := by
  intro φ
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
      have hsn : SNt s := hs.sn
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
              obtain ⟨t'', hs'', rfl⟩ := Step.rename_reflect t ρ h'
              exact (hred t'' hs'').2 ρ s hs
          | appCong₂ h' =>
              subst hX
              exact ihs _ h' (hs.step h')
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
      intro Δ ρ C K hK
      have hvar : SRed A (Tm.var (Var.here (Γ := Δ) (φ := A))) :=
        ihA trivial (fun _ hy => by cases hy)
      refine sn_plug_neut hvar (hneut.rename ρ) ?_ hK
      intro t' ht'
      obtain ⟨t₀, h₀, rfl⟩ := Step.rename_reflect t ρ ht'
      exact (hred t₀ h₀).rename ρ

/-- Variables are reducible. -/
theorem SRed.var {φ : PLLFormula} {Γ : List PLLFormula} (v : Var Γ φ) :
    SRed φ (.var v) :=
  SRed.cr3 trivial (fun _ hy => by cases hy)

/-! ### Closure lemmas

The β-connective lemmas are the retrofitted `PLLReducibility.lean` proofs
re-run over `Step` (which adds no rules at those heads); `val` and `bind`
are new, via the pole and the principal lemma respectively.
-/

/-- Reduction sequences from `inl` stay `inl`. -/
theorem steps_inl : ∀ {Γ : List PLLFormula} {A B : PLLFormula}
    {x z : Tm Γ (A.or B)}, Steps x z →
    ∀ {a : Tm Γ A}, x = .inl a → ∃ a', z = .inl a' ∧ Steps a a' := by
  intro Γ A B x z h
  induction h with
  | refl t =>
      intro a hx
      exact ⟨a, hx, .refl a⟩
  | head h₁ _ ih =>
      intro a hx
      subst hx
      cases h₁ with
      | inlCong h' =>
          obtain ⟨a', rfl, hsteps⟩ := ih rfl
          exact ⟨a', rfl, .head h' hsteps⟩

/-- Reduction sequences from `inr` stay `inr`. -/
theorem steps_inr : ∀ {Γ : List PLLFormula} {A B : PLLFormula}
    {x z : Tm Γ (A.or B)}, Steps x z →
    ∀ {a : Tm Γ B}, x = .inr a → ∃ a', z = .inr a' ∧ Steps a a' := by
  intro Γ A B x z h
  induction h with
  | refl t =>
      intro a hx
      exact ⟨a, hx, .refl a⟩
  | head h₁ _ ih =>
      intro a hx
      subst hx
      cases h₁ with
      | inrCong h' =>
          obtain ⟨a', rfl, hsteps⟩ := ih rfl
          exact ⟨a', rfl, .head h' hsteps⟩

/-- Abort terms over SN scrutinees are reducible. -/
theorem sred_abort {Γ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ .falsePLL} (h : SNt t) : SRed φ (.abort φ t) :=
  Acc.selfInduction (P := fun t => SRed φ (Tm.abort φ t)) h fun t _ ih =>
    SRed.cr3 trivial fun y hy => by
      cases hy with
      | abortCong h' => exact ih _ h'

/-- β-expansion for application. -/
theorem sred_beta_exp {Γ : List PLLFormula} {A B : PLLFormula}
    {b : Tm (A :: Γ) B} (hbsn : SNt b) {s : Tm Γ A} (hs : SRed A s)
    (H : ∀ s' : Tm Γ A, SRed A s' → SRed B (b.subst1 s')) :
    SRed B (.app (.lam b) s) := by
  refine Acc.pairInduction (P := fun b s =>
      SRed A s → (∀ s', SRed A s' → SRed B (b.subst1 s')) →
      SRed B (.app (.lam b) s)) hbsn hs.sn ?_ hs H
  intro b s _ _ ihb ihs hs H
  refine SRed.cr3 trivial fun y hy => ?_
  cases hy with
  | beta _ _ => exact H s hs
  | appCong₁ h' =>
      cases h' with
      | lamCong h'' =>
          exact ihb _ h'' hs
            (fun s' hs' => (H s' hs').step (Step.subst _ h''))
  | appCong₂ h' => exact ihs _ h' (hs.step h') H

/-- Abstractions with reducible instances are reducible. -/
theorem sred_lam {Γ : List PLLFormula} {A B : PLLFormula} {b : Tm (A :: Γ) B}
    (hbsn : SNt b)
    (H : ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) (s : Tm Δ A),
      SRed A s → SRed B ((b.rename ρ.lift).subst1 s)) :
    SRed (A.ifThen B) (.lam b) :=
  ⟨hbsn.lam, fun ρ _s hs =>
    sred_beta_exp (hbsn.rename ρ.lift) hs (fun s' hs' => H ρ s' hs')⟩

/-- Pairs of reducibles are reducible. -/
theorem sred_pair {Γ : List PLLFormula} {A B : PLLFormula}
    {a : Tm Γ A} {b : Tm Γ B} (ha : SRed A a) (hb : SRed B b) :
    SRed (A.and B) (.pair a b) := by
  refine Acc.pairInduction (P := fun a b =>
      SRed A a → SRed B b → SRed (A.and B) (.pair a b)) ha.sn hb.sn ?_ ha hb
  intro a b _ _ iha ihb ha hb
  refine ⟨SNt.pair ha.sn hb.sn, ?_, ?_⟩
  · refine SRed.cr3 trivial fun y hy => ?_
    cases hy with
    | fstPair _ _ => exact ha
    | fstCong h' =>
        cases h' with
        | pairCong₁ h'' => exact (iha _ h'' (ha.step h'') hb).2.1
        | pairCong₂ h'' => exact (ihb _ h'' ha (hb.step h'')).2.1
  · refine SRed.cr3 trivial fun y hy => ?_
    cases hy with
    | sndPair _ _ => exact hb
    | sndCong h' =>
        cases h' with
        | pairCong₁ h'' => exact (iha _ h'' (ha.step h'') hb).2.2
        | pairCong₂ h'' => exact (ihb _ h'' ha (hb.step h'')).2.2

/-- Left injections of reducibles are reducible. -/
theorem sred_inl {Γ : List PLLFormula} {A B : PLLFormula} {a : Tm Γ A}
    (ha : SRed A a) : SRed (A.or B) (.inl a) :=
  ⟨SNt.inl ha.sn,
   fun hst => by
     obtain ⟨a', heq, hsteps⟩ := steps_inl hst rfl
     cases heq
     exact ha.steps hsteps,
   fun hst => by
     obtain ⟨a', heq, _⟩ := steps_inl hst rfl
     cases heq⟩

/-- Right injections of reducibles are reducible. -/
theorem sred_inr {Γ : List PLLFormula} {A B : PLLFormula} {a : Tm Γ B}
    (ha : SRed B a) : SRed (A.or B) (.inr a) := by
  -- (Lean ≥4.31: see `red_inr` in PLLReducibility.lean for why the
  -- impossible branch, listed first here, needs `refine` up front rather
  -- than a plain term-mode anonymous constructor.)
  refine ⟨SNt.inr ha.sn, fun hst => ?_, fun hst => ?_⟩
  · obtain ⟨a', heq, _⟩ := steps_inr hst rfl
    cases heq
  · obtain ⟨a', heq, hsteps⟩ := steps_inr hst rfl
    cases heq
    exact ha.steps hsteps

/-- `val`s of reducibles are reducible: immediate from the pole. -/
theorem sred_val {Γ : List PLLFormula} {A : PLLFormula} {a : Tm Γ A}
    (ha : SRed A a) : SRed (somehow A) (.val a) := by
  refine ⟨SNt.val ha.sn, ?_⟩
  intro Δ ρ C K hK
  have h := hK (fun {_} v => v) (a.rename ρ) (ha.rename ρ)
  rw [Kont.rename_id] at h
  exact h

/-- Case analysis over reducibles with reducible branches is reducible. -/
theorem sred_case {Γ : List PLLFormula} {A B χ : PLLFormula}
    {t : Tm Γ (A.or B)} {u₁ : Tm (A :: Γ) χ} {u₂ : Tm (B :: Γ) χ}
    (h1sn : SNt u₁) (h2sn : SNt u₂) (ht : SRed (A.or B) t)
    (H₁ : ∀ s : Tm Γ A, SRed A s → SRed χ (u₁.subst1 s))
    (H₂ : ∀ s : Tm Γ B, SRed B s → SRed χ (u₂.subst1 s)) :
    SRed χ (.case t u₁ u₂) := by
  refine Acc.tripleInduction (P := fun t u₁ u₂ =>
      SRed (A.or B) t → (∀ s, SRed A s → SRed χ (u₁.subst1 s)) →
      (∀ s, SRed B s → SRed χ (u₂.subst1 s)) → SRed χ (.case t u₁ u₂))
    ht.sn h1sn h2sn ?_ ht H₁ H₂
  intro t u₁ u₂ _ _ _ iht ih1 ih2 ht H₁ H₂
  refine SRed.cr3 trivial fun y hy => ?_
  cases hy with
  | caseInl s _ _ => exact H₁ s (ht.2.1 (.refl _))
  | caseInr s _ _ => exact H₂ s (ht.2.2 (.refl _))
  | caseCong₀ h' => exact iht _ h' (ht.step h') H₁ H₂
  | caseCong₁ h' =>
      exact ih1 _ h' ht (fun s hs => (H₁ s hs).step (Step.subst _ h')) H₂
  | caseCong₂ h' =>
      exact ih2 _ h' ht H₁ (fun s hs => (H₂ s hs).step (Step.subst _ h'))

/-- **Binds of reducibles with reducible bodies are reducible** — the
lemma the whole file exists for.  The `◯`-clause of `bind t u` at a stack
`K` is, definitionally, the `◯`-clause of `t` at the extended stack
`cons u K`; reducibility of the extended stack is exactly the principal
lemma. -/
theorem sred_bind {Γ : List PLLFormula} {A B : PLLFormula}
    {t : Tm Γ (somehow A)} {u : Tm (A :: Γ) (somehow B)}
    (ht : SRed (somehow A) t)
    (H : ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) (s : Tm Δ A),
      SRed A s → SRed (somehow B) ((u.rename ρ.lift).subst1 s)) :
    SRed (somehow B) (.bind t u) := by
  have hcl : ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) {C : PLLFormula}
      (K : Kont Δ C B), KRedP (SRed B) K →
      SNt (K.plug ((Tm.bind t u).rename ρ)) := by
    intro Δ ρ C K hK
    show SNt ((Kont.cons (u.rename ρ.lift) K).plug (t.rename ρ))
    refine ht.2 ρ (Kont.cons (u.rename ρ.lift) K) ?_
    intro Δ' ρ' s hs
    show SNt ((K.rename ρ').plug
      (.bind (.val s) ((u.rename ρ.lift).rename ρ'.lift)))
    refine principal s _ (K.rename ρ') hs.sn ?_
    have hu : SRed (somehow B)
        (((u.rename ρ.lift).rename ρ'.lift).subst1 s) := by
      rw [Tm.rename_rename,
        show u.rename (fun v => Ren.lift ρ' (Ren.lift ρ v))
            = u.rename (Ren.lift fun v => ρ' (ρ v)) from
          u.rename_congr (by lift_cases)]
      exact H (fun v => ρ' (ρ v)) s hs
    exact hu.plugSN (hK.rename ρ')
  have hnil : KRedP (SRed B) (Kont.nil (Γ := Γ) (C := B)) :=
    fun _ s hs => SNt.val hs.sn
  have h0 := hcl (fun {_} v => v) Kont.nil hnil
  rw [Tm.rename_id] at h0
  exact ⟨h0, hcl⟩

/-! ### The fundamental theorem and strong normalisation -/

/-- Reducibility-respecting substitutions. -/
def SRedS {Γ Δ : List PLLFormula} (σ : Sub Γ Δ) : Prop :=
  ∀ {φ : PLLFormula} (v : Var Γ φ), SRed φ (σ v)

theorem SRedS.ids {Γ : List PLLFormula} : SRedS (Sub.ids (Γ := Γ)) :=
  fun v => SRed.var v

theorem SRedS.cons {Γ Δ : List PLLFormula} {A : PLLFormula}
    {s : Tm Δ A} {σ : Sub Γ Δ} (hs : SRed A s) (hσ : SRedS σ) :
    SRedS (Sub.cons s σ) := by
  intro φ v
  cases v with
  | here => exact hs
  | there w => exact hσ w

theorem SRedS.rename {Γ Δ Δ' : List PLLFormula} {σ : Sub Γ Δ}
    (ρ : Ren Δ Δ') (hσ : SRedS σ) :
    SRedS (fun {χ} v => (σ v).rename ρ) :=
  fun v => (hσ v).rename ρ

theorem SRedS.lift {Γ Δ : List PLLFormula} {A : PLLFormula} {σ : Sub Γ Δ}
    (hσ : SRedS σ) : SRedS (Sub.lift (ψ := A) σ) := by
  intro φ v
  cases v with
  | here => exact SRed.var .here
  | there w => exact (hσ w).rename (fun v => .there v)

/-- **The fundamental theorem of the logical relation** for the full
reduction: substituting reducibles into any term yields a reducible
term. -/
theorem fundamental_step : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) {Δ : List PLLFormula} (σ : Sub Γ Δ),
    SRedS σ → SRed φ (t.subst σ) := by
  intro Γ φ t
  induction t with
  | var v =>
      intro Δ σ hσ
      exact hσ v
  | abort φ t ih =>
      intro Δ σ hσ
      exact sred_abort (SRed.sn (ih σ hσ))
  | lam b ihb =>
      intro Δ σ hσ
      refine sred_lam (SRed.sn (ihb σ.lift (SRedS.lift hσ))) ?_
      intro Δ' ρ s hs
      rw [subst_lift_rename_subst1]
      exact ihb (Sub.cons s (fun {χ} v => (σ v).rename ρ))
        (SRedS.cons hs (SRedS.rename ρ hσ))
  | app t s iht ihs =>
      intro Δ σ hσ
      have h := (iht σ hσ).2 (fun {χ} v => v) (s.subst σ) (ihs σ hσ)
      rwa [Tm.rename_id] at h
  | pair t s iht ihs =>
      intro Δ σ hσ
      exact sred_pair (iht σ hσ) (ihs σ hσ)
  | fst t ih =>
      intro Δ σ hσ
      exact (ih σ hσ).2.1
  | snd t ih =>
      intro Δ σ hσ
      exact (ih σ hσ).2.2
  | inl t ih =>
      intro Δ σ hσ
      exact sred_inl (ih σ hσ)
  | inr t ih =>
      intro Δ σ hσ
      exact sred_inr (ih σ hσ)
  | case t u₁ u₂ iht ih1 ih2 =>
      intro Δ σ hσ
      refine sred_case (SRed.sn (ih1 σ.lift (SRedS.lift hσ)))
        (SRed.sn (ih2 σ.lift (SRedS.lift hσ))) (iht σ hσ) ?_ ?_
      · intro s hs
        rw [Tm.subst_lift_subst1]
        exact ih1 (Sub.cons s σ) (SRedS.cons hs hσ)
      · intro s hs
        rw [Tm.subst_lift_subst1]
        exact ih2 (Sub.cons s σ) (SRedS.cons hs hσ)
  | val t ih =>
      intro Δ σ hσ
      exact sred_val (ih σ hσ)
  | bind t u iht ihu =>
      intro Δ σ hσ
      refine sred_bind (iht σ hσ) ?_
      intro Δ' ρ s hs
      rw [subst_lift_rename_subst1]
      exact ihu (Sub.cons s (fun {χ} v => (σ v).rename ρ))
        (SRedS.cons hs (SRedS.rename ρ hσ))

/-- **Strong normalisation of the full PLL proof-term reduction**: every
term is strongly normalising for `Step` — β for every connective and
`let`-assoc, freely interleaved. -/
theorem strong_normalisation {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) : SNt t := by
  have h := fundamental_step t Sub.ids SRedS.ids
  rw [Tm.subst_ids] at h
  exact h.sn

/-! ### The total normaliser

Strong normalisation upgrades the certified one-step reducer `Tm.step?`
of `PLLStrongNorm.lean` from fuelled to total: iterate it, with
`strong_normalisation` as the termination argument.  The result is a
computable function producing a normal form (`Nf`, the grammar of
`PLLNormal.lean`) reachable by reduction.
-/

/-- Reverse reduction is well-founded: the strong-normalisation theorem
packaged for `termination_by`. -/
instance (priority := high) instWFStep {Γ : List PLLFormula} {φ : PLLFormula} :
    WellFoundedRelation (Tm Γ φ) :=
  ⟨fun a b => Step b a, ⟨fun t => strong_normalisation t⟩⟩

/-- The total normaliser. -/
def Tm.normalize {Γ : List PLLFormula} {φ : PLLFormula} (t : Tm Γ φ) : Tm Γ φ :=
  match t.step? with
  | some t' => t'.1.normalize
  | none => t
termination_by t
decreasing_by exact t'.2

/-- The normaliser computes a normal form reachable by reduction. -/
theorem Tm.normalize_spec {Γ : List PLLFormula} {φ : PLLFormula} (t : Tm Γ φ) :
    Steps t t.normalize ∧ Nf t.normalize := by
  refine Acc.selfInduction (P := fun t => Steps t t.normalize ∧ Nf t.normalize)
    (strong_normalisation t) ?_
  intro t _ ih
  rw [Tm.normalize]
  split
  next t' heq =>
      obtain ⟨hsteps, hnf⟩ := ih t'.1 t'.2
      exact ⟨.head t'.2 hsteps, hnf⟩
  next heq => exact ⟨.refl t, Tm.step?_none heq⟩

end PLLND
