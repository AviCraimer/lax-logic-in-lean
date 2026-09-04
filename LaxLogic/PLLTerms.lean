import LaxLogic.PLLNDCore

/-!
# Proof terms for PLL: the computational metalanguage, slime-free

An intrinsically-typed term calculus whose typing derivations *are* `LaxND`
derivations: Moggi's computational metalanguage / the term assignment for
lax logic (Benton–Bierman–de Paiva's computational logic), with `◯` as a
strong monad — `val` for `laxIntro` and `bind` (monadic `let`) for
`laxElim`.

The slime-free discipline of `PLLNDCore.lean` carries over verbatim, with
one upgrade forced by computation: proof terms must *compute*, so variables
cannot be `Prop`-membership — they are de Bruijn witnesses `Var Γ φ`, a
`Type`-valued membership whose indices are again only variables and
`φ :: Γ`.  Renaming and substitution are the standard parallel
(σ-calculus-style) traversals; no index cast appears anywhere.

## Reduction and cut elimination

`Step` is β-reduction for every connective plus the two monadic rules

  `bind (val s) t   ⟶  t[s]`          (`let`-β)
  `bind (bind s t) u ⟶ bind s (bind t u↑)`   (`let`-assoc)

Because the calculus is intrinsically typed, **subject reduction is free**:
`Step` only relates terms of the same sequent.

The relationship with the cut-elimination procedure of `PLLSequent.lean` is
exact and worth recording (each row: reduction rule ↔ principal case of
`cut_aux`):

| term rule        | cut-elimination case              |
|------------------|-----------------------------------|
| `app`-β          | `impR` vs `impL` principal        |
| `fst`/`snd`-β    | `andR` vs `andL` principal        |
| `case`-β         | `orR₁`/`orR₂` vs `orL` principal  |
| `bind`-`val`-β   | `laxR` vs `laxL` principal — F&M Figure 2 |
| (congruences)    | left/right commutation (`leftCommute`) |

and cut itself is substitution: `Tm.cut = subst1` below.  The two
inductions differ in metric — cut elimination is lexicographic in (cut
formula, derivation heights), normalisation in the term structure — which
is why cut admissibility (a weak-normalisation statement for one strategy)
is available `Prop`-level, while strong normalisation of `Step` is a
genuinely stronger, term-level fact.
-/

open PLLFormula

namespace PLLND

/-- `Type`-valued membership: de Bruijn variables with their type. -/
inductive Var : List PLLFormula → PLLFormula → Type
  | here {Γ : List PLLFormula} {φ : PLLFormula} : Var (φ :: Γ) φ
  | there {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Var Γ φ → Var (ψ :: Γ) φ

/-- Proof terms for PLL — the computational metalanguage. -/
inductive Tm : List PLLFormula → PLLFormula → Type
  | var {Γ : List PLLFormula} {φ : PLLFormula} :
      Var Γ φ → Tm Γ φ
  | abort {Γ : List PLLFormula} (φ : PLLFormula) :
      Tm Γ .falsePLL → Tm Γ φ
  | lam {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Tm (φ :: Γ) ψ → Tm Γ (φ.ifThen ψ)
  | app {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Tm Γ (φ.ifThen ψ) → Tm Γ φ → Tm Γ ψ
  | pair {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Tm Γ φ → Tm Γ ψ → Tm Γ (φ.and ψ)
  | fst {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Tm Γ (φ.and ψ) → Tm Γ φ
  | snd {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Tm Γ (φ.and ψ) → Tm Γ ψ
  | inl {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Tm Γ φ → Tm Γ (φ.or ψ)
  | inr {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Tm Γ ψ → Tm Γ (φ.or ψ)
  | case {Γ : List PLLFormula} {φ ψ χ : PLLFormula} :
      Tm Γ (φ.or ψ) → Tm (φ :: Γ) χ → Tm (ψ :: Γ) χ → Tm Γ χ
  | val {Γ : List PLLFormula} {φ : PLLFormula} :
      Tm Γ φ → Tm Γ (somehow φ)
  | bind {Γ : List PLLFormula} {φ ψ : PLLFormula} :
      Tm Γ (somehow φ) → Tm (φ :: Γ) (somehow ψ) → Tm Γ (somehow ψ)

/-! ### Renaming and substitution (parallel, σ-calculus style) -/

/-- Renamings: type-preserving maps of variables. -/
def Ren (Γ Δ : List PLLFormula) : Type :=
  ∀ {φ : PLLFormula}, Var Γ φ → Var Δ φ

/-- Lift a renaming under a binder. -/
def Ren.lift {Γ Δ : List PLLFormula} {ψ : PLLFormula} (ρ : Ren Γ Δ) :
    Ren (ψ :: Γ) (ψ :: Δ) := fun {χ} v =>
  match χ, v with
  | _, .here => .here
  | _, .there w => .there (ρ w)

/-- Weaken a context in second position. -/
def Ren.skip1 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Ren (ψ :: Γ) (ψ :: φ :: Γ) := fun {χ} v =>
  match χ, v with
  | _, .here => .here
  | _, .there w => .there (.there w)

/-- Renaming of terms. -/
def Tm.rename : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula},
    Ren Γ Δ → Tm Γ φ → Tm Δ φ
  | _, _, _, ρ, .var v => .var (ρ v)
  | _, _, _, ρ, .abort φ t => .abort φ (t.rename ρ)
  | _, _, _, ρ, .lam t => .lam (t.rename ρ.lift)
  | _, _, _, ρ, .app t s => .app (t.rename ρ) (s.rename ρ)
  | _, _, _, ρ, .pair t s => .pair (t.rename ρ) (s.rename ρ)
  | _, _, _, ρ, .fst t => .fst (t.rename ρ)
  | _, _, _, ρ, .snd t => .snd (t.rename ρ)
  | _, _, _, ρ, .inl t => .inl (t.rename ρ)
  | _, _, _, ρ, .inr t => .inr (t.rename ρ)
  | _, _, _, ρ, .case t u₁ u₂ =>
      .case (t.rename ρ) (u₁.rename ρ.lift) (u₂.rename ρ.lift)
  | _, _, _, ρ, .val t => .val (t.rename ρ)
  | _, _, _, ρ, .bind t u => .bind (t.rename ρ) (u.rename ρ.lift)

/-- Weakening. -/
def Tm.weaken {Γ : List PLLFormula} {φ ψ : PLLFormula} (t : Tm Γ φ) :
    Tm (ψ :: Γ) φ :=
  t.rename fun v => .there v

/-- Substitutions: type-preserving maps of variables to terms. -/
def Sub (Γ Δ : List PLLFormula) : Type :=
  ∀ {φ : PLLFormula}, Var Γ φ → Tm Δ φ

/-- Lift a substitution under a binder. -/
def Sub.lift {Γ Δ : List PLLFormula} {ψ : PLLFormula} (σ : Sub Γ Δ) :
    Sub (ψ :: Γ) (ψ :: Δ) := fun {χ} v =>
  match χ, v with
  | _, .here => .var .here
  | _, .there w => (σ w).weaken

/-- The identity substitution. -/
def Sub.ids {Γ : List PLLFormula} : Sub Γ Γ := fun v => .var v

/-- Extend a substitution with a term for the head variable. -/
def Sub.cons {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (s : Tm Δ φ) (σ : Sub Γ Δ) : Sub (φ :: Γ) Δ := fun {χ} v =>
  match χ, v with
  | _, .here => s
  | _, .there w => σ w

/-- Parallel substitution. -/
def Tm.subst : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula},
    Sub Γ Δ → Tm Γ φ → Tm Δ φ
  | _, _, _, σ, .var v => σ v
  | _, _, _, σ, .abort φ t => .abort φ (t.subst σ)
  | _, _, _, σ, .lam t => .lam (t.subst σ.lift)
  | _, _, _, σ, .app t s => .app (t.subst σ) (s.subst σ)
  | _, _, _, σ, .pair t s => .pair (t.subst σ) (s.subst σ)
  | _, _, _, σ, .fst t => .fst (t.subst σ)
  | _, _, _, σ, .snd t => .snd (t.subst σ)
  | _, _, _, σ, .inl t => .inl (t.subst σ)
  | _, _, _, σ, .inr t => .inr (t.subst σ)
  | _, _, _, σ, .case t u₁ u₂ =>
      .case (t.subst σ) (u₁.subst σ.lift) (u₂.subst σ.lift)
  | _, _, _, σ, .val t => .val (t.subst σ)
  | _, _, _, σ, .bind t u => .bind (t.subst σ) (u.subst σ.lift)

/-- Substitute for the head variable only. -/
def Tm.subst1 {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (t : Tm (φ :: Γ) ψ) (s : Tm Γ φ) : Tm Γ ψ :=
  t.subst (Sub.cons s Sub.ids)

/-- **Cut is substitution**: the term-level content of `SC.cut` /
`LaxND.cut1`. -/
def Tm.cut {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (s : Tm Γ φ) (t : Tm (φ :: Γ) ψ) : Tm Γ ψ :=
  t.subst1 s

/-! ### Reduction -/

/-- One-step reduction: β for every connective, the two monadic laws, and
congruence closure.  Intrinsic typing makes subject reduction definitional:
`Step` only relates terms of one sequent. -/
inductive Step : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Tm Γ φ → Tm Γ φ → Prop
  | beta {Γ : List PLLFormula} {φ ψ : PLLFormula} (t : Tm (φ :: Γ) ψ) (s : Tm Γ φ) :
      Step (.app (.lam t) s) (t.subst1 s)
  | fstPair {Γ : List PLLFormula} {φ ψ : PLLFormula} (t : Tm Γ φ) (s : Tm Γ ψ) :
      Step (.fst (.pair t s)) t
  | sndPair {Γ : List PLLFormula} {φ ψ : PLLFormula} (t : Tm Γ φ) (s : Tm Γ ψ) :
      Step (.snd (.pair t s)) s
  | caseInl {Γ : List PLLFormula} {φ ψ χ : PLLFormula} (s : Tm Γ φ) (u₁ : Tm (φ :: Γ) χ) (u₂ : Tm (ψ :: Γ) χ) :
      Step (.case (.inl s) u₁ u₂) (u₁.subst1 s)
  | caseInr {Γ : List PLLFormula} {φ ψ χ : PLLFormula} (s : Tm Γ ψ) (u₁ : Tm (φ :: Γ) χ) (u₂ : Tm (ψ :: Γ) χ) :
      Step (.case (.inr s) u₁ u₂) (u₂.subst1 s)
  | bindVal {Γ : List PLLFormula} {φ ψ : PLLFormula} (s : Tm Γ φ) (t : Tm (φ :: Γ) (somehow ψ)) :
      Step (.bind (.val s) t) (t.subst1 s)
  | bindAssoc {Γ : List PLLFormula} {φ ψ χ : PLLFormula} (s : Tm Γ (somehow φ))
      (t : Tm (φ :: Γ) (somehow ψ)) (u : Tm (ψ :: Γ) (somehow χ)) :
      Step (.bind (.bind s t) u)
        (.bind s (.bind t (u.rename Ren.skip1)))
  | abortCong {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ .falsePLL} :
      Step t t' → Step (.abort φ t) (.abort φ t')
  | lamCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm (φ :: Γ) ψ} :
      Step t t' → Step (.lam t) (.lam t')
  | appCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ (φ.ifThen ψ)} {s : Tm Γ φ} :
      Step t t' → Step (.app t s) (.app t' s)
  | appCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula} {t : Tm Γ (φ.ifThen ψ)} {s s' : Tm Γ φ} :
      Step s s' → Step (.app t s) (.app t s')
  | pairCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ φ} {s : Tm Γ ψ} :
      Step t t' → Step (.pair t s) (.pair t' s)
  | pairCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula} {t : Tm Γ φ} {s s' : Tm Γ ψ} :
      Step s s' → Step (.pair t s) (.pair t s')
  | fstCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ (φ.and ψ)} :
      Step t t' → Step (.fst t) (.fst t')
  | sndCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ (φ.and ψ)} :
      Step t t' → Step (.snd t) (.snd t')
  | inlCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ φ} :
      Step t t' → Step (.inl (ψ := ψ) t) (.inl t')
  | inrCong {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ ψ} :
      Step t t' → Step (.inr (φ := φ) t) (.inr t')
  | caseCong₀ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t t' : Tm Γ (φ.or ψ)}
      {u₁ : Tm (φ :: Γ) χ} {u₂ : Tm (ψ :: Γ) χ} :
      Step t t' → Step (.case t u₁ u₂) (.case t' u₁ u₂)
  | caseCong₁ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t : Tm Γ (φ.or ψ)}
      {u₁ u₁' : Tm (φ :: Γ) χ} {u₂ : Tm (ψ :: Γ) χ} :
      Step u₁ u₁' → Step (.case t u₁ u₂) (.case t u₁' u₂)
  | caseCong₂ {Γ : List PLLFormula} {φ ψ χ : PLLFormula} {t : Tm Γ (φ.or ψ)}
      {u₁ : Tm (φ :: Γ) χ} {u₂ u₂' : Tm (ψ :: Γ) χ} :
      Step u₂ u₂' → Step (.case t u₁ u₂) (.case t u₁ u₂')
  | valCong {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ φ} :
      Step t t' → Step (.val t) (.val t')
  | bindCong₁ {Γ : List PLLFormula} {φ ψ : PLLFormula} {t t' : Tm Γ (somehow φ)} {u : Tm (φ :: Γ) (somehow ψ)} :
      Step t t' → Step (.bind t u) (.bind t' u)
  | bindCong₂ {Γ : List PLLFormula} {φ ψ : PLLFormula} {t : Tm Γ (somehow φ)} {u u' : Tm (φ :: Γ) (somehow ψ)} :
      Step u u' → Step (.bind t u) (.bind t u')

/-- Strong normalisation of a term: accessibility of the reverse reduction
relation. -/
def SNt {Γ : List PLLFormula} {φ : PLLFormula} (t : Tm Γ φ) : Prop :=
  Acc (fun a b : Tm Γ φ => Step b a) t

/-! ### Curry–Howard against `LaxND` -/

/-- Variables are (in particular) membership proofs. -/
def Var.toMem : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Var Γ φ → φ ∈ Γ
  | _, _, .here => .head _
  | _, _, .there v => .tail _ v.toMem

/-- Every proof term is a natural deduction derivation. -/
def Tm.toND : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Tm Γ φ → LaxND Γ φ
  | _, _, .var v => .iden v.toMem
  | _, _, .abort φ t => .falsoElim φ t.toND
  | _, _, .lam t => .impIntro t.toND
  | _, _, .app t s => .impElim t.toND s.toND
  | _, _, .pair t s => .andIntro t.toND s.toND
  | _, _, .fst t => .andElim1 t.toND
  | _, _, .snd t => .andElim2 t.toND
  | _, _, .inl t => .orIntro1 t.toND
  | _, _, .inr t => .orIntro2 t.toND
  | _, _, .case t u₁ u₂ => .orElim t.toND u₁.toND u₂.toND
  | _, _, .val t => .laxIntro t.toND
  | _, _, .bind t u => .laxElim t.toND u.toND

/-- `Prop`-membership yields a variable up to inhabitation (the `Prop`/`Type`
boundary again: a membership proof carries no occurrence data, so only
`Nonempty` survives). -/
theorem exists_var : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    φ ∈ Γ → Nonempty (Var Γ φ)
  | _ :: _, _, .head _ => ⟨.here⟩
  | _ :: _, _, .tail _ h => (exists_var h).elim fun v => ⟨.there v⟩

/-- Every natural deduction derivation is realised by a proof term. -/
theorem exists_tm : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    LaxND Γ φ → Nonempty (Tm Γ φ) := by
  intro Γ φ p
  induction p with
  | iden h => exact (exists_var h).elim fun v => ⟨.var v⟩
  | falsoElim φ _ ih => exact ih.elim fun t => ⟨.abort φ t⟩
  | impIntro _ ih => exact ih.elim fun t => ⟨.lam t⟩
  | impElim _ _ ih₁ ih₂ =>
      exact ih₁.elim fun t => ih₂.elim fun s => ⟨.app t s⟩
  | andIntro _ _ ih₁ ih₂ =>
      exact ih₁.elim fun t => ih₂.elim fun s => ⟨.pair t s⟩
  | andElim1 _ ih => exact ih.elim fun t => ⟨.fst t⟩
  | andElim2 _ ih => exact ih.elim fun t => ⟨.snd t⟩
  | orIntro1 _ ih => exact ih.elim fun t => ⟨.inl t⟩
  | orIntro2 _ ih => exact ih.elim fun t => ⟨.inr t⟩
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      exact ih₀.elim fun t => ih₁.elim fun u₁ => ih₂.elim fun u₂ =>
        ⟨.case t u₁ u₂⟩
  | laxIntro _ ih => exact ih.elim fun t => ⟨.val t⟩
  | laxElim _ _ ih₁ ih₂ =>
      exact ih₁.elim fun t => ih₂.elim fun u => ⟨.bind t u⟩

/-- **Curry–Howard for PLL**: proof terms and natural deduction derivations
realise the same sequents. -/
theorem curry_howard {Γ : List PLLFormula} {φ : PLLFormula} :
    Nonempty (Tm Γ φ) ↔ Nonempty (LaxND Γ φ) :=
  ⟨fun ⟨t⟩ => ⟨t.toND⟩, fun ⟨p⟩ => exists_tm p⟩

end PLLND
