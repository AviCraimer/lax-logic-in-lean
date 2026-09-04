/- Challenge: `conservativity_prop` from LaxLogic/PLLNDCore.lean:208
   Ground truth exists (14-line proof); the goal here is
   to re-derive it. Group: nd-core. -/
import LaxLogic.PLLFormula

/-!
# A slime-free core ND system for PLL, with conservativity over IPL

This file is the "canonical system" produced by the transport-problem audit
(see `transport-problem-brief.md` §6).  Design rules applied:

* Contexts are `List PLLFormula`, extended only by `φ :: Γ` — every index in a
  constructor return type is a variable or a constructor form (no `++`, no
  `∪`, no `map`): McBride's no-green-slime rule.
* The identity rule takes a membership hypothesis `φ ∈ Γ` instead of pinning
  `φ` at a position in the context.  Exchange, weakening and contraction are
  then *admissible* (`LaxND.rename`) rather than structural rules, so the
  `move`/exchange rule of `LaxNDList` is derivable (`LaxND.move`) and no cast
  is ever needed.
* `orElim` carries its major premise `Γ ⊢ φ ∨ ψ` (missing from the other
  systems in this repo, which makes them derive everything — see the audit).

Consequences: the erasure translation `LaxND.erased` and both conservativity
theorems below are entirely cast-free — no `▸`, no `cast`, no `HEq`.
-/

open PLLFormula

namespace PLLND

/-- Erase the lax modality: `◯φ ↦ φ` recursively.  (Same function as
`eraseSomehow`/`zapSomehow` elsewhere in this repo, kept local so this file
only depends on `PLLFormula`.) -/
@[simp]
def erase : PLLFormula → PLLFormula
  | .prop a     => .prop a
  | .falsePLL   => .falsePLL
  | .ifThen φ ψ => .ifThen (erase φ) (erase ψ)
  | .and φ ψ    => .and (erase φ) (erase ψ)
  | .or φ ψ     => .or (erase φ) (erase ψ)
  | .somehow φ  => erase φ

/-- A formula is an IPL formula iff it contains no `somehow`. -/
@[simp]
def isIPL : PLLFormula → Prop
  | .prop _     => True
  | .falsePLL   => True
  | .ifThen φ ψ => isIPL φ ∧ isIPL ψ
  | .and φ ψ    => isIPL φ ∧ isIPL ψ
  | .or φ ψ     => isIPL φ ∧ isIPL ψ
  | .somehow _  => False

@[simp]
lemma isIPL_erase (φ : PLLFormula) : isIPL (erase φ) := by
  induction φ <;> simp [*]

lemma erase_eq_self_of_isIPL : ∀ φ : PLLFormula, isIPL φ → erase φ = φ
  | .prop _, _ => rfl
  | .falsePLL, _ => rfl
  | .ifThen φ ψ, ⟨hφ, hψ⟩ => by
      simp [erase_eq_self_of_isIPL φ hφ, erase_eq_self_of_isIPL ψ hψ]
  | .and φ ψ, ⟨hφ, hψ⟩ => by
      simp [erase_eq_self_of_isIPL φ hφ, erase_eq_self_of_isIPL ψ hψ]
  | .or φ ψ, ⟨hφ, hψ⟩ => by
      simp [erase_eq_self_of_isIPL φ hφ, erase_eq_self_of_isIPL ψ hψ]

lemma map_erase_eq_self : ∀ Γ : List PLLFormula, (∀ ψ ∈ Γ, isIPL ψ) → Γ.map erase = Γ
  | [], _ => rfl
  | φ :: Γ, h => by
      rw [List.map_cons, erase_eq_self_of_isIPL φ (h φ (List.mem_cons_self ..)),
        map_erase_eq_self Γ (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))]

/-- Natural deduction for PLL, proof-term (`Type`-valued) version.
All context indices are variables or `φ :: Γ`. -/
inductive LaxND : List PLLFormula → PLLFormula → Type
  | iden {Γ : List PLLFormula} {φ : PLLFormula} (h : φ ∈ Γ) : LaxND Γ φ
  | falsoElim {Γ : List PLLFormula} (φ : PLLFormula)
      (p : LaxND Γ .falsePLL) : LaxND Γ φ
  | impIntro {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : LaxND (φ :: Γ) ψ) : LaxND Γ (.ifThen φ ψ)
  | impElim {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p₁ : LaxND Γ (.ifThen φ ψ)) (p₂ : LaxND Γ φ) : LaxND Γ ψ
  | andIntro {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p₁ : LaxND Γ φ) (p₂ : LaxND Γ ψ) : LaxND Γ (.and φ ψ)
  | andElim1 {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : LaxND Γ (.and φ ψ)) : LaxND Γ φ
  | andElim2 {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : LaxND Γ (.and φ ψ)) : LaxND Γ ψ
  | orIntro1 {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : LaxND Γ φ) : LaxND Γ (.or φ ψ)
  | orIntro2 {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : LaxND Γ ψ) : LaxND Γ (.or φ ψ)
  | orElim {Γ : List PLLFormula} {φ ψ χ : PLLFormula}
      (p₀ : LaxND Γ (.or φ ψ))
      (p₁ : LaxND (φ :: Γ) χ) (p₂ : LaxND (ψ :: Γ) χ) : LaxND Γ χ
  | laxIntro {Γ : List PLLFormula} {φ : PLLFormula}
      (p : LaxND Γ φ) : LaxND Γ (.somehow φ)
  | laxElim {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p₁ : LaxND Γ (.somehow φ)) (p₂ : LaxND (φ :: Γ) (.somehow ψ)) :
      LaxND Γ (.somehow ψ)

infix:70 " ⊢- " => LaxND

/-- `Γ ⊬ φ`: `φ` is NOT derivable from `Γ`.

`Γ ⊢- φ` is the *type* of derivations, so underivability is the emptiness of that
type.  Lean's general spelling for that is `¬ Nonempty _`, or as a class
`IsEmpty _` (`not_nonempty_iff : ¬ Nonempty α ↔ IsEmpty α`); `Empty` is the empty
type itself, not this.  Here it is worth a name of its own: refutation results are
half of this development, the repo's comments have always written them `⊬`, and a
`reducible` definition displays that way in goals while still unifying silently
with the `¬ Nonempty (LaxND …)` and `¬ Deriv …` spellings already in use — so
existing certificates typecheck against it unchanged. -/
abbrev Underivable (Γ : List PLLFormula) (φ : PLLFormula) : Prop :=
  ¬ Nonempty (LaxND Γ φ)

@[inherit_doc] infix:70 " ⊬ " => Underivable

/-! ## Admissible structural rules

Because `iden` is membership-based, one renaming traversal gives weakening,
exchange and contraction all at once, with no casts. -/

/-- If `Γ ⊆ Γ'` as sets, any derivation over `Γ` transports to `Γ'`.
This subsumes weakening, exchange and contraction. -/
def LaxND.rename {Γ Γ' : List PLLFormula} {φ : PLLFormula}
    (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ') : LaxND Γ φ → LaxND Γ' φ
  | .iden h => .iden (H _ h)
  | .falsoElim φ p => .falsoElim φ (p.rename H)
  | .impIntro p => .impIntro (p.rename (consMono H))
  | .impElim p₁ p₂ => .impElim (p₁.rename H) (p₂.rename H)
  | .andIntro p₁ p₂ => .andIntro (p₁.rename H) (p₂.rename H)
  | .andElim1 p => .andElim1 (p.rename H)
  | .andElim2 p => .andElim2 (p.rename H)
  | .orIntro1 p => .orIntro1 (p.rename H)
  | .orIntro2 p => .orIntro2 (p.rename H)
  | .orElim p₀ p₁ p₂ =>
      .orElim (p₀.rename H) (p₁.rename (consMono H)) (p₂.rename (consMono H))
  | .laxIntro p => .laxIntro (p.rename H)
  | .laxElim p₁ p₂ => .laxElim (p₁.rename H) (p₂.rename (consMono H))
where
  consMono {Γ Γ' : List PLLFormula} {χ : PLLFormula}
      (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ') : ∀ ψ, ψ ∈ χ :: Γ → ψ ∈ χ :: Γ' := by
    intro ψ h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (H _ h)

/-- Weakening. -/
def LaxND.weaken {Γ : List PLLFormula} {φ : PLLFormula} (ψ : PLLFormula) :
    LaxND Γ φ → LaxND (ψ :: Γ) φ :=
  .rename fun _ h => List.mem_cons_of_mem _ h

/-- The `move`/exchange rule of `LaxNDList` is admissible — one line,
no cast, no induction over derivations at the call site. -/
def LaxND.move {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    (p : LaxND (φ :: (Γ ++ Δ)) ψ) : LaxND (Γ ++ φ :: Δ) ψ :=
  p.rename (by intro χ h; simp only [List.mem_cons, List.mem_append] at h ⊢; tauto)

/-! ## The usual PLL theorems, exchange-free -/

def OI (Γ : List PLLFormula) (φ : PLLFormula) : Γ ⊢- .ifThen φ (.somehow φ) :=
  .impIntro (.laxIntro (.iden (List.mem_cons_self ..)))

def OM (Γ : List PLLFormula) (φ : PLLFormula) :
    Γ ⊢- .ifThen (.somehow (.somehow φ)) (.somehow φ) :=
  .impIntro (.laxElim (.iden (List.mem_cons_self ..))
    (.iden (List.mem_cons_self ..)))

def OSR (Γ : List PLLFormula) (φ ψ : PLLFormula) :
    Γ ⊢- .ifThen (.and (.somehow φ) (.somehow ψ)) (.somehow (.and φ ψ)) :=
  .impIntro <|
    .laxElim (.andElim1 (.iden (List.mem_cons_self ..))) <|
      .laxElim (.andElim2 (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) <|
        .laxIntro (.andIntro
          (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (.iden (List.mem_cons_self ..)))

/-! ## Route A: conservativity as a `Prop`-level statement

Instead of a predicate `isIPLProof` on PLL proof terms, define the IPL
fragment as its own judgment and translate.  No proof terms, no casts. -/

/-- Natural deduction for IPL (no lax rules), as a `Prop`-valued judgment. -/
inductive IPLND : List PLLFormula → PLLFormula → Prop
  | iden {Γ : List PLLFormula} {φ : PLLFormula} (h : φ ∈ Γ) : IPLND Γ φ
  | falsoElim {Γ : List PLLFormula} (φ : PLLFormula)
      (p : IPLND Γ .falsePLL) : IPLND Γ φ
  | impIntro {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : IPLND (φ :: Γ) ψ) : IPLND Γ (.ifThen φ ψ)
  | impElim {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p₁ : IPLND Γ (.ifThen φ ψ)) (p₂ : IPLND Γ φ) : IPLND Γ ψ
  | andIntro {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p₁ : IPLND Γ φ) (p₂ : IPLND Γ ψ) : IPLND Γ (.and φ ψ)
  | andElim1 {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : IPLND Γ (.and φ ψ)) : IPLND Γ φ
  | andElim2 {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : IPLND Γ (.and φ ψ)) : IPLND Γ ψ
  | orIntro1 {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : IPLND Γ φ) : IPLND Γ (.or φ ψ)
  | orIntro2 {Γ : List PLLFormula} {φ ψ : PLLFormula}
      (p : IPLND Γ ψ) : IPLND Γ (.or φ ψ)
  | orElim {Γ : List PLLFormula} {φ ψ χ : PLLFormula}
      (p₀ : IPLND Γ (.or φ ψ))
      (p₁ : IPLND (φ :: Γ) χ) (p₂ : IPLND (ψ :: Γ) χ) : IPLND Γ χ

/-- **Conservativity, Prop form.**  Any PLL derivation erases to an IPL
derivation of the erased sequent.  Every case is a direct constructor
application: `List.map` computes definitionally on `[]` and `::`, which is
exactly what the slime-free indices buy. -/
theorem conservativity_prop {Γ : List PLLFormula} {φ : PLLFormula}
    (p : LaxND Γ φ) : IPLND (Γ.map erase) (erase φ) := by
  sorry
