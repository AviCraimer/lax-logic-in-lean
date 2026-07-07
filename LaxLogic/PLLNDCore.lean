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
  induction p with
  | iden h => exact .iden (List.mem_map.mpr ⟨_, h, rfl⟩)
  | falsoElim φ _ ih => exact .falsoElim _ ih
  | impIntro _ ih => exact .impIntro ih
  | impElim _ _ ih₁ ih₂ => exact .impElim ih₁ ih₂
  | andIntro _ _ ih₁ ih₂ => exact .andIntro ih₁ ih₂
  | andElim1 _ ih => exact .andElim1 ih
  | andElim2 _ ih => exact .andElim2 ih
  | orIntro1 _ ih => exact .orIntro1 ih
  | orIntro2 _ ih => exact .orIntro2 ih
  | orElim _ _ _ ih₀ ih₁ ih₂ => exact .orElim ih₀ ih₁ ih₂
  | laxIntro _ ih => exact ih
  | laxElim _ _ ih₁ ih₂ => exact .impElim (.impIntro ih₂) ih₁

/-- **Conservativity, classic form.**  If context and conclusion are already
IPL, a PLL derivation yields an IPL derivation of the same sequent. -/
theorem conservativity_IPL {Γ : List PLLFormula} {φ : PLLFormula}
    (hφ : isIPL φ) (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (p : LaxND Γ φ) : IPLND Γ φ := by
  have h := conservativity_prop p
  rwa [map_erase_eq_self Γ hΓ, erase_eq_self_of_isIPL φ hφ] at h

/-! ## Route B: conservativity on proof terms

The same translation as a total function on proof terms, plus the
`isIPLProof` predicate.  Still cast-free. -/

/-- Erasure translation on proof terms.  Compare `erasePLLProof` in
`PLLNDProofPostZoom.lean`, which needs 15 `cast`s for the same job. -/
def LaxND.erased : {Γ : List PLLFormula} → {φ : PLLFormula} →
    LaxND Γ φ → LaxND (Γ.map erase) (erase φ)
  | _, _, .iden h => .iden (List.mem_map.mpr ⟨_, h, rfl⟩)
  | _, _, .falsoElim φ p => .falsoElim (erase φ) p.erased
  | _, _, .impIntro p => .impIntro p.erased
  | _, _, .impElim p₁ p₂ => .impElim p₁.erased p₂.erased
  | _, _, .andIntro p₁ p₂ => .andIntro p₁.erased p₂.erased
  | _, _, .andElim1 p => .andElim1 p.erased
  | _, _, .andElim2 p => .andElim2 p.erased
  | _, _, .orIntro1 p => .orIntro1 p.erased
  | _, _, .orIntro2 p => .orIntro2 p.erased
  | _, _, .orElim p₀ p₁ p₂ => .orElim p₀.erased p₁.erased p₂.erased
  | _, _, .laxIntro p => p.erased
  | _, _, .laxElim p₁ p₂ => .impElim (.impIntro p₂.erased) p₁.erased

/-- A PLL proof term is an IPL proof if it uses no lax rules and its
identity leaves are IPL formulas. -/
@[simp]
def LaxND.isIPLProof : {Γ : List PLLFormula} → {φ : PLLFormula} →
    LaxND Γ φ → Prop
  | _, _, @LaxND.iden _ φ _ => isIPL φ
  | _, _, .falsoElim _ p => p.isIPLProof
  | _, _, .impIntro p => p.isIPLProof
  | _, _, .impElim p₁ p₂ => p₁.isIPLProof ∧ p₂.isIPLProof
  | _, _, .andIntro p₁ p₂ => p₁.isIPLProof ∧ p₂.isIPLProof
  | _, _, .andElim1 p => p.isIPLProof
  | _, _, .andElim2 p => p.isIPLProof
  | _, _, .orIntro1 p => p.isIPLProof
  | _, _, .orIntro2 p => p.isIPLProof
  | _, _, .orElim p₀ p₁ p₂ => p₀.isIPLProof ∧ p₁.isIPLProof ∧ p₂.isIPLProof
  | _, _, .laxIntro _ => False
  | _, _, .laxElim _ _ => False

/-- **Conservativity, proof-term form** — the statement that is `sorry`ed as
`PLLconservative` in `PLLNDProof.lean`/`PLLNDProofPostZoom.lean`. -/
theorem conservativity {Γ : List PLLFormula} {φ : PLLFormula}
    (p : LaxND Γ φ) : p.erased.isIPLProof := by
  induction p with
  | iden h => exact isIPL_erase _
  | falsoElim φ _ ih => exact ih
  | impIntro _ ih => exact ih
  | impElim _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | andIntro _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | andElim1 _ ih => exact ih
  | andElim2 _ ih => exact ih
  | orIntro1 _ ih => exact ih
  | orIntro2 _ ih => exact ih
  | orElim _ _ _ ih₀ ih₁ ih₂ => exact ⟨ih₀, ih₁, ih₂⟩
  | laxIntro _ ih => exact ih
  | laxElim _ _ ih₁ ih₂ => exact ⟨ih₂, ih₁⟩

end PLLND
