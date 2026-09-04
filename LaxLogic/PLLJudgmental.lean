import LaxLogic.PLLNDCore

/-!
# Judgmental PLL: the two-judgment (Pfenning–Davies) presentation

Pfenning and Davies, *A Judgmental Reconstruction of Modal Logic* (MSCS), §7,
present lax logic with **two judgments** rather than one:

    Γ ⊢ A true        A is true
    Γ ⊢ A lax         A is true under some constraint

`wip/polarity.lean` establishes why this matters here. In a single-judgment
calculus the inversion `Γ ⊢ ◯A ⟹ Γ ⊢ A` is **false**
(`Polarity.box_right_not_invertible`), so `◯` cannot be given negative polarity;
the invertibility that licenses the negative assignment is bought entirely by
the second judgment, where `◯A true` and `A lax` are interderivable by
construction. Polarities cannot be painted onto `SC`/`LaxND`. So the second
judgment is step one of the polarised programme
(`docs/lax-logic-interpolation-handoff.md`, `docs/ui-two-routes.md` §2), and
this file builds it.

## What is here

* `JD` — the two judgments, and `PD : JD → List PLLFormula → PLLFormula → Type`,
  the natural-deduction system with both.
* **Soundness**, unconditional and proved: `PD .tru` erases to `LaxND`, and
  `PD .lax Γ φ` erases to `LaxND Γ (◯φ)` (`sound_tru`, `sound_lax`).
* **Completeness**, also unconditional (`complete`, `equiv_nd`, `equiv_lax`).
  It was planned to be conditional on the inversion of `◯`-introduction, stated
  as an explicit hypothesis rather than assumed with `sorry`; that turned out to
  be unnecessary, because `circInvert` is `circE` with the identity
  continuation — the monad law `bind m return = m`. So the first step of the
  polarised programme carries **no debt**.
* Everything in this file is **axiom-free** (`#print axioms` pins at the foot).

## Why the entanglement moves

`SC`'s `laxL` fires only when the **succedent is `◯`-shaped** — a condition
relating antecedent to consequent, which is what uniform interpolation must
break. Here the corresponding rule `circE` instead concludes in the **`lax`
judgment**. The restriction has moved from the shape of a formula to the choice
of judgment, and a judgment is what a focusing phase tracks. That is the
mechanism the polarised route is betting on.
-/

namespace PLLND

/-- The two judgments of the Pfenning–Davies presentation. -/
inductive JD where
  | tru
  | lax
  deriving DecidableEq, Repr

/-- Judgmental PLL. `PD .tru Γ φ` is `Γ ⊢ φ true`; `PD .lax Γ φ` is
`Γ ⊢ φ lax`. Hypotheses are always `true`-hypotheses, as in Pfenning–Davies. -/
inductive PD : JD → List PLLFormula → PLLFormula → Type
  | hyp {Γ φ} (h : φ ∈ Γ) : PD .tru Γ φ
  | botE {Γ} (φ) (p : PD .tru Γ .falsePLL) : PD .tru Γ φ
  | impI {Γ φ ψ} (p : PD .tru (φ :: Γ) ψ) : PD .tru Γ (.ifThen φ ψ)
  | impE {Γ φ ψ} (p₁ : PD .tru Γ (.ifThen φ ψ)) (p₂ : PD .tru Γ φ) : PD .tru Γ ψ
  | andI {Γ φ ψ} (p₁ : PD .tru Γ φ) (p₂ : PD .tru Γ ψ) : PD .tru Γ (.and φ ψ)
  | andE1 {Γ φ ψ} (p : PD .tru Γ (.and φ ψ)) : PD .tru Γ φ
  | andE2 {Γ φ ψ} (p : PD .tru Γ (.and φ ψ)) : PD .tru Γ ψ
  | orI1 {Γ φ ψ} (p : PD .tru Γ φ) : PD .tru Γ (.or φ ψ)
  | orI2 {Γ φ ψ} (p : PD .tru Γ ψ) : PD .tru Γ (.or φ ψ)
  | orE {Γ φ ψ χ} (p₀ : PD .tru Γ (.or φ ψ))
      (p₁ : PD .tru (φ :: Γ) χ) (p₂ : PD .tru (ψ :: Γ) χ) : PD .tru Γ χ
  /-- The unit, at the level of judgments: what is true is lax. -/
  | laxU {Γ φ} (p : PD .tru Γ φ) : PD .lax Γ φ
  /-- `◯`-introduction: `A lax` justifies `◯A true`. -/
  | circI {Γ φ} (p : PD .lax Γ φ) : PD .tru Γ (.somehow φ)
  /-- `◯`-elimination.  Note the conclusion is in the **`lax`** judgment: this
  is where `SC`'s "succedent must be `◯`-shaped" side condition has gone. -/
  | circE {Γ φ χ} (p₁ : PD .tru Γ (.somehow φ)) (p₂ : PD .lax (φ :: Γ) χ) :
      PD .lax Γ χ

namespace PD

variable {Γ Γ' : List PLLFormula} {φ ψ χ : PLLFormula}

/-! ## Structural rules

As in `LaxND`, membership-based hypotheses make weakening, exchange and
contraction one traversal. -/

/-- Renaming: subsumes weakening, exchange and contraction, in both judgments. -/
def rename : ∀ {j : JD} {Γ Γ' : List PLLFormula} {φ : PLLFormula},
    (∀ ψ ∈ Γ, ψ ∈ Γ') → PD j Γ φ → PD j Γ' φ
  | _, _, _, _, H, .hyp h => .hyp (H _ h)
  | _, _, _, _, H, .botE φ p => .botE φ (rename H p)
  | _, _, _, _, H, .impI p =>
      .impI (rename (fun θ hθ => by
        rcases List.mem_cons.mp hθ with rfl | hθ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (H _ hθ)) p)
  | _, _, _, _, H, .impE p₁ p₂ => .impE (rename H p₁) (rename H p₂)
  | _, _, _, _, H, .andI p₁ p₂ => .andI (rename H p₁) (rename H p₂)
  | _, _, _, _, H, .andE1 p => .andE1 (rename H p)
  | _, _, _, _, H, .andE2 p => .andE2 (rename H p)
  | _, _, _, _, H, .orI1 p => .orI1 (rename H p)
  | _, _, _, _, H, .orI2 p => .orI2 (rename H p)
  | _, _, _, _, H, .orE p₀ p₁ p₂ =>
      .orE (rename H p₀)
        (rename (fun θ hθ => by
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (H _ hθ)) p₁)
        (rename (fun θ hθ => by
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (H _ hθ)) p₂)
  | _, _, _, _, H, .laxU p => .laxU (rename H p)
  | _, _, _, _, H, .circI p => .circI (rename H p)
  | _, _, _, _, H, .circE p₁ p₂ =>
      .circE (rename H p₁)
        (rename (fun θ hθ => by
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (H _ hθ)) p₂)

/-! ## Soundness, unconditional

`A true` erases to `Γ ⊢ A` and `A lax` erases to `Γ ⊢ ◯A`.  The two are proved
together, since `circI` and `circE` cross between them. -/

/-- Erasure of both judgments into `LaxND`, by mutual recursion:
`.tru` goes to `φ`, `.lax` goes to `◯φ`. -/
def erase : ∀ {j : JD} {Γ : List PLLFormula} {φ : PLLFormula},
    PD j Γ φ → LaxND Γ (match j with | .tru => φ | .lax => φ.somehow)
  | _, _, _, .hyp h => .iden h
  | _, _, _, .botE φ p => .falsoElim φ (erase p)
  | _, _, _, .impI p => .impIntro (erase p)
  | _, _, _, .impE p₁ p₂ => .impElim (erase p₁) (erase p₂)
  | _, _, _, .andI p₁ p₂ => .andIntro (erase p₁) (erase p₂)
  | _, _, _, .andE1 p => .andElim1 (erase p)
  | _, _, _, .andE2 p => .andElim2 (erase p)
  | _, _, _, .orI1 p => .orIntro1 (erase p)
  | _, _, _, .orI2 p => .orIntro2 (erase p)
  | _, _, _, .orE p₀ p₁ p₂ => .orElim (erase p₀) (erase p₁) (erase p₂)
  | _, _, _, .laxU p => .laxIntro (erase p)
  | _, _, _, .circI p => erase p
  | _, _, _, .circE p₁ p₂ => .laxElim (erase p₁) (erase p₂)

/-- **Soundness for `true`**: `Γ ⊢ φ true` gives `Γ ⊢ φ` in `LaxND`. -/
theorem sound_tru (p : PD .tru Γ φ) : Nonempty (LaxND Γ φ) := ⟨erase p⟩

/-- **Soundness for `lax`**: `Γ ⊢ φ lax` gives `Γ ⊢ ◯φ` in `LaxND` — the
`lax` judgment *is* the boxed one, which is the content of the presentation. -/
theorem sound_lax (p : PD .lax Γ φ) : Nonempty (LaxND Γ φ.somehow) := ⟨erase p⟩

/-! ## Completeness

The only place completeness needs anything beyond the rules is `laxElim`:
`LaxND`'s rule takes `Γ ⊢ ◯φ` and `φ :: Γ ⊢ ◯χ` to `Γ ⊢ ◯χ`, and to apply
`circE` we must turn `φ :: Γ ⊢ ◯χ true` into `φ :: Γ ⊢ χ lax`.  That step is
exactly the inversion of `circI`.

The plan was to state it as an explicit hypothesis rather than assume it with
`sorry`.  It proved unnecessary: see `circInvert` immediately below.
Semantically it is the judgmental form of "`◯A true` and `A lax` are
interderivable", which is what makes `◯` negative in the polarised setting —
see `wip/polarity.lean`. -/

/-- The inversion of `◯`-introduction: from `◯φ true` recover `φ lax`.

**It needed no hypothesis.**  The plan was to assume this and discharge it
later by a normalisation argument, since a derivation of `◯φ` ending in an
elimination is not normal and cannot be inverted by inspection.  But `circE`
already does the work with the *identity continuation*: eliminate `◯φ` and
return the bound variable.  This is the monad law `bind m return = m`, and it
is why the second judgment costs nothing to set up.

The consequence is that `complete` below is unconditional, and the polarised
route's first step carries no debt. -/
def circInvert (p : PD .tru Γ (.somehow φ)) : PD .lax Γ φ :=
  .circE p (.laxU (.hyp (List.mem_cons_self ..)))

/-- Retained as an abbreviation because the design note above, and
`docs/ui-two-routes.md`, refer to it by name. -/
abbrev CircInvert : Type :=
  ∀ {Γ : List PLLFormula} {φ : PLLFormula}, PD .tru Γ (.somehow φ) → PD .lax Γ φ

/-- The hypothesis is inhabited, so anything stated modulo it is unconditional. -/
def circInvertHolds : CircInvert := fun p => circInvert p

/-- **Completeness**, unconditional: every `LaxND` derivation lifts to a `true`
derivation of the judgmental system. -/
def complete : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    LaxND Γ φ → PD .tru Γ φ
  | _, _, .iden h => .hyp h
  | _, _, .falsoElim φ p => .botE φ (complete p)
  | _, _, .impIntro p => .impI (complete p)
  | _, _, .impElim p₁ p₂ => .impE (complete p₁) (complete p₂)
  | _, _, .andIntro p₁ p₂ => .andI (complete p₁) (complete p₂)
  | _, _, .andElim1 p => .andE1 (complete p)
  | _, _, .andElim2 p => .andE2 (complete p)
  | _, _, .orIntro1 p => .orI1 (complete p)
  | _, _, .orIntro2 p => .orI2 (complete p)
  | _, _, .orElim p₀ p₁ p₂ =>
      .orE (complete p₀) (complete p₁) (complete p₂)
  | _, _, .laxIntro p => .circI (.laxU (complete p))
  | _, _, .laxElim p₁ p₂ =>
      -- `◯φ true` and `φ :: Γ ⊢ ◯χ true`; invert the second to `χ lax`,
      -- then `circE`, then `circI`.
      .circI (.circE (complete p₁) (circInvert (complete p₂)))

/-- **The equivalence**: judgmental PLL and `LaxND` prove the same sequents. -/
theorem equiv_nd : Nonempty (PD .tru Γ φ) ↔ Nonempty (LaxND Γ φ) :=
  ⟨fun ⟨p⟩ => sound_tru p, fun ⟨p⟩ => ⟨complete p⟩⟩

/-- And in the `lax` judgment: `Γ ⊢ φ lax` iff `Γ ⊢ ◯φ` in `LaxND`.  This is
the precise sense in which the second judgment *is* the modality. -/
theorem equiv_lax : Nonempty (PD .lax Γ φ) ↔ Nonempty (LaxND Γ φ.somehow) :=
  ⟨fun ⟨p⟩ => sound_lax p, fun ⟨p⟩ => ⟨circInvert (complete p)⟩⟩

/-! ## The unit and the two derived shapes, unconditional

These need no hypothesis, and they are what the polarised route will use: the
`lax` judgment is closed under the operations the interpolant recursion has to
descend through. -/

/-- `A true ⟹ ◯A true`: `LaxND`'s `laxIntro`, factored through the judgment. -/
def unitT (p : PD .tru Γ φ) : PD .tru Γ (.somehow φ) := .circI (.laxU p)

/-- `◯`-elimination in the form `SC` uses: from `◯φ` and `φ :: Γ ⊢ ◯χ true`,
conclude `◯χ true` — but note this needs the inversion, exactly as `laxElim`
did.  Recorded to show precisely where the hypothesis bites. -/
def circE_tru (p₁ : PD .tru Γ (.somehow φ))
    (p₂ : PD .tru (φ :: Γ) (.somehow χ)) : PD .tru Γ (.somehow χ) :=
  .circI (.circE p₁ (circInvert p₂))

/-- `lax` is closed under the unit in the other direction: `φ lax` from
`◯φ true` is exactly `CircInvert`, while `◯φ lax` from `φ lax` is free. -/
def laxBox (p : PD .lax Γ φ) : PD .lax Γ (.somehow φ) := .laxU (.circI p)

end PD
end PLLND

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'PLLND.PD.circInvert' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.PD.circInvert

/-- info: 'PLLND.PD.erase' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.PD.erase

/-- info: 'PLLND.PD.complete' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.PD.complete

/-- info: 'PLLND.PD.equiv_nd' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.PD.equiv_nd

/-- info: 'PLLND.PD.equiv_lax' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.PD.equiv_lax
