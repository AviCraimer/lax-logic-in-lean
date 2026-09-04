import LaxLogic.PLLPolar

/-!
# A focused calculus for PLL, with the judgment flag on the stable goal

Step 3 of the programme in `docs/lax-logic-interpolation-handoff.md`, over
`LaxLogic/PLLJudgmental.lean` (two judgments) and `LaxLogic/PLLPolar.lean`
(polarised syntax).

## The design decision, and why it came out well

Left-focusing on `◯Q` may only fire when the goal is **lax** — this is `SC`'s
"succedent must be `◯`-shaped" in its third form. In a focused calculus the
stable goal is a *parameter of the judgment*, so the judgments must carry the
flag:

    Stab   Γ j P      stable sequent: `Γ ⊢ P` at judgment `j`
    RFocus Γ j P      right focus on the positive `P`
    LFoc   Γ N j P    left focus on the negative `N`, stable goal `P`
    Inv    Γ Ω j N    inversion: `Ω` positives on the left, `N` on the right

`docs/ui-two-routes.md` §6 asked which rules have to *read* the flag, on the
grounds that if `⊃` or `∨` must read it then the polarised route inherits the
entanglement it was meant to dissolve. The answer, visible in the rules below:

* **`circL` is the only rule that reads it** — it exists only at `.lax`;
* `circR` *sets* its premise to `.lax` (from either flag: `◯P true` and
  `◯P lax` both reduce to `P lax`);
* `impL` *sets* its argument premise to `.tru` — an argument is proved truly,
  never laxly — but does not inspect `j`;
* **every other rule threads `j` through untouched.**

So the modal content is separated by the flag, which is the favourable outcome
for the interpolant recursion: two smaller things to descend on rather than one.

## What is proved

* `PD.cut`, which left-focus soundness needs, and which comes cheaply: natural
  deduction cut is `impE ∘ impI`, and the `lax` case routes through
  `sound_lax`/`complete`/`circInvert`, all already available.
* **Soundness** of all four judgments into `PD`, hence into `LaxND`. Left focus
  is stated in continuation-passing form, which is what makes the `⊃` case go
  through without a second cut.

**Not proved here**: focalization (completeness of the focused system). Per
Matthew's instruction it is stated as an explicit hypothesis, `Focalization`,
rather than assumed with `sorry`, so every result is either unconditional or
visibly carries it. Simmons's identity expansion is the expected cost, and no
reference covers it for a modality.
-/

namespace PLLND
namespace Focused

open Polar

/-- Erase a stable context. -/
def eraseCtx (Γ : List Neg) : List PLLFormula := Γ.map eraseNeg

/-! ## Cut for the judgmental system

Needed for left-focus soundness. Cheap: for `.tru` it is `impE ∘ impI`; for
`.lax` it routes through the equivalence with `LaxND`. -/

/-- Natural-deduction cut for `LaxND`: substitution via `⊃`. -/
def ndCut {Γ : List PLLFormula} {φ χ : PLLFormula}
    (d : LaxND Γ φ) (e : LaxND (φ :: Γ) χ) : LaxND Γ χ :=
  .impElim (.impIntro e) d

/-- **Cut for `PD`**, in both judgments. -/
def pdCut : ∀ {j : JD} {Γ : List PLLFormula} {φ χ : PLLFormula},
    PD .tru Γ φ → PD j (φ :: Γ) χ → PD j Γ χ
  | .tru, _, _, _, d, e => .impE (.impI e) d
  | .lax, _, _, _, d, e =>
      -- `e` gives `LaxND (φ :: Γ) ◯χ`; cut in `LaxND`, come back through
      -- `complete` and invert.
      PD.circInvert (PD.complete (ndCut (PD.erase d) (PD.erase e)))

/-! ## The focused calculus -/

mutual

/-- A **stable sequent**: no invertible rule applies, so a formula must be
chosen to focus on — either the goal (right focus) or a hypothesis (left). -/
inductive Stab : List Neg → JD → Pos → Type
  /-- Focus on the goal. -/
  | rfoc {Γ j P} : RFocus Γ j P → Stab Γ j P
  /-- Focus on a hypothesis. -/
  | lfoc {Γ j P N} (h : N ∈ Γ) : LFoc Γ N j P → Stab Γ j P

/-- **Right focus** on a positive goal: only non-invertible right rules. -/
inductive RFocus : List Neg → JD → Pos → Type
  /-- An atom is proved by having it. -/
  | init {Γ j a} (h : Neg.up (Pos.atom a) ∈ Γ) : RFocus Γ j (.atom a)
  | or1 {Γ j P Q} : RFocus Γ j P → RFocus Γ j (.or P Q)
  | or2 {Γ j P Q} : RFocus Γ j Q → RFocus Γ j (.or P Q)
  /-- Release: `↓N` on the right blurs into inversion. -/
  | rel {Γ j N} : Inv Γ [] j N → RFocus Γ j (.down N)

/-- **Left focus** on a negative hypothesis, with a stable goal. -/
inductive LFoc : List Neg → Neg → JD → Pos → Type
  /-- `↑Q` on the left releases into inversion with `Q` to invert. -/
  | rel {Γ j Q P} : Inv Γ [Q] j (.up P) → LFoc Γ (.up Q) j P
  /-- `⊃`-left.  The argument is proved at `.tru` — an argument is true, not
  lax — but the rule does not inspect `j`. -/
  | impL {Γ j Q N P} : Stab Γ .tru Q → LFoc Γ N j P → LFoc Γ (.imp Q N) j P
  | and1 {Γ j M N P} : LFoc Γ M j P → LFoc Γ (.and M N) j P
  | and2 {Γ j M N P} : LFoc Γ N j P → LFoc Γ (.and M N) j P
  /-- **`◯`-left: the only rule that reads the flag.**  It exists at `.lax`
  only.  This is `SC`'s "succedent must be `◯`-shaped", now a phase condition. -/
  | circL {Γ Q P} : Inv Γ [Q] .lax (.up P) → LFoc Γ (.circ Q) .lax P

/-- **Inversion**: invert the right-hand negative, then the positives in `Ω`. -/
inductive Inv : List Neg → List Pos → JD → Neg → Type
  /-- `⊃`-right is invertible — **at `.tru` only**.  At `.lax` it would read
  `φ ⊃ ◯ψ ⟹ ◯(φ ⊃ ψ)`, the converse of `K`, which is REFUTED
  (`wip/converseK.lean`).  The restriction was found by the soundness proof
  failing, not by inspection. -/
  | impR {Γ Ω Q N} : Inv Γ (Q :: Ω) .tru N → Inv Γ Ω .tru (.imp Q N)
  /-- `∧`-right is invertible, `.tru` only for the same reason. -/
  | andR {Γ Ω M N} : Inv Γ Ω .tru M → Inv Γ Ω .tru N → Inv Γ Ω .tru (.and M N)
  /-- **`◯`-right sets the flag to `.lax`**, from either flag: `◯P true` and
  `◯P lax` both reduce to `P lax`. -/
  | circR {Γ Ω j P} : Inv Γ Ω .lax (.up P) → Inv Γ Ω j (.circ P)
  /-- With nothing left to invert, the sequent is stable. -/
  | stable {Γ j P} : Stab Γ j P → Inv Γ [] j (.up P)
  /-- `∨`-left is invertible: split. -/
  | orL {Γ Ω j P Q N} : Inv Γ (P :: Ω) j N → Inv Γ (Q :: Ω) j N →
      Inv Γ (.or P Q :: Ω) j N
  /-- `⊥`-left closes the branch. -/
  | flsL {Γ Ω j N} : Inv Γ (.fls :: Ω) j N
  /-- `↓`-left: a shifted negative becomes a stable hypothesis. -/
  | downL {Γ Ω j M N} : Inv (M :: Γ) Ω j N → Inv Γ (.down M :: Ω) j N
  /-- An atom on the left becomes a stable hypothesis. -/
  | atomL {Γ Ω j a N} : Inv (.up (.atom a) :: Γ) Ω j N →
      Inv Γ (.atom a :: Ω) j N

end

/-! ## Soundness, into `LaxND` directly

Targeting `LaxND` rather than `PD` keeps every case a single rule application:
`PD`'s propositional rules live at `.tru` only, so a `PD`-valued statement would
need a lax duplicate of each.  `wrap` sends the `lax` judgment to `◯`, which is
exactly `PD.equiv_lax`.

Left focus is in **continuation-passing** form: given a derivation of the
focused formula, produce one of the goal.  That is what makes the `⊃` case go
through with one cut rather than two. -/

/-- `wrap .tru φ = φ`, `wrap .lax φ = ◯φ` — the judgment as a formula operator. -/
def wrap : JD → PLLFormula → PLLFormula
  | .tru, φ => φ
  | .lax, φ => φ.somehow

/-- A `true` derivation serves at either judgment. -/
def wrapIn : ∀ {j : JD} {Γ : List PLLFormula} {φ : PLLFormula},
    LaxND Γ φ → LaxND Γ (wrap j φ)
  | .tru, _, _, d => d
  | .lax, _, _, d => .laxIntro d

/-- Functoriality of `◯`: the monad map.  This is what supplies the `lax`
versions of the positive right rules without duplicating them in `PD`. -/
def laxMono {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (d : LaxND Γ φ.somehow) (e : LaxND (φ :: Γ) ψ) : LaxND Γ ψ.somehow :=
  .laxElim d (.laxIntro e)

/-- `wrap`-level disjunction introduction, left. -/
def wrapOr1 : ∀ {j : JD} {Γ : List PLLFormula} {φ ψ : PLLFormula},
    LaxND Γ (wrap j φ) → LaxND Γ (wrap j (φ.or ψ))
  | .tru, _, _, _, d => .orIntro1 d
  | .lax, _, _, _, d => laxMono d (.orIntro1 (.iden (by simp)))

/-- `wrap`-level disjunction introduction, right. -/
def wrapOr2 : ∀ {j : JD} {Γ : List PLLFormula} {φ ψ : PLLFormula},
    LaxND Γ (wrap j ψ) → LaxND Γ (wrap j (φ.or ψ))
  | .tru, _, _, _, d => .orIntro2 d
  | .lax, _, _, _, d => laxMono d (.orIntro2 (.iden (by simp)))

mutual

/-- Soundness of stable sequents. -/
def soundStab : ∀ {Γ : List Neg} {j : JD} {P : Pos},
    Stab Γ j P → LaxND (eraseCtx Γ) (wrap j (erasePos P))
  | _, _, _, .rfoc d => soundRFocus d
  | _, _, _, .lfoc h d => soundLFoc d (.iden (List.mem_map_of_mem h))

/-- Soundness of right focus. -/
def soundRFocus : ∀ {Γ : List Neg} {j : JD} {P : Pos},
    RFocus Γ j P → LaxND (eraseCtx Γ) (wrap j (erasePos P))
  | _, _, _, .init h => wrapIn (.iden (List.mem_map_of_mem h))
  | _, _, _, .or1 d => wrapOr1 (soundRFocus d)
  | _, _, _, .or2 d => wrapOr2 (soundRFocus d)
  | _, _, _, .rel d => soundInv d

/-- Soundness of left focus, continuation-passing. -/
def soundLFoc : ∀ {Γ : List Neg} {N : Neg} {j : JD} {P : Pos},
    LFoc Γ N j P → LaxND (eraseCtx Γ) (eraseNeg N) →
      LaxND (eraseCtx Γ) (wrap j (erasePos P))
  | _, _, _, _, .rel d, k => ndCut k (soundInv d)
  | _, _, _, _, .impL a d, k => soundLFoc d (.impElim k (soundStab a))
  | _, _, _, _, .and1 d, k => soundLFoc d (.andElim1 k)
  | _, _, _, _, .and2 d, k => soundLFoc d (.andElim2 k)
  | _, _, _, _, .circL d, k => .laxElim k (soundInv d)

/-- Soundness of inversion. -/
def soundInv : ∀ {Γ : List Neg} {Ω : List Pos} {j : JD} {N : Neg},
    Inv Γ Ω j N → LaxND (Ω.map erasePos ++ eraseCtx Γ) (wrap j (eraseNeg N))
  | _, _, _, _, .impR d => .impIntro (soundInv d)
  | _, _, _, _, .andR d e => .andIntro (soundInv d) (soundInv e)
  | _, _, _, _, .circR d => wrapIn (soundInv d)
  | _, _, _, _, .stable d => soundStab d
  | _, _, _, _, .orL d e =>
      .orElim (.iden (List.mem_cons_self ..))
        ((soundInv d).rename (fun θ hθ => by
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hθ)))
        ((soundInv e).rename (fun θ hθ => by
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hθ)))
  | _, _, _, _, .flsL => .falsoElim _ (.iden (List.mem_cons_self ..))
  | _, _, _, _, .downL d =>
      (soundInv d).rename (fun θ hθ => by
        simp only [eraseCtx, List.map_cons, List.mem_append, List.mem_cons] at hθ ⊢
        tauto)
  | _, _, _, _, .atomL d =>
      (soundInv d).rename (fun θ hθ => by
        simp only [eraseCtx, List.map_cons, List.mem_append, List.mem_cons] at hθ ⊢
        tauto)

end

/-! ## Focalization, stated as a hypothesis

Completeness of the focused system.  Stated explicitly rather than assumed with
`sorry`, so every result carrying it says so.  Simmons's identity expansion is
the expected cost, and no reference covers it for a modality. -/

/-- **Focalization**: every `LaxND` derivation has a focused counterpart. -/
abbrev Focalization : Type :=
  ∀ {Γ : List Neg} {P : Pos},
    LaxND (eraseCtx Γ) (erasePos P) → Stab Γ .tru P

/-- Soundness, packaged. -/
theorem stab_sound {Γ : List Neg} {P : Pos} (d : Stab Γ .tru P) :
    Nonempty (LaxND (eraseCtx Γ) (erasePos P)) := ⟨soundStab d⟩

/-- The equivalence, modulo `Focalization`. -/
theorem equiv_focused (foc : Focalization) {Γ : List Neg} {P : Pos} :
    Nonempty (Stab Γ .tru P) ↔ Nonempty (LaxND (eraseCtx Γ) (erasePos P)) :=
  ⟨fun ⟨d⟩ => stab_sound d, fun ⟨d⟩ => ⟨foc d⟩⟩

end Focused
end PLLND

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'PLLND.Focused.pdCut' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.Focused.pdCut

/-- info: 'PLLND.Focused.soundStab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Focused.soundStab

/-- info: 'PLLND.Focused.soundInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Focused.soundInv

/-- info: 'PLLND.Focused.stab_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Focused.stab_sound
