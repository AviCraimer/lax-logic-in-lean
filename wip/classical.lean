import wip.schemeext
import Mathlib.Order.Nucleus

/-!
# PLL + excluded middle: the closed fragment has EXACTLY FOUR elements

The classical rung of the ladder.  Constructively the variable-free
(closed) fragment of PLL is infinite and richly structured — the
Rieger–Nishimura ladder embedded via `p ↦ ◯⊥`, an infinite antichain of gaps,
a strict `◯`-depth hierarchy.  This file settles the classical half:

> **`varfree_exactly_four`.**  In PLL + excluded middle every variable-free
> formula is interderivable with exactly one of
>
>     ⊥ ,   ◯⊥ ,   ¬◯⊥ ,   ⊤ ,
>
> and these four are pairwise non-interderivable: the closed fragment has
> **exactly four** elements.

What is machine-checked is the count and the representatives
(`varfree_exactly_four`, `rep4_inj`).  That the resulting four-element algebra
*is* the free Boolean algebra on the generator `◯⊥` is the natural reading of
that data — the `◯`-action is `x ↦ x ∨ ◯⊥` (`box_closed`, `box_nobot_em`) —
but the algebra structure is not itself formalised here.

The count is sharp at both ends and the statement is a sandwich: the
classification is proved from the **single closed instance**
`◯⊥ ∨ ¬◯⊥` (`IsEM0`), and the four are already distinguished in the **full**
scheme `A ∨ ¬A` (`IsEM`), so every system in between has exactly four classes
(`varfree_exactly_four_of`).

## The mechanism, and the Heyting/Boolean boundary

Algebraically PLL is a Heyting algebra with a nucleus `j`; adding excluded
middle makes the algebra Boolean.  The load-bearing step is

* `nucleus_eq_closed` — **on a Boolean algebra every nucleus is closed**:
  `j x = x ⊔ j ⊥`.  Proof: `j x = (j x ⊓ x) ⊔ (j x ⊓ xᶜ)` by `x ⊔ xᶜ = ⊤`,
  and `j x ⊓ xᶜ ≤ j x ⊓ j xᶜ = j (x ⊓ xᶜ) = j ⊥`.  Booleanness really does
  rescue the closed form.
* `nucleus_not_closed_Fin3` — and it is genuinely Booleanness that does it:
  on the three-element **Heyting** chain the nucleus `j 0 = 0`, `j 1 = j 2 = 2`
  has `j ⊥ = ⊥` but `j 1 = 2 ≠ 1`.

Syntactically the same step is `box_closed`:

    ◯A  ⊣⊢  A ∨ ◯⊥          (one instance of excluded middle, for `A`)

proved by `laxElim` in the `¬A` branch.  Two corollaries:

* `dist_of_em` — **classical PLL contains PCLL**: `◯(A∨B) ⊃ (◯A ∨ ◯B)` is
  derivable from excluded middle alone.
* `box_trivial` — **F&M's remark (Inf. Comput. 137(1), p. 6) machine-checked**:
  excluded middle *together with* `¬◯⊥` trivialises `◯` (`◯A ⊣⊢ A`), for
  arbitrary `A`, not just closed `A`.  Excluded middle **alone** does not:
  `◯⊥` survives as a genuine element, which is exactly why the closed
  fragment is four and not two.

## `K`, and what it does not give

`SchemeExt.ndK` proves `◯(A ⊃ B) ⊃ (◯A ⊃ ◯B)` in **plain** PLL.  Since PLL
has a countermodel to distribution (`PLLND.not_provable_somehow_or_dist`,
F&M Figure 3 middle), `K` does not force distribution:
`K_does_not_force_dist` records the pair.

## The lower bound

`modelEM` is the three-world model `u`, `v`, `f` with `f` fallible, `u`, `v`
`Rᵢ`-incomparable, `v Rₘ f`.  Excluded middle is valid there by the frame
condition `SymmOffF` (`Rᵢ` is symmetric off the fallible worlds), and

    ⊥ = ∅ ,   ◯⊥ = {v} ,   ¬◯⊥ = {u} ,   ⊤ = {u,v}   (off `f`)

separates the four classes.
-/

open PLLFormula

namespace PLLND
namespace ClassicalLax

open SchemeExt
open NoFall (VarFree)

/-! ## 1. The system -/

/-- One instance of excluded middle. -/
def emF (A : PLLFormula) : PLLFormula := A.or (notPLL A)

/-- The excluded middle **scheme**: all instances.  A scheme with variables,
so the axiom set (not a single persistent hypothesis) is the right form —
this is the substitution-closed extension. -/
def IsEM (θ : PLLFormula) : Prop := ∃ A, θ = emF A

/-- The **single closed instance** `◯⊥ ∨ ¬◯⊥`.  Being closed, hypothesis form
and axiom form agree for it (as for `¬◯⊥` in `PLLNoFall.lean`). -/
def IsEM0 (θ : PLLFormula) : Prop := θ = emF boxBot

theorem isEM_of_isEM0 : ∀ θ, IsEM0 θ → IsEM θ := fun _ h => ⟨boxBot, h⟩

/-- PLL + excluded middle. -/
abbrev DerivEM : List PLLFormula → PLLFormula → Prop := DerivX IsEM

/-- PLL + `◯⊥ ∨ ¬◯⊥`. -/
abbrev DerivEM0 : List PLLFormula → PLLFormula → Prop := DerivX IsEM0

/-! ## 2. The closed-nucleus law, syntactically -/

variable {X : PLLFormula → Prop} {Δ : List PLLFormula} {A B : PLLFormula}

/-- **The closed-nucleus law**:

    ◯A  ⊣⊢  A ∨ ◯⊥

from the single instance `A ∨ ¬A`.  The `¬A` branch is where the modality is
computed: `◯A` and `¬A` give `◯⊥` by `laxElim`. -/
theorem box_closed (hX : X (emF A)) : Interd X Δ (somehow A) (A.or boxBot) := by
  constructor
  · refine DerivX.orE (φ := A) (ψ := notPLL A) (DerivX.ax hX) ?_ ?_
    · exact DerivX.orI₁ (φ := A) (ψ := boxBot) (DerivX.hyp (by simp))
    · refine DerivX.orI₂ (φ := A) (ψ := boxBot) ?_
      have h : DerivX X (A :: (notPLL A :: Δ)) falsePLL :=
        DerivX.mp (φ := A) (ψ := falsePLL) (DerivX.hyp (by simp))
          (DerivX.hyp (by simp))
      exact (box_mono h).rename (by intro θ hθ; simp at hθ ⊢; tauto)
  · refine DerivX.orE (φ := A) (ψ := boxBot) (DerivX.hyp (by simp)) ?_ ?_
    · exact DerivX.unit (DerivX.hyp (by simp))
    · exact box_mono (bot_imp A)

/-- **Classical PLL contains PCLL**: the distribution scheme

    ◯(A ∨ B) ⊃ (◯A ∨ ◯B)

is derivable from the single instance `(A∨B) ∨ ¬(A∨B)` of excluded middle. -/
theorem dist_of_em (hX : X (emF (A.or B))) :
    DerivX X Δ ((somehow (A.or B)).ifThen ((somehow A).or (somehow B))) := by
  refine DerivX.deduction ?_
  have hc : DerivX X (somehow (A.or B) :: Δ) ((A.or B).or boxBot) :=
    (box_closed hX).1
  refine DerivX.orE (φ := A.or B) (ψ := boxBot) hc ?_ ?_
  · refine DerivX.orE (φ := A) (ψ := B) (DerivX.hyp (by simp)) ?_ ?_
    · exact DerivX.orI₁ (φ := somehow A) (ψ := somehow B)
        (DerivX.unit (DerivX.hyp (by simp)))
    · exact DerivX.orI₂ (φ := somehow A) (ψ := somehow B)
        (DerivX.unit (DerivX.hyp (by simp)))
  · exact DerivX.orI₁ (φ := somehow A) (ψ := somehow B) (box_mono (bot_imp A))

/-- **F&M's remark (Inf. Comput. 137(1), p. 6), machine-checked.**  Excluded
middle together with `¬◯⊥` trivialises the modality: `◯A ⊣⊢ A`, for every `A`
(not only variable-free `A`). -/
theorem box_trivial (hX : X (emF A)) (hΔ : NoFall.nobot ∈ Δ) :
    Interd X Δ (somehow A) A := by
  refine (box_closed hX).trans (or_absorb_right ?_)
  exact DerivX.exfalso (DerivX.mp (φ := boxBot) (ψ := falsePLL)
    (DerivX.hyp (List.mem_cons_of_mem _ hΔ)) (DerivX.hyp (by simp))) A

/-- **`K` is a theorem of plain PLL, and `K` does not force distribution.**
Left: every instance of `◯(A ⊃ B) ⊃ (◯A ⊃ ◯B)` is derivable with no extra
axiom.  Right: distribution is not (F&M Figure 3, middle model —
`PLLND.not_provable_somehow_or_dist`).  So the two are independent: the
chain-based argument for distribution is financed by linearity, not by `K`. -/
theorem K_does_not_force_dist :
    (∀ A B : PLLFormula, Nonempty (LaxND []
        ((somehow (A.ifThen B)).ifThen ((somehow A).ifThen (somehow B)))))
      ∧ ¬ Nonempty (LaxND []
        ((somehow ((prop "A").or (prop "B"))).ifThen
          ((somehow (prop "A")).or (somehow (prop "B"))))) :=
  ⟨fun A B => ⟨ndK A B⟩, not_provable_somehow_or_dist⟩

/-! ## 3. The four classes -/

/-- The four representatives `⊥`, `◯⊥`, `¬◯⊥`, `⊤`. -/
def rep4 (i : Fin 4) : PLLFormula :=
  if i.val = 0 then falsePLL
  else if i.val = 1 then boxBot
  else if i.val = 2 then NoFall.nobot
  else truePLL

@[simp] theorem rep4_zero : rep4 0 = falsePLL := rfl
@[simp] theorem rep4_one : rep4 1 = boxBot := rfl
@[simp] theorem rep4_two : rep4 2 = NoFall.nobot := rfl
@[simp] theorem rep4_three : rep4 3 = truePLL := rfl

theorem varFree_rep4 (i : Fin 4) : VarFree (rep4 i) := by
  fin_cases i
  exacts [trivial, trivial, ⟨trivial, trivial⟩, NoFall.varFree_truePLL]

/-- The class index: first coordinate the value under `◯⊥`, second the value
under `¬◯⊥`. -/
def idx4 (x y : Fin 2) : Fin 4 :=
  ⟨x.val + 2 * y.val, by have := x.isLt; have := y.isLt; omega⟩

@[simp] theorem idx4_00 : idx4 0 0 = 0 := rfl
@[simp] theorem idx4_10 : idx4 1 0 = 1 := rfl
@[simp] theorem idx4_01 : idx4 0 1 = 2 := rfl
@[simp] theorem idx4_11 : idx4 1 1 = 3 := rfl

/-! ### The four bridges -/

theorem br_bot (x y : Fin 2) : DerivX X [rep2 x, boxBot] (rep4 (idx4 x y)) := by
  fin_cases x <;> fin_cases y
  · exact bot_imp _
  · exact bot_imp _
  · exact DerivX.hyp (by simp)
  · exact DerivX.top

theorem br_bot' (x y : Fin 2) :
    DerivX X [rep4 (idx4 x y), boxBot] (rep2 x) := by
  fin_cases x <;> fin_cases y
  · exact DerivX.hyp (by simp)
  · exact DerivX.mp (φ := boxBot) (ψ := falsePLL)
      (DerivX.hyp (by simp [NoFall.nobot])) (DerivX.hyp (by simp))
  · exact DerivX.top
  · exact DerivX.top

theorem br_no (x y : Fin 2) :
    DerivX X [rep2 y, NoFall.nobot] (rep4 (idx4 x y)) := by
  fin_cases x <;> fin_cases y
  · exact bot_imp _
  · exact DerivX.hyp (by simp [NoFall.nobot])
  · exact bot_imp _
  · exact DerivX.top

theorem br_no' (x y : Fin 2) :
    DerivX X [rep4 (idx4 x y), NoFall.nobot] (rep2 y) := by
  fin_cases x <;> fin_cases y
  · exact DerivX.hyp (by simp [NoFall.nobot])
  · exact DerivX.top
  · exact DerivX.mp (φ := boxBot) (ψ := falsePLL)
      (DerivX.hyp (by simp [NoFall.nobot])) (DerivX.hyp (by simp [NoFall.nobot]))
  · exact DerivX.top

/-- **The upper bound**: from the single closed instance `◯⊥ ∨ ¬◯⊥`, every
variable-free formula falls into one of the four classes. -/
theorem four_complete (hX : X (emF boxBot)) :
    ∀ A : PLLFormula, VarFree A → ∃ i, Interd X [] A (rep4 i) := by
  intro A hA
  obtain ⟨x, hx⟩ := dich_bot (X := X) (Δ := [boxBot]) (by simp) A hA
  obtain ⟨y, hy⟩ := dich_nobot (X := X) (Δ := [NoFall.nobot]) (by simp) A hA
  exact ⟨idx4 x y, combine (P := boxBot) (Q := notPLL boxBot)
    (rep := fun a b => rep4 (idx4 a b)) (fun _ => DerivX.ax hX)
    (br_bot x y) (br_bot' x y) (br_no x y) (br_no' x y) hx hy⟩

/-! ## 4. The lower bound: a three-world classical model -/

/-- Worlds of `modelEM`: `u` (no fallible successor), `v` (one), `f`
(fallible). -/
inductive WEM : Type
  | u | v | f
  deriving DecidableEq, Fintype

/-- `Rᵢ`: reflexive, plus everything below the fallible world `f`.  `u` and
`v` are incomparable. -/
def riEM (x y : WEM) : Prop := x = y ∨ y = .f

instance : DecidableRel riEM := fun x y =>
  inferInstanceAs (Decidable (x = y ∨ y = .f))

/-- `Rₘ`: reflexive, plus `v Rₘ f`. -/
def rmEM (x y : WEM) : Prop := x = y ∨ (x = .v ∧ y = .f)

instance : DecidableRel rmEM := fun x y =>
  inferInstanceAs (Decidable (x = y ∨ (x = .v ∧ y = .f)))

@[reducible] def modelEM : ConstraintModel where
  W := WEM
  Ri := riEM
  Rm := rmEM
  F := {x | x = .f}
  V _ := {x | x = .f}
  refl_i _ := .inl rfl
  trans_i {x y z} h h' :=
    (by decide : ∀ x y z : WEM, riEM x y → riEM y z → riEM x z) x y z h h'
  refl_m _ := .inl rfl
  trans_m {x y z} h h' :=
    (by decide : ∀ x y z : WEM, rmEM x y → rmEM y z → rmEM x z) x y z h h'
  sub_mi {x y} h := (by decide : ∀ x y : WEM, rmEM x y → riEM x y) x y h
  hered_F {x y} h hw :=
    (by decide : ∀ x y : WEM, riEM x y → x = .f → y = .f) x y h hw
  hered_V {_ x y} h hw :=
    (by decide : ∀ x y : WEM, riEM x y → x = .f → y = .f) x y h hw
  full_F hw := hw

instance (φ : PLLFormula) (w : modelEM.W) : Decidable (modelEM.force w φ) :=
  modelEM.decForce φ w

/-- **The frame condition for excluded middle**: `Rᵢ` is symmetric off the
fallible worlds.  (Where it fails, a valuation separating a world from a
non-fallible successor refutes `p ∨ ¬p`.) -/
def SymmOffF (C : ConstraintModel) : Prop :=
  ∀ {w u : C.W}, C.Ri w u → u ∉ C.F → C.Ri u w

/-- Soundness half of the correspondence: on a `SymmOffF` model every instance
of excluded middle is forced everywhere. -/
theorem force_em_of_symmOffF {C : ConstraintModel} (hC : SymmOffF C) (w : C.W)
    (A : PLLFormula) : C.force w (emF A) := by
  by_cases hA : C.force w A
  · exact Or.inl hA
  · refine Or.inr ?_
    intro v hwv hv
    by_contra hf
    exact hA (C.force_hered (hC hwv hf) hv)

theorem modelEM_symm : SymmOffF modelEM := by
  intro w x h hx
  exact (by decide : ∀ w x : WEM, riEM w x → ¬ (x = .f) → riEM x w) w x h hx

/-- Soundness of the full excluded-middle system over `modelEM`. -/
theorem sound_EM {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivEM Γ φ)
    (w : modelEM.W) (hΓ : ∀ ψ ∈ Γ, modelEM.force w ψ) : modelEM.force w φ := by
  refine sound (fun θ hθ w => ?_) h w hΓ
  obtain ⟨A, rfl⟩ := hθ
  exact force_em_of_symmOffF modelEM_symm w A

theorem transfer {P Q : PLLFormula} (h : DerivEM [P] Q) (w : modelEM.W)
    (hP : modelEM.force w P) : modelEM.force w Q :=
  sound_EM h w (by intro ψ hψ; simp at hψ; subst hψ; exact hP)

/-- **The lower bound**: the four representatives are pairwise
non-interderivable, already in the full excluded-middle system. -/
theorem rep4_inj {i j : Fin 4} (h : Interd IsEM [] (rep4 i) (rep4 j)) : i = j := by
  have hu : modelEM.force .u (rep4 i) ↔ modelEM.force .u (rep4 j) :=
    ⟨fun hf => transfer h.1 .u hf, fun hf => transfer h.2 .u hf⟩
  have hv : modelEM.force .v (rep4 i) ↔ modelEM.force .v (rep4 j) :=
    ⟨fun hf => transfer h.1 .v hf, fun hf => transfer h.2 .v hf⟩
  revert hu hv
  fin_cases i <;> fin_cases j <;> decide

/-! ## 5. The theorem -/

/-- **THE CLASSICAL COLLAPSE.**  For any axiom set `X` between the single
closed instance `◯⊥ ∨ ¬◯⊥` and the full excluded-middle scheme, every
variable-free formula is interderivable with **exactly one** of

    ⊥ ,   ◯⊥ ,   ¬◯⊥ ,   ⊤ .

The closed fragment of classical PLL therefore has **exactly four** elements:
the free Boolean algebra on the generator `◯⊥`. -/
theorem varfree_exactly_four_of (h0 : X (emF boxBot))
    (hX : ∀ θ, X θ → IsEM θ) (A : PLLFormula) (hA : VarFree A) :
    ∃! i : Fin 4, Interd X [] A (rep4 i) := by
  obtain ⟨i, hi⟩ := four_complete h0 A hA
  refine ⟨i, hi, fun j hj => ?_⟩
  exact rep4_inj ((hj.mono hX).symm.trans (hi.mono hX))

/-- The collapse for PLL + the full excluded-middle scheme. -/
theorem varfree_exactly_four (A : PLLFormula) (hA : VarFree A) :
    ∃! i : Fin 4, Interd IsEM [] A (rep4 i) :=
  varfree_exactly_four_of ⟨boxBot, rfl⟩ (fun _ h => h) A hA

/-- The collapse already for PLL + the single closed axiom `◯⊥ ∨ ¬◯⊥`. -/
theorem varfree_exactly_four_em0 (A : PLLFormula) (hA : VarFree A) :
    ∃! i : Fin 4, Interd IsEM0 [] A (rep4 i) :=
  varfree_exactly_four_of (X := IsEM0) rfl isEM_of_isEM0 A hA

/-- Nondegeneracy, spelled out: the four classes are distinct, so "four" is
exact and not an upper bound. -/
theorem four_distinct :
    ¬ Interd IsEM [] falsePLL boxBot ∧ ¬ Interd IsEM [] falsePLL NoFall.nobot ∧
      ¬ Interd IsEM [] falsePLL truePLL ∧ ¬ Interd IsEM [] boxBot NoFall.nobot ∧
      ¬ Interd IsEM [] boxBot truePLL ∧ ¬ Interd IsEM [] NoFall.nobot truePLL := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  exacts [absurd (rep4_inj (i := 0) (j := 1) h) (by decide),
    absurd (rep4_inj (i := 0) (j := 2) h) (by decide),
    absurd (rep4_inj (i := 0) (j := 3) h) (by decide),
    absurd (rep4_inj (i := 1) (j := 2) h) (by decide),
    absurd (rep4_inj (i := 1) (j := 3) h) (by decide),
    absurd (rep4_inj (i := 2) (j := 3) h) (by decide)]

/-- The `◯`-action on the four classes, at the one place it is not immediate:

    ◯¬◯⊥  ⊣⊢  ⊤

(the others are `◯⊥ = ◯⊥`, `◯◯⊥ ⊣⊢ ◯⊥`, `◯⊤ ⊣⊢ ⊤`).  So `◯` acts on the
four-element algebra by `⊥ ↦ ◯⊥`, `◯⊥ ↦ ◯⊥`, `¬◯⊥ ↦ ⊤`, `⊤ ↦ ⊤` — the closed
nucleus `x ↦ x ∨ ◯⊥`, as `nucleus_eq_closed` predicts.  This also shows the
classification is not vacuous: `◯¬◯⊥` is class `3`, not class `2`. -/
theorem box_nobot_em (hX : X (emF boxBot)) :
    Interd X [] (somehow NoFall.nobot) truePLL := by
  refine ⟨DerivX.top, ?_⟩
  refine DerivX.orE (φ := boxBot) (ψ := notPLL boxBot) (DerivX.ax hX) ?_ ?_
  · exact box_mono (bot_imp _)
  · exact DerivX.unit (DerivX.hyp (by simp [NoFall.nobot]))

/-! ## 6. The algebraic boundary: Booleanness forces the closed nucleus -/

/-- **On a Boolean algebra every nucleus is closed**: `j x = x ⊔ j ⊥`.
This is the algebraic content of `box_closed`, and the step that fails in a
general Heyting algebra: it uses `x ⊔ xᶜ = ⊤`. -/
theorem nucleus_eq_closed {B : Type*} [BooleanAlgebra B] (j : Nucleus B)
    (x : B) : j x = x ⊔ j ⊥ := by
  refine le_antisymm ?_ (sup_le j.le_apply (OrderHomClass.mono j bot_le))
  have hbot : j x ⊓ xᶜ ≤ j ⊥ := by
    calc j x ⊓ xᶜ ≤ j x ⊓ j xᶜ := inf_le_inf_left _ j.le_apply
      _ = j (x ⊓ xᶜ) := j.map_inf.symm
      _ = j ⊥ := by rw [inf_compl_eq_bot]
  calc j x = j x ⊓ (x ⊔ xᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = (j x ⊓ x) ⊔ (j x ⊓ xᶜ) := inf_sup_left ..
    _ ≤ x ⊔ j ⊥ := sup_le_sup inf_le_right hbot

/-- A nucleus on the three-element **Heyting** chain that is not closed:
`j 0 = 0`, `j 1 = j 2 = 2`. -/
def midNucleus : Nucleus (Fin 3) where
  toFun x := if x = 0 then 0 else 2
  map_inf' x y := by revert x y; decide
  le_apply' x := by revert x; decide
  idempotent' x := by revert x; decide

@[simp] theorem midNucleus_apply (x : Fin 3) :
    midNucleus x = if x = 0 then 0 else 2 := rfl

/-- **Booleanness is what does the work.**  On the three-element chain
`midNucleus` has `j ⊥ = ⊥` but `j 1 = 2 ≠ 1 = 1 ⊔ j ⊥`, so the closed form
is not a consequence of the nucleus laws over a Heyting algebra. -/
theorem nucleus_not_closed_Fin3 :
    ∃ (j : Nucleus (Fin 3)) (x : Fin 3), j x ≠ x ⊔ j ⊥ := by
  refine ⟨midNucleus, 1, ?_⟩
  simp only [midNucleus_apply]
  decide

end ClassicalLax
end PLLND

/-! ### Axiom audit — clean-classical, measured and pinned on creation
(2026-08-07); every entry transcribed from actual `#print axioms` output. -/

/-- info: 'PLLND.ClassicalLax.box_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.ClassicalLax.box_closed

/-- info: 'PLLND.ClassicalLax.dist_of_em' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.ClassicalLax.dist_of_em

/--
info: 'PLLND.ClassicalLax.box_trivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.box_trivial

/--
info: 'PLLND.ClassicalLax.K_does_not_force_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.K_does_not_force_dist

/--
info: 'PLLND.ClassicalLax.four_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.four_complete

/-- info: 'PLLND.ClassicalLax.rep4_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.ClassicalLax.rep4_inj

/--
info: 'PLLND.ClassicalLax.varfree_exactly_four_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.varfree_exactly_four_of

/--
info: 'PLLND.ClassicalLax.varfree_exactly_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.varfree_exactly_four

/--
info: 'PLLND.ClassicalLax.varfree_exactly_four_em0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.varfree_exactly_four_em0

/--
info: 'PLLND.ClassicalLax.four_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.four_distinct

/--
info: 'PLLND.ClassicalLax.nucleus_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.nucleus_eq_closed

/--
info: 'PLLND.ClassicalLax.nucleus_not_closed_Fin3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.nucleus_not_closed_Fin3

/--
info: 'PLLND.ClassicalLax.box_nobot_em' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ClassicalLax.box_nobot_em
