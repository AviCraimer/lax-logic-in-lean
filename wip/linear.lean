import wip.schemeext

/-!
# PLL + linearity: the closed fragment has EXACTLY SIX elements

The Gödel–Dummett rung of the ladder.  The axiom is the **scheme**

    linF A B  :=  (A ⊃ B) ∨ (B ⊃ A)

with variables, so — unlike `¬◯⊥` in `PLLNoFall.lean`, which is closed and may
be carried as one persistent hypothesis — the extension is by the *set* of all
instances (`SchemeExt.DerivX IsLin`), which is the substitution-closed
extension.  Hypothesis form for a single instance would be strictly weaker.

## What is proved here

1. **The system** `DerivLin = DerivX IsLin`, with `SchemeExt`'s admissible
   structure.

2. **The frame condition and soundness.**  `Connected C`:

       ∀ w v u,  w Rᵢ v → w Rᵢ u  →  v Rᵢ u ∨ u Rᵢ v

   (the `Rᵢ`-successors of any world are linearly ordered: rooted models are
   chains).  `force_lin_of_connected` / `sound_lin`.

3. **Linearity forces distribution** (`dist_of_lin`): from the single instance
   `linF A B`,

       ◯(A ∨ B) ⊃ (◯A ∨ ◯B)

   is derivable in **plain PLL** — in the `A ⊃ B` branch `A ∨ B ⊢ B`, so
   `◯(A∨B) ⊢ ◯B`, and symmetrically.  So PLL + linearity already contains
   PCLL, and Matthew's semantic intuition about chains is financed by
   linearity.  It is **not** financed by `K`: `SchemeExt.ndK` derives
   `◯(A ⊃ B) ⊃ (◯A ⊃ ◯B)` in plain PLL, which has a countermodel to
   distribution (`PLLND.not_provable_somehow_or_dist`), so `K` does not force
   distribution (`K_does_not_force_dist` in `wip/classical.lean`).

4. **The collapse** (`varfree_exactly_six`).  Every variable-free formula is
   interderivable with exactly one of

       ⊥ ,  ¬◯⊥ ,  ◯⊥ ,  ◯⊥ ∨ ¬◯⊥ ,  ¬¬◯⊥ ,  ⊤

   and no two of these are interderivable: the closed fragment has **exactly
   six** elements.  Compare: infallible (`PLLNoFall`) collapses it to **2**,
   classical (`wip/classical.lean`) to **4**, linear to **6**, and PLL itself
   leaves it infinite.

   Machine-checked is the count and the representatives
   (`varfree_exactly_six`, `rep6_inj`).  The six are exactly the elements of
   the free 1-generated Gödel algebra on the generator `◯⊥` — `2 × 3`, a
   Boolean factor and a three-element chain factor, with `◯` acting by
   `⊥ ↦ ◯⊥`, `◯⊥ ↦ ◯⊥`, `¬◯⊥ ↦ ◯⊥ ∨ ¬◯⊥` (`box_nobot`), `¬¬◯⊥ ↦ ¬¬◯⊥`,
   `⊤ ↦ ⊤` — but that identification is a reading of the data, not part of the
   formalised statement.

   Sharpness, as in the classical case, is a sandwich: the classification needs
   only the single **closed** axiom `¬◯⊥ ∨ ¬¬◯⊥` (weak excluded middle at
   `◯⊥`, `IsWem0`), which linearity derives (`wem_of_lin`); and the six are
   already separated in the full linear system.

5. **Completeness** (`derivLin_iff_valid`): `DerivLin` is sound and complete
   for the mutually confluent **connected** constraint models, by relativising
   the canonical model of `PLLConfluentComplete.lean` to the prime theories
   containing every instance of linearity.  The relativisation is as cheap as
   the template's: `obInv` preserves the extra property (each instance is
   `◯`-ed into `T` by the unit), `prime_extension` needs no re-run, and
   connectedness of the canonical frame is the classical Gödel–Dummett
   argument on prime theories:

       φ ∈ U \ V,  ψ ∈ V \ U,  (φ⊃ψ)∨(ψ⊃φ) ∈ T ⊆ U ∩ V,  T prime  ⟹  ⊥ .

   The scheme's infinitely many instances are handled by taking the axiom
   **set** into the worlds — set-level derivability `SDeriv` is already the
   right shape, so no re-run of Zorn is needed.

## The three branches of the classification

`⊥ ⊢ ...` splits on `¬◯⊥ ∨ ¬¬◯⊥`:

* under `¬◯⊥`  the fragment is `{⊥, ⊤}`      (`SchemeExt.dich_nobot`);
* under `¬¬◯⊥` it is `{⊥, ◯⊥, ⊤}`            (`SchemeExt.dich_nnbot`);

and the six global classes are the six pairs.
-/

open PLLFormula

namespace PLLND
namespace LinearLax

open SchemeExt
open NoFall (VarFree)

/-! ## 1. The system -/

/-- One instance of the Gödel–Dummett linearity scheme. -/
def linF (A B : PLLFormula) : PLLFormula := (A.ifThen B).or (B.ifThen A)

/-- The linearity **scheme**: all instances. -/
def IsLin (θ : PLLFormula) : Prop := ∃ A B, θ = linF A B

/-- The **single closed axiom** `¬◯⊥ ∨ ¬¬◯⊥` — weak excluded middle at `◯⊥`.
Being closed, hypothesis form and axiom form agree for it. -/
def IsWem0 (θ : PLLFormula) : Prop := θ = (NoFall.nobot).or nnbot

/-- PLL + linearity. -/
abbrev DerivLin : List PLLFormula → PLLFormula → Prop := DerivX IsLin

/-- PLL + `¬◯⊥ ∨ ¬¬◯⊥`. -/
abbrev DerivWem0 : List PLLFormula → PLLFormula → Prop := DerivX IsWem0

variable {X : PLLFormula → Prop} {Δ : List PLLFormula} {A B : PLLFormula}

/-! ## 2. Weak excluded middle, and distribution, from linearity -/

/-- **Linearity gives weak excluded middle** (the Gödel–Dummett → De Morgan
inclusion, `LC ⊆ KC`):

    ¬A ∨ ¬¬A

from the single instance `linF A (¬A)`. -/
theorem wem_of_lin (hX : X (linF A (notPLL A))) :
    DerivX X Δ ((notPLL A).or (notPLL (notPLL A))) := by
  refine DerivX.orE (φ := A.ifThen (notPLL A)) (ψ := (notPLL A).ifThen A)
    (DerivX.ax hX) ?_ ?_
  · -- `A ⊃ ¬A` gives `¬A`
    refine DerivX.orI₁ (φ := notPLL A) (ψ := notPLL (notPLL A))
      (DerivX.deduction ?_)
    exact DerivX.mp (φ := A) (ψ := falsePLL)
      (DerivX.mp (φ := A) (ψ := notPLL A) (DerivX.hyp (by simp))
        (DerivX.hyp (by simp))) (DerivX.hyp (by simp))
  · -- `¬A ⊃ A` gives `¬¬A`
    refine DerivX.orI₂ (φ := notPLL A) (ψ := notPLL (notPLL A))
      (DerivX.deduction ?_)
    exact DerivX.mp (φ := A) (ψ := falsePLL) (DerivX.hyp (by simp))
      (DerivX.mp (φ := notPLL A) (ψ := A) (DerivX.hyp (by simp))
        (DerivX.hyp (by simp)))

/-- The instance of weak excluded middle at `◯⊥`, from linearity. -/
theorem wem0_of_lin (hX : X (linF boxBot (notPLL boxBot))) :
    DerivX X Δ ((NoFall.nobot).or nnbot) :=
  wem_of_lin hX

/-- **Linearity forces distribution.**  From the single instance
`(A ⊃ B) ∨ (B ⊃ A)`,

    ◯(A ∨ B) ⊃ (◯A ∨ ◯B)

is derivable.  In the `A ⊃ B` branch `A ∨ B ⊢ B`, so `◯`-monotonicity gives
`◯B`; symmetrically in the other.  Hence PLL + linearity ⊇ PCLL, and the
chain-based validity of distribution is financed by **linearity**, not by
`K` (which is a theorem of plain PLL and forces nothing). -/
theorem dist_of_lin (hX : X (linF A B)) :
    DerivX X Δ ((somehow (A.or B)).ifThen ((somehow A).or (somehow B))) := by
  refine DerivX.deduction ?_
  refine DerivX.orE (φ := A.ifThen B) (ψ := B.ifThen A)
    (DerivX.ax hX) ?_ ?_
  · -- `A ⊃ B` in context: `◯(A∨B) ⊢ ◯B`
    refine DerivX.orI₂ (φ := somehow A) (ψ := somehow B) ?_
    have step : DerivX X (A.or B :: ((A.ifThen B) :: Δ)) B :=
      DerivX.orE (φ := A) (ψ := B) (DerivX.hyp (by simp))
        (DerivX.mp (φ := A) (ψ := B) (DerivX.hyp (by simp))
          (DerivX.hyp (by simp)))
        (DerivX.hyp (by simp))
    exact (box_mono step).rename (by intro θ hθ; simp at hθ ⊢; tauto)
  · -- `B ⊃ A` in context: `◯(A∨B) ⊢ ◯A`
    refine DerivX.orI₁ (φ := somehow A) (ψ := somehow B) ?_
    have step : DerivX X (A.or B :: ((B.ifThen A) :: Δ)) A :=
      DerivX.orE (φ := A) (ψ := B) (DerivX.hyp (by simp))
        (DerivX.hyp (by simp))
        (DerivX.mp (φ := B) (ψ := A) (DerivX.hyp (by simp))
          (DerivX.hyp (by simp)))
    exact (box_mono step).rename (by intro θ hθ; simp at hθ ⊢; tauto)

/-- The weak-excluded-middle system is contained in the linear one. -/
theorem derivWem0_le_derivLin {Γ : List PLLFormula} {φ : PLLFormula}
    (h : DerivWem0 Γ φ) : DerivLin Γ φ := by
  refine DerivX.of_derivable_axioms (fun θ hθ => ?_) h
  subst hθ
  exact wem0_of_lin ⟨boxBot, notPLL boxBot, rfl⟩

/-! ## 3. The frame condition, and soundness -/

/-- **The frame condition for linearity**: the `Rᵢ`-successors of any world
are linearly ordered — rooted models are chains. -/
def Connected (C : ConstraintModel) : Prop :=
  ∀ {w v u : C.W}, C.Ri w v → C.Ri w u → C.Ri v u ∨ C.Ri u v

/-- **Soundness half of the frame correspondence**: on a connected model every
instance of linearity is forced everywhere. -/
theorem force_lin_of_connected {C : ConstraintModel} (hC : Connected C)
    (w : C.W) (A B : PLLFormula) : C.force w (linF A B) := by
  by_cases h : ∀ v, C.Ri w v → C.force v A → C.force v B
  · exact Or.inl h
  · refine Or.inr ?_
    push Not at h
    obtain ⟨v, hwv, hvA, hvB⟩ := h
    intro u hwu huB
    rcases hC hwv hwu with hvu | huv
    · exact C.force_hered hvu hvA
    · exact absurd (C.force_hered huv huB) hvB

/-! ## 4. The six classes -/

/-- The six representatives, in the order given by the class index:

    ⊥ ,  ¬◯⊥ ,  ◯⊥ ,  ◯⊥ ∨ ¬◯⊥ ,  ¬¬◯⊥ ,  ⊤ . -/
def rep6 (i : Fin 6) : PLLFormula :=
  if i.val = 0 then falsePLL
  else if i.val = 1 then NoFall.nobot
  else if i.val = 2 then boxBot
  else if i.val = 3 then boxBot.or NoFall.nobot
  else if i.val = 4 then nnbot
  else truePLL

@[simp] theorem rep6_zero : rep6 0 = falsePLL := rfl
@[simp] theorem rep6_one : rep6 1 = NoFall.nobot := rfl
@[simp] theorem rep6_two : rep6 2 = boxBot := rfl
@[simp] theorem rep6_three : rep6 3 = boxBot.or NoFall.nobot := rfl
@[simp] theorem rep6_four : rep6 4 = nnbot := rfl
@[simp] theorem rep6_five : rep6 5 = truePLL := rfl

theorem varFree_rep6 (i : Fin 6) : VarFree (rep6 i) := by
  fin_cases i
  exacts [trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, ⟨trivial, trivial⟩⟩,
    varFree_nnbot, NoFall.varFree_truePLL]

/-- The class index: first coordinate the value under `¬◯⊥` (two classes),
second the value under `¬¬◯⊥` (three classes). -/
def idx6 (x : Fin 2) (y : Fin 3) : Fin 6 :=
  ⟨x.val + 2 * y.val, by have := x.isLt; have := y.isLt; omega⟩

@[simp] theorem idx6_00 : idx6 0 0 = 0 := rfl
@[simp] theorem idx6_01 : idx6 0 1 = 2 := rfl
@[simp] theorem idx6_02 : idx6 0 2 = 4 := rfl
@[simp] theorem idx6_10 : idx6 1 0 = 1 := rfl
@[simp] theorem idx6_11 : idx6 1 1 = 3 := rfl
@[simp] theorem idx6_12 : idx6 1 2 = 5 := rfl

/-! ### The four bridges between branch classes and global classes -/

theorem b1 (x : Fin 2) (y : Fin 3) :
    DerivX X [rep2 x, NoFall.nobot] (rep6 (idx6 x y)) := by
  fin_cases x <;> fin_cases y
  · exact bot_imp _
  · exact bot_imp _
  · exact bot_imp _
  · exact DerivX.hyp (by simp)
  · show DerivX X _ (boxBot.or NoFall.nobot)
    exact DerivX.orI₂ (φ := boxBot) (ψ := NoFall.nobot) (DerivX.hyp (by simp))
  · exact DerivX.top

theorem b1' (x : Fin 2) (y : Fin 3) :
    DerivX X [rep6 (idx6 x y), NoFall.nobot] (rep2 x) := by
  fin_cases x <;> fin_cases y
  · exact DerivX.hyp (by simp)
  · exact DerivX.mp (φ := boxBot) (ψ := falsePLL)
      (DerivX.hyp (by simp [NoFall.nobot])) (DerivX.hyp (by simp))
  · exact DerivX.mp (φ := NoFall.nobot) (ψ := falsePLL)
      (DerivX.hyp (by simp [NoFall.nobot])) (DerivX.hyp (by simp))
  · exact DerivX.top
  · exact DerivX.top
  · exact DerivX.top

theorem b2 (x : Fin 2) (y : Fin 3) :
    DerivX X [rep3 y, nnbot] (rep6 (idx6 x y)) := by
  fin_cases x <;> fin_cases y
  · exact bot_imp _
  · exact DerivX.hyp (by simp)
  · exact DerivX.hyp (by simp)
  · exact bot_imp _
  · show DerivX X _ (boxBot.or NoFall.nobot)
    exact DerivX.orI₁ (φ := boxBot) (ψ := NoFall.nobot) (DerivX.hyp (by simp))
  · exact DerivX.top

theorem b2' (x : Fin 2) (y : Fin 3) :
    DerivX X [rep6 (idx6 x y), nnbot] (rep3 y) := by
  fin_cases x <;> fin_cases y
  · exact DerivX.hyp (by simp)
  · exact DerivX.hyp (by simp)
  · exact DerivX.top
  · exact DerivX.mp (φ := NoFall.nobot) (ψ := falsePLL)
      (DerivX.hyp (by simp [NoFall.nobot])) (DerivX.hyp (by simp))
  · refine DerivX.orE (φ := boxBot) (ψ := NoFall.nobot)
      (DerivX.hyp (by simp)) (DerivX.hyp (by simp)) ?_
    exact DerivX.exfalso (DerivX.mp (φ := NoFall.nobot) (ψ := falsePLL)
      (DerivX.hyp (by simp [NoFall.nobot])) (DerivX.hyp (by simp))) _
  · exact DerivX.top

/-- **The upper bound**: from the single closed axiom `¬◯⊥ ∨ ¬¬◯⊥`, every
variable-free formula falls into one of the six classes. -/
theorem six_complete
    (hsplit : ∀ Θ : List PLLFormula, DerivX X Θ ((NoFall.nobot).or nnbot)) :
    ∀ A : PLLFormula, VarFree A → ∃ i, Interd X [] A (rep6 i) := by
  intro A hA
  obtain ⟨x, hx⟩ := dich_nobot (X := X) (Δ := [NoFall.nobot]) (by simp) A hA
  obtain ⟨y, hy⟩ := dich_nnbot (X := X) (Δ := [nnbot]) (by simp) A hA
  exact ⟨idx6 x y, combine (P := NoFall.nobot) (Q := nnbot)
    (rep := fun a b => rep6 (idx6 a b)) hsplit
    (b1 x y) (b1' x y) (b2 x y) (b2' x y) hx hy⟩

/-- The `◯`-action on the six classes, at the one place it is not immediate:

    ◯¬◯⊥  ⊣⊢  ◯⊥ ∨ ¬◯⊥ .

(The others are `◯⊥ = ◯⊥`, `◯◯⊥ ⊣⊢ ◯⊥`, `◯¬¬◯⊥ ⊣⊢ ¬¬◯⊥`, `◯⊤ ⊣⊢ ⊤`.) -/
theorem box_nobot
    (hsplit : ∀ Θ : List PLLFormula, DerivX X Θ ((NoFall.nobot).or nnbot)) :
    Interd X [] (somehow NoFall.nobot) (boxBot.or NoFall.nobot) := by
  constructor
  · refine DerivX.orE (φ := NoFall.nobot) (ψ := nnbot) (hsplit _) ?_ ?_
    · exact DerivX.orI₂ (φ := boxBot) (ψ := NoFall.nobot) (DerivX.hyp (by simp))
    · refine DerivX.orI₁ (φ := boxBot) (ψ := NoFall.nobot) ?_
      have step : DerivX X (NoFall.nobot :: (nnbot :: [somehow NoFall.nobot]))
          falsePLL :=
        DerivX.mp (φ := NoFall.nobot) (ψ := falsePLL)
          (DerivX.hyp (by simp [NoFall.nobot])) (DerivX.hyp (by simp))
      exact (box_mono step).rename (by intro θ hθ; simp at hθ ⊢; tauto)
  · refine DerivX.orE (φ := boxBot) (ψ := NoFall.nobot) (DerivX.hyp (by simp))
      ?_ ?_
    · exact box_mono (bot_imp _)
    · exact DerivX.unit (DerivX.hyp (by simp))

/-! ## 5. The lower bound: a connected four-world model -/

/-- Worlds of `modelLin`: the isolated infallible point `n`, and the chain
`r ⊑ v ⊑ f` with `f` fallible and `v Rₘ f`. -/
inductive WLin : Type
  | n | r | v | f
  deriving DecidableEq, Fintype

/-- `Rᵢ`: `n` isolated; `r ⊑ v ⊑ f`.  Each world's up-set is a chain, so the
frame is connected, though it is not itself linear. -/
def riLin (x y : WLin) : Prop :=
  x = y ∨ (x = .r ∧ (y = .v ∨ y = .f)) ∨ (x = .v ∧ y = .f)

instance : DecidableRel riLin := fun x y =>
  inferInstanceAs (Decidable
    (x = y ∨ (x = .r ∧ (y = .v ∨ y = .f)) ∨ (x = .v ∧ y = .f)))

/-- `Rₘ`: reflexive, plus `v Rₘ f` — so `◯⊥` holds at `v` and fails at `n`
and at `r`. -/
def rmLin (x y : WLin) : Prop := x = y ∨ (x = .v ∧ y = .f)

instance : DecidableRel rmLin := fun x y =>
  inferInstanceAs (Decidable (x = y ∨ (x = .v ∧ y = .f)))

@[reducible] def modelLin : ConstraintModel where
  W := WLin
  Ri := riLin
  Rm := rmLin
  F := {x | x = .f}
  V _ := {x | x = .f}
  refl_i _ := .inl rfl
  trans_i {x y z} h h' :=
    (by decide : ∀ x y z : WLin, riLin x y → riLin y z → riLin x z) x y z h h'
  refl_m _ := .inl rfl
  trans_m {x y z} h h' :=
    (by decide : ∀ x y z : WLin, rmLin x y → rmLin y z → rmLin x z) x y z h h'
  sub_mi {x y} h := (by decide : ∀ x y : WLin, rmLin x y → riLin x y) x y h
  hered_F {x y} h hw :=
    (by decide : ∀ x y : WLin, riLin x y → x = .f → y = .f) x y h hw
  hered_V {_ x y} h hw :=
    (by decide : ∀ x y : WLin, riLin x y → x = .f → y = .f) x y h hw
  full_F hw := hw

instance (φ : PLLFormula) (w : modelLin.W) : Decidable (modelLin.force w φ) :=
  modelLin.decForce φ w

theorem modelLin_connected : Connected modelLin := by
  intro w a b h h'
  exact (by decide : ∀ w a b : WLin, riLin w a → riLin w b →
    riLin a b ∨ riLin b a) w a b h h'

/-- Soundness of the full linear system over `modelLin`. -/
theorem sound_lin {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivLin Γ φ)
    (w : modelLin.W) (hΓ : ∀ ψ ∈ Γ, modelLin.force w ψ) :
    modelLin.force w φ := by
  refine sound (fun θ hθ w => ?_) h w hΓ
  obtain ⟨A, B, rfl⟩ := hθ
  exact force_lin_of_connected modelLin_connected w A B

theorem transfer {P Q : PLLFormula} (h : DerivLin [P] Q) (w : modelLin.W)
    (hP : modelLin.force w P) : modelLin.force w Q :=
  sound_lin h w (by intro ψ hψ; simp at hψ; subst hψ; exact hP)

/-- **The lower bound**: the six representatives are pairwise
non-interderivable, already in the full linear system.  The three test worlds
`n`, `r`, `v` give the six value-vectors

    ⊥ (F,F,F)   ¬◯⊥ (T,F,F)   ◯⊥ (F,F,T)
    ◯⊥∨¬◯⊥ (T,F,T)   ¬¬◯⊥ (F,T,T)   ⊤ (T,T,T) . -/
theorem rep6_inj {i j : Fin 6} (h : Interd IsLin [] (rep6 i) (rep6 j)) :
    i = j := by
  have hn : modelLin.force .n (rep6 i) ↔ modelLin.force .n (rep6 j) :=
    ⟨fun hf => transfer h.1 .n hf, fun hf => transfer h.2 .n hf⟩
  have hr : modelLin.force .r (rep6 i) ↔ modelLin.force .r (rep6 j) :=
    ⟨fun hf => transfer h.1 .r hf, fun hf => transfer h.2 .r hf⟩
  have hv : modelLin.force .v (rep6 i) ↔ modelLin.force .v (rep6 j) :=
    ⟨fun hf => transfer h.1 .v hf, fun hf => transfer h.2 .v hf⟩
  revert hn hr hv
  fin_cases i <;> fin_cases j <;> decide

/-! ## 6. The theorem -/

/-- **THE LINEAR COLLAPSE.**  For any axiom set `X` between the single closed
axiom `¬◯⊥ ∨ ¬¬◯⊥` and the full linearity scheme, every variable-free formula
is interderivable with **exactly one** of

    ⊥ ,  ¬◯⊥ ,  ◯⊥ ,  ◯⊥ ∨ ¬◯⊥ ,  ¬¬◯⊥ ,  ⊤ .

So the closed fragment of PLL + linearity has **exactly six** elements: the
free 1-generated Gödel algebra on the generator `◯⊥`. -/
theorem varfree_exactly_six_of
    (hsplit : ∀ Θ : List PLLFormula, DerivX X Θ ((NoFall.nobot).or nnbot))
    (hle : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, DerivX X Γ φ →
      DerivLin Γ φ)
    (A : PLLFormula) (hA : VarFree A) :
    ∃! i : Fin 6, Interd X [] A (rep6 i) := by
  obtain ⟨i, hi⟩ := six_complete hsplit A hA
  refine ⟨i, hi, fun j hj => ?_⟩
  have h : Interd X [] (rep6 j) (rep6 i) := hj.symm.trans hi
  exact rep6_inj ⟨hle h.1, hle h.2⟩

/-- The collapse for PLL + the full linearity scheme. -/
theorem varfree_exactly_six (A : PLLFormula) (hA : VarFree A) :
    ∃! i : Fin 6, Interd IsLin [] A (rep6 i) :=
  varfree_exactly_six_of (X := IsLin)
    (fun _ => wem0_of_lin ⟨boxBot, notPLL boxBot, rfl⟩) (fun h => h) A hA

/-- The collapse already for PLL + the single closed axiom `¬◯⊥ ∨ ¬¬◯⊥` — so
six is the count for every system between that and full linearity. -/
theorem varfree_exactly_six_wem0 (A : PLLFormula) (hA : VarFree A) :
    ∃! i : Fin 6, Interd IsWem0 [] A (rep6 i) :=
  varfree_exactly_six_of (X := IsWem0) (fun _ => DerivX.ax rfl)
    derivWem0_le_derivLin A hA

/-- The six classes are pairwise distinct. -/
theorem six_pairwise {i j : Fin 6} (h : i ≠ j) :
    ¬ Interd IsLin [] (rep6 i) (rep6 j) := fun hij => h (rep6_inj hij)

/-! ## 7. Completeness: the relativised canonical model

The template's relativisation (`PLLNoFall.lean` §5), with the axiom **set** in
place of the single axiom: worlds are the closed prime theories containing
every instance of linearity.  Set-level derivability `SDeriv` already takes a
set of hypotheses, so the scheme's infinitely many instances cost nothing —
this is the point at which a scheme with variables would otherwise break the
single-hypothesis shortcut. -/

open ConfluentU

/-- Worlds: closed prime theories containing every instance of linearity. -/
def LWld : Type :=
  {T : Set PLLFormula // SClosed T ∧ SPrime T ∧ ∀ θ, IsLin θ → θ ∈ T}

theorem lin_mem_obInv {T : Set PLLFormula} (hc : SClosed T)
    (hl : ∀ θ, IsLin θ → θ ∈ T) : ∀ θ, IsLin θ → θ ∈ obInv T :=
  fun θ hθ => hc _ ((SDeriv.of_mem (hl θ hθ)).unit)

/-- The relativised canonical model: `canonU` restricted to the prime theories
containing linearity. -/
@[reducible] def canonL : ConstraintModel where
  W := LWld
  Ri T U := T.1 ⊆ U.1
  Rm T U := T.1 ⊆ U.1 ∧ ∀ ψ ∈ U.1, somehow ψ ∈ T.1
  F := {T | falsePLL ∈ T.1}
  V a := {T | prop a ∈ T.1}
  refl_i _ := le_refl _
  trans_i h h' := le_trans h h'
  refl_m {T} := ⟨le_refl _, fun _ h => subset_obInv T.2.1 h⟩
  trans_m := by
    intro T U W h h'
    refine ⟨le_trans h.1 h'.1, fun ψ hψ => ?_⟩
    have hmm : somehow (somehow ψ) ∈ T.1 := h.2 _ (h'.2 ψ hψ)
    have hM : LaxND ([] : List PLLFormula)
        ((somehow (somehow ψ)).ifThen (somehow ψ)) :=
      .impIntro (.laxElim (φ := somehow ψ) (.iden (by simp)) (.iden (by simp)))
    exact T.2.1 _ (SDeriv.mp ⟨[], by simp, .of_nd hM⟩ (SDeriv.of_mem hmm))
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := h hw
  full_F {a T} hT :=
    T.2.1 _ ⟨[falsePLL], by simpa using hT,
      .of_nd (.falsoElim _ (.iden (by simp)))⟩

/-- The `obInv` world over a relativised world. -/
def obInvLW (T : LWld) : LWld :=
  ⟨obInv T.1, obInv_closed T.2.1, obInv_prime T.2.1 T.2.2.1,
    lin_mem_obInv T.2.1 T.2.2.2⟩

theorem rm_obInvLW (T : LWld) : canonL.Rm T (obInvLW T) :=
  ⟨subset_obInv T.2.1, fun _ h => h⟩

theorem canonL_confluent : MutuallyConfluent canonL := by
  intro T U V hm hi
  exact ⟨obInvLW V, fun ψ hψ => hi (hm.2 ψ hψ), rm_obInvLW V⟩

/-- **The canonical frame is connected** — the Gödel–Dummett argument on prime
theories.  If `φ ∈ U \ V` and `ψ ∈ V \ U` with `T ⊆ U`, `T ⊆ V`, then the
instance `(φ ⊃ ψ) ∨ (ψ ⊃ φ)` lies in `T`, which is prime: the first disjunct
puts `ψ` in `U`, the second puts `φ` in `V`.  Both contradict. -/
theorem canonL_connected : Connected canonL := by
  intro T U V hTU hTV
  by_contra hcon
  obtain ⟨hUV, hVU⟩ := not_or.mp hcon
  obtain ⟨φ, hφU, hφV⟩ := Set.not_subset.mp hUV
  obtain ⟨ψ, hψV, hψU⟩ := Set.not_subset.mp hVU
  have hlin : linF φ ψ ∈ T.1 := T.2.2.2 _ ⟨φ, ψ, rfl⟩
  rcases T.2.2.1 _ _ hlin with h | h
  · exact hψU (U.2.1 _ (SDeriv.mp (SDeriv.of_mem (hTU h)) (SDeriv.of_mem hφU)))
  · exact hφV (V.2.1 _ (SDeriv.mp (SDeriv.of_mem (hTV h)) (SDeriv.of_mem hψV)))

/-- Relativised Lindenbaum: no new Zorn argument, the extension produced by
`prime_extension` already contains everything `S` does. -/
theorem prime_extension_L {S : Set PLLFormula} {B : PLLFormula}
    (hS : ∀ θ, IsLin θ → θ ∈ S) (h : ¬ SDeriv S B) :
    ∃ T : LWld, S ⊆ T.1 ∧ B ∉ T.1 := by
  obtain ⟨T, hST, hBT⟩ := prime_extension h
  exact ⟨⟨T.1, T.2.1, T.2.2, fun θ hθ => hST (hS θ hθ)⟩, hST, hBT⟩

/-- The truth lemma for the relativised model. -/
theorem truthL : ∀ (φ : PLLFormula) (T : LWld), canonL.force T φ ↔ φ ∈ T.1 := by
  intro φ
  induction φ with
  | prop a => exact fun T => Iff.rfl
  | falsePLL => exact fun T => Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro T
      constructor
      · rintro ⟨h₁, h₂⟩
        exact T.2.1 _ (SDeriv.andI (SDeriv.of_mem ((ihφ T).mp h₁))
          (SDeriv.of_mem ((ihψ T).mp h₂)))
      · intro h
        exact ⟨(ihφ T).mpr (T.2.1 _ (SDeriv.andE₁ (SDeriv.of_mem h))),
          (ihψ T).mpr (T.2.1 _ (SDeriv.andE₂ (SDeriv.of_mem h)))⟩
  | or φ ψ ihφ ihψ =>
      intro T
      constructor
      · rintro (h | h)
        · exact T.2.1 _ (SDeriv.orI₁ (SDeriv.of_mem ((ihφ T).mp h)))
        · exact T.2.1 _ (SDeriv.orI₂ (SDeriv.of_mem ((ihψ T).mp h)))
      · intro h
        rcases T.2.2.1 _ _ h with h | h
        exacts [Or.inl ((ihφ T).mpr h), Or.inr ((ihψ T).mpr h)]
  | ifThen φ ψ ihφ ihψ =>
      intro T
      constructor
      · intro hf
        by_contra hmem
        have hnd : ¬ SDeriv (insert φ T.1) ψ := by
          intro hd
          exact hmem (T.2.1 _ hd.deduction)
        obtain ⟨U, hTU, hψU⟩ := prime_extension_L
          (fun θ hθ => Set.mem_insert_of_mem _ (T.2.2.2 θ hθ)) hnd
        have hφU : φ ∈ U.1 := hTU (Set.mem_insert φ T.1)
        have hfU := hf U (le_trans (Set.subset_insert φ T.1) hTU)
          ((ihφ U).mpr hφU)
        exact hψU ((ihψ U).mp hfU)
      · intro h U hTU hφ
        exact (ihψ U).mpr (U.2.1 _ ((SDeriv.of_mem (hTU h)).mp
          (SDeriv.of_mem ((ihφ U).mp hφ))))
  | somehow φ ih =>
      intro T
      rw [force_somehow_iff_of_confluent canonL_confluent]
      constructor
      · rintro ⟨U, hRm, hU⟩
        exact hRm.2 φ ((ih U).mp hU)
      · intro h
        exact ⟨obInvLW T, rm_obInvLW T, (ih (obInvLW T)).mpr h⟩

/-! ### The bridge: `DerivLin` is PCLL + linearity as well as PLL + linearity -/

/-- **PLL + linearity = PCLL + linearity, at the level of set derivability.**
Left to right is weakening; right to left replaces each distribution
hypothesis by `dist_of_lin`, using the generalised cut `substCtx`.  This is
the precise form of "linearity forces distribution". -/
theorem derivLin_iff_sderiv {Γ : List PLLFormula} {φ : PLLFormula} :
    DerivLin Γ φ ↔ SDeriv ({ψ | ψ ∈ Γ} ∪ {θ | IsLin θ}) φ := by
  constructor
  · rintro ⟨L, hL, ⟨p⟩⟩
    refine ⟨L ++ Γ, ?_, DerivU.of_nd p⟩
    intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    exacts [Or.inr (hL ψ hψ), Or.inl hψ]
  · rintro ⟨Γ', hΓ', D, hD, ⟨p⟩⟩
    refine DerivX.substCtx (Γ := D ++ Γ') (Δ := Γ) ?_ (DerivX.of_nd p)
    intro θ hθ
    rcases List.mem_append.mp hθ with hθ | hθ
    · obtain ⟨A, B, rfl⟩ := hD θ hθ
      exact dist_of_lin (X := IsLin) ⟨A, B, rfl⟩
    · rcases hΓ' θ hθ with hθ' | hθ'
      exacts [DerivX.hyp hθ', DerivX.ax hθ']

/-- Soundness of `DerivLin` over connected models (confluence is not needed
for this half). -/
theorem sound_connected {C : ConstraintModel} (hC : Connected C)
    {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivLin Γ φ) (w : C.W)
    (hΓ : ∀ ψ ∈ Γ, C.force w ψ) : C.force w φ := by
  refine sound (fun θ hθ w => ?_) h w hΓ
  obtain ⟨A, B, rfl⟩ := hθ
  exact force_lin_of_connected hC w A B

/-- **PLL + linearity is sound and complete for the mutually confluent
connected constraint models.**  Soundness needs only connectedness; the
canonical model supplies both properties. -/
theorem derivLin_iff_valid {Γ : List PLLFormula} {φ : PLLFormula} :
    DerivLin Γ φ ↔
      ∀ (C : ConstraintModel), MutuallyConfluent C → Connected C →
        ∀ w : C.W, (∀ ψ ∈ Γ, C.force w ψ) → C.force w φ := by
  constructor
  · intro h C _ hC w hΓ
    exact sound_connected hC h w hΓ
  · intro hval
    by_contra hnd
    have hS : ¬ SDeriv ({ψ | ψ ∈ Γ} ∪ {θ | IsLin θ}) φ := fun h =>
      hnd (derivLin_iff_sderiv.mpr h)
    obtain ⟨T, hΓT, hφT⟩ := prime_extension_L (fun θ hθ => Or.inr hθ) hS
    have hfT := hval canonL canonL_confluent canonL_connected T
      (fun ψ hψ => (truthL ψ T).mpr (hΓT (Or.inl hψ)))
    exact hφT ((truthL φ T).mp hfT)

end LinearLax
end PLLND

/-! ### Axiom audit — clean-classical (Zorn enters through `prime_extension`),
measured and pinned on creation (2026-08-07); every entry transcribed from
actual `#print axioms` output. -/

/-- info: 'PLLND.LinearLax.wem_of_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LinearLax.wem_of_lin

/-- info: 'PLLND.LinearLax.dist_of_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LinearLax.dist_of_lin

/--
info: 'PLLND.LinearLax.force_lin_of_connected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.LinearLax.force_lin_of_connected

/-- info: 'PLLND.LinearLax.six_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LinearLax.six_complete

/-- info: 'PLLND.LinearLax.box_nobot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LinearLax.box_nobot

/-- info: 'PLLND.LinearLax.rep6_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LinearLax.rep6_inj

/--
info: 'PLLND.LinearLax.varfree_exactly_six' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.LinearLax.varfree_exactly_six

/--
info: 'PLLND.LinearLax.varfree_exactly_six_wem0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.LinearLax.varfree_exactly_six_wem0

/-- info: 'PLLND.LinearLax.six_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LinearLax.six_pairwise

/--
info: 'PLLND.LinearLax.canonL_connected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.LinearLax.canonL_connected

/-- info: 'PLLND.LinearLax.truthL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LinearLax.truthL

/--
info: 'PLLND.LinearLax.derivLin_iff_sderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.LinearLax.derivLin_iff_sderiv

/--
info: 'PLLND.LinearLax.derivLin_iff_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.LinearLax.derivLin_iff_valid
