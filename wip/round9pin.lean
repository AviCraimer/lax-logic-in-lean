import round8pin
import round8core
import round5refute

/-!
# ROUND 9 — the room-free route is REFUTED, kernel-checked

PROGRESS §67(h) narrowed the whole campaign to one sequent: the goal-row
absorption at a compound unboxed body `D = C₁ ⊃ C₂` whose antecedent is
FRESH (`C₁ ∉ Γ`), whose inner obligation is the **fresh-row descent**

    E@(f,b)(C₁::Γ) ⊃ A@(f,b)(C₁::Γ, C₂) ,  E@(ft,b+1)(Γ)
      ⟹  E@(f,c)(C₁::Γ) ⊃ A@(f,c)(C₁::Γ, C₂)                (C₁ ∉ Γ, c < b)

This file refutes it, and then refutes the three room-free statements the
route was assembled from.

## Where the corpus was not looking

Every recorded cell of the 1152-record corpus drops one or two members of
the space (`genDrop cfg.defectTarget`), so its context is nearly all of `S`.
The one high-defect instance in the whole inventory is July's `Gk` (a
singleton, defect 8) — and it is the one place where the unboxed room-free
descent is refuted (`AscRefute.not_roomFreeDescent`).  Round 9 went to the
END of that axis: **`Γ = []`**.  Every hypothesis of `Round4.BoxDesc` holds
there (`∀ X ∈ Γ, X ∈ S` is vacuous), the ambient degenerates to `⊤`, and
every `itpAenv` table is empty, so the tables collapse to

    A@(f+1, β)([], ◯D)      = ◯(⊤ ⊃ A@(f,β)([],D)) ∨ ◯(⊤ ⊃ ◯(⊤ ⊃ A@(f,β)([],D)))
    A@(f+1, β)([], C₁ ⊃ C₂) = E@(f,β)(C₁::[]) ⊃ A@(f,β)(C₁::[], C₂)

— the fresh row, undecorated, with NO ambient to help.

## The space and the two models

`vS` is the piece-closure of `◯((◯x ⊃ y) ⊃ z)`: seven formulas, `defect 7`,
`J = 3`, room `35`.  The body `D = (◯x ⊃ y) ⊃ z` is July's `gk` shape and
its antecedent `C₁ = ◯x ⊃ y` is a `⊃◯`-clause, so the grown context
`C₁ :: []` carries budget-GATED conjuncts — the configuration
`AscRefute.not_ambGuardAscent` refutes the guard ascent at.

* `M2` — the two-world chain `0 ⊑ 1`, `0 ⊳ 1`, infallible, `x`, `y`, `z`
  forced exactly at world `1` (July's `Mk` with the atoms renamed).  It
  refutes the fresh row itself, and the unboxed same-context descent.
* `P3c` — the three-world chain `0 ⊑ 1 ⊑ 2` whose ONLY modal step is
  `1 ⊳ 2`, infallible, `x`, `y`, `z` forced exactly at the top.  `M2` alone
  does not refute the `◯`-goal statements (its modal successor is its top
  world, where `z` holds, so the target's boxed disjuncts are satisfied
  there — `Round4Probe3.box_is_load_bearing`'s rescue); `P3c` is `M2` with
  the modal step pushed one world UP, so the failure sits at every world the
  `◯` can see.

## What falls, and what does not

    ¬ Round4.BoxDesc  "p" vS      (fs = ft = 5, b = 1, Γ = [])
    ¬ Round7.CompProd "p" vS      (fs = ft = 5, b = 2, c = 1, Γ = [])
    ¬ Round8.GoalRowAbsorb "p" vS (f = 4, b = 2, c = 1, Γ = [])

The refuted cell has `defect vS [] · (J + 2) = 35` and `b = 1`, so it is
STRICTLY SUB-ROOM.  `Round4.BoxDescR` (the room-carrying obligation) and
`wip/absorb_base.lean`'s `cascade_boxgoal_pos` are therefore untouched:
nothing here says anything about them, and the tower's one `sorry` stands
exactly where it stood.  What is dead is the ROOM-FREE route — PROGRESS
§61(c) alternative 1, §63(e) fork (1), and rounds 6, 7 and 8's whole
assembly.
-/

open PLLFormula

namespace PLLND
namespace Round9Pin

open PLLND.Round4 PLLND.Round7 PLLND.Round8

/-! ## 1. The space -/

def vx : PLLFormula := prop "x"
def vy : PLLFormula := prop "y"
def vz : PLLFormula := prop "z"

/-- The FRESH antecedent: a `⊃◯`-clause (`AscRefute.Xr`'s shape). -/
def vC1 : PLLFormula := (vx.somehow).ifThen vy

/-- The goal body: `D = (◯x ⊃ y) ⊃ z`, July's `gk` shape. -/
def vD : PLLFormula := vC1.ifThen vz

def vSl : List PLLFormula := [vD.somehow, vD, vC1, vx.somehow, vx, vy, vz]
def vS : Finset PLLFormula := vSl.toFinset

theorem vS_piece_closed : Round5Refute.pieceClosedB vSl = true := by
  decide +kernel

theorem vD_box_mem : vD.somehow ∈ vS := by decide +kernel

/-- The context is EMPTY, so the coverage hypothesis is vacuous. -/
theorem vΓ_cover : ∀ X ∈ ([] : List PLLFormula), X ∈ vS := by simp

/-- **The refuted cell is strictly sub-room.**  `Round4.BoxDescR` and
`cascade_boxgoal_pos` carry `Room S Γ b`; here it fails by a factor of 35. -/
theorem vS_room : defect vS [] * ((jumpGoals vS).card + 2) = 35 := by
  decide +kernel

theorem not_room_at_one : ¬ SealLedger.Room vS [] 1 := by
  simp only [SealLedger.Room]
  decide +kernel

theorem not_room_at_two : ¬ SealLedger.Room vS [] 2 := by
  simp only [SealLedger.Room]
  decide +kernel

/-! ## 2. The two models -/

/-- July's `Mk`, atoms renamed: two worlds `0 ⊑ 1`, `0 ⊳ 1`, infallible,
`x`, `y`, `z` exactly at world `1`. -/
def M2 : FinCM := ⟨2, [(0,1)], [(0,1)], [], [(1,"x"),(1,"y"),(1,"z")]⟩

/-- `M2` with the modal step pushed one world up: three worlds
`0 ⊑ 1 ⊑ 2`, the only modal step `1 ⊳ 2`, infallible, `x`, `y`, `z` exactly
at the top. -/
def P3c : FinCM := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], [(2,"x"),(2,"y"),(2,"z")]⟩

/-! ## 3. THE RESIDUE ITSELF — the fresh-row descent, REFUTED

`§67(h)`'s sequent at `Γ = []`, inner fuel `3`, `b = 2`, `c = 1`.  The
ambient premise is `E@(ft,3)([]) = ⊤` and is therefore omitted: the
refutation holds with the ambient in hand, unconditionally. -/

def vRow (f b : Nat) : PLLFormula :=
  (itpE "p" vS f b [vC1]).ifThen (itpA "p" vS f b [vC1] vz)

theorem freshRow_refuted : FinCM.checkB M2 0 [vRow 3 2] (vRow 3 1) = true := by
  decide +kernel

/-- **The fresh-row descent is underivable.**  The last open shape of the
goal-row case (PROGRESS §67(h)) is closed — negatively. -/
theorem freshRow_not_derivable : ¬ G4c [vRow 3 2] (vRow 3 1) := fun h =>
  FinCM.not_provable_of_check freshRow_refuted (G4c.equiv_nd.mp h)

/-- The same at the three-world model, so both pins rest on one model if
wanted. -/
theorem freshRow_refuted_P3c :
    FinCM.checkB P3c 0 [vRow 3 2] (vRow 3 1) = true := by decide +kernel

/-- **The §67(h) residue as a statement.**  The fresh-row descent, universally
quantified exactly as `Round8.GoalRowAbsorb`'s inner obligation arises: the
body's antecedent is a member of the space that is ABSENT from the context, so
both the source and the target goal disjunct carry guard and value at the
SAME budget (the `C₁ ∈ Γ` branch of `itpAgoal`, which lowers the guard, is not
taken).  The ambient is carried, at the elevation the walk has it. -/
def FreshRowDescent (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (f b c : Nat) (Γ Δ : List PLLFormula) (C₁ C₂ : PLLFormula),
    C₁ ∈ S → C₂ ∈ S → (∀ X ∈ Γ, X ∈ S) → C₁ ∉ Γ → 1 ≤ c → c ≤ b →
    G4c Δ (itpE p S (f + 1) (b + 1) Γ) →
    G4c Δ ((itpE p S f b (C₁ :: Γ)).ifThen (itpA p S f b (C₁ :: Γ) C₂)) →
    G4c Δ ((itpE p S f c (C₁ :: Γ)).ifThen (itpA p S f c (C₁ :: Γ) C₂))

theorem vC1_mem : vC1 ∈ vS := by decide +kernel
theorem vz_mem : vz ∈ vS := by decide +kernel

/-- **The residue is FALSE.**  PROGRESS §67(h)'s open shape, closed
negatively at `f = 3`, `b = 2`, `c = 1`, `Γ = []`. -/
theorem not_freshRowDescent : ¬ FreshRowDescent "p" vS := fun h =>
  freshRow_not_derivable
    (h 3 2 1 [] [vRow 3 2] vC1 vz vC1_mem vz_mem vΓ_cover (by simp)
      (Nat.le_refl _) (by omega)
      (by rw [itpE_succ]; exact G4c.andAll_intro (by intro ψ hψ; simp [itpEcls] at hψ))
      (G4c.identity_mem (.head _)))

/-! ### …and the unboxed same-context descent at the EMPTY context

`AscRefute.not_roomFreeDescent` refuted this at July's `Gk`, where the
ambient is non-trivial and could be blamed.  At `Γ = []` the ambient is `⊤`,
so the failure is intrinsic to the value table. -/

theorem unboxed_refuted :
    FinCM.checkB M2 0
      [itpA "p" vS 4 2 [] vD, itpE "p" vS 4 2 []] (itpA "p" vS 4 1 [] vD)
      = true := by decide +kernel

theorem unboxed_not_derivable :
    ¬ G4c [itpA "p" vS 4 2 [] vD, itpE "p" vS 4 2 []]
        (itpA "p" vS 4 1 [] vD) := fun h =>
  FinCM.not_provable_of_check unboxed_refuted (G4c.equiv_nd.mp h)

/-! ## 4. `Round4.BoxDesc` — REFUTED -/

def bdSrc : PLLFormula := itpA "p" vS 5 2 [] vD.somehow
def bdAmb : PLLFormula := itpE "p" vS 5 2 []
def bdTgt : PLLFormula := itpA "p" vS 5 1 [] vD.somehow

theorem boxDesc_refuted : FinCM.checkB P3c 0 [bdSrc, bdAmb] bdTgt = true := by
  decide +kernel

theorem boxDesc_not_derivable : ¬ G4c [bdSrc, bdAmb] bdTgt := fun h =>
  FinCM.not_provable_of_check boxDesc_refuted (G4c.equiv_nd.mp h)

/-- **The room-free `◯`-goal descent is FALSE.**  PROGRESS §61(c)
alternative 1 and §63(e) fork (1) both consume `Round4.BoxDesc`; both are
dead. -/
theorem not_boxDesc : ¬ BoxDesc "p" vS := fun h =>
  boxDesc_not_derivable
    (h 5 5 1 [] [bdSrc, bdAmb] vD vD_box_mem vΓ_cover (Nat.le_refl _)
      (Nat.le_refl _)
      (G4c.identity_mem (.tail _ (.head _)))
      (G4c.identity_mem (.head _)))

/-! ## 5. `Round7.CompProd` — REFUTED -/

def cpComp (b : Nat) : PLLFormula :=
  ((itpE "p" vS 5 b []).ifThen (itpA "p" vS 5 b [] vD.somehow)).somehow
def cpAmb : PLLFormula := itpE "p" vS 5 3 []

theorem compProd_refuted :
    FinCM.checkB P3c 0 [cpComp 2, cpAmb] (cpComp 1) = true := by decide +kernel

theorem compProd_not_derivable : ¬ G4c [cpComp 2, cpAmb] (cpComp 1) := fun h =>
  FinCM.not_provable_of_check compProd_refuted (G4c.equiv_nd.mp h)

/-- **The boxed-component production is FALSE** — round 7's fork (1) in its
own terms. -/
theorem not_compProd : ¬ CompProd "p" vS := fun h =>
  compProd_not_derivable
    (h 5 5 2 1 [] [cpComp 2, cpAmb] vD vD_box_mem vΓ_cover (Nat.le_refl _)
      (Nat.le_refl _) (by omega)
      (G4c.identity_mem (.tail _ (.head _)))
      (G4c.identity_mem (.head _)))

/-- Cross-check: round 7's own upgrade theorem re-derives `¬ BoxDesc` from
`¬ CompProd`, independently of §4. -/
theorem not_boxDesc_via_compProd : ¬ BoxDesc "p" vS :=
  not_boxDesc_of_not_compProd "p" vS not_compProd

/-! ## 6. `Round8.GoalRowAbsorb` — REFUTED -/

def graRow : PLLFormula :=
  ((itpE "p" vS 4 1 []).ifThen (itpA "p" vS 4 2 [] vD)).somehow
def graAmb : PLLFormula := itpE "p" vS 5 3 []
def graTgt : PLLFormula := itpA "p" vS 5 1 [] vD.somehow

theorem goalRowAbsorb_refuted :
    FinCM.checkB P3c 0 [graRow, graAmb] graTgt = true := by decide +kernel

theorem goalRowAbsorb_not_derivable : ¬ G4c [graRow, graAmb] graTgt := fun h =>
  FinCM.not_provable_of_check goalRowAbsorb_refuted (G4c.equiv_nd.mp h)

/-- **The goal-row absorption is FALSE** — round 8's statement, refuted at a
compound unboxed body with a FRESH antecedent, exactly the shape §67(h) left
open. -/
theorem not_goalRowAbsorb : ¬ GoalRowAbsorb "p" vS := fun h =>
  goalRowAbsorb_not_derivable
    (h 4 2 1 [] [graRow, graAmb] vD vD_box_mem vΓ_cover (Nat.le_refl _)
      (by omega) (by omega)
      (G4c.identity_mem (.tail _ (.head _)))
      (G4c.identity_mem (.head _)))

/-- Cross-check: round 8's own upgrade theorem re-derives `¬ BoxDesc`. -/
theorem not_boxDesc_via_goalRowAbsorb : ¬ BoxDesc "p" vS :=
  not_boxDesc_of_not_goalRowAbsorb "p" vS not_goalRowAbsorb

end Round9Pin
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round9Pin.freshRow_not_derivable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round9Pin.freshRow_not_derivable

/--
info: 'PLLND.Round9Pin.not_freshRowDescent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round9Pin.not_freshRowDescent

/--
info: 'PLLND.Round9Pin.not_boxDesc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round9Pin.not_boxDesc

/--
info: 'PLLND.Round9Pin.not_compProd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round9Pin.not_compProd

/--
info: 'PLLND.Round9Pin.not_goalRowAbsorb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round9Pin.not_goalRowAbsorb

/--
info: 'PLLND.Round9Pin.not_boxDesc_via_compProd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round9Pin.not_boxDesc_via_compProd
