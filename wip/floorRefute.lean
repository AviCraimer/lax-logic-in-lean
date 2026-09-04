import wip.starve
import wip.descent2

/-!
# The descent to budget `0` is FALSE, and the budget tier has no base case

`wip/ascRefute.lean` refuted the descent at target budget `1`.  This file
refutes it at target budget `0`, and does so **without a countermodel
search**: the target table is *literally* `⊥` for structural reasons
(`itpA_starve_floor`), so the only semantic fact needed is that the two
hypotheses are jointly consistent.

## Why this matters for the rebuild

`wip/cascadeBox.lean`'s `oth_descent` is a lexicographic induction whose
middle tier is a strong induction on the budget `c`, carrying `1 ≤ c`.
Its three "floor" interfaces (`GammaPairFloorA`, `GammaPairFloorBox`,
`JumpPairFloor`) exist precisely because at `c = 1` that tier has no
recursive call available: the gated environment clauses of the *target*
table at budget `c` put their first component at budget `c − 1`, so the
branch needs the descent at `(c → c−1)`, which at `c = 1` is the descent
to budget `0`.

This file shows that call is not merely unavailable — it is **false**.
Together with `wip/ascRefute.lean` §2 (the descent at target budget `1`
is false) this says the budget tier cannot be given a base case by
raising the floor: a floor at `n` needs the descent at `n − 1`, and both
`n − 1 = 0` and `n − 1 = 1` are refuted.  The recursion has to terminate
on some *other* measure (context growth, or the pigeonhole over jump
goals that `wip/absorb_base.lean`'s `cascade_main` uses), not on the
budget.

## The configuration

    S  = {◯(⊥⊃⊥), ⊥⊃⊥, ⊥}        (piece-closed)
    Γ  = []                        (so every context piece is in S, vacuously)
    g  = ◯(⊥⊃⊥) ∈ S               (a `◯`-shaped goal)

At `Γ = []` the environment table is empty at every budget, so at budget
`0` a `◯`-goal's table is `orAll [] = ⊥` (`itpA_starve_floor`: the goal
clause and the truncation disjunct are both budget-gated).  At budget `1`
the goal clause reappears, and its body is a *theorem* — `⊥∧⊤ ⊃ ⊥` under a
vacuous guard — so the source table is satisfiable.  The descent would
therefore derive `⊥` from consistent hypotheses.

## What it says about the budget law

`Descends` (`wip/descent2.lean`) is the descent with the budget
requirement left as a parameter `need`.  This configuration is an
instance at target budget `0`, so it forces `1 ≤ need S [] g` — at a
space whose *gated-piece count is zero*.  That kills the gate-count
candidate `needGate` a second time, and this time from data rather than
from a proof obligation: `needGate` asks for `0` here, and `0` is not
enough.  The earlier elimination (`needGate_not_floor1`) used the empty
space, which one might dismiss as degenerate; this space is piece-closed
with a genuine `◯`-goal.
-/

open PLLFormula

namespace PLLND
namespace FloorRefute

/-! ## 1. Consistency, from the trivial model -/

/-- The one-world model.  `Rᵢ` and `Rₘ` are reflexive by construction
(`FinCM.riB`, `FinCM.rmB`), so this is the single reflexive point with no
atom forced and no fallible world. -/
def Mz : FinCM := ⟨1, [], [], [], []⟩

/-! ## 2. The refuting configuration -/

/-- The piece-closed space: `◯⊤`, `⊤`, `⊥` (with `⊤ = ⊥⊃⊥`). -/
def Sz : Finset PLLFormula :=
  {(falsePLL.ifThen falsePLL).somehow, falsePLL.ifThen falsePLL, falsePLL}

/-- The `◯`-shaped goal. -/
def gz : PLLFormula := (falsePLL.ifThen falsePLL).somehow

/-- The ambient existential table at budget `1`, empty context. -/
def ambz : PLLFormula := itpE "p" Sz 3 1 []

/-- The source universal table at budget `1`. -/
def srcz : PLLFormula := itpA "p" Sz 3 1 [] gz

theorem gz_mem : gz ∈ Sz := by decide

/-- **The target table is literally `⊥`.**  No semantics involved: at the
empty context the environment table is empty, and at budget `0` both the
`◯`-goal clause and the truncation disjunct are gated off. -/
theorem tgtz_bot : itpA "p" Sz 3 0 [] gz = falsePLL :=
  itpA_starve_floor "p" Sz 2 [] (falsePLL.ifThen falsePLL) rfl

/-- The two hypotheses are jointly consistent: they hold at world `0` of
`Mz`, where `⊥` of course does not. -/
theorem check_fails_z : FinCM.checkB Mz 0 [srcz, ambz] falsePLL = true := by
  decide

/-- **The descent to budget `0` fails on this instance.** -/
theorem not_derivable_z : ¬ G4c [srcz, ambz] (itpA "p" Sz 3 0 [] gz) := by
  rw [tgtz_bot]
  exact fun h => FinCM.not_provable_of_check check_fails_z (G4c.equiv_nd.mp h)

/-! ## 3. The refuted statement -/

/-- The descent at target budget `0`, with every side condition the
`oth_descent` interfaces carry (goal in the space, context inside the
space, head fuel below target fuel).  Refuting the *strongest* form makes
the refutation apply to every weakening of it. -/
def FloorDescent (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fuel fh : Nat) (Γ : List PLLFormula) (g : PLLFormula)
    (Δ : List PLLFormula),
    g ∈ S → (∀ X ∈ Γ, X ∈ S) → fh ≤ fuel →
    G4c Δ (itpE p S fuel 1 Γ) →
    G4c Δ (itpA p S fh 1 Γ g) →
    G4c Δ (itpA p S fuel 0 Γ g)

/-- **The descent to budget `0` is false.** -/
theorem not_floorDescent : ¬ FloorDescent "p" Sz := by
  intro h
  exact not_derivable_z
    (h 3 3 [] gz [srcz, ambz] gz_mem (by simp) (Nat.le_refl _)
      (G4c.identity_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (G4c.identity_mem (List.mem_cons_self ..)))

/-! ## 4. What this forces on the budget law -/

open Descent2

/-- **A second machine-checked lower bound on the unknown budget law**, at
a configuration with no budget-gated pieces at all: every room requirement
that supports the descent asks for at least `1` here. -/
theorem gate_free_lower_bound (need : Need)
    (h : Descends "p" need) : 1 ≤ need Sz [] gz := by
  by_contra hlt
  have h0 : need Sz [] gz ≤ 0 := by omega
  exact not_derivable_z
    (h Sz 3 3 0 [] gz [srcz, ambz] h0 (Nat.le_refl _)
      (G4c.identity_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (G4c.identity_mem (List.mem_cons_self ..)))

/-- The gate count of this space is zero: it contains no formula of either
budget-gated shape (`(A⊃B)⊃D` or `◯A⊃B`). -/
theorem gateCount_Sz : gateCount Sz = 0 := by decide

/-- **The gate-count budget law is refuted by data.**  It asks for nothing
at a space with no gated pieces, and `gate_free_lower_bound` shows nothing
is not enough. -/
theorem needGate_excluded : ¬ Descends "p" needGate := by
  intro h
  have h1 := gate_free_lower_bound needGate h
  rw [show needGate Sz [] gz = gateCount Sz from rfl, gateCount_Sz] at h1
  omega

/-- **The goal-shape law survives this screen too.**  The goal here is
boxed, so `needShape` asks for `1` — exactly the certified lower bound at
this configuration, with nothing to spare. -/
theorem needShape_survives_z : ¬ (needShape Sz [] gz ≤ 0) := by decide

/-- The ledger law survives it as well, with room to spare
(`|jumpGoals Sz| = 0`, `defect Sz [] = 3`, so it asks for `1 + 3·2 = 7`). -/
theorem needKcap_survives_z : ¬ (needKcap Sz [] gz ≤ 0) := by decide

end FloorRefute
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.FloorRefute.not_floorDescent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.FloorRefute.not_floorDescent

/-- info: 'PLLND.FloorRefute.gate_free_lower_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.FloorRefute.gate_free_lower_bound

/-- info: 'PLLND.FloorRefute.needGate_excluded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.FloorRefute.needGate_excluded
