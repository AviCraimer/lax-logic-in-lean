import frontier

/-!
# The frontier sampler's structural finding, machine-checked

Campaign 1 measured that of 692 screened cells only **12** were
simultaneously admissible for `cascade_boxgoal_pos` (the room `≤ b`) and
budget-ACTIVE, and that all twelve sat in the one stratum with no γ-clause.
That is not an accident of the generator; it is arithmetic, and this file
pins it.

A **γ-clause** is a member `◯X ⊃ B ∈ S`.  `jumpGoals` gives such a member the
pair `{X, ◯X}`, and those are distinct, so a single γ-clause already forces
`|jumpGoals S| ≥ 2`.  With `1 ≤ defect S Γ` the room
`defect S Γ · (|jumpGoals S| + 2) ≤ b` therefore forces `4 ≤ b`, hence a fuel
of at least `5` in the sampler's grid — and at `ft = 5` the interpolation
tables of a γ-carrying space weigh 10⁵–10⁶ nodes, which is past what
`FinCM.checkB` can sweep.

Consequence for the campaign, and it is a positive one: the room-carrying
statement's budget-active regime is reachable at feasible sizes **only** at
`J = 1`, i.e. at spaces with a jump clause and no γ-clause — which is exactly
where PROGRESS §62's three residual `JB2` cells live.  Campaign 2's four
strata were aimed there on the strength of this lemma.
-/

open PLLFormula PLLND

namespace PLLND
namespace FrontierPin

/-! ## §1  A formula is never its own box -/

theorem sz_pos (A : PLLFormula) : 0 < TowerKit.sz A := by
  cases A <;> simp [TowerKit.sz]

theorem ne_somehow (A : PLLFormula) : A ≠ A.somehow := by
  intro h
  have h1 : TowerKit.sz A = TowerKit.sz A.somehow := by rw [← h]
  simp only [TowerKit.sz] at h1
  omega

/-! ## §2  A γ-clause forces two jump goals -/

theorem mem_jumpGoals_of_gamma {S : Finset PLLFormula} {X B : PLLFormula}
    (h : (X.somehow).ifThen B ∈ S) :
    X ∈ jumpGoals S ∧ X.somehow ∈ jumpGoals S := by
  constructor <;>
  · rw [jumpGoals, Finset.mem_biUnion]
    exact ⟨_, h, by simp⟩

/-- **The γ-clause bound.**  One `◯X ⊃ B ∈ S` already gives
`2 ≤ |jumpGoals S|`. -/
theorem two_le_jumpGoals_of_gamma {S : Finset PLLFormula} {X B : PLLFormula}
    (h : (X.somehow).ifThen B ∈ S) : 2 ≤ (jumpGoals S).card := by
  obtain ⟨h1, h2⟩ := mem_jumpGoals_of_gamma h
  have hsub : ({X, X.somehow} : Finset PLLFormula) ⊆ jumpGoals S := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact h1
    · exact h2
  have hcard : ({X, X.somehow} : Finset PLLFormula).card = 2 :=
    Finset.card_pair (ne_somehow X)
  calc 2 = ({X, X.somehow} : Finset PLLFormula).card := hcard.symm
    _ ≤ (jumpGoals S).card := Finset.card_le_card hsub

/-! ## §3  Hence the room-carrying band starts at budget 4 -/

/-- **The reachability bound.**  At any space containing a γ-clause and any
context with positive defect, `cascade_boxgoal_pos`'s room hypothesis forces
`4 ≤ b`.  In the sampler's grid `ft = b + 1`, so no room-carrying cell of a
γ-carrying space is screenable below fuel `5`. -/
theorem four_le_budget_of_gamma {S : Finset PLLFormula} {Γ : List PLLFormula}
    {X B : PLLFormula} {b : Nat}
    (hγ : (X.somehow).ifThen B ∈ S) (hd : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ b) : 4 ≤ b := by
  have hJ : 2 ≤ (jumpGoals S).card := two_le_jumpGoals_of_gamma hγ
  have h1 : 1 * ((jumpGoals S).card + 2) ≤ defect S Γ * ((jumpGoals S).card + 2) :=
    Nat.mul_le_mul_right _ hd
  omega

/-- The `J = 1` escape: with a jump clause and NO γ-clause the room is `3`,
one budget lower, which is what makes campaign 2's band decide-feasible.  The
statement is the arithmetic half; that `J = 1` is achievable is witnessed by
`Round5Refute.S1` and by campaign 2's `jb1-*` strata. -/
theorem three_le_budget_of_j1 {S : Finset PLLFormula} {Γ : List PLLFormula}
    {b : Nat} (hJ : (jumpGoals S).card = 1) (hd : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ b) : 3 ≤ b := by
  have h1 : 1 * ((jumpGoals S).card + 2) ≤ defect S Γ * ((jumpGoals S).card + 2) :=
    Nat.mul_le_mul_right _ hd
  omega

/-! ## §4  The witnesses of §3, on the sampler's own instances

`Round5Refute.S1` (the `J = 1` jump family, room `3`) and `Round5Refute.S2`
(the `JB2` nested-box family) are the hand-built ancestors of campaign 2's
`jb1-imp` and `jb1-nbox` strata.  Their jump counts are kernel facts. -/

theorem s1_J : (jumpGoals Round5Refute.i11.S).card = 1 := by decide +kernel

theorem s2_J : (jumpGoals Round5Refute.i21.S).card = 1 := by decide +kernel

/-- A γ-carrying space of the sampler's own `d2-imp` shape: `S3` of PROGRESS
§63, the piece-closure of `◯◯(a⊃b) ⊃ c`.  Its `J` is `2`, so by §3 its
room-carrying cells start at `b = 4`. -/
def S3l : List PLLFormula :=
  [ (((prop "a").ifThen (prop "b")).somehow.somehow).ifThen (prop "c")
  , ((prop "a").ifThen (prop "b")).somehow.somehow
  , ((prop "a").ifThen (prop "b")).somehow
  , (prop "a").ifThen (prop "b"), prop "a", prop "b", prop "c" ]

theorem s3_pieceClosed : Round5Refute.pieceClosedB S3l = true := by decide +kernel

theorem s3_J : (jumpGoals S3l.toFinset).card = 2 := by decide +kernel

end FrontierPin
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.FrontierPin.two_le_jumpGoals_of_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FrontierPin.two_le_jumpGoals_of_gamma

/--
info: 'PLLND.FrontierPin.four_le_budget_of_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FrontierPin.four_le_budget_of_gamma

/--
info: 'PLLND.FrontierPin.three_le_budget_of_j1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FrontierPin.three_le_budget_of_j1

/--
info: 'PLLND.FrontierPin.s3_J' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FrontierPin.s3_J
