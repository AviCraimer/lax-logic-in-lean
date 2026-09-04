import round7core
import round4probe3
import LaxLogic.PLLCountermodelEmit

/-!
# ROUND 7 — the production band's lower boundary, kernel-pinned

`Round7.CompProd` demands `1 ≤ c`.  This file pins that the demand is
EXACT: at `c = 0` the production is refuted by a one-world countermodel at
a five-formula space (the round-7 replay's pass-Z control fired at 344
corpus cells; this is corpus cell `d1-atom/1021`, the smallest).

The space is the piece-closure of `◯a ⊃ b` with the boxed goal re-closed
in; the context drops `a` (defect 1, the γ-gate live); the goal is `◯b`.
At target budget `0` every budget-gated row of the value table
`A@(ft, 0)(Γ, ◯b)` is gone; what survives is the single γ-context row
`◯(E@0(a::Γ) ⊃ A@0(a::Γ, ◯b)) ∨ ⊥`, and at the grown context the inner
value table IS empty, so the row asserts a boxed negation of `a ∧ b`.
Both premises hold in the one-world model where both atoms are true, the
component does not.

Combined with `Round7.compProd_of_boxDesc`, this is also a boundary for
`Round4.BoxDesc` consumption: iterating the room-free descent reaches every
budget down to `1` and no further — the `1 ≤ b` in `BoxDesc` and the
`1 ≤ c` in `CompProd` are the same wall, seen from the two sides.
-/

open PLLFormula

namespace PLLND
namespace Round7Pin

/-- Corpus cell `d1-atom/1021`: pieces of `◯a ⊃ b`, `◯b` re-closed in. -/
def S0 : Finset PLLFormula :=
  { (prop "a").somehow.ifThen (prop "b"), (prop "a").somehow,
    prop "a", prop "b", (prop "b").somehow }

/-- The context: everything but `a` — the γ-gate `◯a ⊃ b` stays live via
its boxed antecedent, `defect = 1`. -/
def G0 : List PLLFormula :=
  [ (prop "a").somehow.ifThen (prop "b"), (prop "a").somehow,
    prop "b", (prop "b").somehow ]

/-- The cell's premises (`fs = 3`, `ft = 4`, `b = 3`). -/
def src0 : PLLFormula := itpA "p" S0 3 4 G0 (prop "b").somehow
def amb0 : PLLFormula := itpE "p" S0 4 4 G0

/-- The component at `c = 0`. -/
def comp0 : PLLFormula :=
  ((itpE "p" S0 4 0 G0).ifThen (itpA "p" S0 4 0 G0 (prop "b").somehow)).somehow

/-- The one-world model: both atoms true, no modal structure. -/
def M0 : FinCM := ⟨1, [], [], [], [(0, "b"), (0, "a")]⟩

/-- **The `c = 0` production fails.**  Kernel-checked countermodel: the
premises hold and the component does not, at world 0. -/
theorem comp0_refuted : FinCM.checkB M0 0 [src0, amb0] comp0 = true := by
  decide +kernel

/-- The underivability reading. -/
theorem comp0_not_derivable : ¬ G4c [src0, amb0] comp0 := fun h =>
  FinCM.not_provable_of_check comp0_refuted (G4c.equiv_nd.mp h)

/-! ## The goal-row landing of the direct walk, refuted at EVERY ambient
elevation

Inside any direct (value-concluding) proof of `CompProd`, the source's goal
row `◯(E@(b−1)(Γ) ⊃ A@(b)(Γ, D))` opens against the lowered ambient and
hands the UNBOXED value `A@(b)(Γ, D)`; the target's goal row needs
`A@(c)(Γ, D)` with `c < b` — the unboxed same-context descent.  The July
refutation (`AscRefute.not_roomFreeDescent`, `Mk`, `gk = (◯r ⊃ s) ⊃ t`
over `Skb` at `Gk`) killed that descent at MATCHED budgets
(ambient = source).  The walk's inner position is better off by exactly one
budget of ambient (the top ambient at `b+1` against a fired value at `b`),
and by two at the `b+2` call sites — so the matched-budget refutation did
not close the question.  These pins do: `Mk` refutes the landing with the
ambient elevated one and two budgets above the source.  The elevation is
NOT load-bearing; the landing is dead at compound unboxed bodies.

Consequence (with `Round6`'s §63(c) band): fork (1) delimits to the γ-head
rows.  The γ-head landing factors through `CompProd` room-free; the
goal-row landing at compound bodies cannot be closed pointwise at any
elevation and must go through the room-priced spine — whose financing dies
below depth 2 (`no_depth2_entry_at_s3`, `no_self_financed_nest`).  The
prove-side residue is therefore unchanged in LOCATION (the depth ≥ 2
compound-body nest) but now pinned in MECHANISM on both rows. -/

/-- The ambient one budget above the source (`srcU` sits at budget 2). -/
def ambE3 : PLLFormula := itpE "p" Round4Probe3.Skb 4 3 AscRefute.Gk

/-- …and two above. -/
def ambE4 : PLLFormula := itpE "p" Round4Probe3.Skb 4 4 AscRefute.Gk

/-- **Elevation by one does not rescue the goal-row landing.** -/
theorem goalrow_landing_refuted_elev1 :
    FinCM.checkB AscRefute.Mk 0 [Round4Probe3.srcU, ambE3]
      Round4Probe3.tgtU = true := by decide +kernel

/-- **Nor does elevation by two.** -/
theorem goalrow_landing_refuted_elev2 :
    FinCM.checkB AscRefute.Mk 0 [Round4Probe3.srcU, ambE4]
      Round4Probe3.tgtU = true := by decide +kernel

/-- The underivability reading at elevation one. -/
theorem goalrow_landing_not_derivable :
    ¬ G4c [Round4Probe3.srcU, ambE3] Round4Probe3.tgtU := fun h =>
  FinCM.not_provable_of_check goalrow_landing_refuted_elev1
    (G4c.equiv_nd.mp h)

end Round7Pin
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round7Pin.comp0_refuted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round7Pin.comp0_refuted

/--
info: 'PLLND.Round7Pin.comp0_not_derivable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round7Pin.comp0_not_derivable

/--
info: 'PLLND.Round7Pin.goalrow_landing_refuted_elev1' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round7Pin.goalrow_landing_refuted_elev1

/--
info: 'PLLND.Round7Pin.goalrow_landing_refuted_elev2' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round7Pin.goalrow_landing_refuted_elev2

/--
info: 'PLLND.Round7Pin.goalrow_landing_not_derivable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round7Pin.goalrow_landing_not_derivable
