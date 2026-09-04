import LaxLogic.PLLDecide
import LaxLogic.PLLG4Gap

/-!
# Multiplicity experiments: Howe's original sequent, and the tower question

Two machine-checked data points about *how much* contraction the
consuming calculus `G4` (Iemhoff's G4iLL) is missing, run through the
verified decider of `PLLDecide.lean`.

1. **Howe's original sequent** (MSCS 2001, §5)
   `B⊃((◯A⊃C)⊃◯A), ◯B, ◯A⊃C ⇒ C` is `G4`-underivable, and derivable
   once the implication `◯A⊃C` is doubled — the same contraction
   failure as the packaged gap sequent of `PLLG4Gap.lean`, on Howe's
   own instance.

2. **The naive tower does not climb.**  Stacking another antecedent —
   `T₂ := ◯(F→(F→◯p))` with `F := ◯p→r` — still needs only *two*
   copies of `F`, not three: `G4`'s additive branching hands each
   premise its own copy of the context, so only `F`-firings nested
   along a *single branch* compound; antecedent-stacking spreads the
   uses across sibling branches.  Whether some sequent needs
   multiplicity 3 (equivalently: whether `G4` with a single built-in
   duplication is still incomplete) is open — and mechanically
   searchable with this decider.
-/

namespace PLLG4Tower

open PLLND PLLFormula PLLG4Gap

/-- Naive second layer: `G₂ := F→G₁ = F→(F→◯p)`. -/
def G2 : PLLFormula := Fa.ifThen Ga

/-- `T₂ := ◯G₂`. -/
def T2 : PLLFormula := G2.somehow

-- One copy of `F`: underivable, as for the base gap sequent.
/-- info: false -/
#guard_msgs in #eval decide (G4 [T2, Fa] (prop "r"))

-- Two copies already suffice — the naive tower does not force 3.
/-- info: true -/
#guard_msgs in #eval decide (G4 [T2, Fa, Fa] (prop "r"))

/-- Howe's major premise `B⊃((◯A⊃C)⊃◯A)` with `A := p`, `B := b`,
`C := c`. -/
def howeMajor : PLLFormula :=
  (prop "b").ifThen
    ((((prop "p").somehow.ifThen (prop "c")).ifThen (prop "p").somehow))

/-- Howe's context: `B⊃((◯A⊃C)⊃◯A), ◯B, ◯A⊃C`. -/
def howeCtx : List PLLFormula :=
  [howeMajor, (prop "b").somehow, (prop "p").somehow.ifThen (prop "c")]

-- **Howe's original sequent is `G4`-underivable** (machine-checked).
/-- info: false -/
#guard_msgs in #eval decide (G4 howeCtx (prop "c"))

-- With the implication `◯A⊃C` doubled it becomes derivable:
-- contraction fails on Howe's own instance.
/-- info: true -/
#guard_msgs in
#eval decide (G4 ((prop "p").somehow.ifThen (prop "c") :: howeCtx) (prop "c"))

end PLLG4Tower
