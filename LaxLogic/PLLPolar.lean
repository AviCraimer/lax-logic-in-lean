import LaxLogic.PLLJudgmental

/-!
# Polarised syntax for PLL

Step 2 of the programme in `docs/lax-logic-interpolation-handoff.md`, over the
two-judgment base of `LaxLogic/PLLJudgmental.lean`.

The polarisation follows the Twelf `lax-logic` development, whose target
declares `circ : prop pos → prop neg` — so `◯` takes a **positive** proposition
to a **negative** one, the shape of an up-shift.  `wip/polarity.lean` records
why the negative assignment is only available once the second judgment is
present.

    Pos ::= p⁺ | ⊥ | P ∨ P | ↓N
    Neg ::= ↑P | P ⊃ N | N ∧ N | ◯P

## What is proved here

* `erase` back to `PLLFormula`, in both categories;
* `polPos` / `polNeg`, the two polarisations of an ordinary formula, with
  **roundtrip** theorems `erase_polPos`, `erase_polNeg` — so polarisation loses
  nothing;
* `shifts`, the phase measure, and `phase φ := (polNeg φ).shifts`.

The roundtrip theorems audit at `[propext]` (from `simp`); `phase_somehow` is
axiom-free.

## A caveat about the phase measure, stated plainly

The handoff's strategic bet is that recasting the contraction metric as a
*polarity-phase* measure makes it **proof-independent**, "because polarity is
fixed by the formula, not by the derivation".  That much is true here, and
`phase` witnesses it — but it is true *by construction* and therefore cheap:
`phase` is a function on `PLLFormula`, so of course it does not depend on a
derivation.

The content the programme actually needs is the **other** half: that the
interpolant recursion **descends** on this measure.  That is not settled by
anything in this file, and stating the measure does not make it more likely.
What this file supplies is the object on which such a descent could be stated;
whether the descent holds is the open question, and it is where the risk sits —
alongside identity expansion, which Simmons calls the major contribution of
*Structural focalization* and which no reference covers for a modality.
-/

namespace PLLND

mutual
/-- Positive (synchronous) propositions. -/
inductive Pos where
  | atom : String → Pos
  | fls  : Pos
  | or   : Pos → Pos → Pos
  | down : Neg → Pos
/-- Negative (asynchronous) propositions.  `circ` takes a positive to a
negative, following the Twelf `lax-logic` declaration. -/
inductive Neg where
  | up   : Pos → Neg
  | imp  : Pos → Neg → Neg
  | and  : Neg → Neg → Neg
  | circ : Pos → Neg
end

namespace Polar

/-! ## Erasure -/

mutual
/-- Erase a positive proposition to an ordinary formula. -/
def erasePos : Pos → PLLFormula
  | .atom a => .prop a
  | .fls    => .falsePLL
  | .or p q => .or (erasePos p) (erasePos q)
  | .down n => eraseNeg n

/-- Erase a negative proposition to an ordinary formula.  Shifts vanish. -/
def eraseNeg : Neg → PLLFormula
  | .up p    => erasePos p
  | .imp p n => .ifThen (erasePos p) (eraseNeg n)
  | .and m n => .and (eraseNeg m) (eraseNeg n)
  | .circ p  => .somehow (erasePos p)
end

/-! ## Polarisation

Atoms are taken positive, as in LJF with all atoms positive; the choice is a
tunable parameter (Liang–Miller) and is recorded here as a decision, not a
necessity.  `∨` and `⊥` are positive, `⊃` and `∧` negative, and `◯` negative
over a positive argument. -/

mutual
/-- The positive polarisation of an ordinary formula. -/
def polPos : PLLFormula → Pos
  | .prop a     => .atom a
  | .falsePLL   => .fls
  | .or φ ψ     => .or (polPos φ) (polPos ψ)
  | .and φ ψ    => .down (.and (polNeg φ) (polNeg ψ))
  | .ifThen φ ψ => .down (.imp (polPos φ) (polNeg ψ))
  | .somehow φ  => .down (.circ (polPos φ))

/-- The negative polarisation of an ordinary formula. -/
def polNeg : PLLFormula → Neg
  | .prop a     => .up (.atom a)
  | .falsePLL   => .up .fls
  | .or φ ψ     => .up (.or (polPos φ) (polPos ψ))
  | .and φ ψ    => .and (polNeg φ) (polNeg ψ)
  | .ifThen φ ψ => .imp (polPos φ) (polNeg ψ)
  | .somehow φ  => .circ (polPos φ)
end

/-! ## Roundtrip: polarisation loses nothing -/

mutual
/-- Erasing the positive polarisation gives the formula back. -/
theorem erase_polPos : ∀ φ : PLLFormula, erasePos (polPos φ) = φ
  | .prop _     => rfl
  | .falsePLL   => rfl
  | .or φ ψ     => by
      simp only [polPos, erasePos, erase_polPos φ, erase_polPos ψ]
  | .and φ ψ    => by
      simp only [polPos, erasePos, eraseNeg, erase_polNeg φ, erase_polNeg ψ]
  | .ifThen φ ψ => by
      simp only [polPos, erasePos, eraseNeg, erase_polPos φ, erase_polNeg ψ]
  | .somehow φ  => by
      simp only [polPos, erasePos, eraseNeg, erase_polPos φ]

/-- Erasing the negative polarisation gives the formula back. -/
theorem erase_polNeg : ∀ φ : PLLFormula, eraseNeg (polNeg φ) = φ
  | .prop _     => rfl
  | .falsePLL   => rfl
  | .or φ ψ     => by
      simp only [polNeg, eraseNeg, erasePos, erase_polPos φ, erase_polPos ψ]
  | .and φ ψ    => by
      simp only [polNeg, eraseNeg, erase_polNeg φ, erase_polNeg ψ]
  | .ifThen φ ψ => by
      simp only [polNeg, eraseNeg, erase_polPos φ, erase_polNeg ψ]
  | .somehow φ  => by
      simp only [polNeg, eraseNeg, erase_polPos φ]
end

/-! ## The phase measure

The number of shifts: each `↓` and each `↑` is a phase boundary.  `◯` is *not*
a boundary on its own — it is negative over a positive argument, so the
boundary it induces is already recorded by the `↓` that `polPos` inserts when
`◯φ` occurs in positive position. -/

mutual
/-- Shift count of a positive proposition. -/
def shiftsPos : Pos → Nat
  | .atom _ => 0
  | .fls    => 0
  | .or p q => shiftsPos p + shiftsPos q
  | .down n => shiftsNeg n + 1

/-- Shift count of a negative proposition. -/
def shiftsNeg : Neg → Nat
  | .up p    => shiftsPos p + 1
  | .imp p n => shiftsPos p + shiftsNeg n
  | .and m n => shiftsNeg m + shiftsNeg n
  | .circ p  => shiftsPos p
end

/-- **The phase measure of an ordinary formula.**  A function of the formula
alone — which is the programme's proof-independence claim, and is true here by
construction.  See the caveat in the module header: the open question is
whether the interpolant recursion *descends* on it. -/
def phase (φ : PLLFormula) : Nat := shiftsNeg (polNeg φ)

/-- `◯` costs exactly one phase boundary more than its argument in positive
position: the `↓` that `polPos` inserts. -/
theorem shifts_polPos_somehow (φ : PLLFormula) :
    shiftsPos (polPos (.somehow φ)) = shiftsPos (polPos φ) + 1 := rfl

/-- In negative position `◯` costs nothing beyond its argument — the boundary
is carried by the argument's own polarisation. -/
theorem phase_somehow (φ : PLLFormula) :
    phase (.somehow φ) = shiftsPos (polPos φ) := rfl

end Polar
end PLLND

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'PLLND.Polar.erase_polPos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.Polar.erase_polPos

/-- info: 'PLLND.Polar.erase_polNeg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.Polar.erase_polNeg

/-- info: 'PLLND.Polar.phase_somehow' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.Polar.phase_somehow
