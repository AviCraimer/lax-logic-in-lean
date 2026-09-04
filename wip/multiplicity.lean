import LaxLogic.PLLDecide

/-!
# Is the contraction multiplicity bounded?

`PLLG4Gap.lean` shows the separating sequent

    ◯((◯p ⊃ r) ⊃ ◯p),  ◯p ⊃ r   ⇒   r

is **not** `G4`-derivable, but **is** with a second copy of `◯p ⊃ r`.  So the
multiplicity there is exactly 2, and `PLLG4Tower.lean` records that the naive
tower also needs only 2.  HANDOFF §7 item 5 asks whether any sequent needs 3.
That question is now the first move of the contraction-bound route
(`docs/ui-two-routes.md` §3): if multiplicity is bounded, pre-expanding the
antecedent gives a contraction-free search and the interpolant becomes a
function of the sequent alone.

## The family

Matthew's steer was to look at the *structure* rather than sweep exhaustively,
and to take the shape from the ladder.  The gap's mechanism is that `F` is
needed **both inside and outside** one `◯`-scope.  Nesting the scopes should
demand one copy per layer.  Writing `F = ◯p ⊃ r`:

    K 0     = ◯p
    K (n+1) = ◯(F ⊃ K n)

so `K 1 = ◯((◯p ⊃ r) ⊃ ◯p)` is exactly the gap's boxed hypothesis, and

    K n,  F, …, F   ⇒   r

is the test.  **Conjecture: the least number of copies is `n + 1`** — so
multiplicity is unbounded and the contraction-bound route needs a bound that
grows with the `◯`-nesting, not a constant.

The decider is `PLLDecide`'s verified `G4` procedure — the one that established
the original gap.  It decides `G4`, the naive (incomplete-for-PLL) calculus,
which is exactly the right instrument here: multiplicity is a question about
what `G4` needs, not about PLL provability.
-/

open PLLFormula PLLND

namespace Multiplicity

/-- `F = ◯p ⊃ r`, the formula whose copies are counted. -/
def F : PLLFormula := ((prop "p").somehow).ifThen (prop "r")

/-- `K 0 = ◯p`;  `K (n+1) = ◯(F ⊃ K n)`.  `K 1` is the gap's hypothesis. -/
def K : Nat → PLLFormula
  | 0     => (prop "p").somehow
  | n + 1 => (F.ifThen (K n)).somehow

/-- `n` copies of `F`. -/
def copies : Nat → List PLLFormula
  | 0     => []
  | n + 1 => F :: copies n

/-- Is `K n, Fᵏ ⇒ r` derivable in `G4`? -/
def test (n k : Nat) : Bool := decide (G4 (K n :: copies k) (prop "r"))

/-- Least `k ≤ bound` with `K n, Fᵏ ⇒ r` derivable, or `none`. -/
def least (n bound : Nat) : Option Nat :=
  (List.range (bound + 1)).find? (fun k => test n k)

end Multiplicity

-- Sanity: `K 1` reproduces the known gap — 1 copy fails, 2 copies succeed.
/-- info: false -/
#guard_msgs in #eval Multiplicity.test 1 1
/-- info: true -/
#guard_msgs in #eval Multiplicity.test 1 2

-- The question: does the least multiplicity climb with the nesting?
#eval IO.println (String.intercalate "\n"
  ((List.range 4).map (fun n =>
    "  K " ++ ToString.toString n ++ " : least copies = " ++
      (match Multiplicity.least n 6 with
       | some k => ToString.toString k
       | none   => "none ≤ 6"))))
