import round7pin

/-!
# ROUND 8 — the goal-row absorption's env route, kernel-refuted at the witness

PROGRESS §66(h) leaves ONE lemma shape open: `Round7.CompProd`'s goal-row
case at compound unboxed bodies — absorb the source table's goal row

    Gsrc = ◯( E@(f, b−1)(Γ) ⊃ A@(f, b)(Γ, D) )      (f = ft − 1)

into the target table `A@(ft, c)(Γ, ◯D)` at `c < b` from the ambient alone.
The target table offers three disjunct families: its own goal row, its env
rows, and its truncation row.  Round 7 killed the POINTWISE route to the
goal row (`goalrow_landing_refuted_elev1/_elev2`).  This file kills the
**γ-env route**: at July's jump witness (`Skb`/`Gk`,
`D = gk = (◯r ⊃ s) ⊃ t` — the residue's compound unboxed shape), the
target's γ-head env disjunct

    envK = ( ◯( E@(f, c−1)(Γ) ⊃ A@(f, c−1)(Γ, ◯p) ) ) ∧ A@(f, c)(r::Γ, ◯D)

is refuted by `Mk` FROM THE FULL WALK POSITION — the goal row, the
introduced guard `E@(ft, c)(Γ)`, and the ambient all held (`ft = 4`,
`b = 2`, `c = 1`).  The γ-head component over the γ-clause `◯p ⊃ r` cannot
be financed by the goal row plus the ambient, at exactly the configuration
where the same premises SATISFY the committed goal clause and the full
target table in the same model (scratch-probed, recorded in the round
report; the searcher instances are in `wip/frontier_g8.txt`).

Consequence for the round-8 residue: the goal-row absorption, if it is
derivable at all, commits to the target's own goal row or its truncation
row — the env family is closed.  Together with round 7's pins this
delimits the build to exactly the committed-goal-clause mechanics.
-/

open PLLFormula

namespace PLLND
namespace Round8Pin

open Round4Probe3 AscRefute

/-- The source table's goal row at the walk position (`ft = 4`, `b = 2`,
inner fuel `f = 3`): `◯(E@(3,1)(Gk) ⊃ A@(3,2)(Gk, gk))`. -/
def gsrcK : PLLFormula :=
  ((itpE "p" Skb 3 1 Gk).ifThen (itpA "p" Skb 3 2 Gk gk)).somehow

/-- The introduced guard of the target component at `c = 1`:
`E@(4,1)(Gk)`.  Ambient-derivable (downward budget monotonicity), carried
so the pinned sequent IS the walk position verbatim. -/
def guardK : PLLFormula := itpE "p" Skb 4 1 Gk

/-- The target table's γ-head env disjunct at `c = 1` (inner fuel 3), for
the γ-clause `◯p ⊃ r ∈ Gk`: boxed head at budget `0`, grown second
component at budget `1` over `r :: Gk`. -/
def envK : PLLFormula :=
  (((itpE "p" Skb 3 0 Gk).ifThen
      (itpA "p" Skb 3 0 Gk (prop "p").somehow)).somehow).and
    (itpA "p" Skb 3 1 (prop "r" :: Gk) gk.somehow)

/-- **The γ-env absorption of the goal row fails at the walk position.**
Kernel-checked countermodel: `Mk` (July's model) forces the goal row, the
guard and the ambient at world 0 and refutes the γ-head env disjunct. -/
theorem genv_absorption_refuted :
    FinCM.checkB Mk 0 [gsrcK, guardK, Round7Pin.ambE3] envK
      = true := by
  decide +kernel

/-- The underivability reading. -/
theorem genv_absorption_not_derivable :
    ¬ G4c [gsrcK, guardK, Round7Pin.ambE3] envK := fun h =>
  FinCM.not_provable_of_check genv_absorption_refuted (G4c.equiv_nd.mp h)

end Round8Pin
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round8Pin.genv_absorption_refuted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round8Pin.genv_absorption_refuted

/--
info: 'PLLND.Round8Pin.genv_absorption_not_derivable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round8Pin.genv_absorption_not_derivable
