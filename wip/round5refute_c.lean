import round5refute_bdefs

/-!
# ROUND 5, battery C — `◯⊥` body under gates, and deep-search controls

`i91`: the ladder's key formula as the body — `D = ⊥`, `◯⊥ ∈ S` — under
the tower-1 gates, with `⊥ ∈ S \ Γ` (a context containing `⊥` forces
everything at any refuting world, so `⊥` must be missing; that puts the
row at defect 2, room 8; fuels are kept small, so these cells screen the
fuel-gap dimension at a high budget, like the July rows).

The `cfg2` re-runs give the stage-1 `~` controls a positive stage deep
enough to settle them (`boxDesc_atom_all` makes the atom rows theorems;
a `P` here is a live-fire test of the positive side of the screen).
-/

open PLLFormula PLLND PLLND.Search

namespace PLLND
namespace Round5Refute

def S9 : List PLLFormula :=
  [xT.ifThen cA, (xT.somehow).ifThen cA, bA.ifThen cA,
   xT.somehow, xT, aA, bA, cA, falsePLL.somehow, falsePLL]
def i91 : BInst :=
  { name := "TOWER1/miss-z,⊥ D=⊥ (◯⊥ body) d=2", Sl := S9
  , ctx := without S9 [cA, falsePLL], body := falsePLL
  , fuels := [(4,4), (3,4), (1,4), (4,5), (5,5)] }

end Round5Refute
end PLLND

open PLLND.Round5Refute

#eval banner "battery C: ◯⊥ body + deep-search controls"
#eval runInst cfg1 60000 i91
#eval runInst cfg2 30000 i35
#eval runInst cfg2 30000 i36
#eval banner "battery C done"
