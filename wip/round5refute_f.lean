import round5refute_bdefs

/-!
# ROUND 5, battery F — tower shapes at truncating fuels

Battery B showed the dense-gate towers are size-infeasible at their
ACTIVE fuels (`fuel > b`: 0.9–17M nodes).  What remains feasible is the
truncating-fuel corner (`fuel ≤ b+1`), where the budget-descent content
is fuel-truncated away but the fuel-gap dimension of the statement is
still exercised at the room budget — the same regime as the July rows.
-/

open PLLND.Round5Refute

def truncFuels : List (Nat × Nat) := [(4,4), (3,4), (1,4), (4,5), (5,5)]

def i81f : BInst := { i81 with name := "TOWER1/miss-z TRUNC", budgets := [4, 5], fuels := truncFuels }
def i84f : BInst := { i84 with name := "TOWER1p/miss-z TRUNC", budgets := [4, 5], fuels := truncFuels }
def i85f : BInst := { i85 with name := "TOWER1/miss-z D=◯X TRUNC", budgets := [4, 5], fuels := truncFuels }
def i82f : BInst := { i82 with name := "TOWER2/miss-z TRUNC", budgets := [5, 6], fuels := truncFuels }

#eval banner "battery F: towers at truncating fuels"
#eval runInst cfg1 60000 i81f
#eval runInst cfg1 60000 i84f
#eval runInst cfg1 60000 i85f
#eval runInst cfg1 60000 i82f
#eval banner "battery F done"
