import round5refute

/-!
# ROUND 5, battery G — final escalation on the residual cells

After battery D the active band is settled `P` except three
`JB2/miss-c` cells at `b = 3` (`(5,5)`, `(4,5)`, `(1,5)`).  This battery
gives the two extreme ones (matched fuels; widest fuel gap) a 30000-node
positive stage under the full widened battery — the round-4 escalation
budget.  The countermodel stage is unchanged (already exhaustive over
the frame battery); a `~` after this is reported as OPEN-at-budget.
-/

open PLLND PLLND.Search PLLND.Round5Refute

def gFrames : List Search.Frame :=
  [ ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],
       [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], []⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(0,1)], []⟩
  , ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],
       [], [4]⟩
  , ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],
       [(3,4)], []⟩
  , ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],
       [], []⟩
  , ⟨3, [(0,1),(0,2)], [(0,1),(0,2)], []⟩ ]

def cfgG : Search.Config :=
  { frames := gFrames ++ xFrames ++ Search.defaultFrames
  , findBudget := some 30000
  , emitClosureCap := 0 }

def i21g1 : BInst := { i21 with name := "JB2/miss-c ESC (5,5) b=3", budgets := [3], fuels := [(5,5)] }
def i21g2 : BInst := { i21 with name := "JB2/miss-c ESC (1,5) b=3", budgets := [3], fuels := [(1,5)] }

#eval banner "battery G: escalation on residual cells"
#eval runInst cfgG 90000 i21g1
#eval runInst cfgG 90000 i21g2
#eval banner "battery G done"
