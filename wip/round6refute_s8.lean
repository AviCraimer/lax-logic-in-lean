import round6refute

/-! # ROUND 6 screen, stage 8 — the third §62 residual cell, re-run

Stage 5's shell was killed after its `(1,5)` and `(4,5)` cells completed
(both `~` at 300000 nodes, no countermodel; (4,5) took 2409 s).  This
file re-runs the remaining `(5,5)` cell alone, same config. -/

open PLLND.Round5Refute PLLND.Round6Refute
open PLLND.Search

def cfgE8 : Config :=
  { frames := xFrames ++ defaultFrames
  , findBudget := some 300000
  , emitClosureCap := 24 }

def e3b : BInst := { i21 with name := "JB2/miss-c ESC10x (5,5) b=3 rerun", budgets := [3], fuels := [(5,5)] }

#eval banner6 "round 6, stage 8: JB2 (5,5) b=3 at 300000 nodes (rerun)"
#eval runInst6 cfgE8 90000 e3b
#eval banner6 "stage 8 done"
