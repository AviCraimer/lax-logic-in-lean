import round6refute

/-! # ROUND 6 screen, stage 5 — the three §62 residual JB2 cells, escalated

`D = ◯((a⊃b)⊃c)` over `S2`, ctx miss-`c`, `b = 3`, `(fs,ft) =
(5,5), (4,5), (1,5)` — round 5 left these `~` at 30000 search nodes with
no countermodel over the widened battery.  They are IMPLIED by `BoxDesc`
(they satisfy its hypotheses), so a countermodel here kills `BoxDesc`
too.  Escalation: 10× the node budget (300000) and the closure emitter
enabled (cap 24).  Expected multi-hour worst case; every line flushes to
`wip/round6refute_out.txt`, so a killed run loses nothing. -/

open PLLND.Round5Refute PLLND.Round6Refute
open PLLND.Search

def cfgE : Config :=
  { frames := xFrames ++ defaultFrames
  , findBudget := some 300000
  , emitClosureCap := 24 }

def e1 : BInst := { i21 with name := "JB2/miss-c ESC10x (1,5) b=3", budgets := [3], fuels := [(1,5)] }
def e2 : BInst := { i21 with name := "JB2/miss-c ESC10x (4,5) b=3", budgets := [3], fuels := [(4,5)] }
def e3 : BInst := { i21 with name := "JB2/miss-c ESC10x (5,5) b=3", budgets := [3], fuels := [(5,5)] }

#eval banner6 "round 6, stage 5: JB2 residual cells, 300000 nodes + emitter(24)"
#eval runInst6 cfgE 90000 e1
#eval runInst6 cfgE 90000 e2
#eval runInst6 cfgE 90000 e3
#eval banner6 "stage 5 done"
