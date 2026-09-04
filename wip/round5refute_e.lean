import round5refute

/-!
# ROUND 5, battery E — the `⊃◯`-gate band at raised cap

Stage 3 size-skipped the whole `⊃◯`-gate family (`J = 2`, room 4 — the
exact gate shape of `cascade_boxgoal`'s three consuming sites) at cap
40000.  The cells up to ~450k nodes are affordable at minutes each, and
the gate band is the single most site-like configuration the screen has,
so they are bought here explicitly.  `i42d` re-runs the budget-inactive
`∨`-growth row with the deep positive stage to settle its `~` cells.
-/

open PLLFormula PLLND PLLND.Search

namespace PLLND
namespace Round5Refute

def i51e : BInst := { i51 with name := "GATE/miss-c D=a RAISED-CAP", budgets := [4] }

def i52e : BInst := { i52 with name := "GATE/miss-c D=a⊃b RAISED-CAP", budgets := [4] }

def i42d : BInst :=
  { i42 with name := "OR/miss-e,f DEEP" }

end Round5Refute
end PLLND

open PLLND.Round5Refute

#eval banner "battery E: ⊃◯-gate band, raised cap"
#eval runInst cfg1 460000 i51e
#eval runInst cfg1 460000 i52e
#eval runInst cfg2 30000 i42d
#eval banner "battery E done"
