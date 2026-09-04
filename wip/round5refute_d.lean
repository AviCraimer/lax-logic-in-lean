import round5refute

/-!
# ROUND 5, battery D — the deep hunt on the unsettled cells

Stage 2 left exactly three `~` cells, all on `JB2/miss-c`
(`D = ◯((a⊃b)⊃c)`, the nested-box jump body) at `b = 3` with the budget
ACTIVE — the only admissible cells of the whole screen so far that
neither side settled.  This battery re-runs that instance with

* the 5-world ladder frames added to the battery (the shapes that
  refuted the July descents live on longer chains),
* a positive stage 10× deeper (`findBudget 4000`),
* the size cap raised to 90000 so the previously SKIPped
  `(6,6)/(5,6)/(2,7)` cells at `b = 4` are screened too.
-/

open PLLFormula PLLND PLLND.Search

namespace PLLND
namespace Round5Refute

def dFrames : List Frame :=
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

def cfgD : Config :=
  { frames := dFrames ++ xFrames ++ defaultFrames
  , findBudget := some 4000
  , emitClosureCap := 0 }

def i21d : BInst := { i21 with name := "JB2/miss-c DEEP", budgets := [3, 4] }

def i11d : BInst := { i11 with name := "JB/miss-c DEEP", budgets := [4] }

end Round5Refute
end PLLND

open PLLND.Round5Refute

#eval banner "battery D: deep hunt on the unsettled cells"
#eval runInst cfgD 90000 i21d
#eval runInst cfgD 90000 i11d
#eval banner "battery D done"
