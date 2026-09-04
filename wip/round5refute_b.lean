import round5refute

/-!
# ROUND 5, battery B — gate towers (piece-closed), maximal gate density

The stage-1 finding: at `J = 0` every table is budget-blind (`act=false`
across the whole room-2 band), so the statement is syntactically an
identity there.  Activity needs live b-gated clauses in the context —
the `⊃⊃` jump gate (guard present) and the `⊃◯` gate.  Battery B builds
the densest piece-closed configurations the room admits: both gate
shapes over one shared consequent `z`, defect 1 (only `z` missing), the
body being the JUMP GOAL itself (`X = a⊃b`, `◯X ∈ S`), so the descent's
jump clause carries the body's own value one budget down — exactly the
step PROGRESS §60(d) identifies as the pigeonhole site.

`towerP` puts the eliminated variable in the jump goal (`X = p⊃b`): the
`p`-antecedent clause of the tables is dropped when `p ∉ Γ`, so the
elimination is genuinely lossy at every gate.
-/

open PLLFormula PLLND PLLND.Search

namespace PLLND
namespace Round5Refute

/-- k = 1 tower: `X⊃z`, `◯X⊃z`, guard `b⊃z`; `J = {X, ◯X}`, room 4. -/
def xT : PLLFormula := aA.ifThen bA
def S7 : List PLLFormula :=
  [xT.ifThen cA, (xT.somehow).ifThen cA, bA.ifThen cA, xT.somehow, xT, aA, bA, cA]
def i81 : BInst :=
  { name := "TOWER1/miss-z  D=X=a⊃b (jump+box gates)", Sl := S7
  , ctx := without S7 [cA], body := xT }

/-- k = 2 tower: adds `◯◯X⊃z`, `◯◯X`; `J = {X, ◯X, ◯◯X}`, room 5. -/
def S8 : List PLLFormula :=
  [xT.ifThen cA, (xT.somehow).ifThen cA, (xT.somehow.somehow).ifThen cA,
   bA.ifThen cA, xT.somehow.somehow, xT.somehow, xT, aA, bA, cA]
def i82 : BInst :=
  { name := "TOWER2/miss-z  D=X=a⊃b", Sl := S8
  , ctx := without S8 [cA], body := xT }

/-- Tower 1 at defect 2 (`z` and `b` missing): room 8. -/
def i83 : BInst :=
  { name := "TOWER1/miss-b,z d=2", Sl := S7
  , ctx := without S7 [bA, cA], body := xT }

/-- Tower 1 with the eliminated variable inside the jump goal. -/
def xP : PLLFormula := pA.ifThen bA
def S7p : List PLLFormula :=
  [xP.ifThen cA, (xP.somehow).ifThen cA, bA.ifThen cA, xP.somehow, xP, pA, bA, cA]
def i84 : BInst :=
  { name := "TOWER1p/miss-z D=X=p⊃b (elim var in jump goal)", Sl := S7p
  , ctx := without S7p [cA], body := xP }

/-- Tower 1 with a BOXED body one level up: body `◯X`, `◯◯X ∈ S`. -/
def S7b : List PLLFormula :=
  [xT.ifThen cA, (xT.somehow).ifThen cA, bA.ifThen cA,
   xT.somehow.somehow, xT.somehow, xT, aA, bA, cA]
def i85 : BInst :=
  { name := "TOWER1/miss-z  D=◯X (nested box body)", Sl := S7b
  , ctx := without S7b [cA], body := xT.somehow }

end Round5Refute
end PLLND

open PLLND.Round5Refute

#eval banner "battery B: gate towers, max density"
#eval runInst cfg1 60000 i81
#eval runInst cfg1 60000 i84
#eval runInst cfg1 60000 i85
#eval runInst cfg1 60000 i82
#eval runInst cfg1 60000 i83
#eval banner "battery B done"
