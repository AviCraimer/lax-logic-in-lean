import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnEmbed
import wip.rnDict

/-!
# The `◯` column on the ladder, and whether distribution is free there

The rungs are ◯-free, so the ladder says nothing about `◯(rnSub n)`.
This probe asks two things and nothing else, so it finishes.

* Where does `◯` send each rung?  Matched against the rungs themselves
  and against the 15 dictionary representatives.
* Is `◯(A ∨ B) ⊃ (◯A ∨ ◯B)` PLL-derivable at rung arguments?  The
  instance asked about is `(i, j) = (4, 3)`, which is run first and on
  its own.

Run: `lake build ladderbox && .lake/build/bin/ladderbox`.
-/

open PLLFormula PLLND PLLND.Search

namespace LadderBox

open PLLND.RNEmbed
open PLLND.SemUI.RND

def cfg : Config := { findBudget := some 60000, emitClosureCap := 30 }

def tag1 (A B : PLLFormula) : String :=
  match settleWhy cfg [A] B with
  | .proved _ => "Y"
  | .refuted _ _ _ => "n"
  | .unknown _ => "?"

def eqv (A B : PLLFormula) : Bool := tag1 A B == "Y" && tag1 B A == "Y"

def rungs : List PLLFormula := (List.range 9).map rnSub

def dict : List PLLFormula :=
  [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14]

def matchIn (l : List PLLFormula) (A : PLLFormula) : String := Id.run do
  let mut i := 0
  for B in l do
    if eqv A B then return s!"{i}"
    i := i + 1
  return "-"

/-- `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`. -/
def distr (A B : PLLFormula) : PLLFormula :=
  (A.or B).somehow.ifThen ((A.somehow).or (B.somehow))

def verdict0 (C : PLLFormula) : String :=
  match settleWhy cfg [] C with
  | .proved t => s!"PROVED ({t.size} nodes)"
  | .refuted M w _ =>
      s!"REFUTED (countermodel n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} at {w})"
  | .unknown _ => "? (search cut off — asserts nothing)"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush

  pl "===== THE QUESTION ASKED ====="
  pl ""
  pl "Is  box(rnSub 4 v rnSub 3) -> (box rnSub 4 v box rnSub 3)  PLL-derivable?"
  let inst := distr (rnSub 4) (rnSub 3)
  pl s!"  {inst.toString}"
  let v ← IO.lazyPure (fun _ => verdict0 inst)
  let _ ← IO.lazyPure (fun _ => v.length)
  pl s!"  VERDICT: {v}"
  pl ""

  pl "===== THE BOX COLUMN ====="
  pl "  box(rnSub k) matched against rungs 0..8, then dict q0..q14"
  for k in List.range 7 do
    let B := (rnSub k).somehow
    let r ← IO.lazyPure (fun _ => matchIn rungs B)
    let _ ← IO.lazyPure (fun _ => r.length)
    let d ← IO.lazyPure (fun _ => matchIn dict B)
    let _ ← IO.lazyPure (fun _ => d.length)
    pl s!"  box(rnSub {k}) = rung {r} | dict q{d}"
  pl ""

  pl "===== DISTRIBUTION OVER RUNG PAIRS ====="
  pl "  |- box(rnSub i v rnSub j) -> (box rnSub i v box rnSub j) ?"
  pl "  Y = derivable in PLL, n = refuted (so PCLL is strictly stronger there),"
  pl "  ? = search cut off (asserts nothing)"
  for i in List.range 7 do
    let mut row := ""
    for j in List.range 7 do
      let s := match settleWhy cfg [] (distr (rnSub i) (rnSub j)) with
        | .proved _ => "Y"
        | .refuted _ _ _ => "n"
        | .unknown _ => "?"
      row := row ++ s ++ " "
    pl s!"  i={i}: {row}"
  pl ""
  pl "===== done ====="

end LadderBox

def main : IO Unit := LadderBox.main
