import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnEmbed
import wip.rnDict

/-!
# The ladder image for 8 rungs: order, the `◯` column, and distribution

Three questions, all decidable, all settled by the two-sided oracle.

1. **The order.**  `rnEmbed.rnSub_deriv_iff` already decides it by
   arithmetic (truth-set inclusion in the ladder frame `ℕ`).  This probe
   recomputes it with the *searcher*, which is an independent route, so
   the two must agree.  A disagreement would mean one of them is wrong.

2. **The `◯` column.**  Where does `◯` send each rung?  The rungs are
   ◯-free, so `◯(rnSub n)` is new data, not determined by the ladder.
   Each is matched against the rungs and against the 15 dictionary
   representatives of `wip/rnDict.lean`.

3. **Distribution.**  Is `◯(A ∨ B) ⊃ (◯A ∨ ◯B)` already PLL-derivable
   when `A`, `B` are rungs?  `rnSub_derivU_iff_deriv` does NOT answer
   this: it compares PLL and PCLL on `rnSub i ⊢ rnSub j` only, and a
   distribution instance has neither that premise shape nor that
   conclusion shape.  So it has to be decided directly.

Run: `lake build ladder8probe && .lake/build/bin/ladder8probe`.
-/

open PLLFormula PLLND PLLND.Search

namespace Ladder8

open PLLND.RNEmbed
open PLLND.SemUI.RND

def cfg : Config := { findBudget := some 120000, emitClosureCap := 40 }

/-- Verdict tag for the single-premise sequent `[A] ⊢ B`. -/
def tag1 (A B : PLLFormula) : String :=
  match settleWhy cfg [A] B with
  | .proved _ => "Y"
  | .refuted _ _ _ => "n"
  | .unknown _ => "?"

/-- Verdict tag for the closed sequent `⊢ C`. -/
def tag0 (C : PLLFormula) : String :=
  match settleWhy cfg [] C with
  | .proved t => s!"PROVED({t.size})"
  | .refuted M w _ => s!"REFUTED(n={M.n})"
  | .unknown _ => "?"

/-- `EQ` when interderivable; otherwise the two directions. -/
def interd (A B : PLLFormula) : String :=
  let f := tag1 A B
  let g := tag1 B A
  if f == "Y" && g == "Y" then "EQ" else s!"[{f}{g}]"

def rungs : List PLLFormula := (List.range 9).map rnSub

def dict : List PLLFormula :=
  [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14]

/-- The truth set of rung `n` in the ladder frame, from `sat_rn_odd` /
`sat_rn_even`: `rn 0 = ∅`, `rn (2k+1) = {w | w ≤ k}`,
`rn (2k+2) = {w | w < k} ∪ {k+1}`.  Computed here over `w < 12`. -/
def truthSet (n : Nat) : List Nat :=
  (List.range 12).filter fun w =>
    if n = 0 then false
    else
      let m := n - 1
      if m % 2 = 0 then w ≤ m / 2          -- n = 2k+1, k = m/2
      else (w + 1 ≤ m / 2 || w = m / 2 + 1) -- n = 2k+2, k = m/2

/-- Truth-set inclusion: what `rnSub_deriv_iff` says the order is. -/
def satLe (i j : Nat) : Bool := (truthSet i).all fun w => (truthSet j).contains w

/-- Find the first index in `l` interderivable with `A`. -/
def matchIn (l : List PLLFormula) (A : PLLFormula) : String := Id.run do
  let mut i := 0
  for B in l do
    if tag1 A B == "Y" && tag1 B A == "Y" then return s!"{i}"
    i := i + 1
  return "none"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush

  pl "===== THE LADDER IMAGE, 8 RUNGS ====="
  pl ""
  pl "-- the rungs, and their truth sets in the ladder frame --"
  let mut n := 0
  for A in rungs do
    pl s!"rnSub {n} = {A.toString}"
    pl s!"          truth set {truthSet n}   weight {A.weight}"
    n := n + 1
  pl ""

  pl "-- (1) ORDER: searcher vs truth-set inclusion (must agree) --"
  pl "     rows i, cols j: does rnSub i |- rnSub j ?"
  pl "     'Y'/'n' = searcher; '*' marks disagreement with satLe"
  let mut disagree := 0
  for i in List.range 9 do
    let mut row := ""
    for j in List.range 9 do
      let s := tag1 (rnSub i) (rnSub j)
      let pred := if satLe i j then "Y" else "n"
      if s != pred then
        disagree := disagree + 1
        row := row ++ s ++ "* "
      else
        row := row ++ s ++ "  "
    pl s!"  i={i}: {row}"
  pl s!"  disagreements: {disagree}"
  pl ""

  pl "-- (2) THE BOX COLUMN: box(rnSub n), matched against rungs then dict --"
  for k in List.range 8 do
    let B := (rnSub k).somehow
    let r := matchIn rungs B
    let d := matchIn dict B
    pl s!"  box(rnSub {k}) : rung {r} | dict q{d}"
  pl ""

  pl "-- (3) DISTRIBUTION at rung arguments --"
  pl "     is  |- box(A v B) -> (box A v box B)  derivable in PLL?"
  pl "     THE INSTANCE YOU ASKED ABOUT is (i,j) = (4,3):"
  let inst : PLLFormula :=
    ((rnSub 4).or (rnSub 3)).somehow.ifThen
      (((rnSub 4).somehow).or ((rnSub 3).somehow))
  pl s!"     {inst.toString}"
  pl s!"     verdict: {tag0 inst}"
  pl ""
  pl "     the whole table over rung pairs i,j <= 7:"
  for i in List.range 8 do
    let mut row := ""
    for j in List.range 8 do
      let f : PLLFormula :=
        ((rnSub i).or (rnSub j)).somehow.ifThen
          (((rnSub i).somehow).or ((rnSub j).somehow))
      let s := match settleWhy cfg [] f with
        | .proved _ => "Y"
        | .refuted _ _ _ => "n"
        | .unknown _ => "?"
      row := row ++ s ++ " "
    pl s!"  i={i}: {row}"
  pl ""
  pl "===== done ====="

end Ladder8

def main : IO Unit := Ladder8.main
