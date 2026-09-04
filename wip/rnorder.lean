import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnEmbed
import wip.rnDict

/-!
# The order on the 15 dictionary classes, and which are in the image of `h`

For the picture we need two things the dictionary does not record
directly:

* the **order** `q_i ⊢ q_j` on all 225 pairs (the dictionary stores the
  ∧/∨/⊃/◯ operation tables, not the order), and
* which classes lie in the image of `h : p ↦ ◯⊥`, i.e. which are
  interderivable with a Rieger–Nishimura rung.

Both are small-formula questions, so the searcher settles them.  Cells
it cannot settle are printed `?` and must be read as *unknown*, not as
`no`.

Run: `lake build rnorder && .lake/build/bin/rnorder`.
-/

open PLLFormula PLLND PLLND.Search

namespace RNOrder

open PLLND.RNEmbed
open PLLND.SemUI.RND

def cfg : Config := { findBudget := some 40000, emitClosureCap := 25 }

def dict : List PLLFormula :=
  [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14]

def cell (A B : PLLFormula) : String :=
  match settleWhy cfg [A] B with
  | .proved _ => "Y"
  | .refuted _ _ _ => "n"
  | .unknown _ => "?"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush

  pl "===== THE 15 DICTIONARY CLASSES ====="
  let mut i := 0
  for A in dict do
    pl s!"  q{i} = {A.toString}"
    i := i + 1
  pl ""

  pl "===== ORDER MATRIX: rows i, cols j -- does q_i |- q_j ? ====="
  pl "     j: 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14"
  let mut r := 0
  for A in dict do
    let mut row := ""
    for B in dict do
      let s ← IO.lazyPure (fun _ => cell A B)
      let _ ← IO.lazyPure (fun _ => s.length)
      row := row ++ " " ++ s ++ " "
    pl s!"  i={r}:{row}"
    r := r + 1
  pl ""

  pl "===== IMAGE OF h : p |-> box bot ====="
  pl "  which dictionary classes are Rieger-Nishimura rungs?"
  let mut k := 0
  for A in dict do
    let mut hit := "OUTSIDE"
    for n in List.range 12 do
      let f ← IO.lazyPure (fun _ =>
        (cell A (rnSub n) == "Y") && (cell (rnSub n) A == "Y"))
      let _ ← IO.lazyPure (fun _ => f)
      if f && hit == "OUTSIDE" then hit := s!"rung {n}"
    pl s!"  q{k}: {hit}"
    k := k + 1
  pl ""

  pl "===== THE BOX MAP on all 15 ====="
  let mut m := 0
  for A in dict do
    let mut tgt := "outside the 15"
    let mut j := 0
    for B in dict do
      let f ← IO.lazyPure (fun _ =>
        (cell A.somehow B == "Y") && (cell B A.somehow == "Y"))
      let _ ← IO.lazyPure (fun _ => f)
      if f && tgt == "outside the 15" then tgt := s!"q{j}"
      j := j + 1
    pl s!"  box q{m} = {tgt}"
    m := m + 1
  pl ""
  pl "===== done ====="

end RNOrder

def main : IO Unit := RNOrder.main
