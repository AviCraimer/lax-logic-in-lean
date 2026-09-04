import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnEmbed
import wip.rnDict

/-!
# Do the rungs above 7 give classes the dictionary does not have?

The dictionary of `wip/rnDict.lean` has 15 classes.  The ladder of
`wip/rnEmbed.lean` has infinitely many, pairwise non-interderivable for
EVERY pair (`rn_pairwise_pll`).  Rungs 0–7 are certified equal to
`q0, q2, q3, q4, q6, q7, q10, q11`.  The question is what rungs 8, 9,
10, … are: new classes, or ones the dictionary already names?

`rnSub 8` has weight 64 and the direct forms grow fast, so this uses
the SMALL representatives instead.  Rungs 0–7 are interderivable with
the listed `q`s (certified in `wip/ladderfast_out.txt`), and the RN
recursion is

    rn (2k+3) = rn (2k+1) ∨ rn (2k+2),   rn (2k+4) = rn (2k+3) ⊃ rn (2k+1)

so `s n` below is interderivable with `rnSub n` by `Interd.or_congr` /
`Interd.imp_congr`, and is far smaller.

Run: `lake build rungnew && .lake/build/bin/rungnew`.
-/

open PLLFormula PLLND PLLND.Search

namespace RungNew

open PLLND.RNEmbed
open PLLND.SemUI.RND

def cfg : Config := { findBudget := some 60000, emitClosureCap := 30 }

/-- Small representatives of the rungs.  `s n ⊣⊢ rnSub n`. -/
def s : Nat → PLLFormula
  | 0 => q0
  | 1 => q2
  | 2 => q3
  | 3 => q4
  | 4 => q6
  | 5 => q7
  | 6 => q10
  | 7 => q11
  | n + 8 =>
      -- indices ≥ 8: even → implication, odd → join, by the RN recursion
      if (n + 8) % 2 = 0 then (s (n + 7)).ifThen (s (n + 5))
      else (s (n + 6)).or (s (n + 7))
  decreasing_by all_goals omega

def dict : List PLLFormula :=
  [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14]

def tag (A B : PLLFormula) : String :=
  match settleWhy cfg [A] B with
  | .proved _ => "Y" | .refuted _ _ _ => "n" | .unknown _ => "?"

def eqv (A B : PLLFormula) : Bool := tag A B == "Y" && tag B A == "Y"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (t : String) : IO Unit := do out.putStrLn t; out.flush

  pl "===== do rungs 8+ give NEW classes? ====="
  pl ""
  pl "-- first, the small forms agree with rnSub on rungs 0..7 (sanity) --"
  for n in List.range 8 do
    let r ← IO.lazyPure (fun _ => if eqv (s n) (rnSub n) then "OK" else "MISMATCH!")
    let _ ← IO.lazyPure (fun _ => r.length)
    pl s!"  s {n} vs rnSub {n}: {r}   (weights {(s n).weight} vs {(rnSub n).weight})"
  pl ""
  pl "-- now rungs 8..13 against every dictionary class --"
  for n in [8, 9, 10, 11, 12, 13] do
    let mut hit := "NEW — matches none of the 15"
    let mut i := 0
    for B in dict do
      let f ← IO.lazyPure (fun _ => eqv (s n) B)
      let _ ← IO.lazyPure (fun _ => f)
      if f && hit.startsWith "NEW" then hit := s!"= q{i}"
      i := i + 1
    pl s!"  rung {n} (weight {(s n).weight}): {hit}"
  pl ""
  pl "===== done ====="

end RungNew

def main : IO Unit := RungNew.main
