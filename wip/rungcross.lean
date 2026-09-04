import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import LaxLogic.PLLSearchNoFall
import LaxLogic.PLLSearchConf
import wip.rnEmbed
import wip.rnDict

/-!
# Cross-relating rungs 8–13 with the seven off-ladder classes

Rungs 0–7 are certified equal to `q0, q2, q3, q4, q6, q7, q10, q11`.
The other seven dictionary classes — `q1, q5, q8, q9, q12, q13, q14` —
are not rungs, and nothing has ever computed how the higher rungs sit
relative to them.  That is the gap between the two structures.

This settles it cell by cell: for each rung `n ∈ 8…13` and each
off-ladder class `q`, both `rung n ⊢ q` and `q ⊢ rung n`.

The rungs are taken in their SMALL form `s n` (certified interderivable
with `rnSub n` for `n ≤ 7` in `wip/rungnew_out.txt`, and built by the
same RN recursion above that).  Each verdict prints as it lands, so a
partial run is still usable.

One row is predictable and serves as a control: `q1 = ⊤`, so every rung
proves it, and none is proved by it — no rung is a theorem, since each
is refuted somewhere on the ladder.

Run: `lake build rungcross && .lake/build/bin/rungcross`.
-/

open PLLFormula PLLND PLLND.Search

namespace RungCross

open PLLND.RNEmbed
open PLLND.SemUI.RND

/-- Countermodels are cheap and the positive stage is the expensive one,
so the budget is kept modest: an unsettled cell prints `?` rather than
stalling the run. -/
def cfg : Config := { findBudget := some 40000, emitClosureCap := 26 }

/-- Small representatives of the rungs; `s n ⊣⊢ rnSub n`. -/
def s : Nat → PLLFormula
  | 0 => q0 | 1 => q2 | 2 => q3 | 3 => q4
  | 4 => q6 | 5 => q7 | 6 => q10 | 7 => q11
  | n + 8 =>
      if (n + 8) % 2 = 0 then (s (n + 7)).ifThen (s (n + 5))
      else (s (n + 6)).or (s (n + 7))
  decreasing_by all_goals omega

/-- The seven dictionary classes that are not rungs. -/
def offLadder : List (String × PLLFormula) :=
  [("q1", q1), ("q5", q5), ("q8", q8), ("q9", q9),
   ("q12", q12), ("q13", q13), ("q14", q14)]

def verdict (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match settleWhy cfg Γ C with
  | .proved t => s!"Y({t.size})"
  | .refuted M _ _ => s!"n[{M.n}w{if RNC.confB M then ",conf" else ""}]"
  | .unknown _ => "?"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (t : String) : IO Unit := do out.putStrLn t; out.flush

  pl "===== rungs 8-13 against the seven off-ladder classes ====="
  pl "  Y(k) = derivable, proof of k nodes"
  pl "  n[Nw] = refuted by an N-world countermodel ('conf' = mutually confluent,"
  pl "          so it refutes PCLL too)"
  pl "  ?     = search cut off; asserts nothing"
  pl ""
  for n in [8, 9, 10, 11, 12, 13] do
    let A := s n
    pl s!"-- rung {n}  (weight {A.weight}) --"
    for (nm, B) in offLadder do
      let t0 ← IO.monoMsNow
      let up ← IO.lazyPure (fun _ => verdict [A] B)
      let _ ← IO.lazyPure (fun _ => up.length)
      let dn ← IO.lazyPure (fun _ => verdict [B] A)
      let _ ← IO.lazyPure (fun _ => dn.length)
      let t1 ← IO.monoMsNow
      let rel :=
        if up.startsWith "Y" && dn.startsWith "Y" then "  <-- EQUAL"
        else if up.startsWith "Y" then "  rung < class"
        else if dn.startsWith "Y" then "  class < rung"
        else if up.startsWith "n" && dn.startsWith "n" then "  incomparable"
        else ""
      pl s!"   rung {n} |- {nm}: {up}    {nm} |- rung {n}: {dn}{rel}   ({t1 - t0} ms)"
    pl ""
  pl "===== done ====="

end RungCross

def main : IO Unit := RungCross.main
