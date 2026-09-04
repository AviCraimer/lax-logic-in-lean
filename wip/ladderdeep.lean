import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import LaxLogic.PLLSearchNoFall
import LaxLogic.PLLSearchConf
import wip.rnDict

/-!
# The open cell that the distribution question lands on

The instance asked about,

    ◯(rnSub 4 ∨ rnSub 3) ⊃ (◯ rnSub 4 ∨ ◯ rnSub 3)

reduces through the certified identifications of `wip/ladderfast.lean`
(`rnSub 4 ≡ q6`, `rnSub 3 ≡ q4`, `rnSub 4 ∨ rnSub 3 ≡ q7`,
`◯q6 ≡ q6`, `◯q4 ≡ q5`) to

    q12 ⊢ q9,   i.e.   ◯(¬◯⊥ ∨ ¬¬◯⊥) ⊢ ◯¬◯⊥ ∨ ¬¬◯⊥

which `wip/rnDict.lean` records as an OPEN CELL: `cImp_12_9`, sorried,
"candidates [1, 11, 13] neither proved (both searchers) nor refuted
(exhaustive ≤4-world battery)".

This probe escalates past that.  `findBudget := none` runs the positive
stage to EXHAUSTION rather than cutting it off, which turns a `~` into
real information: `allStagesMissed` then means the space was searched
out with no proof AND the frame battery found no countermodel.  With
`emitClosureCap` above the sequent's closure size the emitter is
complete over that closure too.

The same escalation is applied to `◯q11` (`cBox_11`, the other open cell
the ladder runs into, at rung 7).

Run: `lake build ladderdeep && .lake/build/bin/ladderdeep`.
-/

open PLLFormula PLLND PLLND.Search

namespace LadderDeep

open PLLND.SemUI.RND

def report (out : IO.FS.Stream) (nm : String) (cf : Config)
    (Γ : List PLLFormula) (C : PLLFormula) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := settleWhy cf Γ C
  let s ← IO.lazyPure (fun _ =>
    match v with
    | .proved t => s!"PROVED ({t.size} nodes)"
    | .refuted M w _ =>
        s!"REFUTED  n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} val={M.val} at {w}\n\
             [infallible={NoFall.infB M}, mutually-confluent={RNC.confB M}]"
    | .unknown (.budgetExhausted k) => s!"~ (positive stage cut at {k} — asserts nothing)"
    | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > cap {cap})"
    | .unknown .allStagesMissed =>
        "ALL STAGES COMPLETE, NONE CERTIFIED (search exhausted, battery and emitter empty)")
  let _ ← IO.lazyPure (fun _ => s.length)
  let t1 ← IO.monoMsNow
  out.putStrLn s!"    {nm}: {s}   ({t1 - t0} ms)"
  out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush

  pl "===== THE OPEN CELL: q12 |- q9 ====="
  pl s!"  q12 = {q12.toString}"
  pl s!"  q9  = {q9.toString}"
  pl s!"  weights: q12 {q12.weight}, q9 {q9.weight}"
  pl ""
  report out "bounded 200k             " { findBudget := some 200000, emitClosureCap := 0 } [q12] q9
  report out "EXHAUSTIVE positive      " { findBudget := none, emitClosureCap := 0 } [q12] q9
  report out "EXHAUSTIVE + emitter 120 " { findBudget := none, emitClosureCap := 120 } [q12] q9
  pl ""
  pl "  the closed form:"
  report out "|- q12 -> q9, exhaustive " { findBudget := none, emitClosureCap := 120 } [] (q12.ifThen q9)
  pl ""

  pl "===== THE OTHER OPEN CELL THE LADDER HITS: box q11 (rung 7) ====="
  pl s!"  q11 = {q11.toString}"
  report out "|- box q11, exhaustive   " { findBudget := none, emitClosureCap := 120 } [] (q11.somehow)
  report out "box q11 |- q1 (= top)    " { findBudget := none, emitClosureCap := 120 } [q11.somehow] q1
  pl ""

  pl "===== CONTROL: a cell known PROVED, same shape ====="
  report out "|- q12 -> q10 (certified) " { findBudget := some 200000, emitClosureCap := 0 } [] (q12.ifThen q10)
  pl ""
  pl "===== done ====="

end LadderDeep

def main : IO Unit := LadderDeep.main
