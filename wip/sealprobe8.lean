import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchNoFall
import LaxLogic.PLLSearchConf
import LaxLogic.PLLSearchPin

/-!
# Is the floor branch at a boxed goal TRUE?  Exhaustive stages at small fuel

PROGRESS §92 leaves one shape: the floor branch at a boxed goal `◯D`.  Every
probe so far has returned `~ (budget k exhausted)`, which asserts nothing — the
positive stage was cut off, so neither side is known.

Two things make a real verdict reachable here.

* The obligation quantifies over the **fuel**, so a refutation may use any fuel
  it likes.  Dropping to fuel `2` shrinks the tables by orders of magnitude.
* With `findBudget := none` the positive stage runs to **exhaustion**, and
  exhaustion is information: `allStagesMissed` means the frame battery found no
  countermodel, the search space was exhausted with no proof, and the closure
  emitter proposed nothing that cleared `checkB`.  With `emitClosureCap` above
  the sequent's closure size the emitter is complete over that closure, so
  `allStagesMissed` then becomes strong evidence of underivability rather than a
  budget artefact.

Both are run, at fuels 2 and 3, on the one-live-γ-clause space (smallest) and
with the goal `◯s`.  For contrast the same cells are run at the `⊃`-shaped goal
`r ⊃ s`, where PROGRESS §92 has a 9-node proof — so if the harness is asking the
right question, that column should come out `PROVED` and the boxed column
should not.

Run: `lake build sealprobe8 && .lake/build/bin/sealprobe8`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe8

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }
def G1 : List PLLFormula := [gam "r" "s"]

def report (out : IO.FS.Stream) (nm : String) (cf : Config)
    (hyps : List PLLFormula) (goal : PLLFormula) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := settleWhy cf hyps goal
  let s ← IO.lazyPure (fun _ =>
    match v with
    | .proved t => s!"PROVED ({t.size} nodes)"
    | .refuted M w _ =>
        s!"REFUTED!  n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} val={M.val} \
at {w}  [inf={NoFall.infB M}, conf={RNC.confB M}]"
    | .unknown (.budgetExhausted k) => s!"~ (positive stage cut at {k})"
    | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > cap {cap})"
    | .unknown .allStagesMissed =>
        "ALL STAGES COMPLETE, NONE CERTIFIED (search exhausted, battery and \
emitter empty)")
  let _ ← IO.lazyPure (fun _ => s.length)
  let t1 ← IO.monoMsNow
  out.putStrLn s!"      {nm}: {s}  ({t1 - t0} ms)"
  out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== is the floor branch at a boxed goal true?  exhaustive stages =="
  pl ""
  let A := prop "r"
  let B := prop "s"
  for f in [2, 3] do
    for (cnm, C) in [("◯s", (prop "s").somehow),
                     ("r ⊃ s", (prop "r").ifThen (prop "s"))] do
      let amb := itpE "p" S1 (f + 1) 2 G1
      let box := (((itpE "p" S1 f 1 G1).ifThen
        (itpA "p" S1 f 1 G1 A.somehow)).somehow)
      let snd := itpA "p" S1 (f + 1) 1 (B :: G1) C
      let goal := orAll (itpAoth "p" S1 f 1 G1 C)
      let hyps := [amb, box, snd]
      let hw := (hyps.map PLLFormula.weight).foldl (· + ·) 0
      pl s!"fuel {f}, C = {cnm}   (hypothesis weight {hw}, goal weight {goal.weight})"
      report out "bounded  (find 20k)              "
        { findBudget := some 20000, emitClosureCap := 0 } hyps goal
      report out "EXHAUSTIVE positive (find none)  "
        { findBudget := none, emitClosureCap := 0 } hyps goal
      report out "EXHAUSTIVE + complete emitter    "
        { findBudget := none, emitClosureCap := 80 } hyps goal
  pl ""
  pl "== done =="

end SealProbe8

def main : IO Unit := SealProbe8.main
