import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchNoFall
import LaxLogic.PLLSearchConf

/-!
# Is the boxed γ-branch obligation itself true?  Small fuel, exhaustive stages

`wip/sealRefute.lean` refutes all three *uniform routes* to the boxed
γ-disjunct at target budget `1`.  It leaves open whether the branch
**obligation** — reach *some* target disjunct — is true.  No countermodel has
been found, but every search so far was bounded: `~ (budget k exhausted)` says
the positive stage was truncated, so nothing at all is known, and the battery
is a fixed frame list rather than a complete method.

The obligation is a statement about *all* fuels, so a refutation may use any
fuel it likes.  Dropping the fuel from 5 to 2 or 3 shrinks the tables by orders
of magnitude and brings two complete stages into range:

* the positive stage with `findBudget := none`, which then either finds a proof
  or **exhausts the search space** — and exhaustion is real information;
* the `emit` stage, which is complete over the subformula closure of the
  sequent, once `emitClosureCap` is above that closure's size.

So at small fuel `settleWhy` can return a genuine verdict instead of `~`.  Both
the one-live-clause space (where the second hypothesis collapses to an atom, so
the obligation is expected to be *trivially* true) and the two-live-clause space
(where it does not) are run, at fuels 2, 3, 4, with the routes reported
alongside the whole obligation.

Run: `lake build sealprobe5 && .lake/build/bin/sealprobe5`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe5

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

/-- One live γ-clause. -/
def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }

def G1 : List PLLFormula := [gam "r" "s"]

/-- Two live γ-clauses, so `s :: Γ` still has one. -/
def S2 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    gam "u" "v", (prop "u").somehow, prop "u", prop "v", prop "z" }

def G2 : List PLLFormula := [gam "r" "s", gam "u" "v"]

def report (out : IO.FS.Stream) (nm : String) (cf : Config)
    (hyps : List PLLFormula) (goal : PLLFormula) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := settleWhy cf hyps goal
  let s ← IO.lazyPure (fun _ =>
    match v with
    | .proved _ => "PROVED"
    | .refuted M w _ =>
        s!"REFUTED!  n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} val={M.val} \
at {w}  [inf={NoFall.infB M}, conf={RNC.confB M}]"
    | .unknown (.budgetExhausted k) => s!"~ (budget {k})"
    | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > cap {cap})"
    | .unknown .allStagesMissed =>
        "UNDERIVABLE-OR-MISSED (all stages complete, none certified)")
  let _ ← IO.lazyPure (fun _ => s.length)
  let t1 ← IO.monoMsNow
  out.putStrLn s!"      {nm}: {s}  ({t1 - t0} ms)"
  out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== is the boxed γ-branch obligation true?  small fuel, complete stages =="
  pl ""
  let A := prop "r"
  let B := prop "s"
  let C := prop "z"
  for (snm, S, Γ) in [("S1 (one live γ-clause)", S1, G1),
                      ("S2 (two live γ-clauses)", S2, G2)] do
    pl s!"{snm}  defect = {defect S Γ}"
    for f in [2, 3, 4] do
      let hyps : List PLLFormula :=
        [ itpE "p" S (f + 1) 2 Γ,
          (((itpE "p" S f 1 Γ).ifThen (itpA "p" S f 1 Γ A.somehow)).somehow),
          itpA "p" S f 1 (B :: Γ) C ]
      let goal := orAll (itpAoth "p" S f 1 Γ C)
      let hw := (hyps.map PLLFormula.weight).foldl (· + ·) 0
      pl s!"   fuel = {f}   (hypothesis weight {hw}, goal weight {goal.weight})"
      report out "whole, bounded  (find 20k, emitCap 0) "
        { findBudget := some 20000, emitClosureCap := 0 } hyps goal
      report out "whole, EXHAUSTIVE (find none, emit 40)"
        { findBudget := none, emitClosureCap := 40 } hyps goal
      report out "whole, exhaustive + inf&conf filter  "
        { findBudget := none, emitClosureCap := 40,
          accept := fun M => NoFall.infB M && RNC.confB M } hyps goal
  pl ""
  pl "== done =="

end SealProbe5

def main : IO Unit := SealProbe5.main
