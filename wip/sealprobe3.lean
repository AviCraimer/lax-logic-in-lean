import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchNoFall
import LaxLogic.PLLSearchConf

/-!
# Refuting the boxed γ-branch: a γ-head that is not the eliminated variable

PROGRESS §86 closes the boxed γ-branch at every target budget `≥ 2` and shows
that at target budget `1` the probed family is saved by a collapse to `◯⊥` —
a route that works only because that family's γ-clause is `◯p ⊃ r`, whose
head is the **eliminated variable** `p`.  The goal clause of `p` is empty at
every budget, which is what forces the collapse.

This file tests the prediction that follows.  Take a γ-clause whose head is an
ordinary atom:

    S ⊇ {◯r ⊃ s, ◯r, r, s},   Γ = [◯r ⊃ s],   A = r,   B = s.

Then at budget `0`

* `A@0(Γ, ◯r) = ⊥` still — the `◯`-goal clause is budget-gated and the
  environment clause is too, so the target's boxed component is `◯⊥`;
* but `A@0(Γ, r) ⊇ r` — the *atom* goal clause is **not** gated, so the plain
  component is not starved and the collapse argument fails.

So in an **infallible** model with `r` false at the root and true at a
`⊳`-successor, the source's boxed component should hold while every target
disjunct fails.  If the battery finds such a model, `GammaPairFloorBox` is
**individually false**, not merely one of an unsatisfiable four, and the
branch must be re-cut rather than proved.

Both the unfiltered search and an infallibility-filtered search are run: a
countermodel that is infallible and mutually confluent refutes the statement
over PCLL, PILL and PICLL too, so the obstruction would not be an artefact of
fallible worlds or of the missing distribution scheme.  Filters are passed as
`Config.accept` rather than applied afterwards, because mutual confluence is
not inherited by submodels.

Run: `lake build sealprobe3 && .lake/build/bin/sealprobe3`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe3

/-- The space: a γ-clause `◯r ⊃ s` with an ordinary head, piece-closed, with
the eliminated variable `p` present as an atom and a goal atom `z`. -/
def S1 : Finset PLLFormula :=
  { ((prop "r").somehow).ifThen (prop "s"), (prop "r").somehow,
    prop "r", prop "s", prop "p", prop "z" }

def G1 : List PLLFormula := [((prop "r").somehow).ifThen (prop "s")]

/-- The γ-head, an ordinary atom (not `p`). -/
def A1 : PLLFormula := prop "r"

/-- The γ-consequent. -/
def B1 : PLLFormula := prop "s"

/-- A larger variant: the same γ-clause with a second, `p`-headed clause
present as well, so the space is not artificially `p`-free. -/
def S2 : Finset PLLFormula :=
  { ((prop "r").somehow).ifThen (prop "s"), (prop "r").somehow,
    prop "r", prop "s",
    ((prop "p").somehow).ifThen (prop "r"), (prop "p").somehow,
    prop "p", prop "z" }

def G2 : List PLLFormula := [((prop "r").somehow).ifThen (prop "s")]

def cfgPlain (bud cap : Nat) : Config :=
  { findBudget := some bud, emitClosureCap := cap }

/-- Infallibility as a search-time filter (not applied afterwards: a
submodel of a confluent model need not be confluent). -/
def cfgInf (bud cap : Nat) : Config :=
  { findBudget := some bud, emitClosureCap := cap,
    accept := fun M => NoFall.infB M }

/-- Infallible **and** mutually confluent. -/
def cfgInfConf (bud cap : Nat) : Config :=
  { findBudget := some bud, emitClosureCap := cap,
    accept := fun M => NoFall.infB M && RNC.confB M }

def report (out : IO.FS.Stream) (nm : String) (cf : Config)
    (hyps : List PLLFormula) (goal : PLLFormula) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := settleWhy cf hyps goal
  let s ← IO.lazyPure (fun _ =>
    match v with
    | .proved _ => "PROVED"
    | .refuted M w _ =>
        s!"REFUTED!  model n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} \
val={M.val} at world {w}  [infallible={NoFall.infB M}, \
mutuallyConfluent={RNC.confB M}]"
    | .unknown (.budgetExhausted k) => s!"~ (search budget {k} exhausted)"
    | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > cap {cap})"
    | .unknown .allStagesMissed => "~ (every stage ran, none certified)")
  let _ ← IO.lazyPure (fun _ => s.length)
  let t1 ← IO.monoMsNow
  out.putStrLn s!"    {nm}: {s}  ({t1 - t0} ms)"
  out.flush

/-- The boxed γ-branch obligation at target budget `1`. -/
def boxedObligation (S : Finset PLLFormula) (F fl : Nat)
    (Γ : List PLLFormula) (A B C : PLLFormula) :
    List PLLFormula × PLLFormula :=
  ([ itpE "p" S (fl + 1) 2 Γ,
     (((itpE "p" S F 1 Γ).ifThen (itpA "p" S F 1 Γ A.somehow)).somehow),
     itpA "p" S F 1 (B :: Γ) C ],
   orAll (itpAoth "p" S fl 1 Γ C))

/-- The plain γ-branch obligation, as the control. -/
def plainObligation (S : Finset PLLFormula) (F fl : Nat)
    (Γ : List PLLFormula) (A B C : PLLFormula) :
    List PLLFormula × PLLFormula :=
  ([ itpE "p" S (fl + 1) 2 Γ,
     itpA "p" S F 1 Γ A,
     itpA "p" S F 1 (B :: Γ) C ],
   orAll (itpAoth "p" S fl 1 Γ C))

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== boxed γ-branch with a γ-head that is NOT the eliminated variable =="
  pl ""
  for (nm, S, Γ) in [("S1 (p-free γ-clause only)", S1, G1),
                     ("S2 (both a p-headed and an r-headed γ-clause)", S2, G2)] do
    let F := 4
    let fl := 4
    pl s!"{nm}: Γ = {Γ.map (fun F => F.toString)}, γ-head ◯r, defect = {defect S Γ}"
    let a0box := (itpA "p" S F 0 Γ A1.somehow).toString
    let a0 := (itpA "p" S F 0 Γ A1).toString
    let e0 := (itpE "p" S F 0 Γ).toString
    pl s!"   A@0(Γ,◯r) = {a0box}"
    pl s!"   A@0(Γ,r)  = {a0}"
    pl s!"   E@0(Γ)    = {e0}"
    for (cn, C) in [("z", prop "z"), ("s", prop "s"),
                    ("◯s", (prop "s").somehow), ("r", prop "r")] do
      pl s!"  C = {cn}"
      let (h, g) := boxedObligation S F fl Γ A1 B1 C
      report out "BOXED, unfiltered   " (cfgPlain 4000 12) h g
      report out "BOXED, infallible   " (cfgInf 4000 12) h g
      report out "BOXED, inf+confluent" (cfgInfConf 4000 12) h g
      let (h2, g2) := plainObligation S F fl Γ A1 B1 C
      report out "PLAIN (control)     " (cfgPlain 20000 12) h2 g2
  pl ""
  pl "== done =="

end SealProbe3

def main : IO Unit := SealProbe3.main
