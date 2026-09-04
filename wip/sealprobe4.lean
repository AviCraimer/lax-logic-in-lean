import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchNoFall
import LaxLogic.PLLSearchConf

/-!
# Which of the three routes closes the boxed γ-branch at the floor?

At target budget `1` the target table `⋁ itpAoth p S fl 1 Γ C` has exactly
three kinds of disjunct available to the boxed γ-branch, and the branch's
second hypothesis `A@1(B::Γ, C)` is *already* the second conjunct of the two
γ-disjuncts.  So the branch closes iff one of

    (a)  A@0(Γ, A)                       -- the plain γ-disjunct's first component
    (b)  ◯( E@0(Γ) ⇢ A@0(Γ, ◯A) )        -- the boxed one; `= ◯⊥` when starved
    (c)  the goal clause of C

is derivable from the three hypotheses

    E@2(Γ) ,   ◯( E@1(Γ) ⇢ A@1(Γ, ◯A) ) ,   A@1(B::Γ, C).

Asking the oracle for the whole obligation is a large search (`~` at
`findBudget` 200 000, `wip/sealprobe.lean`).  Asking it for each of (a), (b),
(c) separately is a *small* search, because each goal is tiny — and a `PROVED`
on any one of them is the route, written out.

`wip/sealprobe3.lean` showed why the probed families are uninformative: with
`Γ = [◯r ⊃ s]` the second hypothesis **collapses to an atom** (every
environment clause of `s::Γ` is guard-dead once `s` is in the context), so it
forces (c) or (a) for trivial reasons.  This file therefore adds a
configuration where the grown context still has a live clause:

    Γ = [◯r ⊃ s, ◯u ⊃ v],   A = r,   B = s

so `s::Γ` retains the live γ-clause `◯u ⊃ v`, and `A@1(s::Γ, C)` has genuine
environment disjuncts of its own.

Run: `lake build sealprobe4 && .lake/build/bin/sealprobe4`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe4

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

/-- One live γ-clause (the `wip/sealprobe3.lean` configuration). -/
def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "p", prop "z" }

def G1 : List PLLFormula := [gam "r" "s"]

/-- Two live γ-clauses, so the grown context `s::Γ` still has one. -/
def S2 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    gam "u" "v", (prop "u").somehow, prop "u", prop "v",
    prop "p", prop "z" }

def G2 : List PLLFormula := [gam "r" "s", gam "u" "v"]

/-- Two live γ-clauses, the second `p`-headed (so the space is not `p`-free
and the eliminated variable really occurs in a gated position). -/
def S3 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    gam "p" "v", (prop "p").somehow, prop "p", prop "v",
    prop "z" }

def G3 : List PLLFormula := [gam "r" "s", gam "p" "v"]

def cfg (bud : Nat) : Config := { findBudget := some bud, emitClosureCap := 0 }

def cfgInfConf (bud : Nat) : Config :=
  { findBudget := some bud, emitClosureCap := 0,
    accept := fun M => NoFall.infB M && RNC.confB M }

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
    | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > {cap})"
    | .unknown .allStagesMissed => "~ (all stages, none certified)")
  let _ ← IO.lazyPure (fun _ => s.length)
  let t1 ← IO.monoMsNow
  out.putStrLn s!"      {nm}: {s}  ({t1 - t0} ms)"
  out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== which route closes the boxed γ-branch at the floor? =="
  pl ""
  let F := 5
  let fl := 5
  let A := prop "r"
  let B := prop "s"
  for (nm, S, Γ) in [("S1: one live γ-clause", S1, G1),
                     ("S2: two live γ-clauses (◯u ⊃ v survives in s::Γ)", S2, G2),
                     ("S3: two live, the second p-headed", S3, G3)] do
    pl s!"{nm}   defect = {defect S Γ}"
    let a0 := itpA "p" S fl 0 Γ A
    let a0b := itpA "p" S fl 0 Γ A.somehow
    let e0 := itpE "p" S fl 0 Γ
    pl s!"   A@0(Γ,r)  = {a0.toString}"
    pl s!"   A@0(Γ,◯r) = {a0b.toString}"
    pl s!"   E@0(Γ)    = {e0.toString}"
    for (cn, C) in [("z", prop "z"), ("◯s", (prop "s").somehow)] do
      let hyps : List PLLFormula :=
        [ itpE "p" S (fl + 1) 2 Γ,
          (((itpE "p" S F 1 Γ).ifThen (itpA "p" S F 1 Γ A.somehow)).somehow),
          itpA "p" S F 1 (B :: Γ) C ]
      let w2 := (itpA "p" S F 1 (B :: Γ) C).weight
      pl s!"    C = {cn}   (2nd hyp weight {w2})"
      report out "(a) ⊢ A@0(Γ,r)          " (cfg 100000) hyps a0
      report out "(b) ⊢ ◯⊥                " (cfg 100000) hyps falsePLL.somehow
      report out "(b') ⊢ ◯(E@0(Γ)⇢A@0(Γ,◯r))" (cfg 100000) hyps
        ((e0.ifThen a0b).somehow)
      report out "(c) ⊢ goal clause of C  " (cfg 100000) hyps
        (orAll (itpAgoal "p" S fl 1 Γ C))
      report out "WHOLE obligation        " (cfg 100000) hyps
        (orAll (itpAoth "p" S fl 1 Γ C))
      report out "WHOLE, inf+conf filter  " (cfgInfConf 100000) hyps
        (orAll (itpAoth "p" S fl 1 Γ C))
  pl ""
  pl "== done =="

end SealProbe4

def main : IO Unit := SealProbe4.main
