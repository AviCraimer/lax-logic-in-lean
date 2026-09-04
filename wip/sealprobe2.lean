import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch

/-!
# The missing link in the boxed γ-branch

`wip/sealprobe.lean` asks the oracle for the whole branch obligation and gets
`~` on the boxed disjunct.  Hand computation on the chain2 configuration
(`Γ = [◯p ⊃ r]`, `A = p`, `B = r`) narrows it to one implication.  At target
budget `1` the target table for a goal `C` is

    ⋁ [ C-goal clause ,
        A@0(Γ,p) ∧ A@1(r::Γ,C) ,
        ◯( E@0(Γ) ⇢ A@0(Γ,◯p) ) ∧ A@1(r::Γ,C) ]

and there the second component `A@1(r::Γ,C)` is a hypothesis (the defect
tier supplies it).  The second disjunct is dead: `A@0(Γ,p) = ⊥`, because at
budget `0` the gated environment clause vanishes and the goal clause of the
*eliminated variable* `p` is empty at every budget.  So everything hinges on
the third disjunct's first component

    ◯( E@0(Γ) ⇢ A@0(Γ, ◯p) ).

The matching route from the source's boxed component would be
`box_remap_free` with the value conversion `A@1(Γ,◯p) ⊢ A@0(Γ,◯p)` — the
descent to budget `0` at a boxed goal, **certified false**.  But there is a
second route.  On this configuration `E@0(Γ) = ⊤` and `A@0(Γ,◯p) = ⊥`
(both starved), so the component *is* `◯⊥`; and every disjunct of
`A@1(Γ,◯p)` implies `◯⊥` — using `◯◯X ⊢ ◯X` for the boxed ones.

So the sequents worth deciding are, in increasing generality:

1. `A@1(Γ,◯p)  ⊢  ◯⊥`
2. `E@2(Γ), A@1(Γ,◯p)  ⊢  ◯( E@0(Γ) ⇢ A@0(Γ,◯p) )`
3. the same at budget `b+1 → b` for `b ≥ 1`, and at the `⊃⊃`-gated chain,
   to see whether the route is configuration-specific or general.

If (2) is derivable in general it replaces the refuted value conversion and
the boxed branch closes; if it is derivable only when the target component
starves, the branch needs a starvation case split — which is exactly the
classification `wip/starve.lean` was started for.

Run: `lake build sealprobe2 && .lake/build/bin/sealprobe2`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe2

def atomAt : Nat → PLLFormula
  | 0 => prop "p" | 1 => prop "r" | 2 => prop "s" | 3 => prop "t"
  | 4 => prop "u" | 5 => prop "v" | _ => prop "w"

def chainPieces (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i => ((atomAt i).somehow).ifThen (atomAt (i + 1)))

def chainClosure (n : Nat) : List PLLFormula :=
  (List.range (n + 1)).flatMap (fun i => [atomAt i, (atomAt i).somehow])

def goalPiece (n : Nat) : PLLFormula :=
  (((atomAt (n - 1)).somehow).ifThen (atomAt n)).ifThen (prop "z")

def chainList (n : Nat) : List PLLFormula :=
  (chainPieces n ++ chainClosure n ++ [goalPiece n, prop "z"]).dedup

def chainSpace (n : Nat) : Finset PLLFormula := (chainList n).toFinset

def cfgOf (bud : Nat) : Config := { findBudget := some bud, emitClosureCap := 0 }
def cfgExhaust : Config := { findBudget := none, emitClosureCap := 0 }

def verdictStr (cf : Config) (hyps : List PLLFormula) (goal : PLLFormula) :
    String :=
  match settleWhy cf hyps goal with
  | .proved _ => "PROVED"
  | .refuted _ _ _ => "REFUTED!"
  | .unknown (.budgetExhausted k) => s!"~ (search budget {k} exhausted)"
  | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > cap {cap})"
  | .unknown .allStagesMissed => "~ (every stage ran, none certified)"

def run (out : IO.FS.Stream) (nm : String) (cfs : List (String × Config))
    (hyps : List PLLFormula) (goal : PLLFormula) : IO Unit := do
  for (cn, cf) in cfs do
    let t0 ← IO.monoMsNow
    let v ← IO.lazyPure (fun _ => verdictStr cf hyps goal)
    let _ ← IO.lazyPure (fun _ => v.length)
    let t1 ← IO.monoMsNow
    out.putStrLn s!"    {nm} [{cn}]: {v}  (goal weight {goal.weight}, {t1 - t0} ms)"
    out.flush

def cheap : List (String × Config) := [("20k", cfgOf 20000), ("200k", cfgOf 200000)]

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== the missing link in the boxed γ-branch =="
  pl ""
  for n in [2, 3] do
    let S := chainSpace n
    let Γ := [chainPieces n |>.headD (prop "p")]
    let A := atomAt 0
    let F := n + 2
    pl s!"chain{n}: Γ = {Γ.map (fun F => F.toString)}, γ-head ◯{A.toString}"
    -- (0) is the target component literally ⊥ / ⊤ here?
    let a0box := (itpA "p" S F 0 Γ A.somehow).toString
    let e0 := (itpE "p" S F 0 Γ).toString
    let a0 := (itpA "p" S F 0 Γ A).toString
    pl s!"   A@0(Γ,◯A) = {a0box}"
    pl s!"   E@0(Γ)    = {e0}"
    pl s!"   A@0(Γ,A)  = {a0}"
    -- (1) the ◯⊥ collapse
    run out "(1) A@1(Γ,◯A) ⊢ ◯⊥" cheap
      [itpA "p" S F 1 Γ A.somehow] falsePLL.somehow
    -- (2) the replacement for the refuted value conversion
    for b in [1, 2] do
      run out s!"(2) E@{b+2}(Γ), A@{b}(Γ,◯A) ⊢ ◯(E@{b-1}(Γ) ⇢ A@{b-1}(Γ,◯A))"
        cheap
        [itpE "p" S (F + 1) (b + 2) Γ, itpA "p" S F b Γ A.somehow]
        (((itpE "p" S F (b - 1) Γ).ifThen
          (itpA "p" S F (b - 1) Γ A.somehow)).somehow)
    -- (3) the refuted value conversion itself, for contrast
    run out "(3) E@1(Γ), A@1(Γ,◯A) ⊢ A@0(Γ,◯A)  [known REFUTED]" cheap
      [itpE "p" S F 1 Γ, itpA "p" S F 1 Γ A.somehow]
      (itpA "p" S F 0 Γ A.somehow)
  pl ""
  pl "-- exhaustive search on the two smallest cells (findBudget = none) --"
  let S := chainSpace 2
  let Γ := [chainPieces 2 |>.headD (prop "p")]
  let A := atomAt 0
  run out "(1) chain2 exhaustive" [("none", cfgExhaust)]
    [itpA "p" S 4 1 Γ A.somehow] falsePLL.somehow
  pl ""
  pl "== done =="

end SealProbe2

def main : IO Unit := SealProbe2.main
