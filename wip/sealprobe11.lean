import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin

/-!
# Does the fresh-antecedent branch need the ∃-ascent?

`wip/sealprobe10.lean` found that at `C = r ⊃ s` the fresh-antecedent goal branch
closes in **9 nodes** at target budget `1`, reaching the target's own goal clause
in 8 — and it does so while the ∃-ascent instance the "natural" route would need
is itself undecided.  So the branch does not have to go through the ascent.

At `C = r ⊃ z` (consequent unrelated to the γ-clause) the same cell is `~`: the
two non-goal disjuncts are refuted, and the goal clause is undecided at
`findBudget` 20 000.  That is the cell that decides whether the second residual
branch really depends on the refuted ascent.

This probe pushes exactly that cell, and the corresponding ascent instance, at
`findBudget` 200 000, 2 000 000 and `none`.

Run: `lake build sealprobe11 && .lake/build/bin/sealprobe11`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe11

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
    | .proved t => s!"PROVED ({t.size} nodes)\n        term: {t.toLeanSrc}"
    | .refuted _ w _ => s!"REFUTED at world {w}"
    | .unknown (.budgetExhausted k) => s!"~ (cut at {k})"
    | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > {cap})"
    | .unknown .allStagesMissed => "ALL STAGES COMPLETE, NONE CERTIFIED")
  let _ ← IO.lazyPure (fun _ => s.length)
  let t1 ← IO.monoMsNow
  out.putStrLn s!"   {nm}: {s}  ({t1 - t0} ms)"
  out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== does the fresh-antecedent branch need the ascent? =="
  pl ""
  let C₁ := prop "r"
  let C₂ := prop "z"
  let C := C₁.ifThen C₂
  let F := 3
  let fl := 3
  let amb := itpE "p" S1 (fl + 1) 2 G1
  let src := (itpE "p" S1 F 2 (C₁ :: G1)).ifThen (itpA "p" S1 F 2 (C₁ :: G1) C₂)
  let tgt0 := (itpAoth "p" S1 fl 1 G1 C).getD 0 falsePLL
  pl s!"goal clause of `r ⊃ z` at Γ has weight {tgt0.weight}"
  for (bn, cf) in [("200k", ({ findBudget := some 200000,
                               emitClosureCap := 0 } : Config)),
                   ("2M", { findBudget := some 2000000, emitClosureCap := 0 }),
                   ("none", { findBudget := none, emitClosureCap := 0 })] do
    report out s!"branch ⊢ goal clause  [{bn}]" cf [amb, src] tgt0
  pl ""
  pl "the ascent instance the natural route would need:"
  for (bn, cf) in [("200k", ({ findBudget := some 200000,
                               emitClosureCap := 0 } : Config)),
                   ("2M", { findBudget := some 2000000, emitClosureCap := 0 })] do
    report out s!"E@2(r::Γ) from E@1(r::Γ) + ambient  [{bn}]" cf
      [amb, itpE "p" S1 F 1 (C₁ :: G1)] (itpE "p" S1 F 2 (C₁ :: G1))
  pl ""
  pl "== done =="

end SealProbe11

def main : IO Unit := SealProbe11.main
