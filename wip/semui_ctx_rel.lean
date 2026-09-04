import wip.semui_ctx_core

/-!
# Probe: the FRAME-RELATIVE commutation prediction (route doc §0(j))

PREDICTION under test (OPEN, recorded 2026-07-19 morning): computing
the IPC quantifier RELATIVE to the frame theory Θ = {α_w ⊃ ⊥ : w
fallible} restores constraint-commutation for ⊥-valued M **iff every
Rₘ-stable world of the generating model is fallible**.

Stable worlds:  chain2 {1} (fallible) — prediction: rel-comm HOLDS;
chain3 {0,2} with 0 NON-fallible — prediction: rel-comm FAILS;
fork {0,1,3} with 0,1 NON-fallible — prediction: rel-comm FAILS.

Rows: the two frozen-C failures `◯p⊃p` (value ⊥) and `◯(◯p⊃p)`
(value ◯⊥), plus the box-free control `p∨¬p` (value ⊥, commutes
frozen already).  Tower runs with Θ in the context and the space
enlarged to cover Θ; equivalence judged RELATIVE to Θ by the
fuel-free `G4cTm.find` oracle (sound on `true`).

Run compiled: `lake build ctxrel && .lake/build/bin/ctxrel`.
-/
open PLLFormula PLLND PLLND.Ctx

namespace CtxRel

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== frame-relative commutation: the fallibility prediction =="
  for (mname, m, expect) in
      [("chain2", mChain2, true), ("chain3", mChain3, false),
       ("fork", mFork, false)] do
    let C := c0Of m
    let Θ := falAxioms m
    let stabNF := ((worlds m).filter (stable m)).filter (fun w => !(m.fal w))
    pl s!"-- {mname}: C = {C.map (fun kl => (pf kl.1, pf kl.2))}, Θ = {Θ.map pf}, non-fallible stable worlds = {stabNF} (prediction rel-comm = {expect} for value-⊥ rows)"
    for (tname, M, vA) in targets do
      let T := nf (subC C M)
      let vA' := nf (subC C vA)
      if T.weight > WCAP then
        pl s!"   {tname}: SKIPPED (w={T.weight})"
      else
        let t0 ← IO.monoMsNow
        let A1 := towerARel Θ T 1
        let A2 := towerARel Θ T 2
        let stab := equivRel Θ A1 A2
        let comm := equivRel Θ A2 vA'
        let t1 ← IO.monoMsNow
        pl s!"   {tname}: Tw={T.weight} rel-stab={stab} rel-comm={comm} (A2={pf A2}, vA'={pf vA'})  ({t1 - t0} ms)"
  pl "== done =="

end CtxRel

def main : IO Unit := CtxRel.main
