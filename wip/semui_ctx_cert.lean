import wip.oracle2
import wip.semui_ctx_core

/-!
# Certifier: upgrade `rel-comm=false` / `comm=false` to VERIFIED countermodels

`equivO`/`equivRel` returning `false` is tool-grade ("no proof found").
This runner recomputes the tower values for the failing rows of the
constraint-commutation probes and hands each direction of the failed
equivalence to `Oracle2.decide2` — a REFUTED verdict carries a finite
constraint model gated by the VERIFIED `FinCM.checkB`, turning the
α-top-residue prediction (route doc §0(j)) into certified
non-commutation.  Run compiled: `lake build ctxcert && .lake/build/bin/ctxcert`.
-/

open PLLFormula PLLND PLLND.Ctx CtxRel

namespace CtxCert

def showV : Oracle2.Verdict → String
  | .proved => "PROVED"
  | .refuted M w => s!"REFUTED (n={M.n} fall={M.fall} val={M.val} @w{w})"
  | .unknown => "UNKNOWN"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== certifier: failed commutation rows → verified countermodels =="
  for (mname, m) in [("fork", mFork), ("chain3", mChain3)] do
    let C := c0Of m
    let Θ := falAxioms m
    for (tname, M, vA) in targets do
      let T := nf (subC C M)
      let vA' := nf (subC C vA)
      if T.weight > 200 then
        pl s!"-- {mname} / {tname}: SKIPPED (w={T.weight})"
      else do
        let t0 ← IO.monoMsNow
        -- plain tower (frozen C) and relative tower (Θ in context)
        let Apl := nf (itpA "p" (pieceClosure T) TFUEL 2 [] T)
        let Arel := towerARel Θ T 2
        let t1 ← IO.monoMsNow
        pl s!"-- {mname} / {tname}: towers done ({t1 - t0} ms; plain w={Apl.weight}, rel w={Arel.weight})"
        -- the DECISIVE direction (tower value ⊢ translated value): the
        -- α-top-residue refutation lives here and the battery is instant
        let d1 := Oracle2.decide2 [Apl] vA'
        pl s!"   plain  A⊢v: {showV d1}"
        let r1 := Oracle2.decide2 (Arel :: Θ) vA'
        pl s!"   rel    A⊢v: {showV r1}"
        -- the sandwich lower bound (provable side): find grinds on very
        -- large inputs, so weight-gate it
        if Apl.weight ≤ 100 then
          pl s!"   plain  v⊢A: {showV (Oracle2.decide2 [vA'] Apl)}"
        else
          pl s!"   plain  v⊢A: SKIPPED-BIG (w={Apl.weight})"
        if Arel.weight ≤ 100 then
          pl s!"   rel    v⊢A: {showV (Oracle2.decide2 (vA' :: Θ) Arel)}"
        else
          pl s!"   rel    v⊢A: SKIPPED-BIG (w={Arel.weight})"
  pl "== done =="

end CtxCert

def main : IO Unit := CtxCert.main
