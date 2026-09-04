import wip.oracle2
import LaxLogic.PLLSemUILaw

/-!
# Certified sweep of the per-instance reconstruction law

Tests the LIBRARY's law objects (`LaxLogic/PLLSemUILaw.lean`) — the
probe is faithful to the formal conjecture by construction:

    ∀-law:  poolAll p M  ⊢  M      (list form of [allCandP p M] ⊢ M)
    ∃-law:  M  ⊢  exCandP p M

over ALL raw one-variable formulas up to `MAXW`, with the certified
two-sided oracle: per row, battery countermodels FIRST (a REFUTED
verdict = a checkB-verified COUNTEREXAMPLE TO THE LAW — the prize),
then the fuel-free `G4cTm.find` on nf-forms (`true` sound).  The old
sweep (fueled, weight ≤ 7) is superseded: fuel-free, higher weight,
certified negatives.

Run compiled: `lake build lawsweep && .lake/build/bin/lawsweep`.
-/

open PLLFormula PLLND PLLND.SemUI

namespace LawSweep

def pf (F : PLLFormula) : String := F.toString

/-- Raw formula table by weight (from the original sweep). -/
def buildTable (leaves : List PLLFormula) (maxW : Nat) :
    Array (List PLLFormula) := Id.run do
  let mut tbl : Array (List PLLFormula) := #[[]]
  for n in List.range maxW do
    let w := n + 1
    let mut acc : List PLLFormula := []
    if w = 1 then
      acc := leaves
    else
      for i in List.range (w - 1) do
        let a := i
        let b := w - 2 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < tbl.size ∧ b < tbl.size then
          for x in tbl[a]! do
            for y in tbl[b]! do
              acc := (x.and y) :: acc
      for i in List.range w do
        let a := i
        let b := w - 1 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < tbl.size ∧ b < tbl.size then
          for x in tbl[a]! do
            for y in tbl[b]! do
              acc := (x.or y) :: acc
              acc := (x.ifThen y) :: acc
      if w ≥ 2 ∧ w - 1 < tbl.size then
        for x in tbl[w-1]! do
          acc := x.somehow :: acc
    tbl := tbl.push acc
  return tbl

def pV : PLLFormula := .prop "p"

def MAXW : Nat := 9

def showV : Oracle2.Verdict → String
  | .proved => "PROVED"
  | .refuted M w => s!"REFUTED (n={M.n} fall={M.fall} val={M.val} @w{w})"
  | .unknown => "UNKNOWN"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl s!"== per-instance reconstruction LAW sweep (weight ≤ {MAXW}, certified oracle) =="
  let tbl := buildTable [pV, .falsePLL] MAXW
  let p := "p"
  for wi in List.range MAXW do
    let w := wi + 1
    let rows := tbl[w]!
    let t0 ← IO.monoMsNow
    let mut nA := 0
    let mut nE := 0
    let mut bad := 0
    for M in rows do
      -- ∀-law, list form (battery-first inside decide2; certified both ways)
      let vA := Oracle2.decide2 (poolAll p M) M
      match vA with
      | .proved => nA := nA + 1
      | .refuted Mo wo =>
          bad := bad + 1
          pl s!"   !!∀-LAW REFUTED at {pf M}: model n={Mo.n} fall={Mo.fall} val={Mo.val} @w{wo}"
      | .unknown => pl s!"   ?∀ UNKNOWN at {pf M}"
      -- ∃-law
      let vE := Oracle2.decide2 [M] (exCandP p M)
      match vE with
      | .proved => nE := nE + 1
      | .refuted Mo wo =>
          bad := bad + 1
          pl s!"   !!∃-LAW REFUTED at {pf M}: model n={Mo.n} fall={Mo.fall} val={Mo.val} @w{wo}"
      | .unknown => pl s!"   ?∃ UNKNOWN at {pf M}"
    let t1 ← IO.monoMsNow
    pl s!"-- weight {w}: {rows.length} formulas, ∀-law {nA}/{rows.length}, ∃-law {nE}/{rows.length}, refuted {bad}  ({t1 - t0} ms)"
  pl "== done =="

end LawSweep

def main : IO Unit := LawSweep.main
