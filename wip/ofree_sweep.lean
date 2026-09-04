import wip.oracle2
import LaxLogic.PLLSemUILaw
import LaxLogic.PLLSemUIOFree

/-!
# Sweep: do the semantic quantifiers agree with IPC on the ◯-free fragment?

For every ◯-free one-variable formula M (the RN({p}) fragment) up to
`MAXW`, the IPC/Pitts values are ⊤ (if ⊢ M) or ⊥ (if ⊬ M) on the
∀-side, and ⊥ (if M ⊢ ⊥) or ⊤ on the ∃-side.  Agreement with the PLL
semantic quantifiers means:

* ∀-side: no closed ladder rung ξ > ⊥ has [ξ] ⊢ M for underivable M
  (theorem-backed for both cones: `no_lower_bound_above_boxBot` /
  `no_lower_bound_above_negBoxBot`), and the certified value
  `allCandP p M` derives ⊥;
* ∃-side: no rung ξ < ⊤ has [M] ⊢ ξ for consistent M, and the
  certified value `exCandP p M` is derivable outright.

Any `!!ESCAPE` line = a machine-checked DISAGREEMENT with IPC (the
failure signal for climbing the free variables).  Section 0 checks the
two-cone coverage of the tested rungs (each rung should be derivable
from ◯⊥ or from ¬◯⊥ — the hypothesis of the conditional collapse
theorem `semAll_value_bot_of_cones`).

Run compiled: `lake build ofreesweep && .lake/build/bin/ofreesweep`.
-/

open PLLFormula PLLND PLLND.SemUI

namespace OFreeSweep

def pf (F : PLLFormula) : String := F.toString

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

def MAXW : Nat := 8

/-- The tested closed ladder rungs (strictly between ⊥ and ⊤). -/
def rungs : List (String × PLLFormula) :=
  [("◯⊥", gB), ("¬◯⊥", nF gB), ("¬¬◯⊥", nF (nF gB)),
   ("◯¬◯⊥", (nF gB).somehow), ("¬◯⊥∨◯⊥", (nF gB).or gB),
   ("¬¬◯⊥⊃◯⊥", (nF (nF gB)).ifThen gB),
   ("◯(¬◯⊥∨◯⊥)", ((nF gB).or gB).somehow)]

/-- ◯-free formula table by weight (the lawsweep builder without the
`somehow` clause — exactly the RN({p}) syntax). -/
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
    tbl := tbl.push acc
  return tbl

inductive V3 | yes | no | unk
def dec (Γ : List PLLFormula) (C : PLLFormula) : V3 :=
  match Oracle2.decide2 Γ C with
  | .proved => .yes
  | .refuted _ _ => .no
  | .unknown => .unk

def vs : V3 → String
  | .yes => "yes" | .no => "no" | .unk => "UNKNOWN"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl s!"== ◯-free fragment vs IPC: agreement sweep (weight ≤ {MAXW}) =="
  -- Section 0: two-cone coverage of the rungs
  pl "-- (0) cone coverage: rung ∈ cone(◯⊥) / cone(¬◯⊥)?"
  for (nm, ξ) in rungs do
    let c1 := dec [gB] ξ
    let c2 := dec [nF gB] ξ
    let covered := match c1, c2 with | .yes, _ => "covered" | _, .yes => "covered"
                                     | _, _ => "!!NOT COVERED"
    pl s!"   {nm}:  ◯⊥⊢ξ {vs c1}, ¬◯⊥⊢ξ {vs c2}  → {covered}"
  -- Section 1: the sweep
  let tbl := buildTable [pV, .falsePLL] MAXW
  let p := "p"
  let mut escapes := 0
  let mut unknowns := 0
  for wi in List.range MAXW do
    let w := wi + 1
    let rows := tbl[w]!
    let t0 ← IO.monoMsNow
    let mut nDer := 0
    let mut nBotOK := 0
    let mut nIncons := 0
    let mut nTopOK := 0
    let mut nRows := 0
    for M in rows do
      nRows := nRows + 1
      match dec [] M with
      | .yes =>
          -- ∀-value ⊤ (agreement automatic); ∃-side: consistent, value ⊤
          nDer := nDer + 1
      | .unk =>
          unknowns := unknowns + 1
          pl s!"   ?derivability UNKNOWN at {pf M}"
      | .no =>
          -- ∀-side: rungs as lower bounds (expect none)
          for (nm, ξ) in rungs do
            match dec [ξ] M with
            | .yes =>
                escapes := escapes + 1
                pl s!"   !!ESCAPE ∀: [{nm}] ⊢ {pf M}"
            | .unk =>
                unknowns := unknowns + 1
                pl s!"   ?∀-rung {nm} UNKNOWN at {pf M}"
            | .no => pure ()
          -- certified value derives ⊥?
          match dec [allCandP p M] .falsePLL with
          | .yes => nBotOK := nBotOK + 1
          | .no =>
              escapes := escapes + 1
              pl s!"   !!VALUE>⊥ ∀: allCandP ⊬ ⊥ at {pf M}"
          | .unk =>
              unknowns := unknowns + 1
              pl s!"   ?∀-value UNKNOWN at {pf M}"
      -- ∃-side, independent of derivability: consistent or not?
      match dec [M] .falsePLL with
      | .yes =>
          -- inconsistent: ∃-value ⊥; certified value must derive ⊥
          nIncons := nIncons + 1
          match dec [exCandP p M] .falsePLL with
          | .yes => pure ()
          | .no =>
              escapes := escapes + 1
              pl s!"   !!VALUE>⊥ ∃: exCandP ⊬ ⊥ at inconsistent {pf M}"
          | .unk =>
              unknowns := unknowns + 1
              pl s!"   ?∃-value(⊥) UNKNOWN at {pf M}"
      | .unk =>
          unknowns := unknowns + 1
          pl s!"   ?consistency UNKNOWN at {pf M}"
      | .no =>
          -- consistent: rungs as upper bounds (expect none), value ⊤
          for (nm, ξ) in rungs do
            match dec [M] ξ with
            | .yes =>
                escapes := escapes + 1
                pl s!"   !!ESCAPE ∃: [{pf M}] ⊢ {nm}"
            | .unk =>
                unknowns := unknowns + 1
                pl s!"   ?∃-rung {nm} UNKNOWN at {pf M}"
            | .no => pure ()
          match dec [] (exCandP p M) with
          | .yes => nTopOK := nTopOK + 1
          | .no =>
              escapes := escapes + 1
              pl s!"   !!VALUE<⊤ ∃: ⊬ exCandP at consistent {pf M}"
          | .unk =>
              unknowns := unknowns + 1
              pl s!"   ?∃-value(⊤) UNKNOWN at {pf M}"
    let t1 ← IO.monoMsNow
    pl s!"-- weight {w}: {nRows} rows, derivable {nDer}, ∀-value-⊥ certified {nBotOK}, inconsistent {nIncons}, ∃-value-⊤ certified {nTopOK}  ({t1 - t0} ms)"
  pl s!"== done: {escapes} escapes, {unknowns} unknowns =="

end OFreeSweep

def main : IO Unit := OFreeSweep.main
