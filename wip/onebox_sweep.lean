import wip.oracle2
import LaxLogic.PLLSearch
import LaxLogic.PLLSemUI

/-!
# Sweep: the one-◯ two-variable fragment — values and tower coverage

The next climb rung after RN({p}): rows M over {p, q} with AT MOST ONE
◯, quantifying p.  Three questions, oracle-certified per row:

1. **Fragment preservation**: does the ∀p-value (resp. ∃p-value) of
   every row lie in the p-free one-◯ slice over q (the curated
   candidate list below)?  Signal: a row whose lower-bound set has NO
   maximum in the slice (`!!NO ∀-MAX`) — the value escapes the
   fragment, as ◯⊥ escaped the ◯-free fragment... which it did NOT;
   here the analogous escape would need a two-◯ or genuinely new
   value.
2. **The value table**: which slice elements occur as values (the
   observed sub-lattice of RN(◯,{q})).
3. **Tower coverage**: does the current transform stock — substitution
   instances over the slice + `lowT` + `sideT` — derive each row from
   its value's side (pool ⊢ M, pool ⊢ value)?  Certified failures
   (`!!POOL`) are the rows demanding NEW adjunction towers; their
   countermodels are the tower parameters.

Method: precompute the slice's ⊢-order matrix once; per row compute
the lower-bound set L(M) = {ξ ∈ slice : [ξ] ⊢ M} and its maximum
(∀-value candidate), dually the upper-bound set U(M) and its minimum
(∃-value candidate); then the pool tests on underivable rows.
Verdicts countermodel-first (`refute?` over an EXTENDED battery —
certified NO), then `prove?` (fuel-free find — fast exactly on
provables); residual UNKNOWNs reported honestly.  Bound sets are
computed with monotone pruning: a proof [ξ]⊢M propagates down the
slice order, a refutation propagates up — most cells never call the
oracle.

Run compiled: `lake build oneboxsweep && .lake/build/bin/oneboxsweep`.
-/

open PLLFormula PLLND PLLND.SemUI PLLND.Search

namespace OneBoxSweep

def pf (F : PLLFormula) : String := F.toString

def pV : PLLFormula := .prop "p"
def qV : PLLFormula := .prop "q"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

def MAXW : Nat := 5

/-- The p-free candidate slice: vars ⊆ {q}, at most one ◯. -/
def slice : List (String × PLLFormula) :=
  [("⊥", .falsePLL), ("⊤", truePLL), ("q", qV), ("¬q", nF qV),
   ("¬¬q", nF (nF qV)), ("q∨¬q", qV.or (nF qV)),
   ("¬¬q⊃q", (nF (nF qV)).ifThen qV),
   ("(¬q⊃q)⊃q", ((nF qV).ifThen qV).ifThen qV),
   ("◯⊥", gB), ("¬◯⊥", nF gB), ("¬¬◯⊥", nF (nF gB)),
   ("◯q", qV.somehow), ("¬◯q", nF qV.somehow), ("◯¬q", (nF qV).somehow),
   ("◯(q∨¬q)", (qV.or (nF qV)).somehow),
   ("◯(¬¬q⊃q)", ((nF (nF qV)).ifThen qV).somehow),
   ("q∧◯⊥", qV.and gB), ("q∨◯⊥", qV.or gB),
   ("q⊃◯⊥", qV.ifThen gB), ("¬q⊃◯⊥", (nF qV).ifThen gB),
   ("◯q⊃q", qV.somehow.ifThen qV), ("◯q∨¬q", qV.somehow.or (nF qV)),
   ("◯⊥∨¬q", gB.or (nF qV)), ("◯⊥⊃q", gB.ifThen qV)]

/-- Extra refutation frames beyond the default battery: 5-chains,
forks, diamonds, rigid chains — with and without fallible tops. -/
def extraFrames : List Frame :=
  [⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [], [4]⟩,
   ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [(3,4)], [4]⟩,
   ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [], []⟩,
   ⟨3, [(0,1),(0,2)], [], []⟩,
   ⟨3, [(0,1),(0,2)], [], [2]⟩,
   ⟨3, [(0,1),(0,2)], [(0,2)], [2]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [], [3]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [(1,3),(2,3)], [3]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [], []⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], [3]⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], []⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,3),(2,3)], [(0,1)], [3]⟩]

def cfg : Config := { frames := defaultFrames ++ extraFrames }

/-- The pool's substitution instances: the law-style generating set
(base rungs + the q-rungs), not the whole slice — 9 premises total
with the two transforms, the scale the search handles instantly. -/
def poolInst : List PLLFormula :=
  [.falsePLL, truePLL, gB, qV, nF qV, qV.somehow, nF gB]

inductive V3 | yes | no | unk

/-- Countermodel-first over the EXTENDED battery, then the
weight-gated `decide2`. -/
def decPure (Γ : List PLLFormula) (Cc : PLLFormula) : V3 :=
  match refute? cfg Γ Cc with
  | some _ => .no
  | none => match Oracle2.decide2 Γ Cc with
    | .proved => .yes
    | .refuted _ _ => .no
    | .unknown => .unk

/-- Timed oracle call: slow cells (> 1 s) are logged with their
sequent — silent grind becomes visible data.  The `if` on the result
between the timestamps is the IO barrier forcing evaluation. -/
def decT (pl : String → IO Unit) (tag : Unit → String)
    (Γ : List PLLFormula) (Cc : PLLFormula) : IO V3 := do
  let t0 ← IO.monoMsNow
  let r := decPure Γ Cc
  if (match r with | .unk => true | _ => false) then
    pure ()
  let t1 ← IO.monoMsNow
  if t1 - t0 > 1000 then
    pl s!"   [slow {t1 - t0} ms] {tag ()}"
  return r

def isY : V3 → Bool | .yes => true | _ => false

/-- Two-bucket formula table: `tbl[b][w]` = formulas of weight `w`
with exactly `b` occurrences of ◯ (b ∈ {0, 1}). -/
def buildTable2 (leaves : List PLLFormula) (maxW : Nat) :
    Array (Array (List PLLFormula)) := Id.run do
  let mut t0 : Array (List PLLFormula) := #[[]]
  let mut t1 : Array (List PLLFormula) := #[[]]
  for n in List.range maxW do
    let w := n + 1
    let mut acc0 : List PLLFormula := []
    let mut acc1 : List PLLFormula := []
    if w = 1 then
      acc0 := leaves
    else
      -- binary connectives: and (a+b = w-2), or/ifThen (a+b = w-1)
      for i in List.range (w - 1) do
        let a := i
        let b := w - 2 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < t0.size ∧ b < t0.size then
          for x in t0[a]! do
            for y in t0[b]! do
              acc0 := (x.and y) :: acc0
          for x in t0[a]! do
            for y in t1[b]! do
              acc1 := (x.and y) :: acc1
          for x in t1[a]! do
            for y in t0[b]! do
              acc1 := (x.and y) :: acc1
      for i in List.range w do
        let a := i
        let b := w - 1 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < t0.size ∧ b < t0.size then
          for x in t0[a]! do
            for y in t0[b]! do
              acc0 := (x.or y) :: acc0
              acc0 := (x.ifThen y) :: acc0
          for x in t0[a]! do
            for y in t1[b]! do
              acc1 := (x.or y) :: acc1
              acc1 := (x.ifThen y) :: acc1
          for x in t1[a]! do
            for y in t0[b]! do
              acc1 := (x.or y) :: acc1
              acc1 := (x.ifThen y) :: acc1
      -- somehow: lifts bucket 0 to bucket 1
      if w ≥ 2 ∧ w - 1 < t0.size then
        for x in t0[w-1]! do
          acc1 := x.somehow :: acc1
    t0 := t0.push acc0
    t1 := t1.push acc1
  return #[t0, t1]

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl s!"== one-◯ two-variable fragment: values + tower coverage (weight ≤ {MAXW}, slice {slice.length}) =="
  -- (0) the slice ⊢-order matrix
  let t0 ← IO.monoMsNow
  let n := slice.length
  let sliceA := slice.toArray
  let mut mat : Array (Array Bool) := #[]
  for i in List.range n do
    let mut row : Array Bool := #[]
    for j in List.range n do
      row := row.push (isY (← decT pl
        (fun _ => s!"matrix [{(sliceA[i]!).1}] ⊢ {(sliceA[j]!).1}")
        [(sliceA[i]!).2] (sliceA[j]!).2))
    mat := mat.push row
  let t1 ← IO.monoMsNow
  pl s!"-- (0) order matrix ({n}×{n}) in {t1 - t0} ms"
  -- (1) the sweep
  let tbl := buildTable2 [pV, qV, .falsePLL] MAXW
  let mut histA : Array Nat := Array.replicate n 0
  let mut histE : Array Nat := Array.replicate n 0
  let mut noMaxA := 0
  let mut noMinE := 0
  let mut poolFailM := 0
  let mut poolFailV := 0
  let mut unknowns := 0
  for wi in List.range MAXW do
    let w := wi + 1
    let rows := (tbl[0]!)[w]! ++ (tbl[1]!)[w]!
    let tw0 ← IO.monoMsNow
    let mut nDer := 0
    let mut nRows := 0
    let mut nPfree := 0
    for M in rows do
      if !(decide ("p" ∈ M.atoms)) then
        nPfree := nPfree + 1
      else
      nRows := nRows + 1
      -- lower bounds, with monotone pruning
      let mut lbo : Array (Option Bool) := Array.replicate n none
      for i in List.range n do
        if (lbo[i]!).isNone then
          match (← decT pl (fun _ => s!"[{(sliceA[i]!).1}] ⊢ {pf M}") [(sliceA[i]!).2] M) with
          | .yes =>
              lbo := lbo.set! i (some true)
              for j in List.range n do
                if (mat[j]!)[i]! ∧ (lbo[j]!).isNone then
                  lbo := lbo.set! j (some true)
          | .no =>
              lbo := lbo.set! i (some false)
              for j in List.range n do
                if (mat[i]!)[j]! ∧ (lbo[j]!).isNone then
                  lbo := lbo.set! j (some false)
          | .unk =>
              lbo := lbo.set! i (some false)
              unknowns := unknowns + 1
      let lb : Array Bool := lbo.map (fun o => o.getD false)
      -- upper bounds, with monotone pruning
      let mut ubo : Array (Option Bool) := Array.replicate n none
      for i in List.range n do
        if (ubo[i]!).isNone then
          match (← decT pl (fun _ => s!"[{pf M}] ⊢ {(sliceA[i]!).1}") [M] (sliceA[i]!).2) with
          | .yes =>
              ubo := ubo.set! i (some true)
              for j in List.range n do
                if (mat[i]!)[j]! ∧ (ubo[j]!).isNone then
                  ubo := ubo.set! j (some true)
          | .no =>
              ubo := ubo.set! i (some false)
              for j in List.range n do
                if (mat[j]!)[i]! ∧ (ubo[j]!).isNone then
                  ubo := ubo.set! j (some false)
          | .unk =>
              ubo := ubo.set! i (some false)
              unknowns := unknowns + 1
      let ub : Array Bool := ubo.map (fun o => o.getD false)
      let der := lb[1]!  -- [⊤] ⊢ M
      if der then nDer := nDer + 1
      -- ∀-value: maximum of the lower-bound set
      let lidx := (List.range n).filter (fun i => lb[i]!)
      let maxima := lidx.filter (fun i => lidx.all (fun j => (mat[j]!)[i]!))
      match maxima with
      | [] =>
          noMaxA := noMaxA + 1
          pl s!"   !!NO ∀-MAX at {pf M}: lowers {lidx.map (fun i => (sliceA[i]!).1)}"
      | m :: _ =>
          histA := histA.set! m (histA[m]! + 1)
          if m ≥ 11 then
            pl s!"   ∀-value {(sliceA[m]!).1} : {pf M}"
          -- pool test on underivable rows
          if !der then
            let pool := lowT "p" M :: sideT "p" M ::
              poolInst.map (fun c => substP "p" c M)
            match (← decT pl (fun _ => s!"pool ⊢ {pf M}") pool M) with
            | .yes => pure ()
            | .no =>
                poolFailM := poolFailM + 1
                pl s!"   !!POOL⊬M at {pf M} (∀-value {(sliceA[m]!).1})"
            | .unk =>
                unknowns := unknowns + 1
                pl s!"   ?POOL-M UNKNOWN at {pf M}"
            match (← decT pl (fun _ => s!"pool ⊢ value {(sliceA[m]!).1} at {pf M}") pool (sliceA[m]!).2) with
            | .yes => pure ()
            | .no =>
                poolFailV := poolFailV + 1
                pl s!"   !!POOL⊬VALUE at {pf M} (∀-value {(sliceA[m]!).1})"
            | .unk =>
                unknowns := unknowns + 1
                pl s!"   ?POOL-V UNKNOWN at {pf M}"
      -- ∃-value: minimum of the upper-bound set
      let uidx := (List.range n).filter (fun i => ub[i]!)
      let minima := uidx.filter (fun i => uidx.all (fun j => (mat[i]!)[j]!))
      match minima with
      | [] =>
          noMinE := noMinE + 1
          pl s!"   !!NO ∃-MIN at {pf M}: uppers {uidx.map (fun i => (sliceA[i]!).1)}"
      | m :: _ =>
          histE := histE.set! m (histE[m]! + 1)
    let tw1 ← IO.monoMsNow
    pl s!"-- weight {w}: {nRows} rows + {nPfree} p-free skipped ({(tbl[1]!)[w]!.length} with ◯), derivable {nDer}  ({tw1 - tw0} ms)"
  pl "== ∀-value histogram =="
  for i in List.range n do
    if histA[i]! > 0 then
      pl s!"   {(sliceA[i]!).1}: {histA[i]!}"
  pl "== ∃-value histogram =="
  for i in List.range n do
    if histE[i]! > 0 then
      pl s!"   {(sliceA[i]!).1}: {histE[i]!}"
  pl s!"== done: no-∀-max {noMaxA}, no-∃-min {noMinE}, pool⊬M {poolFailM}, pool⊬value {poolFailV}, unknowns {unknowns} =="

end OneBoxSweep

def main : IO Unit := OneBoxSweep.main
