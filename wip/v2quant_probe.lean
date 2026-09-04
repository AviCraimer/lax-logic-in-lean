import LaxLogic.PLLG4Dec
import LaxLogic.PLLSemUILayered
import LaxLogic.PLLSearch

/-!
# Cross-route probe: rank-bounded ∀p/∃p in the old one-variable harness

Matthew's experiment (2026-07-20): the syntactic route's sole open
lemma was H2 = `itpE_stab` (wip/onevar_descent_dev.lean) — the
∃-interpolant's budget-stabilisation, stuck at the ◯-goal truncation
disjunct where the budget sits in negative position, with the X9
recursion `E_{b+1} = ¬◯(E_b ⊃ A_b)` climbing one ◯/¬-alternation per
step.  The semantic route's wall (route doc §0(hh)) is the sharp
one-rank descent at dead-end i-successors: rank-n facts about
successors (¬◯⊥) are rank-(n+1) facts at the base (¬¬◯⊥).  Both live
on the ◯⊃-alternation tower of RN(◯,{}).

This probe plugs the NEW candidates — the Litak–Visser-style
rank-bounded fragment join and meet at one variable,

    ∀p.φ at rank r  :=  ⋁ { D variable-free, crank D ≤ r | D ⊢ φ }
    ∃p.φ at rank r  :=  ⋀ { D variable-free, crank D ≤ r | φ ⊢ D }

— into the old oracle harness and asks the old question of them:
do they STABILISE in r at the formula's own budget (2ν+1), and do the
stabilised values match the old route's frozen dictionary (X9:
A-side ◯(¬◯⊥ ⊃ ◯¬¬◯⊥), E-side ¬◯⊥)?

Method: generate equivalence-class representatives of RN(◯,{}) with
min-seen crank (canonise-as-you-go, oracle dedupe as in
wip/slick_probe.lean), then per battery formula print the r-table of
nf'd joins/meets with the classes newly entering at each rank (the
tower walk), plus oracle match tests.  Caveats: the oracle is
sound-on-true only; min-seen crank over-estimates true class crank,
so a class can enter the join late; the dictionary is truncated.

REVISION (2026-07-25, after the gap-row r=6 stall): one scan call
`entT D ◯(◯p⊃p)` was neither sweep-refutable on `defaultFrames` nor
quickly provable, so `G4cTm.findBounded` ground the full 40000-node
budget for hours.  Fixes: (i) the sweep battery is widened by the
F-free 3-chain and the gadget frames of wip/resid_probe.lean (a known
battery gap), transitively closed on intake per the `Frame` contract;
(ii) the SCAN path (per-class disjunct/conjunct tests) runs at
`findBudget := some 2000` and treats `unknown` as SKIP-this-disjunct,
with skips counted and reported; (iii) `findBudget := some 40000` is
kept ONLY for the final match tests; (iv) each dictionary class is
decided once per row and side (memoised), not once per rank.

Run: `lake build v2quant && .lake/build/bin/v2quant`.
-/

open PLLFormula

namespace PLLND
namespace V2Quant

open SemUI

/-! ## Oracle and sound simplifier (as in wip/onevar_probe.lean) -/

def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C
def entails (X Y : PLLFormula) : Bool := provF 4000 [X] Y
def equivO (X Y : PLLFormula) : Bool := entails X Y && entails Y X

/-! ## Extended sweep battery (the recorded battery-gap fix)

`Search.decide` runs the certified frame sweep BEFORE the bounded
positive searcher, so every extra refuting frame short-circuits a
potentially grinding `findBounded` call.  The battery here is
`defaultFrames` plus the F-free 3-chain plus the twelve gadget frames
of wip/resid_probe.lean.  The `Frame` contract assumes the relation
lists transitively closed, so we close on intake. -/

/-- Transitive closure of a frame's relations (as in
wip/resid_probe.lean). -/
def closeF (f : Search.Frame) : Search.Frame := Id.run do
  let mut ri := f.ri
  let mut rm := f.rm
  let mut changed := true
  while changed do
    changed := false
    for e in ri do
      for e' in ri do
        if e.2 == e'.1 && !(decide ((e.1, e'.2) ∈ ri)) && e.1 != e'.2 then
          ri := ri ++ [(e.1, e'.2)]
          changed := true
    for e in rm do
      for e' in rm do
        if e.2 == e'.1 && !(decide ((e.1, e'.2) ∈ rm)) && e.1 != e'.2 then
          rm := rm ++ [(e.1, e'.2)]
          changed := true
  return ⟨f.n, ri, rm, f.fall⟩

/-- The F-free 3-chain: `defaultFrames` item 6 without the fallible
top. -/
def chain3F : Search.Frame := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], []⟩

/-- The gadget frames from wip/resid_probe.lean (`extraFrames` there):
the 5-chains, the forks, the diamonds, the 4-chains with sparse `Rₘ`. -/
def residFrames : List Search.Frame :=
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

def scanFrames : List Search.Frame :=
  (Search.defaultFrames ++ [chain3F] ++ residFrames).map closeF

/-! ## Two-sided escalation (PLLSearch's countermodel-first oracle)

`search`'s `true` is sound at any fuel, so only FALSE verdicts need
escalation: `dec2` answers with a proof certificate, a countermodel
certificate, or an honest unknown.  Two budgets: `cfgScan` for the
per-class disjunct/conjunct tests and the climb comparisons (unknown =
skip, counted), `cfgFinal` only for the final match tests. -/

def cfgScan : Search.Config :=
  { frames := scanFrames, findBudget := some 2000, emitClosureCap := 0 }
def cfgFinal : Search.Config := { frames := scanFrames, findBudget := some 40000 }

/-- Scan cells forced to `unknown` WITHOUT calling the oracle, as
`(battery row index, dictionary class index)` pairs — the per-cell
10-minute kill rule made concrete.  Seed: the recorded gap-row r=6
stall cell, `D₆ = ◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥) ⊢ ◯(◯p⊃p)`, which still ground
past 10 minutes at findBudget 2000 (its per-node cost is the problem,
not the node count).  Both sides of the cell are skipped.

CORRECTION (2026-07-25, post-run): the grind was misattributed.  The
∀-side `D₆ ⊢ ◯(◯p⊃p)` is sweep-REFUTED at 0ms — the witness is
`defaultFrames` item 6 decorated p@{2}, so it was refutable even
before the battery was widened; `scanRow` computes both sides between
its two prints, and the hang sat in the ∃-side `◯(◯p⊃p) ⊢ D₆` (no
battery frame refutes it; sweep none).  The cell's verdicts: ∀-side
UNDERIVABLE, pinned axiom-clean in wip/d6_gap_cell.lean (so the
gap-row ∀-join stays ◯⊥ through r=9, no climb at r=6); ∃-side OPEN. -/
def skipCells : List (Nat × Nat) := [(3, 8)]

inductive V2 | proved | refuted | unknown
deriving Repr, DecidableEq

def dec2 (cfg : Search.Config) (Γ : List PLLFormula) (C : PLLFormula) : V2 :=
  match Search.decide cfg Γ C with
  | .proved _ => .proved
  | .refuted _ _ _ => .refuted
  | .unknown => .unknown

def vtag : V2 → String
  | .proved => "proved"
  | .refuted => "REFUTED(countermodel)"
  | .unknown => "unknown"

/-- Two-sided entailment verdict tag at the FINAL budget (match tests
only). -/
def tag2 (X Y : PLLFormula) : String := vtag (dec2 cfgFinal [X] Y)

/-- Two-sided entailment verdict tag at the scan budget. -/
def tagS (X Y : PLLFormula) : String := vtag (dec2 cfgScan [X] Y)

/-- Scan-budget entailment: `true` only on a proof certificate. -/
def entS (X Y : PLLFormula) : Bool := dec2 cfgScan [X] Y == .proved

def isTop (X : PLLFormula) : Bool := decide (X = truePLL)
def isBot (X : PLLFormula) : Bool := decide (X = falsePLL)

def simp : PLLFormula → PLLFormula
  | .and a b =>
      let a := simp a; let b := simp b
      if isBot a || isBot b then falsePLL
      else if isTop a then b else if isTop b then a
      else if a = b then a else .and a b
  | .or a b =>
      let a := simp a; let b := simp b
      if isTop a || isTop b then truePLL
      else if isBot a then b else if isBot b then a
      else if a = b then a else .or a b
  | .ifThen a b =>
      let a := simp a; let b := simp b
      if a = b then truePLL
      else if isTop a then b
      else if isTop b then truePLL
      else if isBot a then truePLL
      else .ifThen a b
  | .somehow a =>
      let a := simp a
      if isTop a then truePLL
      else match a with
        | .somehow c => .somehow c
        | _ => .somehow a
  | X => X

def norm : Nat → PLLFormula → PLLFormula
  | 0, X => X
  | n + 1, X => let Y := simp X; if Y = X then X else norm n Y
def nf (X : PLLFormula) : PLLFormula := norm 12 X

def sz : PLLFormula → Nat
  | .and a b => sz a + sz b + 1
  | .or a b => sz a + sz b + 1
  | .ifThen a b => sz a + sz b + 1
  | .somehow a => sz a + 1
  | _ => 1

/-! ## The RN(◯,{}) class dictionary, crank-stratified -/

def RMAX : Nat := 9
def SZMAX : Nat := 16
def DICTMAX : Nat := 40
def ROUNDS : Nat := 6

/-- Dedupe fuel — smaller than the verdict fuel: failing searches pay
full fuel, and the dedupe path is almost always failing. -/
def entailsD (X Y : PLLFormula) : Bool := provF 600 [X] Y
def equivD (X Y : PLLFormula) : Bool := entailsD X Y && entailsD Y X

/-- One generation round: close the dictionary under ◯, ⊃, ∧, ∨,
nf-simplify, cap by crank and size, dedupe first syntactically then by
oracle equivalence (keeping the MINIMUM seen crank per class). -/
def round (dict : List (PLLFormula × Nat)) : List (PLLFormula × Nat) := Id.run do
  let mut d := dict
  let mut cands : List (PLLFormula × Nat) := []
  for (D, c) in dict do
    cands := cands ++ [(nf D.somehow, c + 2)]
    for (D', c') in dict do
      cands := cands ++ [(nf (D.ifThen D'), max c c' + 1),
                         (nf (D.and D'), max c c'),
                         (nf (D.or D'), max c c')]
  for (X, c) in cands do
    if c ≤ RMAX && sz X ≤ SZMAX && d.length < DICTMAX then
      -- the nf'd form may have smaller crank than the bookkept bound
      let c := min c (crank X)
      match d.find? (fun (D, _) => D == X) with
      | some _ =>
          d := d.map fun (D, c₀) => if D == X then (D, min c₀ c) else (D, c₀)
      | none =>
          match d.find? (fun (D, _) => equivD D X) with
          | some (D₀, c₀) =>
              if c < c₀ then
                d := d.map fun (D, cc) => if D == D₀ then (D, c) else (D, cc)
          | none => d := d ++ [(X, c)]
  return d

def dict0 : List (PLLFormula × Nat) := [(falsePLL, 0), (truePLL, 0)]

def flush : IO Unit := do (← IO.getStdout).flush

/-- Build the dictionary with per-round progress (IO for flushing —
compiled stdout to a file is block-buffered). -/
def mkDictIO : IO (List (PLLFormula × Nat)) := do
  let mut d := dict0
  for i in List.range ROUNDS do
    d := round d
    IO.println s!"  [dict] round {i+1}: {d.length} classes"
    flush
  return d

/-! ## The rank-bounded quantifier candidates -/

def joinOf : List PLLFormula → PLLFormula
  | [] => falsePLL
  | [D] => D
  | D :: l => D.or (joinOf l)

def meetOf : List PLLFormula → PLLFormula
  | [] => truePLL
  | [D] => D
  | D :: l => D.and (meetOf l)

/-! ## Budget count ν (generator subformulas, their n_X) -/

def subs : PLLFormula → List PLLFormula
  | .and a b => .and a b :: (subs a ++ subs b)
  | .or a b => .or a b :: (subs a ++ subs b)
  | .ifThen a b => .ifThen a b :: (subs a ++ subs b)
  | .somehow a => .somehow a :: subs a
  | X => [X]

def nu (φ : PLLFormula) : Nat :=
  ((subs φ).eraseDups.filter (fun ψ => isBudget ψ)).length

/-! ## Battery -/

def op : PLLFormula := .prop "p"
def bb : PLLFormula := falsePLL.somehow                  -- ◯⊥
def nbb : PLLFormula := bb.ifThen falsePLL               -- ¬◯⊥
def nnbb : PLLFormula := nbb.ifThen falsePLL             -- ¬¬◯⊥
/-- The old route's frozen X9 A-value: ◯(¬◯⊥ ⊃ ◯¬¬◯⊥). -/
def a9 : PLLFormula := (nbb.ifThen nnbb.somehow).somehow

def battery : List (String × PLLFormula) :=
  [("◯p", op.somehow),
   ("¬p", op.ifThen falsePLL),
   ("p∨¬p", op.or (op.ifThen falsePLL)),
   ("◯(◯p⊃p) [GAP ROW]", (op.somehow.ifThen op).somehow),
   ("◯p⊃p", op.somehow.ifThen op),
   ("¬◯⊥⊃◯p [X9]", nbb.ifThen op.somehow),
   ("(◯p⊃p)⊃p", (op.somehow.ifThen op).ifThen op),
   ("◯◯p⊃p", op.somehow.somehow.ifThen op),
   ("◯¬p", (op.ifThen falsePLL).somehow),
   ("¬◯p", op.somehow.ifThen falsePLL)]

def pf (F : PLLFormula) : String := toString F

/-! ## Per-row memoised scan and table

Each dictionary class is decided ONCE per row and side (∀-side
`D ⊢ φ`, ∃-side `φ ⊢ D`) at the scan budget; the r-table is then a
crank filter over the memoised verdicts, so the previous per-rank
re-decides (the r=6 stall path) are gone.  `unknown` verdicts are
SKIPPED as disjuncts/conjuncts and counted. -/

/-- One row's scan: `(class, crank, ∀-side verdict, ∃-side verdict)`,
with live progress lines (each class printed before its decide, so a
grinding cell is identifiable from the log).  Cells in `skipCells` are
forced to `unknown` on both sides without calling the oracle. -/
def scanRow (rowIdx : Nat) (dict : List (PLLFormula × Nat)) (φ : PLLFormula) :
    IO (List (PLLFormula × Nat × V2 × V2)) := do
  let mut out := []
  let mut i := 0
  for (D, c) in dict do
    if skipCells.contains (rowIdx, i) then
      IO.println s!"    [scan] crank≤{c}  D = {pf D}"
      IO.println s!"      FORCED SKIP (10-min kill rule): both sides unknown"
      flush
      out := out ++ [(D, c, V2.unknown, V2.unknown)]
    else
      IO.println s!"    [scan] crank≤{c}  D = {pf D}"
      flush
      let t0 ← IO.monoMsNow
      let vA := dec2 cfgScan [D] φ
      let t1 ← IO.monoMsNow
      let vE := dec2 cfgScan [φ] D
      let t2 ← IO.monoMsNow
      IO.println s!"      ∀-side D⊢φ: {vtag vA} ({t1-t0}ms)   ∃-side φ⊢D: {vtag vE} ({t2-t1}ms)"
      flush
      out := out ++ [(D, c, vA, vE)]
    i := i + 1
  return out

/-- Print one battery row's r-table from its memoised scan; returns
`(∀-join at RMAX, ∃-meet at RMAX, ∀-side skips, ∃-side skips)`. -/
def printRow (rowIdx : Nat) (name : String) (φ : PLLFormula)
    (dict : List (PLLFormula × Nat)) :
    IO (PLLFormula × PLLFormula × Nat × Nat) := do
  let v := nu φ
  IO.println s!"--- {name}   (ν = {v}, 2ν+1 = {2*v+1}) ---"
  flush
  let scan ← scanRow rowIdx dict φ
  let skA := (scan.filter fun (_, _, vA, _) => vA == .unknown).length
  let skE := (scan.filter fun (_, _, _, vE) => vE == .unknown).length
  if skA + skE > 0 then
    IO.println s!"  [SKIPS] ∀-side unknown disjuncts skipped: {skA}, ∃-side: {skE}"
  let mut prevA : Option PLLFormula := none
  let mut prevE : Option PLLFormula := none
  let mut lastA := falsePLL
  let mut lastE := truePLL
  for r in List.range (RMAX + 1) do
    let A := nf (joinOf ((scan.filter fun (_, c, vA, _) =>
      c ≤ r && vA == .proved).map (·.1)))
    let E := nf (meetOf ((scan.filter fun (_, c, _, vE) =>
      c ≤ r && vE == .proved).map (·.1)))
    -- syntactic-identity shortcut first (the join only changes when a
    -- class enters); oracle climbs at the scan budget otherwise
    let sameA := match prevA with
      | some P =>
          if P == A then " (=)"
          else if entS P A && entS A P then " (=)"
          else s!" (CLIMB: new⊢old {tagS A P}, old⊢new {tagS P A})"
      | none => ""
    let sameE := match prevE with
      | some P =>
          if P == E then " (=)"
          else if entS P E && entS E P then " (=)"
          else s!" (CLIMB: new⊢old {tagS E P}, old⊢new {tagS P E})"
      | none => ""
    let enter := (scan.filter fun (_, c, vA, _) =>
      c == r && vA == .proved).map (fun (D, _, _, _) => pf D)
    IO.println s!"  r={r}: ∀={pf A}{sameA}  ∃={pf E}{sameE}  enters:{enter}"
    flush
    prevA := some A
    prevE := some E
    lastA := A
    lastE := E
  -- name the stabilised values against the dictionary (scan budget)
  match dict.find? (fun (D, _) => entS lastA D && entS D lastA) with
  | some (D, c) => IO.println s!"  ∀-value class at r={RMAX}: {pf D} (crank≤{c})"
  | none => IO.println s!"  ∀-value at r={RMAX}: no dictionary class matched at scan budget"
  match dict.find? (fun (D, _) => entS lastE D && entS D lastE) with
  | some (D, c) => IO.println s!"  ∃-value class at r={RMAX}: {pf D} (crank≤{c})"
  | none => IO.println s!"  ∃-value at r={RMAX}: no dictionary class matched at scan budget"
  flush
  return (lastA, lastE, skA, skE)

def mainLoop : IO Unit := do
  IO.println "=== cross-route probe: rank-bounded ∀p/∃p on the old harness ==="
  IO.println s!"(rev 2026-07-25: sweep battery {scanFrames.length} frames; scan findBudget 2000, unknown=skip; final match tests findBudget 40000)"
  flush
  let dict ← mkDictIO
  IO.println s!"dictionary: {dict.length} classes (crank ≤ {RMAX}, {ROUNDS} rounds)"
  for (D, c) in dict do
    IO.println s!"  class crank≤{c}: {pf D}"
  flush
  let mut aRMAX : List (String × PLLFormula) := []
  let mut skTotA := 0
  let mut skTotE := 0
  let mut ri := 0
  for (name, φ) in battery do
    let (A, _, skA, skE) ← printRow ri name φ dict
    aRMAX := aRMAX ++ [(name, A)]
    skTotA := skTotA + skA
    skTotE := skTotE + skE
    ri := ri + 1
  IO.println s!"[SKIP TOTALS] ∀-side: {skTotA}, ∃-side: {skTotE}"
  flush
  -- match tests against the old frozen values and the known laws
  -- (final budget 40000; the ∀-joins are the memoised r=RMAX values)
  let getA (n : String) : PLLFormula :=
    match aRMAX.find? (fun (m, _) => m == n) with
    | some (_, A) => A
    | none => falsePLL
  let aX9 := getA "¬◯⊥⊃◯p [X9]"
  IO.println "=== match tests (two-sided verdicts, findBudget 40000) ==="
  flush
  IO.println s!"∀p(X9) ⊢ old A-value ◯(¬◯⊥⊃◯¬¬◯⊥): {tag2 aX9 a9};  converse: {tag2 a9 aX9}"
  flush
  IO.println s!"∀p(X9) ⊢ ¬◯⊥⊃◯⊥: {tag2 aX9 (nbb.ifThen bb)};  converse: {tag2 (nbb.ifThen bb) aX9}"
  flush
  let aGap := getA "◯(◯p⊃p) [GAP ROW]"
  IO.println s!"∀p(GAP ROW) ⊢ ◯⊥: {tag2 aGap bb};  converse: {tag2 bb aGap}"
  flush
  let aBox := getA "◯p"
  IO.println s!"∀p(◯p) ⊢ ◯⊥: {tag2 aBox bb};  converse: {tag2 bb aBox}"
  flush
  let aTnd := getA "p∨¬p"
  IO.println s!"∀p(p∨¬p) ⊢ ⊥: {tag2 aTnd falsePLL}"
  IO.println "=== done ==="

end V2Quant
end PLLND

def main : IO Unit := PLLND.V2Quant.mainLoop
