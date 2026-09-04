import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnEmbed

/-!
# ∃-side UI-witness hunt: the mechanical one-variable sweep

Enumerates every `φ` over `{⊥, p}` with `{∧, ∨, ⊃, ◯}` up to a size bound
and runs the filter cascade of the brief.  `⊤` is `⊥ ⊃ ⊥`, so it is in the
space (size 3).

Filters, in the order measured to be cheapest-first:

* `S`  syntax: `p` occurs, and `p` occurs NON-positively (some negative
  occurrence).  Free.
* `G1` `φ ⊢ gap 1` — positive engine (`G4cTm.findBounded`), budget `posBud`.
  A candidate is killed when the search space is EXHAUSTED with budget to
  spare (remainder > 0); a budget cutoff (remainder 0) is recorded as
  UNDECIDED-AT-BUDGET and the candidate is KEPT alive.
* `R`  rung dodge: `φ ⊬ rnSub n` for `n = 1..9`.  (Histogrammed: the least
  rung entailed is the near-miss signature.)
* `W`  `φ ⊬ w15 = gap 1 ∧ rnSub 6`, and `φ ⊬ w28 = gap 1 ∧ gap 2 ∧ rnSub 8`.
* `I`  self-instance dodge: `φ ⊬ φ[p↦⊤]`, `φ ⊬ φ[p↦◯⊥]`, `φ ⊬ φ[p↦rnSub 3]`.
* `G2`–`G5` `φ ⊢ gap k`.

NOTE on imports: `wip.gapWidth`/`wip.witness` cannot be imported by an
executable root — their closure contains `wip.rnc_probe`, which declares a
root-level `main`.  `gap`, `chainF`, `wC` are re-declared here verbatim and
are definitionally the repo's.

Run: `scripts/probe <sec> wsweep <maxSize> <posBudget> <mode>`
  mode = "sweep" (full cascade) | "count" (space only) | "hand" (designs).
-/

open PLLFormula PLLND PLLND.Search PLLND.RNEmbed PLLND.SemUI

namespace WSweep

/-! ## The objects -/

def chainF (k : Nat) : PLLFormula := (rnSub (2 * k + 1)).somehow
def gap (k : Nat) : PLLFormula := (chainF k).ifThen (rnSub (2 * k + 1))
def wC (k : Nat) : PLLFormula := (gap k).and (rnSub (2 * k + 4))

def P : PLLFormula := .prop pv
def Top : PLLFormula := PLLFormula.falsePLL.ifThen PLLFormula.falsePLL

def sz : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => 1 + sz a + sz b
  | .or a b => 1 + sz a + sz b
  | .ifThen a b => 1 + sz a + sz b
  | .somehow a => 1 + sz a

/-! ## Polarity of `p` -/

/-- `(positive occurrence?, negative occurrence?)` of `p` in the formula. -/
def pol : PLLFormula → Bool × Bool
  | .prop _ => (true, false)
  | .falsePLL => (false, false)
  | .and a b => let (pa, na) := pol a; let (pb, nb) := pol b; (pa || pb, na || nb)
  | .or a b => let (pa, na) := pol a; let (pb, nb) := pol b; (pa || pb, na || nb)
  | .ifThen a b => let (pa, na) := pol a; let (pb, nb) := pol b; (na || pb, pa || nb)
  | .somehow a => pol a

def occursP (F : PLLFormula) : Bool := (pol F).1 || (pol F).2
def negOccP (F : PLLFormula) : Bool := (pol F).2

/-! ## Enumeration by size -/

def layer0 : List PLLFormula := [PLLFormula.falsePLL, P]

/-- `buildLayers m` = array whose `i`-th entry is all formulas of size `i+1`. -/
partial def buildLayers (maxSize : Nat) : Array (List PLLFormula) := Id.run do
  let mut acc : Array (List PLLFormula) := #[layer0]
  for n in [2:maxSize+1] do
    let mut cur : List PLLFormula := []
    if n ≥ 2 then
      for A in acc[n-2]! do
        cur := A.somehow :: cur
    for i in [1:n-1] do
      let j := n - 1 - i
      if j ≥ 1 then
        for A in acc[i-1]! do
          for B in acc[j-1]! do
            cur := A.and B :: A.or B :: A.ifThen B :: cur
    acc := acc.push cur
  pure acc

/-! ## Search wrappers -/

def cfgN (b : Nat) : Config := { findBudget := some b, emitClosureCap := 26 }

inductive Res where
  | prov (nodes : Nat)
  | exhausted (nodes : Nat)
  | cutoff
  deriving Repr

/-- Positive engine only, with the budget-cutoff distinction kept. -/
def pos (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Res :=
  match G4cTm.findBounded b Γ C with
  | (some _, r) => .prov (b - r)
  | (none, 0) => .cutoff
  | (none, r) => .exhausted (b - r)

def isProv (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  match pos b Γ C with | .prov _ => true | _ => false

/-- Two-sided verdict (certified both ways), for the report. -/
def verd (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match settleWhy (cfgN b) Γ C with
  | .proved t => s!"PROVED(term {t.size})"
  | .refuted M w _ => s!"REFUTED(checkB n={M.n} w={w})"
  | .unknown (.budgetExhausted bb) => s!"UNDECIDED-AT-BUDGET {bb}"
  | .unknown (.closureTooBig s c) => s!"UNDECIDED(closure {s} > cap {c})"
  | .unknown .allStagesMissed => "UNDECIDED(all stages missed)"

/-! ## The dodge lists -/

def rungDodge : List Nat := [1,2,3,4,5,6,7,8,9]

def w15 : PLLFormula := (gap 1).and (rnSub 6)
def w28 : PLLFormula := (gap 1).and ((gap 2).and (rnSub 8))

def selfInst (F : PLLFormula) : List (String × PLLFormula) :=
  [("φ[p↦⊤]", substP pv Top F),
   ("φ[p↦◯⊥]", substP pv (PLLFormula.falsePLL.somehow) F),
   ("φ[p↦t3]", substP pv (rnSub 3) F)]

/-- The variable-free instances used by the THEOREM-INSTANCE filter `T`.
`wip/wlanding.lean`, `no_theorem_instance`: if `⊢ φ[p↦χ]` for a
variable-free `χ` then `φ` cannot entail every gap (it would make
`gap 2` a theorem).  Cheap and, in the 2026-08-04 data, the single most
productive filter after `S`. -/
def thmInst (F : PLLFormula) : List (String × PLLFormula) :=
  [("⊤", substP pv Top F),
   ("⊥", substP pv PLLFormula.falsePLL F),
   ("◯⊥", substP pv (PLLFormula.falsePLL.somehow) F),
   ("t3", substP pv (rnSub 3) F),
   ("t5", substP pv (rnSub 5) F),
   ("t6", substP pv (rnSub 6) F)]

/-- The `V` family of `wip/wlanding.lean`:
`Vf n = gap 1 ∧ … ∧ gap (n+1) ∧ rnSub (2n+4)`, PROVED to lie in `L`.
Lower than `w15`, hence a strictly stronger dodge filter. -/
def GmeetF : Nat → PLLFormula
  | 0 => gap 1
  | n + 1 => (GmeetF n).and (gap (n + 2))

def Vf (n : Nat) : PLLFormula := (GmeetF n).and (rnSub (2 * n + 4))

/-! ## The cascade bookkeeping -/

structure Stats where
  total : Nat := 0
  killSyn : Nat := 0
  killG1 : Nat := 0
  cutG1 : Nat := 0
  killG2 : Nat := 0
  killG3 : Nat := 0
  killRung : Nat := 0
  killW : Nat := 0
  killInst : Nat := 0
  survived : Nat := 0
  deriving Repr

/-! ## Hand designs (brief §(b)) -/

def T3 : PLLFormula := rnSub 3
def T5 : PLLFormula := rnSub 5
def T6 : PLLFormula := rnSub 6
def bp : PLLFormula := P.somehow
def neg (A : PLLFormula) : PLLFormula := A.ifThen PLLFormula.falsePLL

/-- The hand-designed candidates: collapse conjunct × ladder implication. -/
def hands : List (String × PLLFormula) :=
  [ ("h01  ◯p ⊃ p",                         bp.ifThen P)
  , ("h02  ◯p ⊃ ◯(p ∧ t3)   [phi1]",        bp.ifThen ((P.and T3).somehow))
  , ("h03  (◯p ⊃ p) ∧ (p ⊃ t3)",            (bp.ifThen P).and (P.ifThen T3))
  , ("h04  (◯p ⊃ p) ∧ (t3 ⊃ p)",            (bp.ifThen P).and (T3.ifThen P))
  , ("h05  (◯p ⊃ p) ∧ ◯(p ⊃ t3)",           (bp.ifThen P).and ((P.ifThen T3).somehow))
  , ("h06  (◯p ⊃ p) ∧ (p ⊃ ◯p)",            (bp.ifThen P).and (P.ifThen bp))
  , ("h07  gap1 ∧ ◯(p ⊃ t3)",               (gap 1).and ((P.ifThen T3).somehow))
  , ("h08  gap1 ∧ (p ⊃ t3)",                (gap 1).and (P.ifThen T3))
  , ("h09  gap1 ∧ (◯p ⊃ p)",                (gap 1).and (bp.ifThen P))
  , ("h10  gap1 ∧ (p ⊃ ◯t3)",               (gap 1).and (P.ifThen (T3.somehow)))
  , ("h11  ◯p ⊃ t3",                        bp.ifThen T3)
  , ("h12  (◯p ⊃ t3) ∧ (p ⊃ ◯p)",           (bp.ifThen T3).and (P.ifThen bp))
  , ("h13  (p ⊃ t3) ⊃ t3",                  (P.ifThen T3).ifThen T3)
  , ("h14  (p ⊃ t3) ⊃ p",                   (P.ifThen T3).ifThen P)
  , ("h15  ◯(p ∧ t3) ⊃ (p ∧ t3)",           ((P.and T3).somehow).ifThen (P.and T3))
  , ("h16  ¬¬p ⊃ p",                        (neg (neg P)).ifThen P)
  , ("h17  p ∨ ¬p   [t3 at p]",             P.or (neg P))
  , ("h18  gap1 ∧ t6   [= w15]",            (gap 1).and T6)
  , ("h19  gap1 ∧ (p ⊃ t6) ∧ (t6 ⊃ p)",     (gap 1).and ((P.ifThen T6).and (T6.ifThen P)))
  , ("h20  ◯(p ⊃ t3) ⊃ (◯p ⊃ p)",           ((P.ifThen T3).somehow).ifThen (bp.ifThen P))
  , ("h21  (◯p ⊃ p) ∧ (◯¬p ⊃ ¬p)",          (bp.ifThen P).and (((neg P).somehow).ifThen (neg P)))
  , ("h22  ◯(p ∨ ¬p) ⊃ (p ∨ ¬p)",           ((P.or (neg P)).somehow).ifThen (P.or (neg P)))
  , ("h23  (p ⊃ ◯p) ∧ (◯p ⊃ p) ∧ (t3 ⊃ p)", (P.ifThen bp).and ((bp.ifThen P).and (T3.ifThen P)))
  , ("h24  gap1 ∧ ◯((p ⊃ t3) ∧ (t3 ⊃ p))",  (gap 1).and (((P.ifThen T3).and (T3.ifThen P)).somehow))
  , ("h25  (p ⊃ t3) ⊃ (◯p ⊃ p)",            (P.ifThen T3).ifThen (bp.ifThen P))
  , ("h26  ◯p ⊃ (p ∨ t3)",                  bp.ifThen (P.or T3))
  , ("h27  (◯p ⊃ p) ∧ t6",                  (bp.ifThen P).and T6)
  , ("h28  (◯p ⊃ p) ∧ (p ⊃ t5) ∧ (t3 ⊃ p)", (bp.ifThen P).and ((P.ifThen T5).and (T3.ifThen P)))
  , ("h29  ◯(◯p ⊃ p) ⊃ (◯p ⊃ p)",           ((bp.ifThen P).somehow).ifThen (bp.ifThen P))
  , ("h30  (◯p ⊃ p) ∨ t3",                  (bp.ifThen P).or T3)
  , ("h31  ◯(p ⊃ ◯⊥) ⊃ (p ⊃ ◯⊥)",           ((P.ifThen (PLLFormula.falsePLL.somehow)).somehow).ifThen
                                              (P.ifThen (PLLFormula.falsePLL.somehow)))
  , ("h32  (◯p ⊃ p) ∧ (¬p ⊃ t3)",           (bp.ifThen P).and ((neg P).ifThen T3))
  , ("h33  (◯p ⊃ p) ∧ ((p ⊃ t3) ⊃ t3)",     (bp.ifThen P).and ((P.ifThen T3).ifThen T3))
  , ("h34  ((p ⊃ ◯⊥) ⊃ p) ⊃ p",             (((P.ifThen (PLLFormula.falsePLL.somehow)).ifThen P)).ifThen P)
  ]

/-! ## Reporting -/

def show2 (F : PLLFormula) : String := F.toString

/-- Which rungs `1..9` does `F` entail?  (positive engine, budget `b`) -/
def rungsHit (b : Nat) (F : PLLFormula) : List Nat :=
  rungDodge.filter (fun n => isProv b [F] (rnSub n))

/-- The positive engine's reading, with the budget-cutoff distinction. -/
def posStr (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match pos b Γ C with
  | .prov n => s!"PROVED (nodes {n})"
  | .exhausted n => s!"no proof, SEARCH SPACE EXHAUSTED (nodes {n})"
  | .cutoff => s!"UNDECIDED-AT-BUDGET {b}"

/-- Certified refutation attempt: battery + closure emitter, no proof search. -/
def refStr (cap : Nat) (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match refute? { findBudget := some 1, emitClosureCap := cap } Γ C with
  | some ⟨M, w, _⟩ => s!"REFUTED (checkB n={M.n} w={w})"
  | none => "no countermodel certificate"

def fullReport (pl : String → IO Unit) (b : Nat) (cap : Nat) (nm : String)
    (F : PLLFormula) : IO Unit := do
  pl s!"  φ = {nm}"
  pl s!"      = {show2 F}"
  for k in [1,2,3,4,5] do
    pl s!"     [hg]    φ ⊢ gap {k}   : {posStr b [F] (gap k)} | {refStr cap [F] (gap k)}"
  for n in rungDodge do
    pl s!"     [dodge] φ ⊢ rnSub {n} : {posStr b [F] (rnSub n)} | {refStr cap [F] (rnSub n)}"
  pl s!"     [dodge] φ ⊢ w15      : {posStr b [F] w15} | {refStr cap [F] w15}"
  pl s!"     [dodge] φ ⊢ w28      : {posStr b [F] w28} | {refStr cap [F] w28}"
  for (q, G) in selfInst F do
    pl s!"     [dodge] φ ⊢ {q}  : {posStr b [F] G} | {refStr cap [F] G}"
  pl s!"     [sane]  φ ⊢ ⊥       : {posStr b [F] PLLFormula.falsePLL}"

/-! ## The structured clause pool

The plain size-graded enumeration cannot reach the interesting region:
`rnSub 3` alone has 7 nodes, `gap 1` has 16, so every candidate that
mentions the ladder is far above any feasible size bound.  The pool
enumeration treats the rungs and `gap 1`/`gap 2` as ATOMS and sweeps
conjunctions (and a curated set of implications) of clauses drawn from a
pool of shapes: collapse clauses `◯A ⊃ A`, link clauses `p ⊃ tⱼ`,
`tⱼ ⊃ p`, boxed links `◯(p ⊃ tⱼ)`, and the propagation clause `p ⊃ ◯p`.
-/

def tt (j : Nat) : PLLFormula := rnSub j

/-- One clause = one candidate conjunct, with a printable name. -/
def clausePool : List (String × PLLFormula) := Id.run do
  let mut acc : List (String × PLLFormula) := []
  -- collapse clauses ◯A ⊃ A
  let colls : List (String × PLLFormula) :=
    [("p", P), ("¬p", neg P), ("p∨¬p", P.or (neg P)), ("¬¬p", neg (neg P))]
  for (nA, A) in colls do
    acc := (s!"(◯{nA} ⊃ {nA})", (A.somehow).ifThen A) :: acc
  -- link clauses with the ladder, j = 1..8
  for j in [1,2,3,4,5,6,7,8] do
    acc := (s!"(p ⊃ t{j})", P.ifThen (tt j)) :: acc
    acc := (s!"(t{j} ⊃ p)", (tt j).ifThen P) :: acc
    acc := (s!"(◯p ⊃ t{j})", (P.somehow).ifThen (tt j)) :: acc
    acc := (s!"(t{j} ⊃ ◯p)", (tt j).ifThen (P.somehow)) :: acc
    acc := (s!"(¬p ⊃ t{j})", (neg P).ifThen (tt j)) :: acc
    acc := (s!"(t{j} ⊃ ¬p)", (tt j).ifThen (neg P)) :: acc
    acc := (s!"◯(p ⊃ t{j})", (P.ifThen (tt j)).somehow) :: acc
    acc := (s!"◯(t{j} ⊃ p)", ((tt j).ifThen P).somehow) :: acc
    acc := (s!"((p ⊃ t{j}) ⊃ t{j})", (P.ifThen (tt j)).ifThen (tt j)) :: acc
    acc := (s!"((p ⊃ t{j}) ⊃ p)", (P.ifThen (tt j)).ifThen P) :: acc
    acc := (s!"(◯(p ∧ t{j}) ⊃ (p ∧ t{j}))",
            ((P.and (tt j)).somehow).ifThen (P.and (tt j))) :: acc
    acc := (s!"(◯(p ∨ t{j}) ⊃ (p ∨ t{j}))",
            ((P.or (tt j)).somehow).ifThen (P.or (tt j))) :: acc
    acc := (s!"(p ∨ t{j})", P.or (tt j)) :: acc
    acc := (s!"t{j}", tt j) :: acc
  -- propagation and the two known gaps
  acc := ("(p ⊃ ◯p)", P.ifThen (P.somehow)) :: acc
  acc := ("(◯p ⊃ p)", (P.somehow).ifThen P) :: acc
  acc := ("gap1", gap 1) :: acc
  acc := ("gap2", gap 2) :: acc
  pure acc.reverse

/-- The core sub-pool used for triples (keeps the triple space feasible). -/
def corePool : List (String × PLLFormula) :=
  clausePool.filter (fun q =>
    q.1 == "(◯p ⊃ p)" || q.1 == "(p ⊃ ◯p)" || q.1 == "gap1" || q.1 == "gap2" ||
    q.1 == "(◯(p∨¬p) ⊃ (p∨¬p))" || q.1 == "(◯¬p ⊃ ¬p)" ||
    q.1 == "(p ⊃ t3)" || q.1 == "(t3 ⊃ p)" || q.1 == "(p ⊃ t5)" ||
    q.1 == "(t5 ⊃ p)" || q.1 == "(p ⊃ t6)" || q.1 == "(t6 ⊃ p)" ||
    q.1 == "◯(p ⊃ t3)" || q.1 == "◯(t3 ⊃ p)" || q.1 == "◯(p ⊃ t5)" ||
    q.1 == "◯(t5 ⊃ p)" || q.1 == "(◯p ⊃ t3)" || q.1 == "(t3 ⊃ ◯p)" ||
    q.1 == "((p ⊃ t3) ⊃ p)" || q.1 == "((p ⊃ t3) ⊃ t3)" ||
    q.1 == "t3" || q.1 == "t5" || q.1 == "t6")

def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let pl (x : String) : IO Unit := do out.putStrLn x; out.flush
  let maxSize := (args.getD 0 "7").toNat!
  let posBud := (args.getD 1 "4000").toNat!
  let mode := args.getD 2 "sweep"
  pl s!"maxSize={maxSize} posBudget={posBud} mode={mode}"

  if mode == "pool" || mode == "poolp" then
    let pool := clausePool
    let core := corePool
    pl s!"== POOL: {pool.length} clauses, core {core.length} =="
    for (n, _) in core do pl s!"   core: {n}"
    -- build the candidate list: singles, pairs (pool), triples (core)
    let mut cands : List (String × PLLFormula) := []
    for c in pool do cands := c :: cands
    let pa := pool.toArray
    for i in [0:pa.size] do
      for j in [i+1:pa.size] do
        cands := (s!"{pa[i]!.1} ∧ {pa[j]!.1}", pa[i]!.2.and pa[j]!.2) :: cands
    let ca := core.toArray
    for i in [0:ca.size] do
      for j in [i+1:ca.size] do
        for k in [j+1:ca.size] do
          cands := (s!"{ca[i]!.1} ∧ {ca[j]!.1} ∧ {ca[k]!.1}",
                    ca[i]!.2.and (ca[j]!.2.and ca[k]!.2)) :: cands
    -- curated implications between core clauses
    for i in [0:ca.size] do
      for j in [0:ca.size] do
        if i != j then
          cands := (s!"{ca[i]!.1} ⊃ {ca[j]!.1}", ca[i]!.2.ifThen ca[j]!.2) :: cands
    pl s!"== candidate space: {cands.length} =="
    let t0 ← IO.monoMsNow
    let mut nSyn := 0
    let mut nThm := 0
    let mut nG1 := 0
    let mut cutG1 := 0
    let mut nRung := 0
    let mut nInst := 0
    let mut nW := 0
    let mut nG2 := 0
    let mut cutG2 := 0
    let mut nG3 := 0
    let mut cutG3 := 0
    -- S then T (theorem-instance): both cheap, both applied to everything
    let mut afterT : List (String × PLLFormula) := []
    for (nm, F) in cands do
      if !(occursP F && negOccP F) then
        nSyn := nSyn + 1
      else if (thmInst F).any (fun q => isProv posBud [] q.2) then
        nThm := nThm + 1
      else
        afterT := (nm, F) :: afterT
    let tT ← IO.monoMsNow
    pl s!"== after S and T: {afterT.length} alive (S killed {nSyn}, \
T killed {nThm}) [{tT - t0} ms] =="
    -- `keepCut = false` drops the G1 budget-cutoffs (reported as
    -- UNDECIDED-AT-BUDGET) so the rung stage runs only on candidates whose
    -- `φ ⊢ gap 1` carries a proof term.
    let keepCut := mode == "pool"
    let mut g1alive : List (String × PLLFormula) := []
    for (nm, F) in afterT do
      match pos posBud [F] (gap 1) with
      | .exhausted _ => nG1 := nG1 + 1
      | .cutoff =>
          cutG1 := cutG1 + 1
          if keepCut then g1alive := (nm, F) :: g1alive
      | .prov _ => g1alive := (nm, F) :: g1alive
    let t1 ← IO.monoMsNow
    pl s!"== after G1 (keepCutoffs={keepCut}): {g1alive.length} alive \
(G1 killed {nG1}, G1 cutoff {cutG1}) [{t1 - t0} ms] =="
    -- R  (short-circuiting: rnSub 1, 2, 3 are the cheapest and commonest kills)
    let mut rf : List (String × PLLFormula) := []
    for (nm, F) in g1alive do
      if !(rungDodge.any (fun n => isProv posBud [F] (rnSub n))) then
        rf := (nm, F) :: rf
      else nRung := nRung + 1
    let t2 ← IO.monoMsNow
    pl s!"== after R (rung dodge 1..9): {rf.length} alive (killed {nRung}) [{t2 - t0} ms] =="
    -- I then W
    let mut iw : List (String × PLLFormula) := []
    for (nm, F) in rf do
      if (selfInst F).any (fun q => isProv posBud [F] q.2) then nInst := nInst + 1
      else if isProv posBud [F] w15 || isProv posBud [F] w28 ||
              [0,1,2,3].any (fun n => isProv posBud [F] (Vf n)) then nW := nW + 1
      else iw := (nm, F) :: iw
    let t3 ← IO.monoMsNow
    pl s!"== after I (self-instance) and W/V (w15, w28, Vf 0..3): {iw.length} alive \
(I killed {nInst}, W/V killed {nW}) [{t3 - t0} ms] =="
    -- G2, G3
    let mut g2 : List (String × PLLFormula) := []
    for (nm, F) in iw do
      match pos posBud [F] (gap 2) with
      | .exhausted _ => nG2 := nG2 + 1
      | .cutoff => cutG2 := cutG2 + 1; g2 := (nm, F) :: g2
      | .prov _ => g2 := (nm, F) :: g2
    let t4 ← IO.monoMsNow
    pl s!"== after G2: {g2.length} alive (killed {nG2}, cutoff {cutG2}) [{t4 - t0} ms] =="
    let mut g3 : List (String × PLLFormula) := []
    for (nm, F) in g2 do
      match pos posBud [F] (gap 3) with
      | .exhausted _ => nG3 := nG3 + 1
      | .cutoff => cutG3 := cutG3 + 1; g3 := (nm, F) :: g3
      | .prov _ => g3 := (nm, F) :: g3
    let t5 ← IO.monoMsNow
    pl s!"== after G3: {g3.length} alive (killed {nG3}, cutoff {cutG3}) [{t5 - t0} ms] =="
    pl ""
    pl "== POOL KILL STATISTICS =="
    pl s!"  candidates        : {cands.length}"
    pl s!"  killed by S       : {nSyn}"
    pl s!"  killed by T (theorem instance) : {nThm}"
    pl s!"  killed by G1      : {nG1}    (cutoff {cutG1})"
    pl s!"  killed by R       : {nRung}"
    pl s!"  killed by I       : {nInst}"
    pl s!"  killed by W/V     : {nW}"
    pl s!"  killed by G2      : {nG2}    (cutoff {cutG2})"
    pl s!"  killed by G3      : {nG3}    (cutoff {cutG3})"
    pl s!"  SURVIVORS         : {g3.length}"
    pl ""
    pl s!"== NEAR-MISSES: passed G1 + R ({rf.length}) =="
    for (nm, F) in rf.take 200 do
      pl s!"  {nm}  | inst:{((selfInst F).filter (fun q => isProv posBud [F] q.2)).map (·.1)} \
w15:{isProv posBud [F] w15} gap2:{isProv posBud [F] (gap 2)} gap3:{isProv posBud [F] (gap 3)}"
    pl ""
    pl s!"== SURVIVORS: full certificates ({g3.length}) =="
    for (nm, F) in g3.take 20 do
      fullReport pl posBud 26 nm F
    pl "done"
    return

  if mode == "front" then
    -- The pool sweep's frontier: the only candidates that PROVED both
    -- `gap 1` and `gap 2` while dodging every rung and every self-instance.
    let front : List (String × PLLFormula) :=
      [ ("(p ⊃ t1) ∧ gap2", (P.ifThen (rnSub 1)).and (gap 2))
      , ("(t1 ⊃ ¬p) ∧ gap2", ((rnSub 1).ifThen (neg P)).and (gap 2))
      , ("(p ⊃ t2) ∧ gap2", (P.ifThen (rnSub 2)).and (gap 2))
      , ("(p ⊃ t3) ∧ gap2", (P.ifThen (rnSub 3)).and (gap 2))
      , ("gap2 alone", gap 2) ]
    pl "== FRONTIER: gap 2 and gap 3 at high budget =="
    for (nm, F) in front do
      pl s!"  φ = {nm}"
      for k in [1,2,3] do
        pl s!"     φ ⊢ gap {k} : {posStr posBud [F] (gap k)} | {refStr 30 [F] (gap k)}"
    pl "done"
    return

  if mode == "hand" then
    pl "== HAND DESIGNS: G1 + rung profile =="
    for (nm, F) in hands do
      let g1 := pos posBud [F] (gap 1)
      let tag := match g1 with
        | .prov n => s!"gap1 PROVED (nodes {n})"
        | .exhausted n => s!"gap1 NOT-PROVABLE by exhausted search (nodes {n})"
        | .cutoff => s!"gap1 UNDECIDED-AT-BUDGET {posBud}"
      let rr := rungsHit posBud F
      pl s!"{nm}  |  {tag}  |  rungs entailed: {rr}"
    pl ""
    pl "== full two-sided certificates: hand designs passing G1 with no rung =="
    for (nm, F) in hands do
      if isProv posBud [F] (gap 1) && (rungsHit posBud F).isEmpty then
        fullReport pl posBud 26 nm F
    pl "done"
    return

  let layers := buildLayers maxSize
  pl "== enumeration space =="
  let mut grand := 0
  let mut afterSyn := 0
  for i in [0:maxSize] do
    let l := layers[i]!
    let k := l.filter (fun F => occursP F && negOccP F)
    grand := grand + l.length
    afterSyn := afterSyn + k.length
    pl s!"  size {i+1}: {l.length} formulas, {k.length} survive syntax filter S"
  pl s!"  TOTAL {grand}; after S: {afterSyn}"
  if mode == "count" then return

  -- STAGE G1
  let mut st : Stats := {}
  let t0 ← IO.monoMsNow
  let mut alive : List (Nat × PLLFormula) := []
  let mut cutlist : List (String × PLLFormula) := []
  for i in [0:maxSize] do
    for F in layers[i]! do
      st := { st with total := st.total + 1 }
      if !(occursP F && negOccP F) then
        st := { st with killSyn := st.killSyn + 1 }
      else
        match pos posBud [F] (gap 1) with
        | .exhausted _ => st := { st with killG1 := st.killG1 + 1 }
        | .cutoff =>
            st := { st with cutG1 := st.cutG1 + 1 }
            cutlist := ("G1", F) :: cutlist
            alive := (i+1, F) :: alive
        | .prov _ => alive := (i+1, F) :: alive
    let t ← IO.monoMsNow
    pl s!"  [G1] through size {i+1}: {t - t0} ms, {st.killG1} killed, \
{st.cutG1} cutoff, {alive.length} alive"
  pl ""
  pl s!"== G1 survivors (⊢ gap 1, or undecided): {alive.length} =="

  -- STAGE R
  let mut hist : Array Nat := Array.replicate 11 0
  let mut rungFree : List (Nat × PLLFormula) := []
  for (s, F) in alive do
    let rr := rungsHit posBud F
    match rr.head? with
    | some n => hist := hist.set! n (hist[n]! + 1)
    | none =>
        hist := hist.set! 10 (hist[10]! + 1)
        rungFree := (s, F) :: rungFree
  st := { st with killRung := alive.length - rungFree.length }
  let tR ← IO.monoMsNow
  pl s!"== after R (rung dodge): {rungFree.length} alive [{tR - t0} ms] =="
  pl "   histogram of the LEAST rung entailed among the G1 survivors:"
  for n in rungDodge do
    if hist[n]! > 0 then pl s!"     least rung = rnSub {n} : {hist[n]!}"
  pl s!"     NO rung in 1..9        : {hist[10]!}"

  -- STAGE W and I
  let mut alive2 : List (Nat × PLLFormula) := []
  for (s, F) in rungFree do
    if isProv posBud [F] w15 || isProv posBud [F] w28 then
      st := { st with killW := st.killW + 1 }
    else if (selfInst F).any (fun q => isProv posBud [F] q.2) then
      st := { st with killInst := st.killInst + 1 }
    else
      alive2 := (s, F) :: alive2
  let tW ← IO.monoMsNow
  pl s!"== after W and I: {alive2.length} alive [{tW - t0} ms] =="

  -- STAGE G2..G5
  let mut fin : List (Nat × PLLFormula) := []
  for (s, F) in alive2 do
    let mut ok := true
    for k in [2,3,4,5] do
      if ok then
        match pos posBud [F] (gap k) with
        | .exhausted _ =>
            ok := false
            if k == 2 then st := { st with killG2 := st.killG2 + 1 }
            else if k == 3 then st := { st with killG3 := st.killG3 + 1 }
        | .cutoff => cutlist := (s!"G{k}", F) :: cutlist
        | .prov _ => pure ()
    if ok then fin := (s, F) :: fin
  st := { st with survived := fin.length }
  let t4 ← IO.monoMsNow

  pl ""
  pl s!"== KILL STATISTICS [{t4 - t0} ms total] =="
  pl s!"  total enumerated                        : {st.total}"
  pl s!"  killed by S  (p absent or only positive): {st.killSyn}"
  pl s!"  killed by G1 (⊬ gap 1, search exhausted): {st.killG1}  (cutoff {st.cutG1})"
  pl s!"  killed by R  (entails a rung 1..9)      : {st.killRung}"
  pl s!"  killed by W  (entails w15 or w28)       : {st.killW}"
  pl s!"  killed by I  (entails own vf instance)  : {st.killInst}"
  pl s!"  killed by G2 (⊬ gap 2)                  : {st.killG2}"
  pl s!"  killed by G3 (⊬ gap 3)                  : {st.killG3}"
  pl s!"  SURVIVORS                               : {st.survived}"
  pl ""
  if cutlist.length > 0 then
    pl s!"== budget cutoffs ({cutlist.length}) — UNDECIDED-AT-BUDGET {posBud} =="
    for (s, F) in cutlist.take 80 do
      pl s!"  [{s}] {show2 F}"
    pl ""
  pl s!"== NEAR-MISSES: passed G1 and the rung dodge ({rungFree.length}) =="
  for (s, F) in rungFree.take 120 do
    pl s!"  |{s}| {show2 F}   w15:{isProv posBud [F] w15} w28:{isProv posBud [F] w28} \
inst:{((selfInst F).filter (fun q => isProv posBud [F] q.2)).map (·.1)} \
gap2:{isProv posBud [F] (gap 2)} gap3:{isProv posBud [F] (gap 3)}"
  pl ""
  pl s!"== SURVIVORS: full two-sided certificates ({fin.length}) =="
  for (_, F) in fin.take 25 do
    fullReport pl posBud 26 (show2 F) F
  pl "done"

end WSweep

def main (args : List String) : IO Unit := WSweep.main args
