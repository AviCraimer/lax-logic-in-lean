import LaxLogic.PLLG4Term
import LaxLogic.PLLSemUILayered
import LaxLogic.PLLG4Dec
import LaxLogic.PLLSearch
import wip.rnDict

/-!
# Generator for `wip/rnDict.lean` (discover-then-pin)

Runs the fuel-free-but-budgeted G4iLL″ backward searcher
(`G4cTm.findBounded`) OFFLINE on every nontrivial cell of the
RN(◯,{}) closure tables (15 representatives; ∧/∨/⊃ tables and the ◯
column), classifies each combination against the dictionary, and
PRINTS the certified instantiation `rnDict15 : RNDict` as Lean source
— every emitted `G4cTm` proof term is then checked by the kernel when
`wip/rnDict.lean` is elaborated.  Trivial cells (units, idempotence,
commutative mirrors, syntactic coincidences) are discharged by the
generic lemmas of `wip/rnDictBase.lean` instead of emitted terms.

Run: `lake build rnDictGen && .lake/build/bin/rnDictGen > wip/rnDict.lean`
(progress goes to stderr).
-/

open PLLFormula PLLND PLLND.SemUI

namespace RNGen

/-! ## The fifteen representatives (probe order, wip/v2quant_out3.txt) -/

def Fq : PLLFormula := .falsePLL
def Nq (X : PLLFormula) : PLLFormula := X.ifThen Fq
def Bq (X : PLLFormula) : PLLFormula := X.somehow

def reps : List PLLFormula :=
  [Fq,                                                   -- 0  ⊥
   Nq Fq,                                                -- 1  ⊤
   Bq Fq,                                                -- 2  ◯⊥
   Nq (Bq Fq),                                           -- 3  ¬◯⊥
   (Bq Fq).or (Nq (Bq Fq)),                              -- 4
   Bq (Nq (Bq Fq)),                                      -- 5
   Nq (Nq (Bq Fq)),                                      -- 6
   (Nq (Bq Fq)).or (Nq (Nq (Bq Fq))),                    -- 7
   (Bq (Nq (Bq Fq))).ifThen ((Bq Fq).or (Nq (Bq Fq))),  -- 8
   (Bq (Nq (Bq Fq))).or (Nq (Nq (Bq Fq))),               -- 9
   (Nq (Nq (Bq Fq))).ifThen (Bq Fq),                     -- 10
   (Nq (Nq (Bq Fq))).or ((Nq (Nq (Bq Fq))).ifThen (Bq Fq)), -- 11
   Bq ((Nq (Bq Fq)).or (Nq (Nq (Bq Fq)))),               -- 12
   Bq ((Bq (Nq (Bq Fq))).ifThen ((Bq Fq).or (Nq (Bq Fq)))), -- 13
   ((Nq (Nq (Bq Fq))).ifThen (Bq Fq)).ifThen (Bq (Nq (Bq Fq)))] -- 14

def repIdx? (X : PLLFormula) : Option Nat := reps.findIdx? (· = X)

def budget : Nat := 400000

/-! ## Emission: Lean source for formulas, memberships, proof terms -/

/-- Print a formula, naming representatives with index < `n` as `q<i>`. -/
partial def ppFN (n : Nat) (X : PLLFormula) : String :=
  match (repIdx? X).filter (· < n) with
  | some i => s!"q{i}"
  | none =>
    match X with
    | .prop s => s!"(.prop \"{s}\")"
    | .falsePLL => ".falsePLL"
    | .and a b => s!"(.and {ppFN n a} {ppFN n b})"
    | .or a b => s!"(.or {ppFN n a} {ppFN n b})"
    | .ifThen a b => s!"(.ifThen {ppFN n a} {ppFN n b})"
    | .somehow a => s!"(.somehow {ppFN n a})"

def ppF (X : PLLFormula) : String := ppFN 15 X

def memIdx (X : PLLFormula) : List PLLFormula → Nat
  | [] => 0
  | Y :: R => if X = Y then 0 else memIdx X R + 1

def memStrN : Nat → String
  | 0 => "(.head _)"
  | n + 1 => s!"(.tail _ {memStrN n})"

def memS (X : PLLFormula) (Γ : List PLLFormula) : String :=
  memStrN (memIdx X Γ)

/-- Emit a `G4cTm` proof term as elaborable Lean source.  Left-rule
formula implicits are passed as named arguments (they are not
determined by the conclusion); membership proofs are `.head`/`.tail`
chains computed from the tracked context. -/
partial def emitTm : {Γ : List PLLFormula} → {C : PLLFormula} → G4cTm Γ C → String
  | _, _, @G4cTm.init Γ a _ => s!"(.init {memS (.prop a) Γ})"
  | _, _, @G4cTm.botL Γ _ _ => s!"(.botL {memS .falsePLL Γ})"
  | _, _, @G4cTm.andR _ _ _ t1 t2 => s!"(.andR {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.orR1 _ _ _ t => s!"(.orR1 {emitTm t})"
  | _, _, @G4cTm.orR2 _ _ _ t => s!"(.orR2 {emitTm t})"
  | _, _, @G4cTm.impR _ _ _ t => s!"(.impR {emitTm t})"
  | _, _, @G4cTm.laxR _ _ t => s!"(.laxR {emitTm t})"
  | _, _, @G4cTm.laxL Γ A _ _ t =>
      s!"(.laxL (A := {ppF A}) {memS A.somehow Γ} {emitTm t})"
  | _, _, @G4cTm.andL Γ A B _ _ t =>
      s!"(.andL (A := {ppF A}) (B := {ppF B}) {memS (A.and B) Γ} {emitTm t})"
  | _, _, @G4cTm.orL Γ A B _ _ t1 t2 =>
      s!"(.orL (A := {ppF A}) (B := {ppF B}) {memS (A.or B) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLProp Γ a B _ _ _ t =>
      s!"(.impLProp (a := \"{a}\") (B := {ppF B}) {memS ((PLLFormula.prop a).ifThen B) Γ} {memS (.prop a) Γ} {emitTm t})"
  | _, _, @G4cTm.impLAnd Γ A B D _ _ t =>
      s!"(.impLAnd (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.and B).ifThen D) Γ} {emitTm t})"
  | _, _, @G4cTm.impLOr Γ A B D _ _ t =>
      s!"(.impLOr (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.or B).ifThen D) Γ} {emitTm t})"
  | _, _, @G4cTm.impLImp Γ A B D _ _ t1 t2 =>
      s!"(.impLImp (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.ifThen B).ifThen D) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLLax Γ A B _ _ t1 t2 =>
      s!"(.impLLax (A := {ppF A}) (B := {ppF B}) {memS (A.somehow.ifThen B) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLLaxLax Γ A B X _ _ _ t1 t2 =>
      s!"(.impLLaxLax (A := {ppF A}) (B := {ppF B}) (X := {ppF X}) {memS (A.somehow.ifThen B) Γ} {memS X.somehow Γ} {emitTm t1} {emitTm t2})"

/-! ## Classification against the dictionary -/

/-- Find the representative interderivable with `X`, returning its
index and the two emitted proof-term sources
(`[X] ⊢ rep k`, `[rep k] ⊢ X`).  A double success is self-certifying;
the classes are pairwise distinct, so at most one `k` can succeed. -/
def classifyTm (X : PLLFormula) : Option (Nat × String × String) := Id.run do
  for k in List.range 15 do
    let D := reps.getD k .falsePLL
    match (G4cTm.findBounded budget [X] D).1 with
    | none => pure ()
    | some t1 =>
      match (G4cTm.findBounded budget [D] X).1 with
      | none => pure ()
      | some t2 =>
          return some (k, s!"(ofG4 {emitTm t1})", s!"(ofG4 {emitTm t2})")
  return none

/-! ## Second oracle: the certified-complete `G4s` searcher + the
countermodel battery (v2quant's widened sweep), for diagnosing cells
the `G4cTm` searcher cannot close. -/

def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

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

def chain3F : Search.Frame := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], []⟩

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

def cfgD : Search.Config :=
  { frames := scanFrames, findBudget := some 1, emitClosureCap := 0 }

/-! ### Exhaustive small-frame battery (variable-free sweep)

All well-formed frames with ≤ 4 worlds: `ri` any strict poset
(irreflexive, transitively closed), `rm ⊆ ri` transitive, `fall`
up-closed.  For variable-free sequents the decoration space is a
point, so the sweep is a complete search over ≤4-world countermodels
— every hit is certified by `checkB`. -/

def offdiag (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun a => (List.range n).filterMap fun b =>
    if a ≠ b then some (a, b) else none

def transB (r : List (Nat × Nat)) : Bool :=
  r.all fun e => r.all fun e' =>
    !(e.2 == e'.1) || decide ((e.1, e'.2) ∈ r)

def upclB (n : Nat) (r : List (Nat × Nat)) (f : List Nat) : Bool :=
  f.all fun w => (List.range n).all fun v =>
    !(decide ((w, v) ∈ r)) || decide (v ∈ f)

def framesOf (n : Nat) : List Search.Frame := Id.run do
  let mut out := []
  for ri in (offdiag n).sublists do
    if transB ri then
      for rm in ri.sublists do
        if transB rm then
          for fall in (List.range n).sublists do
            if upclB n ri fall then
              out := out ++ [(⟨n, ri, rm, fall⟩ : Search.Frame)]
  return out

def bigBattery : List Search.Frame :=
  framesOf 1 ++ framesOf 2 ++ framesOf 3 ++ framesOf 4

def cfgBig : Search.Config :=
  { frames := bigBattery, findBudget := some 1, emitClosureCap := 0 }

inductive V3 | proved | refuted | unknown
deriving BEq

/-- Countermodel-first two-sided verdict: certified sweeps (standard
battery, then the exhaustive ≤4-world battery), then the G4cTm
searcher, then the certified-complete `G4s` searcher at `fuel`. -/
def v3 (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : V3 :=
  match Search.decide cfgD Γ C with
  | .refuted _ _ _ => .refuted
  | .proved _ => .proved
  | .unknown =>
    match Search.decide cfgBig Γ C with
    | .refuted _ _ _ => .refuted
    | .proved _ => .proved
    | .unknown =>
      match (G4cTm.findBounded budget Γ C).1 with
      | some _ => .proved
      | none =>
        -- `provF` (the `G4s` searcher) explodes on exhaustive-false
        -- at these sizes; only consult it at tiny fuel.
        if fuel ≤ 12 && provF fuel Γ C then .proved else .unknown

def v3tag : V3 → String
  | .proved => "proved" | .refuted => "REFUTED" | .unknown => "unknown"

/-- Strong-oracle scan of one combination against all 15 classes:
per class, ELIMINATED (a certified countermodel on one side), MATCHED
(proofs both sides), or OPEN. -/
def oracleCell (fuel : Nat) (name : String) (X : PLLFormula) : IO Unit := do
  let mut matched : List Nat := []
  let mut openK : List Nat := []
  for k in List.range 15 do
    let D := reps.getD k .falsePLL
    IO.eprintln s!"    [{name}] k={k} side A"
    (← IO.getStderr).flush
    let a := v3 fuel [X] D
    if a == .refuted then continue
    IO.eprintln s!"    [{name}] k={k} side E (A={v3tag a})"
    (← IO.getStderr).flush
    let b := v3 fuel [D] X
    if b == .refuted then continue
    if a == .proved && b == .proved then matched := matched ++ [k]
    else openK := openK ++ [k]
  match matched, openK with
  | [], [] => IO.println s!"{name}: NEW CLASS (all 15 candidates countermodel-eliminated)"
  | [], l => IO.println s!"{name}: no match, open candidates {l}"
  | m, [] => IO.println s!"{name}: matched {m}"
  | m, l => IO.println s!"{name}: matched {m}, open {l}"
  (← IO.getStdout).flush

def parseCell (c : String) : Option (String × PLLFormula) :=
  let r (i : Nat) : PLLFormula := reps.getD i .falsePLL
  match c.splitOn "_" with
  | ["cAnd", i, j] => some (c, (r i.toNat!).and (r j.toNat!))
  | ["cOr", i, j] => some (c, (r i.toNat!).or (r j.toNat!))
  | ["cImp", i, j] => some (c, (r i.toNat!).ifThen (r j.toNat!))
  | ["cBox", i] => some (c, (r i.toNat!).somehow)
  | _ => none

/-- Escalating two-sided test of a single entailment `[P] ⊢ Q`,
`P`/`Q` given as `q<i>` indices. -/
def entMain (fuel : Nat) (i j : Nat) : IO Unit := do
  let P := reps.getD i .falsePLL
  let Q := reps.getD j .falsePLL
  let t0 ← IO.monoMsNow
  let v := v3 fuel [P] Q
  let t1 ← IO.monoMsNow
  IO.println s!"[q{i}]⊢q{j} at fuel {fuel}: {v3tag v} ({t1-t0}ms)"

/-- Stage-level timing for one (cell, k) pair. -/
def stagesMain (cell : String) (k : Nat) : IO Unit := do
  match parseCell cell with
  | none => IO.eprintln "bad cell"
  | some (_, X) =>
    let D := reps.getD k .falsePLL
    for (nm, Γ, C) in [("A: [X]⊢D", [X], D), ("E: [D]⊢X", [D], X)] do
      let t0 ← IO.monoMsNow
      let r1 := match Search.decide cfgD Γ C with
        | .refuted _ _ _ => "refuted" | .proved _ => "proved" | .unknown => "unknown"
      let t1 ← IO.monoMsNow
      IO.println s!"{nm} cfgD: {r1} ({t1-t0}ms)"; (← IO.getStdout).flush
      let r2 := match Search.decide cfgBig Γ C with
        | .refuted _ _ _ => "refuted" | .proved _ => "proved" | .unknown => "unknown"
      let t2 ← IO.monoMsNow
      IO.println s!"{nm} cfgBig: {r2} ({t2-t1}ms)"; (← IO.getStdout).flush
      let r3 := match (G4cTm.findBounded budget Γ C).1 with
        | some _ => "FOUND" | none => "none"
      let t3 ← IO.monoMsNow
      IO.println s!"{nm} findBounded: {r3} ({t3-t2}ms)"; (← IO.getStdout).flush

def oracleMain (fuel : Nat) (cells : List String) : IO Unit := do
  for c in cells do
    match parseCell c with
    | some (n, X) => oracleCell fuel n X
    | none => IO.eprintln s!"bad cell name {c}"


/-- Cut-chain certificate search for one direction `[P] ⊢ Q`: a direct
G4cTm term, or a chain of direct terms through representative middles,
glued by `Deriv.cutHead` (the searcher misses some derivable sequents;
lemma-introduction recovers those reachable through the dictionary). -/
def chainD : Nat → PLLFormula → PLLFormula → Option String
  | 0, P, Q =>
    match (G4cTm.findBounded budget [P] Q).1 with
    | some t => some s!"(ofG4 {emitTm t})"
    | none => none
  | d + 1, P, Q =>
    match (G4cTm.findBounded budget [P] Q).1 with
    | some t => some s!"(ofG4 {emitTm t})"
    | none =>
      (reps.filterMap fun M =>
        if M = P || M = Q then none
        else match (G4cTm.findBounded budget [P] M).1 with
          | none => none
          | some t1 =>
            match chainD d M Q with
            | none => none
            | some e2 =>
                some s!"(Deriv.cutHead (ofG4 {emitTm t1}) {e2})").head?

/-! ## Cell resolution -/

inductive Conn | cAnd | cOr | cImp
deriving BEq

def Conn.mk : Conn → PLLFormula → PLLFormula → PLLFormula
  | .cAnd, a, b => a.and b
  | .cOr, a, b => a.or b
  | .cImp, a, b => a.ifThen b

def Conn.opStr : Conn → String
  | .cAnd => "and" | .cOr => "or" | .cImp => "ifThen"

def Conn.nm : Conn → String
  | .cAnd => "And" | .cOr => "Or" | .cImp => "Imp"

structure Cell where
  value : Nat
  expr : String
  thm : Option String := none
  searched : Bool := false
deriving Inhabited

/-- Search-backed resolution of one nontrivial cell (shared by the
binary tables and the ◯ column).  Stages: direct two-sided G4cTm
classification; on failure the strong oracle (countermodel-first,
exhaustive ≤4-world battery) categorises the cell — matched (then
cut-chain certificate recovery), NEW CLASS (all candidates
countermodel-eliminated: the 15-class closure fails there), or open —
and un-certificated cells are emitted as isolated `sorry` lemmas with
the category recorded. -/
def resolveSearched (name stmt : String) (impSpecial : Bool)
    (comb : PLLFormula) : IO Cell := do
  let t0 ← IO.monoMsNow
  match classifyTm comb with
  | some (k, e1, e2) =>
      let t1 ← IO.monoMsNow
      IO.eprintln s!"  {name} -> {k}  ({t1 - t0}ms)"
      let head := s!"theorem {name} : {stmt} q{k} :="
      if impSpecial && k == 1 then
        return { value := k, expr := name, searched := true,
                 thm := some s!"{head}\n  ⟨topD, {e2}⟩" }
      else
        return { value := k, expr := name, searched := true,
                 thm := some s!"{head}\n  ⟨{e1},\n   {e2}⟩" }
  | none =>
    let mut matched : List Nat := []
    let mut openK : List Nat := []
    for k in List.range 15 do
      let D := reps.getD k .falsePLL
      let a := v3 40 [comb] D
      if a == .refuted then continue
      let b := v3 40 [D] comb
      if b == .refuted then continue
      if a == .proved && b == .proved then matched := matched ++ [k]
      else openK := openK ++ [k]
    match matched with
    | k :: _ =>
      let D := reps.getD k .falsePLL
      let e1? := if impSpecial && k == 1 then some "topD" else chainD 3 comb D
      let e2? := chainD 3 D comb
      match e1?, e2? with
      | some e1, some e2 =>
          IO.eprintln s!"  {name} -> {k}  (cut-chain)"
          return { value := k, expr := name, searched := true,
                   thm := some s!"theorem {name} : {stmt} q{k} :=\n  ⟨{e1},\n   {e2}⟩" }
      | _, _ =>
          IO.eprintln s!"  !! {name}: SEARCHER GAP at {k} (sorried)"
          return { value := k, expr := name, searched := true,
                   thm := some s!"/-- UNCERTIFIED (searcher gap): the strong oracle proves both\ndirections against class {k}, but no G4cTm certificate was found,\ndirect or cut-chain. -/\ntheorem {name} : {stmt} q{k} := sorry" }
    | [] =>
      match openK with
      | [] =>
        IO.eprintln s!"  !! {name}: NEW CLASS (all 15 eliminated)"
        return { value := 0, expr := name, searched := true,
                 thm := some s!"/-- REFUTED CELL (new class): certified ≤4-world countermodels\neliminate EVERY candidate class — this combination is not\ninterderivable with any of the 15 representatives, so the 15-class\nclosure FAILS here.  The stated collapse (to q0, a placeholder) is\nFALSE; the `sorry` records the failure point. -/\ntheorem {name} : {stmt} q0 := sorry" }
      | l =>
        let k := l.headD 0
        IO.eprintln s!"  !! {name}: OPEN {l} (sorried at {k})"
        return { value := k, expr := name, searched := true,
                 thm := some s!"/-- OPEN CELL: candidates {l} neither proved (both searchers) nor\nrefuted (exhaustive ≤4-world battery).  Sorried at the first open\ncandidate. -/\ntheorem {name} : {stmt} q{k} := sorry" }

/-- Resolve one binary-table cell.  Priority: syntactic coincidence
with a representative; ⊥/⊤ unit laws; idempotence; commutative mirror
(referencing the transposed cell's expression); otherwise offline
search with an emitted certificate. -/
def resolveCell (c : Conn) (i j : Nat) (grid : Array (Array Cell)) :
    IO Cell := do
  let comb := c.mk (reps.getD i .falsePLL) (reps.getD j .falsePLL)
  match repIdx? comb with
  | some k => return { value := k, expr := "Interd.refl _" }
  | none =>
  match c with
  | .cAnd =>
    if i == 0 then return { value := 0, expr := "bot_and_i _" }
    else if j == 0 then
      return { value := 0, expr := "(and_comm_i _ _).trans (bot_and_i _)" }
    else if i == 1 then return { value := j, expr := "top_and_i _" }
    else if j == 1 then
      return { value := i, expr := "(and_comm_i _ _).trans (top_and_i _)" }
    else if i == j then return { value := i, expr := "and_idem_i _" }
    else if i > j then
      let t := (grid.getD j #[]).getD i default
      return { value := t.value,
               expr := s!"(and_comm_i _ _).trans ({t.expr})" }
    else searchCell c i j comb
  | .cOr =>
    if i == 0 then return { value := j, expr := "bot_or_i _" }
    else if j == 0 then
      return { value := i, expr := "(or_comm_i _ _).trans (bot_or_i _)" }
    else if i == 1 then return { value := 1, expr := "top_or_i _" }
    else if j == 1 then
      return { value := 1, expr := "(or_comm_i _ _).trans (top_or_i _)" }
    else if i == j then return { value := i, expr := "or_idem_i _" }
    else if i > j then
      let t := (grid.getD j #[]).getD i default
      return { value := t.value,
               expr := s!"(or_comm_i _ _).trans ({t.expr})" }
    else searchCell c i j comb
  | .cImp =>
    if i == 0 then return { value := 1, expr := "bot_imp_i _" }
    else if i == 1 then return { value := j, expr := "top_imp_i _" }
    else if j == 1 then return { value := 1, expr := "imp_top_i _" }
    else if i == j then return { value := 1, expr := "imp_self_i _" }
    else searchCell c i j comb
where
  searchCell (c : Conn) (i j : Nat) (comb : PLLFormula) : IO Cell :=
    resolveSearched s!"c{c.nm}_{i}_{j}" s!"Interd (q{i}.{c.opStr} q{j})"
      (c == .cImp) comb

/-- Resolve one ◯-column cell. -/
def resolveBox (i : Nat) : IO Cell := do
  let ri := reps.getD i .falsePLL
  let comb := ri.somehow
  match repIdx? comb with
  | some k => return { value := k, expr := "Interd.refl _" }
  | none =>
  match ri with
  | .somehow _ => return { value := i, expr := "box_idem_i _" }
  | _ => resolveSearched s!"cBox_{i}" s!"Interd q{i}.somehow" false comb

/-! ## Assembly -/

def header : String :=
"import wip.stabilise
import wip.rnDictBase

/-!
# The certified RN(◯,{}) dictionary: `rnDict15 : RNDict`

GENERATED FILE — do not edit by hand.  Produced by
`wip/rnDictGen.lean` (`lake build rnDictGen && .lake/build/bin/rnDictGen > wip/rnDict.lean`).

The fifteen interderivability-class representatives of the
variable-free PLL fragment (the RN(◯,{}) dictionary computed by the
v2quant probe, wip/v2quant_out3.txt), with KERNEL-CHECKED closure
tables: for every pair of representatives and each of ∧, ∨, ⊃ (and
every representative under ◯), an `Interd` certificate collapsing the
combination onto its representative.  Nontrivial cells carry G4iLL″
proof terms found by offline search (`G4cTm.findBounded`, pinned as
source per the repo's discover-then-pin discipline) and are bridged to
`LaxND` by `RND.ofG4`; trivial cells go through the generic laws of
`wip/rnDictBase.lean`.

The instantiation plugs into `wip/stabilise.lean`: `dict_collapse`,
`dict_agree_stab`, `vfB_mforthResidue` and
`restricted_amalgamation_oneVar` become unconditional in the
`RNDict` argument.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND
"

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut out : Array String := #[header]
  -- representatives
  out := out.push "/-! ## The fifteen representatives (probe order) -/\n"
  for i in List.range 15 do
    out := out.push s!"def q{i} : PLLFormula := {ppFN i (reps.getD i .falsePLL)}"
  let repList := String.intercalate ", " ((List.range 15).map (s!"q{·}"))
  out := out.push s!"\ndef repsL : List PLLFormula := [{repList}]"
  out := out.push "\ndef rep15 : Fin 15 → PLLFormula := fun i => repsL.getD i.val .falsePLL"
  -- resolve tables
  let conns : List Conn := [.cAnd, .cOr, .cImp]
  let mut grids : Array (Array (Array Cell)) := #[]
  for c in conns do
    IO.eprintln s!"resolving {c.nm} table..."
    let mut grid : Array (Array Cell) := #[]
    for i in List.range 15 do
      let mut row : Array Cell := #[]
      for j in List.range 15 do
        row := row.push (← resolveCell c i j grid)
      grid := grid.push row
    grids := grids.push grid
  IO.eprintln "resolving Box column..."
  let mut boxCol : Array Cell := #[]
  for i in List.range 15 do
    boxCol := boxCol.push (← resolveBox i)
  -- tables
  out := out.push "\n/-! ## The closure tables -/\n"
  for (c, g) in conns.zip grids.toList do
    let rows := g.toList.map fun row =>
      "[" ++ String.intercalate ", " (row.toList.map (s!"{·.value}")) ++ "]"
    out := out.push s!"def {c.nm.toLower}T : List (List Nat) :=\n  [{String.intercalate ",\n   " rows}]"
  out := out.push s!"\ndef boxT : List Nat := [{String.intercalate ", " (boxCol.toList.map (s!"{·.value}"))}]"
  for c in conns do
    out := out.push s!"\ndef {c.nm.toLower}Idx15 (i j : Fin 15) : Fin 15 :=\n  ⟨(({c.nm.toLower}T.getD i.val []).getD j.val 0) % 15, Nat.mod_lt _ (by decide)⟩"
  out := out.push "\ndef boxIdx15 (i : Fin 15) : Fin 15 :=\n  ⟨(boxT.getD i.val 0) % 15, Nat.mod_lt _ (by decide)⟩"
  -- cell certificates
  out := out.push "\n/-! ## Searched-cell certificates (offline G4iLL″ terms, kernel-checked here) -/\n"
  let mut nSearch := 0
  let mut nGeneric := 0
  for g in grids do
    for row in g do
      for cell in row do
        if cell.searched then nSearch := nSearch + 1 else nGeneric := nGeneric + 1
        if let some t := cell.thm then out := out.push (t ++ "\n")
  for cell in boxCol do
    if cell.searched then nSearch := nSearch + 1 else nGeneric := nGeneric + 1
    if let some t := cell.thm then out := out.push (t ++ "\n")
  -- closure theorems
  out := out.push "/-! ## The closure theorems -/\n"
  for (c, g) in conns.zip grids.toList do
    let mut s := s!"theorem {c.nm.toLower}_ok (i j : Fin 15) :\n    Interd ((rep15 i).{c.opStr} (rep15 j)) (rep15 ({c.nm.toLower}Idx15 i j)) :=\n  match i, j with\n"
    for i in List.range 15 do
      for j in List.range 15 do
        s := s ++ s!"  | ⟨{i}, _⟩, ⟨{j}, _⟩ => {((g.getD i #[]).getD j default).expr}\n"
    s := s ++ "  | ⟨_+15, h⟩, _ => absurd h (by omega)\n"
    s := s ++ "  | _, ⟨_+15, h⟩ => absurd h (by omega)\n"
    out := out.push s
  let mut sb := "theorem box_ok (i : Fin 15) :\n    Interd (rep15 i).somehow (rep15 (boxIdx15 i)) :=\n  match i with\n"
  for i in List.range 15 do
    sb := sb ++ s!"  | ⟨{i}, _⟩ => {(boxCol.getD i default).expr}\n"
  sb := sb ++ "  | ⟨_+15, h⟩ => absurd h (by omega)\n"
  out := out.push sb
  -- the dictionary
  let crankMax := (reps.map crank).foldl max 0
  let mut nSorry := 0
  for g in grids do
    for row in g do
      for cell in row do
        if (cell.thm.getD "").endsWith "sorry" then nSorry := nSorry + 1
  for cell in boxCol do
    if (cell.thm.getD "").endsWith "sorry" then nSorry := nSorry + 1
  out := out.push "end RND\n"
  out := out.push ("open RND in
/-- **The certified RN(◯,{}) dictionary**: 15 variable-free
representatives, crank bound " ++ toString crankMax ++ ", connective-closure tables
kernel-checked away from the sorried cells (" ++ Nat.repr nSorry ++ " of 690; when that
count is 0 this record is the full certified dictionary). -/
def rnDict15 : RNDict where
  n := 15
  rep := rep15
  rep_varFree := by decide
  crankBound := " ++ toString crankMax ++ "
  rep_crank_le := by decide
  botIdx := ⟨0, by decide⟩
  bot_interd := Interd.refl _
  andIdx := andIdx15
  orIdx := orIdx15
  impIdx := impIdx15
  boxIdx := boxIdx15
  and_interd := and_ok
  or_interd := or_ok
  imp_interd := imp_ok
  box_interd := box_ok

/-! ## Axiom audit -/
" ++ (if nSorry == 0 then "
/--
info: 'PLLND.SemUI.rnDict15' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnDict15" else "
-- PARTIAL instantiation: " ++ Nat.repr nSorry ++ " cells are sorried (see the
-- per-cell doc comments: REFUTED/OPEN/SEARCHER-GAP).  No #guard_msgs pin.
#print axioms rnDict15") ++ "

end SemUI
end PLLND")
  -- print
  let stdout ← IO.getStdout
  for s in out do
    stdout.putStrLn s
  stdout.flush
  let t1 ← IO.monoMsNow
  IO.eprintln s!"done: {nSearch} searched cells, {nGeneric} generic cells, {nSorry} sorried, {(t1 - t0)}ms, crankMax {crankMax}"

/-! ## Refutation-witness emission (`rnDictGen refute <cell>...`)

For a NEW-CLASS cell, emit the machine-checked witness theorem: for
EVERY candidate class, one direction of the collapse is refuted by a
pinned `checkB` countermodel (`by decide`).  Printed as
`wip/rnDictRefute.lean`. -/

def fmtPairs (l : List (Nat × Nat)) : String :=
  "[" ++ String.intercalate ", " (l.map fun e => s!"({e.1}, {e.2})") ++ "]"

def fmtNats (l : List Nat) : String :=
  "[" ++ String.intercalate ", " (l.map fun e => s!"{e}") ++ "]"

def fmtCM (M : FinCM) : String :=
  s!"⟨{M.n}, {fmtPairs M.ri}, {fmtPairs M.rm}, {fmtNats M.fall}, []⟩"

/-- Find a certified refutation of `Γ ⊢ C`, returning the countermodel. -/
def findCM (Γ : List PLLFormula) (C : PLLFormula) : Option (FinCM × Nat) :=
  match Search.decide cfgD Γ C with
  | .refuted M w _ => some (M, w)
  | _ =>
    match Search.decide cfgBig Γ C with
    | .refuted M w _ => some (M, w)
    | _ => none

/-- One arm of the witness theorem: refute `Interd X (rep k)` via a
countermodel against one of its two directions. -/
def refuteArm (X : PLLFormula) (stmtX : String) (k : Nat) : Option String :=
  let D := reps.getD k .falsePLL
  match findCM [X] D with
  | some (M, w) =>
      -- `C := q<k>` pins the closed representative so the `decide` goal
      -- has no free variables; defeq with `rep15 ⟨k, _⟩` closes the arm.
      some s!"  | ⟨{k}, _⟩ => fun h => FinCM.not_provable_of_check (M := {fmtCM M}) (w := {w}) (C := q{k}) (by decide) h.1"
  | none =>
    match findCM [D] X with
    | some (M, w) =>
        some s!"  | ⟨{k}, _⟩ => fun h => FinCM.not_provable_of_check (M := {fmtCM M}) (w := {w}) (Γ := [q{k}]) (by decide) h.2"
    | none => none

def refuteHeader : String :=
"import wip.rnDict

/-!
# Machine-checked closure failure of the 15-class dictionary

GENERATED FILE (`rnDictGen refute ...`) — do not edit by hand.

For each witness cell below, the theorem eliminates EVERY candidate
class: one direction of the would-be collapse is refuted by a pinned
finite countermodel, checked by the kernel via `FinCM.checkB` +
`FinCM.not_provable_of_check` (`by decide` on closed data).  Hence the
variable-free fragment does NOT collapse onto the 15 representatives:
the RN(◯,{}) dictionary of the v2quant probe (size-capped) is not
connective-closed, and `RNDict` is NOT instantiable with these 15
representatives and ANY tables at the witnessed connectives.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND
"

def refuteCell (name : String) (X : PLLFormula) (stmtX : String) :
    IO (Option String) := do
  let mut arms : Array String := #[]
  for k in List.range 15 do
    match refuteArm X stmtX k with
    | some a => arms := arms.push a
    | none =>
        IO.eprintln s!"  !! {name}: candidate {k} not countermodel-refuted; no witness theorem"
        return none
  let body := String.intercalate "\n" arms.toList
  return some (s!"/-- `{stmtX}` matches NO dictionary class: every candidate is
countermodel-eliminated. -/
theorem refute_{name} : ∀ k : Fin 15, ¬ Interd ({stmtX}) (rep15 k) :=
  fun k => match k with
" ++ body ++ "
  | ⟨_+15, hh⟩ => absurd hh (by omega)
")

def refuteMain (cells : List String) : IO Unit := do
  let mut out : Array String := #[refuteHeader]
  let mut names : Array String := #[]
  for c in cells do
    match parseCell c with
    | none => IO.eprintln s!"bad cell name {c}"
    | some (n, X) =>
      let stmtX :=
        match c.splitOn "_" with
        | ["cAnd", i, j] => s!"q{i}.and q{j}"
        | ["cOr", i, j] => s!"q{i}.or q{j}"
        | ["cImp", i, j] => s!"q{i}.ifThen q{j}"
        | ["cBox", i] => s!"q{i}.somehow"
        | _ => "?"
      match ← refuteCell n X stmtX with
      | some t => out := out.push t; names := names.push s!"refute_{n}"
      | none => pure ()
  out := out.push "/-! ## Axiom audit -/
"
  for n in names do
    out := out.push ("/--
info: 'PLLND.SemUI.RND." ++ n ++ "' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms " ++ n ++ "
")
  out := out.push "end RND
end SemUI
end PLLND"
  let stdout ← IO.getStdout
  for x in out do
    stdout.putStrLn x
  stdout.flush

/-! ## Diagnostic mode (`rnDictGen diag <cellname>...`) -/

def tagB {Γ : List PLLFormula} {C : PLLFormula} :
    Option (G4cTm Γ C) × Nat → String
  | (some _, r) => s!"FOUND (rem {r})"
  | (none, 0) => "BUDGET-OUT"
  | (none, r) => s!"exhausted (rem {r})"

def probeCell (name : String) (X : PLLFormula) : IO Unit := do
  IO.println s!"== {name} =="
  for k in List.range 15 do
    let D := reps.getD k .falsePLL
    let t0 ← IO.monoMsNow
    let a := G4cTm.findBounded budget [X] D
    let t1 ← IO.monoMsNow
    let b := G4cTm.findBounded budget [D] X
    let t2 ← IO.monoMsNow
    IO.println s!"  k={k}: [X]⊢D {tagB a} ({t1-t0}ms)   [D]⊢X {tagB b} ({t2-t1}ms)"
    (← IO.getStdout).flush

def diagMain (cells : List String) : IO Unit := do
  let r (i : Nat) : PLLFormula := reps.getD i .falsePLL
  for c in cells do
    match c.splitOn "_" with
    | ["cAnd", i, j] => probeCell c ((r i.toNat!).and (r j.toNat!))
    | ["cOr", i, j] => probeCell c ((r i.toNat!).or (r j.toNat!))
    | ["cImp", i, j] => probeCell c ((r i.toNat!).ifThen (r j.toNat!))
    | ["cBox", i] => probeCell c (r i.toNat!).somehow
    | _ => IO.eprintln s!"bad cell name {c}"

/-! ## §41 machinery: witnesses, the rooted ≤5-world battery, and
pairwise separation

The four §40 witnesses (combinations matching NO class of the 15) as
candidate representatives 15–18.

The ≤4-world battery `bigBattery` is exhaustive over ALL frames with
≤ 4 worlds.  For 5 worlds we use the ROOTED reduction: a countermodel
`(M, w)` restricts to the submodel generated by `w` (the upward
`ri`-closure of `w`; `rm ⊆ ri` and transitivity keep it closed, and
forcing at `w` only inspects that closure), a rooted frame with root
`w` and no more worlds than `M`.  Relabelling the root to 0: the sweep
over all rooted 5-world frames — root 0 strictly below every other
world, any strict poset on the rest, `rm ⊆ ri` transitive, `fall`
up-closed — together with the exhaustive ≤4-world battery is
exhaustive for variable-free refutation on ≤ 5-world frames. -/

def w1 : PLLFormula := (reps.getD 8 Fq).and (reps.getD 10 Fq)
def w2 : PLLFormula := (reps.getD 9 Fq).ifThen (reps.getD 4 Fq)
def w3 : PLLFormula := (reps.getD 12 Fq).ifThen (reps.getD 4 Fq)
def w4 : PLLFormula := (reps.getD 14 Fq).ifThen (reps.getD 4 Fq)

def reps19 : List PLLFormula := reps ++ [w1, w2, w3, w4]

/-- Display names: `q0`–`q14` for dictionary classes, `w1`–`w4` for
the §40 witnesses. -/
def wName (i : Nat) : String :=
  if i < 15 then s!"q{i}" else s!"w{i - 14}"

/-- All rooted frames on `n` worlds: world 0 strictly below every
other world; the rest of `ri` any strict poset (transitive subset of
the off-diagonal) on `{1,…,n-1}`; `rm ⊆ ri` transitive; `fall`
up-closed.  The union `ri` is transitive: `E` is, `(0,v)` edges only
compose on the right, and the composite is again a root edge. -/
def rootedFramesOf (n : Nat) : List Search.Frame := Id.run do
  let mut out : Array Search.Frame := #[]
  let base := (List.range n).filterMap fun v =>
    if v == 0 then none else some (0, v)
  let pool := (offdiag n).filter fun e => e.1 != 0 && e.2 != 0
  for e in pool.sublists do
    if transB e then
      let ri := base ++ e
      for rm in ri.sublists do
        if transB rm then
          for fall in (List.range n).sublists do
            if upclB n ri fall then
              out := out.push ⟨n, ri, rm, fall⟩
  return out.toList

def battery5 : List Search.Frame := rootedFramesOf 5

def cfg5 : Search.Config :=
  { frames := battery5, findBudget := some 1, emitClosureCap := 0 }

/-- Extra pinned countermodels beyond the exhaustive ≤5-world sweep
(discovered by the bounded rooted 6-world hunt `ref6`). -/
def extraCMs : List FinCM :=
  [⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩,
   ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(0, 2), (1, 4), (3, 4)], [4], []⟩,
   ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(3, 4)], [4], []⟩,
   ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩,
   ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4)], [(0, 2), (1, 4), (3, 4)], [4], []⟩]

/-- Check the pinned extra models directly (verified checker only). -/
def extraCM? (Γ : List PLLFormula) (C : PLLFormula) : Option (FinCM × Nat) :=
  (extraCMs.filterMap fun M =>
    ((List.range M.n).filter fun w => FinCM.checkB M w Γ C).head?.map
      fun w => (M, w)).head?

/-- `findCM` extended by the rooted 5-world battery, then the pinned
extra models (each hit gated by the verified checker). -/
def findCM5 (Γ : List PLLFormula) (C : PLLFormula) : Option (FinCM × Nat) :=
  match findCM Γ C with
  | some r => some r
  | none =>
    match Search.decide cfg5 Γ C with
    | .refuted M w _ => some (M, w)
    | _ =>
      extraCM? Γ C

/-- Print a formula naming all `reps19` members: `q0`–`q18` (for
`rnDict2.lean`, where the witnesses are `q15`–`q18`). -/
partial def ppQ19 (X : PLLFormula) : String :=
  match reps19.findIdx? (· = X) with
  | some i => s!"q{i}"
  | none =>
    match X with
    | .prop s => s!"(.prop \"{s}\")"
    | .falsePLL => ".falsePLL"
    | .and a b => s!"(.and {ppQ19 a} {ppQ19 b})"
    | .or a b => s!"(.or {ppQ19 a} {ppQ19 b})"
    | .ifThen a b => s!"(.ifThen {ppQ19 a} {ppQ19 b})"
    | .somehow a => s!"(.somehow {ppQ19 a})"

/-- Print a formula naming reps as `q0`–`q14`/`w1`–`w4` (for
`rnSep.lean`). -/
partial def ppW (X : PLLFormula) : String :=
  match reps19.findIdx? (· = X) with
  | some i => if i < 15 then s!"q{i}" else s!"w{i - 14}"
  | none =>
    match X with
    | .prop s => s!"(.prop \"{s}\")"
    | .falsePLL => ".falsePLL"
    | .and a b => s!"(.and {ppW a} {ppW b})"
    | .or a b => s!"(.or {ppW a} {ppW b})"
    | .ifThen a b => s!"(.ifThen {ppW a} {ppW b})"
    | .somehow a => s!"(.somehow {ppW a})"

/-- `emitTm` with the representative-naming printer as a parameter. -/
partial def emitTmP (pp : PLLFormula → String) :
    {Γ : List PLLFormula} → {C : PLLFormula} → G4cTm Γ C → String
  | _, _, @G4cTm.init Γ a _ => s!"(.init {memS (.prop a) Γ})"
  | _, _, @G4cTm.botL Γ _ _ => s!"(.botL {memS .falsePLL Γ})"
  | _, _, @G4cTm.andR _ _ _ t1 t2 => s!"(.andR {emitTmP pp t1} {emitTmP pp t2})"
  | _, _, @G4cTm.orR1 _ _ _ t => s!"(.orR1 {emitTmP pp t})"
  | _, _, @G4cTm.orR2 _ _ _ t => s!"(.orR2 {emitTmP pp t})"
  | _, _, @G4cTm.impR _ _ _ t => s!"(.impR {emitTmP pp t})"
  | _, _, @G4cTm.laxR _ _ t => s!"(.laxR {emitTmP pp t})"
  | _, _, @G4cTm.laxL Γ A _ _ t =>
      s!"(.laxL (A := {pp A}) {memS A.somehow Γ} {emitTmP pp t})"
  | _, _, @G4cTm.andL Γ A B _ _ t =>
      s!"(.andL (A := {pp A}) (B := {pp B}) {memS (A.and B) Γ} {emitTmP pp t})"
  | _, _, @G4cTm.orL Γ A B _ _ t1 t2 =>
      s!"(.orL (A := {pp A}) (B := {pp B}) {memS (A.or B) Γ} {emitTmP pp t1} {emitTmP pp t2})"
  | _, _, @G4cTm.impLProp Γ a B _ _ _ t =>
      s!"(.impLProp (a := \"{a}\") (B := {pp B}) {memS ((PLLFormula.prop a).ifThen B) Γ} {memS (.prop a) Γ} {emitTmP pp t})"
  | _, _, @G4cTm.impLAnd Γ A B D _ _ t =>
      s!"(.impLAnd (A := {pp A}) (B := {pp B}) (D := {pp D}) {memS ((A.and B).ifThen D) Γ} {emitTmP pp t})"
  | _, _, @G4cTm.impLOr Γ A B D _ _ t =>
      s!"(.impLOr (A := {pp A}) (B := {pp B}) (D := {pp D}) {memS ((A.or B).ifThen D) Γ} {emitTmP pp t})"
  | _, _, @G4cTm.impLImp Γ A B D _ _ t1 t2 =>
      s!"(.impLImp (A := {pp A}) (B := {pp B}) (D := {pp D}) {memS ((A.ifThen B).ifThen D) Γ} {emitTmP pp t1} {emitTmP pp t2})"
  | _, _, @G4cTm.impLLax Γ A B _ _ t1 t2 =>
      s!"(.impLLax (A := {pp A}) (B := {pp B}) {memS (A.somehow.ifThen B) Γ} {emitTmP pp t1} {emitTmP pp t2})"
  | _, _, @G4cTm.impLLaxLax Γ A B X _ _ _ t1 t2 =>
      s!"(.impLLaxLax (A := {pp A}) (B := {pp B}) (X := {pp X}) {memS (A.somehow.ifThen B) Γ} {memS X.somehow Γ} {emitTmP pp t1} {emitTmP pp t2})"

/-- One side of an escalated decision, with certificate data. -/
inductive SideV
  | proved (src : String)
  | refuted (M : FinCM) (w : Nat)
  | unknown

def SideV.tag : SideV → String
  | .proved _ => "proved"
  | .refuted M w => s!"REFUTED {fmtCM M} @ {w}"
  | .unknown => "unknown"

/-- Cut-chain certificate search through the middles `mids` at budget
`bud` (generalises `chainD`, which is pinned to `reps`/`budget`). -/
def chainVia (pp : PLLFormula → String) (bud : Nat) (mids : List PLLFormula) :
    Nat → PLLFormula → PLLFormula → Option String
  | 0, P, Q =>
    match (G4cTm.findBounded bud [P] Q).1 with
    | some t => some s!"(ofG4 {emitTmP pp t})"
    | none => none
  | d + 1, P, Q =>
    match (G4cTm.findBounded bud [P] Q).1 with
    | some t => some s!"(ofG4 {emitTmP pp t})"
    | none =>
      (mids.filterMap fun M =>
        if M = P || M = Q then none
        else match (G4cTm.findBounded bud [P] M).1 with
          | none => none
          | some t1 =>
            match chainVia pp bud mids d M Q with
            | none => none
            | some e2 =>
                some s!"(Deriv.cutHead (ofG4 {emitTmP pp t1}) {e2})").head?

/-- Escalated one-side decision `[P] ⊢ Q`.  Stage 0 is a SMALL bounded
direct search (variable-free sequents usually exhaust or succeed in
milliseconds, so provable sides do not pay the full battery misses);
then countermodel-first: the standard battery (`cfgD`), the exhaustive
≤4-world battery, the rooted 5-world battery; then the direct G4cTm
searcher inside the cut-chain through `mids` at budget `bud`. -/
def side5 (pp : PLLFormula → String) (bud : Nat) (mids : List PLLFormula)
    (P Q : PLLFormula) : SideV :=
  match (G4cTm.findBounded 20000 [P] Q).1 with
  | some t => .proved s!"(ofG4 {emitTmP pp t})"
  | none =>
  match findCM [P] Q with
  | some (M, w) => .refuted M w
  | none =>
    match Search.decide cfg5 [P] Q with
    | .refuted M w _ => .refuted M w
    | .proved t => .proved s!"(ofG4 {emitTmP pp t})"
    | .unknown =>
      match extraCM? [P] Q with
      | some (M, w) => .refuted M w
      | none =>
        match chainVia pp bud mids 3 P Q with
        | some e => .proved e
        | none => .unknown

def battInfo : IO Unit := do
  IO.println s!"bigBattery: {bigBattery.length} frames"
  IO.println s!"battery5 (rooted, 5 worlds): {battery5.length} frames"
  let t0 ← IO.monoMsNow
  let r := match Search.decide cfg5 [reps.getD 12 Fq] (reps.getD 9 Fq) with
    | .refuted M w _ => s!"REFUTED {fmtCM M} @ {w}"
    | .proved _ => "proved"
    | .unknown => "unknown"
  let t1 ← IO.monoMsNow
  IO.println s!"sample cfg5 decide [q12]⊢q9: {r} ({t1-t0}ms)"

/-- Pairwise separation scan over `reps19` indices: for each pair
`i < j`, the escalated two-sided status and the verdict —
DISTINCT (one side countermodel-refuted), COLLAPSE (both sides
proved), or OPEN. -/
def sepMain (bud : Nat) (idxs : List Nat) : IO Unit := do
  for i in idxs do
    for j in idxs do
      if i < j then
        let A := reps19.getD i Fq
        let B := reps19.getD j Fq
        let t0 ← IO.monoMsNow
        let a := side5 ppW bud reps19 A B
        let b := match a with
          | .refuted _ _ => SideV.unknown   -- already separated; skip cost
          | _ => side5 ppW bud reps19 B A
        let t1 ← IO.monoMsNow
        let verdict := match a, b with
          | .refuted _ _, _ => "DISTINCT"
          | _, .refuted _ _ => "DISTINCT"
          | .proved _, .proved _ => "COLLAPSE"
          | _, _ => "OPEN"
        IO.println s!"{wName i} vs {wName j}: [{wName i}]⊢{wName j} {a.tag} ; [{wName j}]⊢{wName i} {b.tag} => {verdict} ({t1-t0}ms)"
        (← IO.getStdout).flush

/-! ## Separation-certificate emission (`rnDictGen sepemit <bud>`)

Emits `wip/rnSep.lean`: for every pair of the 19 candidate
representatives (the 15 dictionary classes + the four §40 witnesses),
a pinned distinctness certificate `sep_<i>_<j> : ¬ Interd A B`
(one direction refuted by a `checkB`-certified countermodel), or an
`Interd` collapse certificate, or an OPEN record.  If all pairs are
distinct, the aggregate `rep19_pairwise_distinct` is emitted. -/

/-- Refutation-only two-sided scan, cheapest battery level first
across both sides.  `true` marks the `[A]⊢B` direction (kills `h.1`). -/
def sepRefute (A B : PLLFormula) : Option (Bool × FinCM × Nat) :=
  match Search.decide cfgD [A] B with
  | .refuted M w _ => some (true, M, w)
  | _ =>
  match Search.decide cfgD [B] A with
  | .refuted M w _ => some (false, M, w)
  | _ =>
  match Search.decide cfgBig [A] B with
  | .refuted M w _ => some (true, M, w)
  | _ =>
  match Search.decide cfgBig [B] A with
  | .refuted M w _ => some (false, M, w)
  | _ =>
  match Search.decide cfg5 [A] B with
  | .refuted M w _ => some (true, M, w)
  | _ =>
  match Search.decide cfg5 [B] A with
  | .refuted M w _ => some (false, M, w)
  | _ => none

def sepHeader : String :=
"import wip.rnDict

/-!
# Pairwise separation: the 15 base classes and the §40 witnesses

GENERATED FILE (`rnDictGen sepemit`) — do not edit by hand.

For every pair among the 15 dictionary classes `q0`–`q14`
(wip/rnDict.lean), and every (base class, §40 witness) pair, one
direction of the would-be collapse is refuted by a pinned finite
countermodel, checked by the kernel via `FinCM.checkB` +
`FinCM.not_provable_of_check` (`by decide` on closed data).  The
refuting battery is staged: the standard frames, the exhaustive
≤4-world battery, then the exhaustive ROOTED 5-world battery (a
countermodel restricts to the submodel generated by its world, which
is rooted with no more worlds — so together with the ≤4-world battery
this is a complete search over ≤5-world countermodels).  The
previously uncertified triples {q1, q11, q13} and {q9, q12, q14} are
separated by 5-world models — the ≤4-world battery genuinely cannot
see these distinctions.

The four witnesses themselves are pairwise INTERDERIVABLE (ONE new
class): hand-authored certificates in `wip/rnSepColl.lean`, together
with the 16-class aggregate `rep16_pairwise_distinct`.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND

/-! ## The four §40 witnesses -/

def w1 : PLLFormula := q8.and q10
def w2 : PLLFormula := q9.ifThen q4
def w3 : PLLFormula := q12.ifThen q4
def w4 : PLLFormula := q14.ifThen q4
"

def sepThmName (i j : Nat) : String := s!"sep_{i}_{j}"

/-- Lean-source name of representative `i` inside `rnSep.lean`. -/
def sepNm (i : Nat) : String := wName i

def sepEmitMain (bud : Nat) : IO Unit := do
  let mut thms : Array String := #[]
  let mut openPairs : Array (Nat × Nat) := #[]
  let mut collapses : Array (Nat × Nat) := #[]
  for i in List.range 19 do
    for j in List.range 19 do
      if i < j && !(i ≥ 15 && j ≥ 15) then
        let A := reps19.getD i Fq
        let B := reps19.getD j Fq
        let t0 ← IO.monoMsNow
        match sepRefute A B with
        | some (dir, M, w) =>
          let arm := if dir then
            s!"  fun h => FinCM.not_provable_of_check (M := {fmtCM M}) (w := {w}) (Γ := [{sepNm i}]) (C := {sepNm j}) (by decide) h.1"
          else
            s!"  fun h => FinCM.not_provable_of_check (M := {fmtCM M}) (w := {w}) (Γ := [{sepNm j}]) (C := {sepNm i}) (by decide) h.2"
          thms := thms.push
            s!"theorem {sepThmName i j} : ¬ Interd {sepNm i} {sepNm j} :=\n{arm}\n"
          let t1 ← IO.monoMsNow
          IO.eprintln s!"  {sepNm i} vs {sepNm j}: distinct (n={M.n}) ({t1-t0}ms)"
        | none =>
          match chainVia ppW bud reps19 3 A B, chainVia ppW bud reps19 3 B A with
          | some e1, some e2 =>
            collapses := collapses.push (i, j)
            thms := thms.push
              s!"/-- COLLAPSE: the two candidates are interderivable. -/\ntheorem coll_{i}_{j} : Interd {sepNm i} {sepNm j} :=\n  ⟨{e1},\n   {e2}⟩\n"
            IO.eprintln s!"  !! {sepNm i} vs {sepNm j}: COLLAPSE"
          | _, _ =>
            openPairs := openPairs.push (i, j)
            thms := thms.push
              s!"-- OPEN: {sepNm i} vs {sepNm j} — neither refuted (≤5-world exhaustive) nor both directions proved.\n"
            IO.eprintln s!"  ?? {sepNm i} vs {sepNm j}: OPEN"
        (← IO.getStderr).flush
  let mut out : Array String := #[sepHeader]
  out := out.push "/-! ## The pairwise certificates -/\n"
  out := out ++ thms
  if !(openPairs.isEmpty && collapses.isEmpty) then
    out := out.push s!"-- PARTIAL: open pairs {openPairs.toList}, collapses {collapses.toList}.\n"
  out := out.push "/-! ## Axiom audit (the previously uncertified 5-world family) -/\n"
  for nm in ["sep_1_11", "sep_1_13", "sep_11_13", "sep_9_12",
             "sep_9_14", "sep_12_14"] do
    out := out.push ("/--\ninfo: 'PLLND.SemUI.RND." ++ nm ++
      "' depends on axioms: [propext, Quot.sound]\n-/\n#guard_msgs in\n#print axioms " ++ nm ++ "\n")
  out := out.push "end RND\nend SemUI\nend PLLND"
  let stdout ← IO.getStdout
  for s in out do
    stdout.putStrLn s
  stdout.flush

/-! ## The enlarged round (`pending2` / `cells2` / `assemble2` / `refute2`)

One connective-closure round over the 19 representatives (the 15
dictionary classes + the four §40 witnesses as `q15`–`q18`), emitted
as `wip/rnDict2.lean` in namespace `RND2`:

* old CERTIFIED cells are not re-searched — their kernel-checked
  theorems in `wip.rnDict` are referenced by name (`open RND`);
* old SORRIED cells (the 83 open + 4 refuted) and all NEW cells
  (a row/column index ≥ 15) are resolved with the escalated stages
  (`side5`: small direct search, standard battery, exhaustive ≤4-world
  battery, rooted 5-world battery, budgeted search + cut-chains
  through all 19 representatives);
* `cells2` resolves named cells into `wip/gen2/<name>.cell` files so
  the work parallelises across processes; `pending2` prints the
  inventory of cells that need search; `assemble2` reads everything
  back and prints the full `rnDict2.lean`. -/

/-- The 87 sorried cells of `wip/rnDict.lean` (83 open + 4 refuted). -/
def oldSorried : List String :=
  ["cAnd_4_14", "cAnd_8_10", "cAnd_8_11", "cAnd_8_12", "cAnd_8_14",
   "cAnd_9_13", "cAnd_9_14", "cAnd_10_13", "cAnd_10_14", "cAnd_11_13",
   "cAnd_11_14", "cAnd_12_13", "cAnd_12_14", "cAnd_13_14",
   "cOr_2_13", "cOr_2_14", "cOr_3_13", "cOr_3_14", "cOr_4_14",
   "cOr_5_8", "cOr_5_14", "cOr_6_13", "cOr_6_14", "cOr_7_13",
   "cOr_7_14", "cOr_8_9", "cOr_8_10", "cOr_8_11", "cOr_8_12",
   "cOr_8_13", "cOr_8_14", "cOr_9_13", "cOr_9_14", "cOr_10_12",
   "cOr_10_13", "cOr_10_14", "cOr_11_12", "cOr_11_13", "cOr_11_14",
   "cOr_12_13", "cOr_12_14", "cOr_13_14",
   "cImp_8_4", "cImp_8_5", "cImp_8_7", "cImp_8_9", "cImp_8_10",
   "cImp_8_11", "cImp_8_12", "cImp_8_14", "cImp_9_4", "cImp_9_8",
   "cImp_10_4", "cImp_10_7", "cImp_10_8", "cImp_10_9", "cImp_10_12",
   "cImp_10_13", "cImp_10_14", "cImp_11_4", "cImp_11_7", "cImp_11_8",
   "cImp_11_9", "cImp_11_12", "cImp_11_13", "cImp_11_14", "cImp_12_4",
   "cImp_12_7", "cImp_12_8", "cImp_12_9", "cImp_12_11", "cImp_13_5",
   "cImp_13_8", "cImp_13_9", "cImp_13_11", "cImp_13_12", "cImp_13_14",
   "cImp_14_4", "cImp_14_5", "cImp_14_7", "cImp_14_8", "cImp_14_9",
   "cImp_14_11", "cImp_14_12", "cImp_14_13",
   "cBox_11", "cBox_14"]

/-- THE FINAL ENLARGED REPRESENTATIVE LIST for the round-2 dictionary:
the 15 certified classes plus the distinct classes among the §40
witnesses after pairwise separation (w1 ≡ w2 ≡ w3 collapse; `q15` is
the class of q9 ⊃ q4 ≡ q8 ∧ q10 ≡ q12 ⊃ q4; w4 = q14 ⊃ q4 is kept
separately iff distinct — adjust this list when the verdict lands). -/
def repsN : List PLLFormula := reps ++ [w2]

def NREPS : Nat := repsN.length

def repIdxN? (X : PLLFormula) : Option Nat := repsN.findIdx? (· = X)

def rN (i : Nat) : PLLFormula := repsN.getD i Fq

/-- Print a formula naming all `repsN` members `q0`–`q{N-1}` (for
`rnDict2.lean`). -/
partial def ppQN (X : PLLFormula) : String :=
  match repIdxN? X with
  | some i => s!"q{i}"
  | none =>
    match X with
    | .prop s => s!"(.prop \"{s}\")"
    | .falsePLL => ".falsePLL"
    | .and a b => s!"(.and {ppQN a} {ppQN b})"
    | .or a b => s!"(.or {ppQN a} {ppQN b})"
    | .ifThen a b => s!"(.ifThen {ppQN a} {ppQN b})"
    | .somehow a => s!"(.somehow {ppQN a})"

/-- Print a formula naming only representatives with index < `n`
(for the `def q<i>` lines of `rnDict2.lean`). -/
partial def ppFN19 (n : Nat) (X : PLLFormula) : String :=
  match (repIdxN? X).filter (· < n) with
  | some i => s!"q{i}"
  | none =>
    match X with
    | .prop s => s!"(.prop \"{s}\")"
    | .falsePLL => ".falsePLL"
    | .and a b => s!"(.and {ppFN19 n a} {ppFN19 n b})"
    | .or a b => s!"(.or {ppFN19 n a} {ppFN19 n b})"
    | .ifThen a b => s!"(.ifThen {ppFN19 n a} {ppFN19 n b})"
    | .somehow a => s!"(.somehow {ppFN19 n a})"

/-- Old table value for a certified old cell. -/
def oldVal : Conn → Nat → Nat → Nat
  | .cAnd, i, j => (RND.andT.getD i []).getD j 0
  | .cOr, i, j => (RND.orT.getD i []).getD j 0
  | .cImp, i, j => (RND.impT.getD i []).getD j 0

/-- Cell kind in the enlarged table. -/
inductive CK
  | triv (value : Nat) (expr : String)
  | mirror
  | oldcert (value : Nat) (name : String)
  | search

/-- Classify a binary cell of the 19-table (same priority order as
`resolveCell`, so old trivial cells reproduce identically). -/
def classify2 (c : Conn) (i j : Nat) : CK :=
  let comb := c.mk (rN i) (rN j)
  match repIdxN? comb with
  | some k => .triv k "Interd.refl _"
  | none =>
    let old : CK :=
      let nm := s!"c{c.nm}_{i}_{j}"
      if i ≤ 14 && j ≤ 14 && !(oldSorried.contains nm) then
        .oldcert (oldVal c i j) nm
      else .search
    match c with
    | .cAnd =>
      if i == 0 then .triv 0 "bot_and_i _"
      else if j == 0 then .triv 0 "(and_comm_i _ _).trans (bot_and_i _)"
      else if i == 1 then .triv j "top_and_i _"
      else if j == 1 then .triv i "(and_comm_i _ _).trans (top_and_i _)"
      else if i == j then .triv i "and_idem_i _"
      else if i > j then .mirror
      else old
    | .cOr =>
      if i == 0 then .triv j "bot_or_i _"
      else if j == 0 then .triv i "(or_comm_i _ _).trans (bot_or_i _)"
      else if i == 1 then .triv 1 "top_or_i _"
      else if j == 1 then .triv 1 "(or_comm_i _ _).trans (top_or_i _)"
      else if i == j then .triv i "or_idem_i _"
      else if i > j then .mirror
      else old
    | .cImp =>
      if i == 0 then .triv 1 "bot_imp_i _"
      else if i == 1 then .triv j "top_imp_i _"
      else if j == 1 then .triv 1 "imp_top_i _"
      else if i == j then .triv 1 "imp_self_i _"
      else old

/-- Classify a ◯-column cell of the 19-table. -/
def classifyBox2 (i : Nat) : CK :=
  let comb := (rN i).somehow
  match repIdxN? comb with
  | some k => .triv k "Interd.refl _"
  | none =>
    match rN i with
    | .somehow _ => .triv i "box_idem_i _"
    | _ =>
      if i ≤ 14 && !(oldSorried.contains s!"cBox_{i}") then
        .oldcert (RND.boxT.getD i 0) s!"cBox_{i}"
      else .search

/-- Print the inventory of cells needing search in the enlarged round. -/
def pending2Main : IO Unit := do
  let mut n := 0
  for c in [Conn.cAnd, Conn.cOr, Conn.cImp] do
    for i in List.range NREPS do
      for j in List.range NREPS do
        match classify2 c i j with
        | .search => IO.println s!"c{c.nm}_{i}_{j}"; n := n + 1
        | _ => pure ()
  for i in List.range NREPS do
    match classifyBox2 i with
    | .search => IO.println s!"cBox_{i}"; n := n + 1
    | _ => pure ()
  IO.eprintln s!"{n} cells need search"

def parseCell2 (c : String) : Option (String × PLLFormula) :=
  match c.splitOn "_" with
  | ["cAnd", i, j] => some (c, (rN i.toNat!).and (rN j.toNat!))
  | ["cOr", i, j] => some (c, (rN i.toNat!).or (rN j.toNat!))
  | ["cImp", i, j] => some (c, (rN i.toNat!).ifThen (rN j.toNat!))
  | ["cBox", i] => some (c, (rN i.toNat!).somehow)
  | _ => none

def stmt2 (c : String) : String :=
  match c.splitOn "_" with
  | ["cAnd", i, j] => s!"Interd (q{i}.and q{j})"
  | ["cOr", i, j] => s!"Interd (q{i}.or q{j})"
  | ["cImp", i, j] => s!"Interd (q{i}.ifThen q{j})"
  | ["cBox", i] => s!"Interd q{i}.somehow"
  | _ => "?"

/-- Escalated resolution of one searched cell against all 19
candidates: countermodel-first elimination via `side5`, match on both
directions proved (with emitted certificates), NEW CLASS when every
candidate is eliminated, OPEN otherwise. -/
def resolveSearched2 (bud : Nat) (name stmt : String) (comb : PLLFormula) :
    IO Cell := do
  let t0 ← IO.monoMsNow
  let mut matched : Option (Nat × String × String) := none
  let mut openK : List Nat := []
  for k in List.range NREPS do
    let D := rN k
    let a := side5 ppQN bud repsN comb D
    match a with
    | .refuted _ _ => pure ()
    | _ =>
      let b := side5 ppQN bud repsN D comb
      match b with
      | .refuted _ _ => pure ()
      | _ =>
        match a, b with
        | .proved e1, .proved e2 =>
            matched := some (k, (if k == 1 then "topD" else e1), e2)
            break
        | _, _ => openK := openK ++ [k]
  let t1 ← IO.monoMsNow
  match matched with
  | some (k, e1, e2) =>
      IO.eprintln s!"  {name} -> {k} ({t1-t0}ms)"
      return { value := k, expr := name, searched := true,
               thm := some s!"theorem {name} : {stmt} q{k} :=\n  ⟨{e1},\n   {e2}⟩" }
  | none =>
    match openK with
    | [] =>
        IO.eprintln s!"  !! {name}: NEW CLASS (all {NREPS} eliminated) ({t1-t0}ms)"
        return { value := 0, expr := name, searched := true,
                 thm := some s!"/-- REFUTED CELL (new class): certified ≤5-world countermodels\neliminate EVERY candidate — this combination is not interderivable\nwith any of the {NREPS} representatives, so the enlarged closure FAILS\nhere.  The stated collapse (to q0, a placeholder) is FALSE; the\n`sorry` records the failure point. -/\ntheorem {name} : {stmt} q0 := sorry" }
    | l =>
        let k := l.headD 0
        IO.eprintln s!"  ?? {name}: OPEN {l} ({t1-t0}ms)"
        return { value := k, expr := name, searched := true,
                 thm := some s!"/-- OPEN CELL: candidates {l} neither proved (searcher + cut-chains\nthrough all 19 representatives) nor refuted (countermodel batteries\nincluding the exhaustive ≤5-world sweep).  Sorried at the first open\ncandidate. -/\ntheorem {name} : {stmt} q{k} := sorry" }

/-- Resolve the named cells and persist each result to
`wip/gen2/<name>.cell` (value / expr / theorem text). -/
def cells2Main (bud : Nat) (cells : List String) : IO Unit := do
  IO.FS.createDirAll "wip/gen2"
  for c in cells do
    match parseCell2 c with
    | none => IO.eprintln s!"bad cell name {c}"
    | some (n, X) =>
      let cell ← resolveSearched2 bud n (stmt2 n) X
      let thmTxt := cell.thm.getD ""
      IO.FS.writeFile s!"wip/gen2/{n}.cell"
        s!"{cell.value}\n{cell.expr}\n{thmTxt}"
      IO.eprintln s!"  [written] gen2/{n}.cell"
      (← IO.getStderr).flush

/-- Hand-certificate overrides for searcher-hard cells (filled in
after the sweep; the derivations live in `wip/rnSepColl.lean`, which
`wip/rnDict2.lean` imports).  Entries: (cell name, value, theorem
text). -/
def overrides : List (String × Nat × String) := [
  ("cAnd_10_14", 5, "theorem cAnd_10_14 : Interd (q10.and q14) q5 := hand_cAnd_10_14"),
  ("cAnd_10_15", 15, "theorem cAnd_10_15 : Interd (q10.and q15) q15 := hand_cAnd_10_15"),
  ("cAnd_11_14", 9, "theorem cAnd_11_14 : Interd (q11.and q14) q9 := hand_cAnd_11_14"),
  ("cAnd_11_15", 15, "theorem cAnd_11_15 : Interd (q11.and q15) q15 := hand_cAnd_11_15"),
  ("cAnd_12_13", 12, "theorem cAnd_12_13 : Interd (q12.and q13) q12 := hand_cAnd_12_13"),
  ("cAnd_12_14", 12, "theorem cAnd_12_14 : Interd (q12.and q14) q12 := hand_cAnd_12_14"),
  ("cAnd_12_15", 4, "theorem cAnd_12_15 : Interd (q12.and q15) q4 := hand_cAnd_12_15"),
  ("cAnd_13_15", 15, "theorem cAnd_13_15 : Interd (q13.and q15) q15 := hand_cAnd_13_15"),
  ("cAnd_14_15", 4, "theorem cAnd_14_15 : Interd (q14.and q15) q4 := hand_cAnd_14_15"),
  ("cAnd_4_14", 4, "theorem cAnd_4_14 : Interd (q4.and q14) q4 := hand_cAnd_4_14"),
  ("cAnd_8_10", 15, "theorem cAnd_8_10 : Interd (q8.and q10) q15 := hand_cAnd_8_10"),
  ("cAnd_8_15", 15, "theorem cAnd_8_15 : Interd (q8.and q15) q15 := hand_cAnd_8_15"),
  ("cAnd_9_13", 9, "theorem cAnd_9_13 : Interd (q9.and q13) q9 := hand_cAnd_9_13"),
  ("cAnd_9_14", 9, "theorem cAnd_9_14 : Interd (q9.and q14) q9 := hand_cAnd_9_14"),
  ("cAnd_9_15", 4, "theorem cAnd_9_15 : Interd (q9.and q15) q4 := hand_cAnd_9_15"),
  ("cImp_10_15", 8, "theorem cImp_10_15 : Interd (q10.ifThen q15) q8 := hand_cImp_10_15"),
  ("cImp_10_8", 8, "theorem cImp_10_8 : Interd (q10.ifThen q8) q8 := hand_cImp_10_8"),
  ("cImp_10_9", 14, "theorem cImp_10_9 : Interd (q10.ifThen q9) q14 := hand_cImp_10_9"),
  ("cImp_11_12", 14, "theorem cImp_11_12 : Interd (q11.ifThen q12) q14 := hand_cImp_11_12"),
  ("cImp_11_14", 14, "theorem cImp_11_14 : Interd (q11.ifThen q14) q14 := hand_cImp_11_14"),
  ("cImp_12_4", 15, "theorem cImp_12_4 : Interd (q12.ifThen q4) q15 := hand_cImp_12_4"),
  ("cImp_13_8", 8, "theorem cImp_13_8 : Interd (q13.ifThen q8) q8 := hand_cImp_13_8"),
  ("cImp_5_15", 8, "theorem cImp_5_15 : Interd (q5.ifThen q15) q8 := hand_cImp_5_15"),
  ("cImp_7_15", 10, "theorem cImp_7_15 : Interd (q7.ifThen q15) q10 := hand_cImp_7_15"),
  ("cImp_8_10", 10, "theorem cImp_8_10 : Interd (q8.ifThen q10) q10 := hand_cImp_8_10"),
  ("cImp_9_8", 8, "theorem cImp_9_8 : Interd (q9.ifThen q8) q8 := hand_cImp_9_8"),
  ("cOr_11_15", 11, "theorem cOr_11_15 : Interd (q11.or q15) q11 := hand_cOr_11_15"),
  ("cOr_12_13", 13, "theorem cOr_12_13 : Interd (q12.or q13) q13 := hand_cOr_12_13"),
  ("cOr_12_14", 14, "theorem cOr_12_14 : Interd (q12.or q14) q14 := hand_cOr_12_14"),
  ("cOr_13_15", 13, "theorem cOr_13_15 : Interd (q13.or q15) q13 := hand_cOr_13_15"),
  ("cOr_2_13", 13, "theorem cOr_2_13 : Interd (q2.or q13) q13 := hand_cOr_2_13"),
  ("cOr_2_14", 14, "theorem cOr_2_14 : Interd (q2.or q14) q14 := hand_cOr_2_14"),
  ("cOr_2_15", 15, "theorem cOr_2_15 : Interd (q2.or q15) q15 := hand_cOr_2_15"),
  ("cOr_3_13", 13, "theorem cOr_3_13 : Interd (q3.or q13) q13 := hand_cOr_3_13"),
  ("cOr_3_14", 14, "theorem cOr_3_14 : Interd (q3.or q14) q14 := hand_cOr_3_14"),
  ("cOr_3_15", 15, "theorem cOr_3_15 : Interd (q3.or q15) q15 := hand_cOr_3_15"),
  ("cOr_4_14", 14, "theorem cOr_4_14 : Interd (q4.or q14) q14 := hand_cOr_4_14"),
  ("cOr_4_15", 15, "theorem cOr_4_15 : Interd (q4.or q15) q15 := hand_cOr_4_15"),
  ("cOr_5_14", 14, "theorem cOr_5_14 : Interd (q5.or q14) q14 := hand_cOr_5_14"),
  ("cOr_6_13", 13, "theorem cOr_6_13 : Interd (q6.or q13) q13 := hand_cOr_6_13"),
  ("cOr_6_14", 14, "theorem cOr_6_14 : Interd (q6.or q14) q14 := hand_cOr_6_14"),
  ("cOr_7_13", 13, "theorem cOr_7_13 : Interd (q7.or q13) q13 := hand_cOr_7_13"),
  ("cOr_7_14", 14, "theorem cOr_7_14 : Interd (q7.or q14) q14 := hand_cOr_7_14"),
  ("cOr_8_13", 13, "theorem cOr_8_13 : Interd (q8.or q13) q13 := hand_cOr_8_13"),
  ("cOr_8_15", 8, "theorem cOr_8_15 : Interd (q8.or q15) q8 := hand_cOr_8_15"),
  ("cOr_9_14", 14, "theorem cOr_9_14 : Interd (q9.or q14) q14 := hand_cOr_9_14"),
  ("cImp_10_14", 14, "theorem cImp_10_14 : Interd (q10.ifThen q14) q14 := hand_cImp_10_14"),
  ("cImp_11_8", 8, "theorem cImp_11_8 : Interd (q11.ifThen q8) q8 := hand_cImp_11_8"),
  ("cImp_12_15", 15, "theorem cImp_12_15 : Interd (q12.ifThen q15) q15 := hand_cImp_12_15"),
  ("cImp_14_5", 10, "theorem cImp_14_5 : Interd (q14.ifThen q5) q10 := hand_cImp_14_5"),
  ("cImp_8_15", 10, "theorem cImp_8_15 : Interd (q8.ifThen q15) q10 := hand_cImp_8_15"),
  ("cImp_9_15", 15, "theorem cImp_9_15 : Interd (q9.ifThen q15) q15 := hand_cImp_9_15"),
  ("cImp_14_15", 15, "theorem cImp_14_15 : Interd (q14.ifThen q15) q15 := hand_cImp_14_15"),
  ("cImp_14_4", 15, "theorem cImp_14_4 : Interd (q14.ifThen q4) q15 := coll_w2_w4.symm"),
  ("cImp_14_8", 8, "theorem cImp_14_8 : Interd (q14.ifThen q8) q8 := hand_cImp_14_8"),
  ("cBox_14", 14, "theorem cBox_14 : Interd q14.somehow q14 := hand_cBox_14"),
  ("cImp_11_15", 15, "theorem cImp_11_15 : Interd (q11.ifThen q15) q15 := hand_cImp_11_15"),
  ("cImp_13_15", 15, "theorem cImp_13_15 : Interd (q13.ifThen q15) q15 := hand_cImp_13_15"),
  ("cOr_9_13", 13, "theorem cOr_9_13 : Interd (q9.or q13) q13 := hand_cOr_9_13"),
  ("cImp_12_8", 8, "theorem cImp_12_8 : Interd (q12.ifThen q8) q8 := hand_cImp_12_8"),
  ("cImp_10_12", 14, "theorem cImp_10_12 : Interd (q10.ifThen q12) q14 := hand_cImp_10_12"),
  ("cImp_11_9", 14, "theorem cImp_11_9 : Interd (q11.ifThen q9) q14 := hand_cImp_11_9"),
  ("cImp_11_4", 4, "theorem cImp_11_4 : Interd (q11.ifThen q4) q4 := hand_cImp_11_4")]

/-- Read a persisted cell file. -/
def readCell (name : String) : IO (Option Cell) := do
  let path := s!"wip/gen2/{name}.cell"
  if !(← System.FilePath.pathExists path) then
    return none
  let txt ← IO.FS.readFile path
  let lines := txt.splitOn "\n"
  let value := (lines.getD 0 "0").toNat!
  let expr := lines.getD 1 ""
  let thmTxt := String.intercalate "\n" (lines.drop 2)
  return some { value := value, expr := expr, searched := true,
                thm := if thmTxt.trim.isEmpty then none else some thmTxt }

def header2 : String :=
s!"import wip.rnDict2Hand

/-!
# The enlarged RN(◯,{"{}"}) dictionary round: {NREPS} representatives

GENERATED FILE — do not edit by hand.  Produced by
`wip/rnDictGen.lean` (`pending2` / `cells2` / `assemble2` modes).

The 15 certified dictionary classes of `wip/rnDict.lean` enlarged by
the distinct classes among the §40 closure-failure witnesses after
pairwise separation (`wip/rnSep.lean`: w1 ≡ w2 ≡ w3, so q15 is the
class of q9 ⊃ q4 ≡ q8 ∧ q10 ≡ q12 ⊃ q4), closed under
∧/∨/⊃/◯ for ONE round with kernel-checked `Interd` certificates.
Old certified cells reference their `wip.rnDict` theorems by name;
old sorried cells and all new cells were re-resolved with the
escalated stages (exhaustive ≤4-world battery, exhaustive rooted
5-world battery, budgeted G4iLL″ search with cut-chains through all
19 representatives).  Cells that still resist are recorded as sorried
lemmas (OPEN, with candidate shortlists) or as REFUTED CELLS (new
classes beyond the 19 — the closure fails there; witness theorems in
`wip/rnDictRefute2.lean`).
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND2

open RND
"

/-- Assemble `wip/rnDict2.lean` from generic cells, referenced old
certificates, and the persisted `gen2` cell files. -/
def assemble2Main : IO Unit := do
  let conns : List Conn := [.cAnd, .cOr, .cImp]
  let mut missing : Array String := #[]
  -- resolve all cells
  let mut grids : Array (Array (Array Cell)) := #[]
  for c in conns do
    let mut grid : Array (Array Cell) := #[]
    for i in List.range NREPS do
      let mut row : Array Cell := #[]
      for j in List.range NREPS do
        match classify2 c i j with
        | .triv v e => row := row.push { value := v, expr := e }
        | .oldcert v nm => row := row.push { value := v, expr := nm }
        | .mirror => row := row.push default  -- second pass
        | .search =>
          let nm := s!"c{c.nm}_{i}_{j}"
          match overrides.find? (·.1 == nm) with
          | some (_, v, t) =>
              row := row.push { value := v, expr := nm, searched := true, thm := some t }
          | none =>
          match ← readCell nm with
          | some cell => row := row.push cell
          | none => missing := missing.push nm; row := row.push default
      grid := grid.push row
    -- mirror pass
    let comm := if c == .cImp then "" else
      if c == .cAnd then "and_comm_i" else "or_comm_i"
    for i in List.range NREPS do
      for j in List.range NREPS do
        match classify2 c i j with
        | .mirror =>
          let t := ((grid.getD j #[]).getD i default)
          let e := s!"({comm} _ _).trans ({t.expr})"
          let cell : Cell := { value := t.value, expr := e }
          grid := grid.set! i ((grid.getD i #[]).set! j cell)
        | _ => pure ()
    grids := grids.push grid
  let mut boxCol : Array Cell := #[]
  for i in List.range NREPS do
    match classifyBox2 i with
    | .triv v e => boxCol := boxCol.push { value := v, expr := e }
    | .oldcert v nm => boxCol := boxCol.push { value := v, expr := nm }
    | .mirror => boxCol := boxCol.push default
    | .search =>
      let nm := s!"cBox_{i}"
      match overrides.find? (·.1 == nm) with
      | some (_, v, t) =>
          boxCol := boxCol.push { value := v, expr := nm, searched := true, thm := some t }
      | none =>
      match ← readCell nm with
      | some cell => boxCol := boxCol.push cell
      | none => missing := missing.push nm; boxCol := boxCol.push default
  if !missing.isEmpty then
    IO.eprintln s!"MISSING cell files ({missing.size}): {missing.toList}"
    return
  -- emit
  let mut out : Array String := #[header2]
  out := out.push "/-! ## The four new representatives -/\n"
  for i in (List.range NREPS).drop 15 do
    out := out.push s!"def q{i} : PLLFormula := {ppFN19 i (rN i)}"
  let repList := String.intercalate ", " ((List.range NREPS).map (s!"q{·}"))
  out := out.push s!"\ndef repsL2 : List PLLFormula := [{repList}]"
  out := out.push s!"\ndef rep2 : Fin {NREPS} → PLLFormula := fun i => repsL2.getD i.val .falsePLL"
  out := out.push "\n/-! ## The closure tables -/\n"
  for (c, g) in conns.zip grids.toList do
    let rows := g.toList.map fun row =>
      "[" ++ String.intercalate ", " (row.toList.map (s!"{·.value}")) ++ "]"
    out := out.push s!"def {c.nm.toLower}2T : List (List Nat) :=\n  [{String.intercalate ",\n   " rows}]"
  out := out.push s!"\ndef box2T : List Nat := [{String.intercalate ", " (boxCol.toList.map (s!"{·.value}"))}]"
  for c in conns do
    out := out.push s!"\ndef {c.nm.toLower}2Idx (i j : Fin {NREPS}) : Fin {NREPS} :=\n  ⟨(({c.nm.toLower}2T.getD i.val []).getD j.val 0) % {NREPS}, Nat.mod_lt _ (by decide)⟩"
  out := out.push s!"\ndef box2Idx (i : Fin {NREPS}) : Fin {NREPS} :=\n  ⟨(box2T.getD i.val 0) % {NREPS}, Nat.mod_lt _ (by decide)⟩"
  out := out.push "\n/-! ## Searched-cell certificates (escalated round) -/\n"
  let mut nSorry := 0
  let mut sorries : Array String := #[]
  for g in grids do
    for row in g do
      for cell in row do
        if let some t := cell.thm then
          out := out.push (t ++ "\n")
          if t.endsWith "sorry" then
            nSorry := nSorry + 1; sorries := sorries.push cell.expr
  for cell in boxCol do
    if let some t := cell.thm then
      out := out.push (t ++ "\n")
      if t.endsWith "sorry" then
        nSorry := nSorry + 1; sorries := sorries.push cell.expr
  out := out.push "/-! ## The closure theorems -/\n"
  for (c, g) in conns.zip grids.toList do
    let mut s := s!"theorem {c.nm.toLower}2_ok (i j : Fin {NREPS}) :\n    Interd ((rep2 i).{c.opStr} (rep2 j)) (rep2 ({c.nm.toLower}2Idx i j)) :=\n  match i, j with\n"
    for i in List.range NREPS do
      for j in List.range NREPS do
        s := s ++ s!"  | ⟨{i}, _⟩, ⟨{j}, _⟩ => {((g.getD i #[]).getD j default).expr}\n"
    s := s ++ s!"  | ⟨_+{NREPS}, h⟩, _ => absurd h (by omega)\n"
    s := s ++ s!"  | _, ⟨_+{NREPS}, h⟩ => absurd h (by omega)\n"
    out := out.push s
  let mut sb := s!"theorem box2_ok (i : Fin {NREPS}) :\n    Interd (rep2 i).somehow (rep2 (box2Idx i)) :=\n  match i with\n"
  for i in List.range NREPS do
    sb := sb ++ s!"  | ⟨{i}, _⟩ => {(boxCol.getD i default).expr}\n"
  sb := sb ++ s!"  | ⟨_+{NREPS}, h⟩ => absurd h (by omega)\n"
  out := out.push sb
  let crankMax := (repsN.map crank).foldl max 0
  let totalCells := 3 * NREPS * NREPS + NREPS
  out := out.push "end RND2\n"
  out := out.push ("open RND2 in
/-- **The enlarged RN(◯,{}) dictionary round**: " ++ toString NREPS ++ " variable-free
representatives, crank bound " ++ toString crankMax ++ ", connective-closure tables
kernel-checked away from the sorried cells (" ++ Nat.repr nSorry ++ " of " ++ Nat.repr totalCells ++ "; when that
count is 0 this record is a full certified dictionary). -/
def rnDict" ++ toString NREPS ++ " : RNDict where
  n := " ++ toString NREPS ++ "
  rep := RND2.rep2
  rep_varFree := by decide
  crankBound := " ++ toString crankMax ++ "
  rep_crank_le := by decide
  botIdx := ⟨0, by decide⟩
  bot_interd := Interd.refl _
  andIdx := RND2.and2Idx
  orIdx := RND2.or2Idx
  impIdx := RND2.imp2Idx
  boxIdx := RND2.box2Idx
  and_interd := RND2.and2_ok
  or_interd := RND2.or2_ok
  imp_interd := RND2.imp2_ok
  box_interd := RND2.box2_ok

/-! ## Axiom audit -/
" ++ (if nSorry == 0 then "
/--
info: 'PLLND.SemUI.rnDict" ++ toString NREPS ++ "' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnDict" ++ toString NREPS ++ "" else "
-- PARTIAL instantiation: " ++ Nat.repr nSorry ++ " cells are sorried (see the
-- per-cell doc comments: REFUTED/OPEN).  No #guard_msgs pin.
#print axioms rnDict" ++ toString NREPS ++ "") ++ "

end SemUI
end PLLND")
  let stdout ← IO.getStdout
  for s in out do
    stdout.putStrLn s
  stdout.flush
  IO.eprintln s!"assembled: {nSorry} sorried cells: {sorries.toList}"

/-! ## Refutation-witness emission over the 19 classes
(`rnDictGen refute2 <cell>...` → `wip/rnDictRefute2.lean`) -/

def refuteArm2 (X : PLLFormula) (k : Nat) : Option String :=
  let D := rN k
  match findCM5 [X] D with
  | some (M, w) =>
      some s!"  | ⟨{k}, _⟩ => fun h => FinCM.not_provable_of_check (M := {fmtCM M}) (w := {w}) (C := q{k}) (by decide) h.1"
  | none =>
    match findCM5 [D] X with
    | some (M, w) =>
        some s!"  | ⟨{k}, _⟩ => fun h => FinCM.not_provable_of_check (M := {fmtCM M}) (w := {w}) (Γ := [q{k}]) (by decide) h.2"
    | none => none

def refuteHeader2 : String :=
s!"import wip.rnDict2

/-!
# Machine-checked closure failure of the enlarged ({NREPS}-class) round

GENERATED FILE (`rnDictGen refute2 ...`) — do not edit by hand.

For each witness cell below, the theorem eliminates EVERY candidate
class among the {NREPS}: one direction of the would-be collapse is refuted
by a pinned finite countermodel (staged batteries up to the exhaustive
rooted 5-world sweep), checked by the kernel via `FinCM.checkB` +
`FinCM.not_provable_of_check` (`by decide` on closed data).  Each
witness is therefore a NEW interderivability class beyond the 19.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND2

open RND
"

def refute2Cell (name : String) (X : PLLFormula) (stmtX : String) :
    IO (Option String) := do
  let mut arms : Array String := #[]
  for k in List.range NREPS do
    match refuteArm2 X k with
    | some a => arms := arms.push a
    | none =>
        IO.eprintln s!"  !! {name}: candidate {k} not countermodel-refuted; no witness theorem"
        return none
  let body := String.intercalate "\n" arms.toList
  return some (s!"/-- `{stmtX}` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_{name} : ∀ k : Fin {NREPS}, ¬ Interd ({stmtX}) (rep2 k) :=
  fun k => match k with
" ++ body ++ s!"
  | ⟨_+{NREPS}, hh⟩ => absurd hh (by omega)
")

def stmtOf2 (c : String) : String :=
  match c.splitOn "_" with
  | ["cAnd", i, j] => s!"q{i}.and q{j}"
  | ["cOr", i, j] => s!"q{i}.or q{j}"
  | ["cImp", i, j] => s!"q{i}.ifThen q{j}"
  | ["cBox", i] => s!"q{i}.somehow"
  | _ => "?"

def refute2Main (cells : List String) : IO Unit := do
  let mut out : Array String := #[refuteHeader2]
  let mut names : Array String := #[]
  for c in cells do
    match parseCell2 c with
    | none => IO.eprintln s!"bad cell name {c}"
    | some (n, X) =>
      match ← refute2Cell n X (stmtOf2 c) with
      | some t => out := out.push t; names := names.push s!"refute_{n}"
      | none => pure ()
  out := out.push "/-! ## Axiom audit -/\n"
  for n in names do
    out := out.push ("/--\ninfo: 'PLLND.SemUI.RND2." ++ n ++ "' depends on axioms: [propext, Quot.sound]\n-/\n#guard_msgs in\n#print axioms " ++ n ++ "\n")
  out := out.push "end RND2\nend SemUI\nend PLLND"
  let stdout ← IO.getStdout
  for x in out do
    stdout.putStrLn x
  stdout.flush

/-- Formula size (nodes). -/
def sz' : PLLFormula → Nat
  | .and a b => sz' a + sz' b + 1
  | .or a b => sz' a + sz' b + 1
  | .ifThen a b => sz' a + sz' b + 1
  | .somehow a => sz' a + 1
  | _ => 1

/-- Crank data for the band/plateau analysis (PROGRESS §41): the
crank of every representative and of the given cells' combinations. -/
def cranksMain (cells : List String) : IO Unit := do
  for i in List.range NREPS do
    IO.println s!"crank q{i} = {crank (rN i)}  (sz {sz' (rN i)})"
  for c in cells do
    match parseCell2 c with
    | some (n, X) => IO.println s!"crank {n} = {crank X}  (sz {sz' X})"
    | none => IO.eprintln s!"bad cell name {c}"

/-- Raw bounded-search probe between two cells' combinations:
distinguishes BUDGET-OUT from search-space exhaustion. -/
def probeBMain (bud : Nat) (ca cb : String) : IO Unit := do
  match parseCell2 ca, parseCell2 cb with
  | some (_, A), some (_, B) =>
    let t0 ← IO.monoMsNow
    let r1 := G4cTm.findBounded bud [A] B
    let t1 ← IO.monoMsNow
    IO.println s!"[{ca}]⊢{cb}: {tagB r1} ({t1-t0}ms)"
    (← IO.getStdout).flush
    let r2 := G4cTm.findBounded bud [B] A
    let t2 ← IO.monoMsNow
    IO.println s!"[{cb}]⊢{ca}: {tagB r2} ({t2-t1}ms)"
  | _, _ => IO.eprintln "bad cell names"

/-- Certified-complete `G4s` truth probe (sound both ways at full
fuel, but only run at small fuel — an external timeout is advised;
`true` genuinely means derivable). -/
def provfMain (fuel : Nat) (ca cb : String) : IO Unit := do
  match parseCell2 ca, parseCell2 cb with
  | some (_, A), some (_, B) =>
    let t0 ← IO.monoMsNow
    let r := provF fuel [A] B
    let t1 ← IO.monoMsNow
    IO.println s!"provF {fuel} [{ca}]⊢{cb}: {r} ({t1-t0}ms)"
  | _, _ => IO.eprintln "bad cell names"

/-! ## Gap-row re-audit (`gaprow <bud> <idx>...`)

The v2quant ∀-side membership test for the gap row ◯(◯p⊃p): a class
`D` enters the ∀-join iff `[D] ⊢ ◯(◯p⊃p)` with `p` a fresh atom.  The
recorded value ∀p.◯(◯p⊃p) = ◯⊥ survives an enlargement iff no new
class derives the row without itself deriving ◯⊥. -/

def gapRow : PLLFormula :=
  ((PLLFormula.prop "p").somehow.ifThen (PLLFormula.prop "p")).somehow

def gaprowMain (bud : Nat) (idxs : List Nat) : IO Unit := do
  for i in idxs do
    let D := rN i
    let t0 ← IO.monoMsNow
    let v :=
      match Search.decide cfgD [D] gapRow with
      | .refuted M w _ => s!"REFUTED(cfgD) {fmtCM M} @ {w}"
      | .proved _ => "proved"
      | .unknown =>
        match Search.decide cfgBig [D] gapRow with
        | .refuted M w _ => s!"REFUTED(big4) {fmtCM M} @ {w}"
        | .proved _ => "proved"
        | .unknown =>
          match (G4cTm.findBounded bud [D] gapRow).1 with
          | some _ => "proved"
          | none =>
            match Search.decide cfg5 [D] gapRow with
            | .refuted M w _ => s!"REFUTED(rooted5) {fmtCM M} @ {w}"
            | .proved _ => "proved"
            | .unknown => "unknown"
    let t1 ← IO.monoMsNow
    IO.println s!"[q{i}] ⊢ ◯(◯p⊃p): {v} ({t1-t0}ms)"
    if v == "proved" then
      let bb := rN 2
      let v2 :=
        match Search.decide cfgD [D] bb with
        | .refuted _ _ _ => "REFUTED — the ∀-join RISES above ◯⊥"
        | .proved _ => "proved — join stays ◯⊥"
        | .unknown =>
          match (G4cTm.findBounded bud [D] bb).1 with
          | some _ => "proved — join stays ◯⊥"
          | none => "unknown"
      IO.println s!"  [q{i}] ⊢ ◯⊥: {v2}"
    (← IO.getStdout).flush

/-- Streaming bounded rooted 6-world refuter for `[A] ⊢ B` (`A`, `B`
given as cell names; `A = "top"` for the empty context).  Enumerates
rooted 6-world frames — root 0 below all, any strict poset on
`{1..5}`, `rm ⊆ ri` with `|rm| ≤ rmMax` transitive, `fall` up-closed
with `|fall| ≤ fallMax` — testing world 0 with the fast vector scan
and gating hits through the verified `FinCM.checkB`.  NOT exhaustive
at 6 worlds (the rm/fall caps are real); a hit is still a pinned
certificate. -/
def ref6Main (rmMax fallMax : Nat) (ca cb : String) : IO Unit := do
  let Γ : List PLLFormula ←
    if ca == "top" then pure []
    else match parseCell2 ca with
      | some (_, A) => pure [A]
      | none => do IO.eprintln s!"bad cell name {ca}"; return
  match parseCell2 cb with
  | none => IO.eprintln s!"bad cell name {cb}"
  | some (_, B) =>
    let n := 6
    let base := (List.range n).filterMap fun v =>
      if v == 0 then none else some (0, v)
    let pool := (offdiag n).filter fun e => e.1 != 0 && e.2 != 0
    let mut tested : Nat := 0
    let t0 ← IO.monoMsNow
    for e in pool.sublists do
      if transB e then
        let ri := base ++ e
        for rm in ri.sublists do
          if rm.length ≤ rmMax && transB rm then
            for fall in (List.range n).sublists do
              if fall.length ≤ fallMax && upclB n ri fall then
                let f : Search.Frame := ⟨n, ri, rm, fall⟩
                let M := Search.toFinCM f []
                let vΓ := Γ.map (Search.forceV M)
                let vB := Search.forceV M B
                tested := tested + 1
                if vΓ.all (fun v => v.getD 0 false) && !(vB.getD 0 false) then
                  if FinCM.checkB M 0 Γ B then
                    let t1 ← IO.monoMsNow
                    IO.println s!"REFUTED [{ca}]⊢{cb}: {fmtCM M} @ 0  ({tested} frames, {t1-t0}ms)"
                    return
    let t1 ← IO.monoMsNow
    IO.println s!"no refutation: [{ca}]⊢{cb} unrefuted on {tested} rooted 6-world frames (rm ≤ {rmMax}, fall ≤ {fallMax}) ({t1-t0}ms)"

/-- Gap-row membership for named cells' combinations (spawned
classes): `[X] ⊢ ◯(◯p⊃p)`, then `[X] ⊢ ◯⊥` on a proof. -/
def gaprowCMain (bud : Nat) (cells : List String) : IO Unit := do
  for c in cells do
    match parseCell2 c with
    | none => IO.eprintln s!"bad cell name {c}"
    | some (n, D) =>
      let t0 ← IO.monoMsNow
      let v :=
        match Search.decide cfgD [D] gapRow with
        | .refuted M w _ => s!"REFUTED(cfgD) {fmtCM M} @ {w}"
        | .proved _ => "proved"
        | .unknown =>
          match Search.decide cfgBig [D] gapRow with
          | .refuted M w _ => s!"REFUTED(big4) {fmtCM M} @ {w}"
          | .proved _ => "proved"
          | .unknown =>
            match (G4cTm.findBounded bud [D] gapRow).1 with
            | some _ => "proved"
            | none => "unknown"
      let t1 ← IO.monoMsNow
      IO.println s!"[{n}] ⊢ ◯(◯p⊃p): {v} ({t1-t0}ms)"
      (← IO.getStdout).flush

/-- Pairwise escalated comparison of the named cells' combinations
(for classifying spawned classes among themselves). -/
def xsepMain (bud : Nat) (cells : List String) : IO Unit := do
  let parsed := cells.filterMap parseCell2
  for (na, A) in parsed do
    for (nb, B) in parsed do
      if na < nb then
        let t0 ← IO.monoMsNow
        let a := side5 ppQN bud repsN A B
        let b := match a with
          | .refuted _ _ => SideV.unknown
          | _ => side5 ppQN bud repsN B A
        let t1 ← IO.monoMsNow
        let verdict := match a, b with
          | .refuted _ _, _ => "DISTINCT"
          | _, .refuted _ _ => "DISTINCT"
          | .proved _, .proved _ => "COLLAPSE"
          | _, _ => "OPEN"
        IO.println s!"{na} vs {nb}: fwd {a.tag} ; bwd {b.tag} => {verdict} ({t1-t0}ms)"
        (← IO.getStdout).flush

end RNGen

def main : List String → IO Unit
  | [] => RNGen.main
  | "diag" :: cells => RNGen.diagMain cells
  | "oracle" :: fuel :: cells => RNGen.oracleMain fuel.toNat! cells
  | "refute" :: cells => RNGen.refuteMain cells
  | ["ent", fuel, i, j] => RNGen.entMain fuel.toNat! i.toNat! j.toNat!
  | ["stages", cell, k] => RNGen.stagesMain cell k.toNat!
  | ["battinfo"] => RNGen.battInfo
  | "sep" :: bud :: idxs =>
      RNGen.sepMain bud.toNat!
        (if idxs.isEmpty then List.range 19 else idxs.map (·.toNat!))
  | ["sepemit", bud] => RNGen.sepEmitMain bud.toNat!
  | ["pending2"] => RNGen.pending2Main
  | "cells2" :: bud :: cells => RNGen.cells2Main bud.toNat! cells
  | ["assemble2"] => RNGen.assemble2Main
  | "refute2" :: cells => RNGen.refute2Main cells
  | "xsep" :: bud :: cells => RNGen.xsepMain bud.toNat! cells
  | "gaprow" :: bud :: idxs =>
      RNGen.gaprowMain bud.toNat!
        (if idxs.isEmpty then List.range RNGen.NREPS else idxs.map (·.toNat!))
  | ["probeb", bud, ca, cb] => RNGen.probeBMain bud.toNat! ca cb
  | "cranks" :: cells => RNGen.cranksMain cells
  | "gaprowc" :: bud :: cells => RNGen.gaprowCMain bud.toNat! cells
  | ["ref6", rmMax, fallMax, ca, cb] =>
      RNGen.ref6Main rmMax.toNat! fallMax.toNat! ca cb
  | ["provf", fuel, ca, cb] => RNGen.provfMain fuel.toNat! ca cb
  | _ => IO.eprintln "usage: rnDictGen [diag|oracle|refute|ent|stages|battinfo|sep|sepemit|pending2|cells2|assemble2|refute2|xsep ...]"
