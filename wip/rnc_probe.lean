import LaxLogic.PLLSearch
import LaxLogic.PLLConfluentComplete
import LaxLogic.PLLSearchConf

/-!
# RNC(◯,{}) probe: the PCLL quotient of the variable-free dictionary

PCLL = PLL + the distribution scheme `◯(A∨B) ⊃ (◯A∨◯B)`; derivability
from premises is `ConfluentU.DerivU` (finitely many scheme instances as
extra hypotheses).  This probe decides, for the 15 PLL-class
representatives `q0 … q14` (wip/rnDict.lean) together with the four
closure witnesses of wip/rnDictRefute.lean, the full matrix of
PCLL-entailments, and reports the PCLL quotient RNC(◯,{}) of the
candidate set.

Verdict discipline (two-sided, certificate-carrying at probe level):

* PROVED — `Search.decide` finds a G4iLL″ proof term for
  `distF-instances ++ [X] ⊢ Y`; sound for PCLL whatever instances were
  added (`derivU_of_proved` below).  Tiers record the instantiation
  depth: 0 = no instances (plain PLL), 1 = instances for the
  ∨-subformulas of the sequent's closure (plus the four canonical
  fragment disjunctions), 2 = tier 1 enlarged once with the boxed
  variants `distF ◯A ◯B`, 3 = all pairs over the closure (capped).
* REFUTED — a world in a MUTUALLY CONFLUENT finite countermodel forces
  `X` but not `Y`.  Confluent models validate every `distF` instance
  (`force_somehow_or_dist_of_confluent`), so this refutes `DerivU`
  (`not_derivU_of_checkConf` below).  The battery is the complete
  enumeration of well-formed confluent frames on ≤ 4 worlds (no
  valuations needed: the fragment is variable-free).
* UNKNOWN — neither; asserts nothing.
-/

open PLLFormula

namespace PLLND
namespace RNC

/-! ## The 15 PLL representatives (probe order of wip/rnDict.lean) -/

def q0 : PLLFormula := .falsePLL
def q1 : PLLFormula := (.ifThen q0 q0)
def q2 : PLLFormula := (.somehow q0)
def q3 : PLLFormula := (.ifThen q2 q0)
def q4 : PLLFormula := (.or q2 q3)
def q5 : PLLFormula := (.somehow q3)
def q6 : PLLFormula := (.ifThen q3 q0)
def q7 : PLLFormula := (.or q3 q6)
def q8 : PLLFormula := (.ifThen q5 q4)
def q9 : PLLFormula := (.or q5 q6)
def q10 : PLLFormula := (.ifThen q6 q2)
def q11 : PLLFormula := (.or q6 q10)
def q12 : PLLFormula := (.somehow q7)
def q13 : PLLFormula := (.somehow q8)
def q14 : PLLFormula := (.ifThen q10 q5)

/-! ## The four closure witnesses (wip/rnDictRefute.lean) -/

def w15 : PLLFormula := q8.and q10
def w16 : PLLFormula := q9.ifThen q4
def w17 : PLLFormula := q12.ifThen q4
def w18 : PLLFormula := q14.ifThen q4

def candL : List (String × PLLFormula) :=
  [("q0", q0), ("q1", q1), ("q2", q2), ("q3", q3), ("q4", q4),
   ("q5", q5), ("q6", q6), ("q7", q7), ("q8", q8), ("q9", q9),
   ("q10", q10), ("q11", q11), ("q12", q12), ("q13", q13), ("q14", q14),
   ("w15=q8&q10", w15), ("w16=q9>q4", w16), ("w17=q12>q4", w17),
   ("w18=q14>q4", w18)]

def cands : Array PLLFormula := (candL.map (·.2)).toArray
def cnames : Array String := (candL.map (·.1)).toArray

/-! ## PCLL certificates

The refutation side (mutual confluence of a `FinCM`, computably, and the
certificate theorem gluing `FinCM.checkB` to `derivU_sound`) and the
positive bridge used to live here.  They have been **promoted into the
library** as `LaxLogic/PLLSearchConf.lean`, in the *same* namespace
`PLLND.RNC` and with the same statements, so a PCLL user need not
`import wip.…` any more.

The names re-exported by that import, and used unchanged below and in
`wip/rncCert.lean` / `wip/rncCertPos.lean`:

* `confB : FinCM → Bool`, `mutuallyConfluent_of_confB`;
* `not_derivU_of_checkConf` — the negative certificate theorem;
* `derivU_of_proved`, `derivU_of_proved'` — the positive bridge.

New there, and worth preferring over the hand-rolled battery below:
`refuteConf?` (confluence-filtered countermodel search) and
`WitnessConf.snippet` (paste-ready pinned theorem). -/

/-! ## The confluent battery: ALL well-formed confluent frames on ≤ 4
worlds (strict-poset `Rᵢ`, transitive `Rₘ ⊆ Rᵢ`, up-closed fallible
set; no valuations — the fragment is variable-free). -/

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => (subsets as) ++ (subsets as).map (a :: ·)

def pairsOf (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun a =>
    (List.range n).filterMap fun b => if a = b then none else some (a, b)

def memP (r : List (Nat × Nat)) (p : Nat × Nat) : Bool := decide (p ∈ r)

def transL (r : List (Nat × Nat)) : Bool :=
  r.all fun p => r.all fun q =>
    !(decide (p.2 = q.1)) || memP r (p.1, q.2)

def antisymL (r : List (Nat × Nat)) : Bool :=
  r.all fun p => !(memP r (p.2, p.1))

def upClosedL (r : List (Nat × Nat)) (s : List Nat) : Bool :=
  s.all fun w => r.all fun p =>
    !(decide (p.1 = w)) || decide (p.2 ∈ s)

def framesN (n : Nat) : List FinCM :=
  ((subsets (pairsOf n)).filter fun ri => transL ri && antisymL ri).flatMap
    fun ri =>
      ((subsets ri).filter transL).flatMap fun rm =>
        ((subsets (List.range n)).filter (upClosedL ri)).filterMap fun fall =>
          let M : FinCM := ⟨n, ri, rm, fall, []⟩
          if M.wellB && confB M then some M else none

def battery : Array FinCM :=
  (framesN 1 ++ framesN 2 ++ framesN 3 ++ framesN 4).toArray

/-! ## Positive tiers: distribution-instance selection -/

def subsF : PLLFormula → List PLLFormula
  | .and A B => .and A B :: (subsF A ++ subsF B)
  | .or A B => .or A B :: (subsF A ++ subsF B)
  | .ifThen A B => .ifThen A B :: (subsF A ++ subsF B)
  | .somehow A => .somehow A :: subsF A
  | F => [F]

def closureL (l : List PLLFormula) : List PLLFormula :=
  (l.flatMap subsF).eraseDups

def orPairs (l : List PLLFormula) : List (PLLFormula × PLLFormula) :=
  l.filterMap fun φ =>
    match φ with
    | .or A B => some (A, B)
    | _ => none

/-- The four disjunctions generating the fragment's ∨-structure:
`q4 = q2∨q3`, `q7 = q3∨q6`, `q9 = q5∨q6`, `q11 = q6∨q10`. -/
def canon4 : List (PLLFormula × PLLFormula) :=
  [(q2, q3), (q3, q6), (q5, q6), (q6, q10)]

def tier1 (X Y : PLLFormula) : List (PLLFormula × PLLFormula) :=
  (orPairs (closureL [X, Y]) ++ canon4).eraseDups

def tier2 (X Y : PLLFormula) : List (PLLFormula × PLLFormula) :=
  let t1 := tier1 X Y
  (t1 ++ t1.map fun p => (somehow p.1, somehow p.2)).eraseDups

def tier3 (X Y : PLLFormula) : List (PLLFormula × PLLFormula) :=
  let S := closureL [X, Y]
  let base := tier2 X Y
  if S.length ≤ 8 then
    ((S.flatMap fun A => S.map fun B => (A, B)) ++ base).eraseDups
  else base

def distsOf (ps : List (PLLFormula × PLLFormula)) : List PLLFormula :=
  ps.map fun p => ConfluentU.distF p.1 p.2

/-! ## The decision wrappers -/

/-- Strip a chain of top-level implications. -/
def stripImp : PLLFormula → List PLLFormula × PLLFormula
  | .ifThen A B => let (as, h) := stripImp B; (A :: as, h)
  | C => ([], C)

/-- Cheap syntactic derivability: `A₁ ⊃ … ⊃ H` with `H` among the
antecedents or the premises is LaxND-derivable (iden + weakening +
impIntro), likewise `H = ⊤`-shaped `q1`.  Guards against searcher
divergence on weakening-trivial cells (observed: `[q4] ⊢ q14⊃q4`). -/
def trivHead (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  let (as, h) := stripImp C
  decide (h ∈ Γ) || decide (h ∈ as) || decide (h = q1)

/-- ∧-leaves of a formula (with all intermediate conjunctions
implied). -/
def andParts : PLLFormula → List PLLFormula
  | .and A B => andParts A ++ andParts B
  | F => [F]

/-- Sound sequent preprocessing: uncurry the goal's top ⊃-chain into
premises (deduction theorem), then split every ∧-premise into its
leaves (andElim).  `LaxND Γ' C' → LaxND Γ C`, and the searcher fares
far better on the decomposed form (observed: it exhausts 200000 nodes
on the raw `[q8∧q10] ⊢ q8`). -/
def preprocess : List PLLFormula → PLLFormula → List PLLFormula × PLLFormula
  | Γ, .ifThen A B => preprocess (A :: Γ) B
  | Γ, C => (Γ.flatMap andParts, C)

def provedAt (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  trivHead Γ C ||
  -- emitClosureCap 0: stage 3 (the exponential closure emitter) can
  -- only produce refutations, which this positive wrapper discards —
  -- running it on every failing call is pure waste.  The stage-1
  -- battery sweep stays: its (non-confluent, PLL-level) refutations
  -- short-circuit hopeless `find` calls cheaply.
  (let (Γ', C') := preprocess Γ C
   decide (C' ∈ Γ') ||
   match Search.decide { findBudget := some b, emitClosureCap := 0 } Γ' C' with
   | .proved _ => true
   | _ => false)

inductive Verd where
  | proved (tier : Nat)
  | refuted (fi : Nat) (w : Nat)
  | unknown
deriving Repr, DecidableEq

def Verd.tag : Verd → String
  | .proved t => s!"P{t}"
  | .refuted fi w => s!"R[{fi}.{w}]"
  | .unknown => "?"

def Verd.isProved : Verd → Bool
  | .proved _ => true
  | _ => false

/-- ONE application of distribution, cut-style: find `(A, B)` with
`[X] ⊢ ◯(A∨B)` and `[◯A∨◯B, X] ⊢ Y`, both PLAIN PLL sequents (the
distF instance itself never enters the searcher's context — the two
halves compose through `DerivU.dist` + `DerivU.mp` + cut).  This is
the shape every PCLL-proper proof in this fragment actually has, and
the searcher handles both halves easily where it drowns with the
instance as a premise. -/
def provedDist1 (b : Nat) (X Y : PLLFormula) : Bool :=
  (tier1 X Y).any fun p =>
    let mid := (somehow p.1).or (somehow p.2)
    provedAt b [X] (somehow (p.1.or p.2)) && provedAt b [mid, X] Y

/-- Two nested applications of distribution, cut-style. -/
def provedDist2 (b : Nat) (X Y : PLLFormula) : Bool :=
  (tier1 X Y).any fun p =>
    let mid := (somehow p.1).or (somehow p.2)
    provedAt b [X] (somehow (p.1.or p.2)) &&
      ((tier1 mid Y).any fun q =>
        let mid2 := (somehow q.1).or (somehow q.2)
        provedAt b [mid, X] (somehow (q.1.or q.2)) &&
          provedAt b [mid2, mid, X] Y)

/-- Tier ladder.  0 = plain PLL; 1 = one distribution application
(cut-style); 2 = two nested applications; 3 = one distF instance as a
premise (searcher-hostile fallback); 4 = the full tier-1 instance
list.  The visited-set makes node budgets superlinear in time, so the
deep tiers are reserved for phase R's targeted push. -/
def decidePosT (cap : Nat) (X Y : PLLFormula) : Verd :=
  if provedAt 20000 [X] Y then .proved 0
  else if cap ≥ 1 && provedDist1 15000 X Y then .proved 1
  else if cap ≥ 2 && provedDist2 12000 X Y then .proved 2
  else if cap ≥ 3 &&
      (tier1 X Y).any (fun p => provedAt 8000 [X, ConfluentU.distF p.1 p.2] Y) then
    .proved 3
  else if cap ≥ 4 && provedAt 40000 (X :: distsOf (tier1 X Y)) Y then .proved 4
  else .unknown

/-- The matrix runs tier 0 and the two cut-style dist tiers; residual
`?` cells go to phase R (5-world sweep already folded into the battery;
big-budget push for survivors). -/
def decidePos (X Y : PLLFormula) : Verd := decidePosT 2 X Y

/-! ## The ROOTED 5-world confluent battery

A refuting world of any ≤5-world confluent model generates a rooted
≤5-world confluent submodel (up-sets are closed under `Rᵢ` and
`Rₘ ⊆ Rᵢ`, truth and mutual confluence restrict), so rooted frames with
the refuting world at the root are exhaustive at this size.  Frames are
deduplicated up to the permutation action on the non-root worlds
(lex-least `(ri₄, rm)` orbit representative). -/

def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true else if b < a then false else ltKey as bs

def keyOf (r : List (Nat × Nat)) : List Nat :=
  (r.map fun q => q.1 * 16 + q.2).mergeSort (fun a b => a ≤ b)

def pairKey (ri rm : List (Nat × Nat)) : List Nat :=
  keyOf ri ++ [999] ++ keyOf rm

def applyPerm (p : List Nat) (k : Nat) : Nat :=
  if k = 0 then 0 else p.getD (k - 1) k

def isCanon (ri4 rm : List (Nat × Nat)) : Bool :=
  let k0 := pairKey ri4 rm
  ([1, 2, 3, 4].permutations).all fun p =>
    let ri' := ri4.map fun q => (applyPerm p q.1, applyPerm p q.2)
    let rm' := rm.map fun q => (applyPerm p q.1, applyPerm p q.2)
    !(ltKey (pairKey ri' rm') k0)

def framesRooted5 : List FinCM :=
  let inner := (pairsOf 4).map fun q => (q.1 + 1, q.2 + 1)
  ((subsets inner).filter fun ri4 => transL ri4 && antisymL ri4).flatMap
    fun ri4 =>
      let ri := ((List.range 4).map fun k => (0, k + 1)) ++ ri4
      (((subsets ri).filter transL).filter (isCanon ri4)).flatMap fun rm =>
        if confB ⟨5, ri, rm, [], []⟩ then
          ((subsets (List.range 5)).filter (upClosedL ri)).filterMap
            fun fall =>
              let M : FinCM := ⟨5, ri, rm, fall, []⟩
              if M.wellB && confB M then some M else none
        else []

/-! ## The main loop -/

def vecOf (M : FinCM) (φ : PLLFormula) : Array Bool :=
  (Array.range M.n).map fun w => M.forceB w φ

/-- Precomputed forcing vectors: `bv[fi][ci][w]`. -/
def batVecs (fs : Array FinCM) (cs : Array PLLFormula) :
    Array (Array (Array Bool)) :=
  fs.map fun M => cs.map fun φ => vecOf M φ

/-- First confluent countermodel for `[cands[i]] ⊢ cands[j]` from the
precomputed vectors. -/
def refuteIdx (fs : Array FinCM) (bv : Array (Array (Array Bool)))
    (i j : Nat) : Option (Nat × Nat) :=
  let rec goF (fi : Nat) : Option (Nat × Nat) :=
    if _h : fi < fs.size then
      let vi := (bv.getD fi #[]).getD i #[]
      let vj := (bv.getD fi #[]).getD j #[]
      let rec goW (w : Nat) : Option Nat :=
        if w < vi.size then
          if vi.getD w false && !(vj.getD w false) then some w
          else goW (w + 1)
        else none
        termination_by vi.size - w
      match goW 0 with
      | some w => some (fi, w)
      | none => goF (fi + 1)
    else none
    termination_by fs.size - fi
  goF 0

def mainLoop : IO Unit := do
  let out ← IO.getStdout
  IO.println "=== RNC(◯,{}) probe: PCLL quotient of the variable-free dictionary ==="
  let t0 ← IO.monoMsNow
  let b4 := battery
  let b5 := framesRooted5.toArray
  let bat := b4 ++ b5
  IO.println s!"confluent battery: {b4.size} frames (ALL well-formed confluent frames ≤ 4 worlds) + {b5.size} rooted 5-world frames (canonical orbits; exhaustive at 5 by the generated-submodel argument)"
  let bv := batVecs bat cands
  let t1 ← IO.monoMsNow
  IO.println s!"  vectors precomputed in {t1 - t0} ms"
  -- the full 19×19 verdict matrix (ordered pairs, i ≠ j)
  let n := cands.size
  let mut verdicts : Array (Array Verd) := #[]
  for i in [0:n] do
    let mut row : Array Verd := #[]
    for j in [0:n] do
      if i = j then
        row := row.push (.proved 0)
      else
        match refuteIdx bat bv i j with
        | some (fi, w) => row := row.push (.refuted fi w)
        | none =>
          let ts ← IO.monoMsNow
          let v := decidePos (cands.getD i .falsePLL) (cands.getD j .falsePLL)
          let te ← IO.monoMsNow
          if te - ts > 3000 then
            IO.println s!"  [slow cell {cnames.getD i ""} ⊢ {cnames.getD j ""}: {te - ts} ms → {v.tag}]"
          row := row.push v
    verdicts := verdicts.push row
    IO.println s!"row {cnames.getD i ""}: {String.intercalate " " ((row.toList.map Verd.tag))}"
    out.flush
  let tm ← IO.monoMsNow
  IO.println s!"matrix done in {tm - t0} ms"
  -- A-table: the four witnesses vs the 15 representatives
  IO.println ""
  IO.println "=== (A) witnesses vs the 15 representatives (w⊢ρ / ρ⊢w) ==="
  for i in [15:19] do
    let mut line := s!"{cnames.getD i ""}: "
    for j in [0:15] do
      let a := (verdicts.getD i #[]).getD j .unknown
      let b := (verdicts.getD j #[]).getD i .unknown
      line := line ++ s!" {cnames.getD j ""}:{a.tag}/{b.tag}"
    IO.println line
  -- B-quotient: partition the 19 candidates by two-sided proved
  IO.println ""
  IO.println "=== (B) the PCLL quotient ==="
  let interd := fun (i j : Nat) =>
    ((verdicts.getD i #[]).getD j .unknown).isProved &&
    ((verdicts.getD j #[]).getD i .unknown).isProved
  let mut classes : Array (List Nat) := #[]
  for i in [0:n] do
    let mut placed := false
    for k in [0:classes.size] do
      if !placed then
        match (classes.getD k []).head? with
        | some r =>
          if interd i r then
            classes := classes.set! k ((classes.getD k []) ++ [i])
            placed := true
        | none => pure ()
    if !placed then
      classes := classes.push [i]
  IO.println s!"classes among the 19 candidates: {classes.size}"
  for k in [0:classes.size] do
    let members := (classes.getD k []).map fun i => cnames.getD i ""
    IO.println s!"  class {k}: {String.intercalate " ≡ " members}"
  -- consistency scan: interderivability must be transitive on proved data;
  -- flag any cross-class proved-both-ways pair (would indicate tier
  -- asymmetry, not a logic failure)
  let mut warn := 0
  for i in [0:n] do
    for j in [0:n] do
      if i < j && interd i j then
        let ci := classes.findIdx? (fun c => c.contains i)
        let cj := classes.findIdx? (fun c => c.contains j)
        if ci ≠ cj then
          warn := warn + 1
          IO.println s!"  WARNING: {cnames.getD i ""} ≡ {cnames.getD j ""} across classes"
  if warn = 0 then
    IO.println "  (partition consistent: no cross-class interderivable pair)"
  -- unresolved cells
  IO.println ""
  IO.println "=== unknown cells ==="
  let mut unk := 0
  for i in [0:n] do
    for j in [0:n] do
      if (verdicts.getD i #[]).getD j .unknown = .unknown then
        unk := unk + 1
        IO.println s!"  {cnames.getD i ""} ⊢ {cnames.getD j ""}: UNKNOWN"
  IO.println s!"total unknown: {unk}"
  -- frames used by refutations, for the record
  IO.println ""
  IO.println "=== battery frames cited above (index: n, ri, rm, fall) ==="
  let mut used : List Nat := []
  for i in [0:n] do
    for j in [0:n] do
      match (verdicts.getD i #[]).getD j .unknown with
      | .refuted fi _ => if !(used.contains fi) then used := used ++ [fi]
      | _ => pure ()
  for fi in used do
    let M := bat.getD fi ⟨0, [], [], [], []⟩
    IO.println s!"  [{fi}] n={M.n} ri={M.ri} rm={M.rm} fall={M.fall}"
  let tz ← IO.monoMsNow
  IO.println s!"=== done in {tz - t0} ms ==="

/-! ## Phase C: connective closure of the PCLL quotient

Run as `rncprobe c i0,i1,…` with the candidate indices of the class
representatives found by phase 1 (e.g. `rncprobe c 0,1,2,3,4,5,6,7,8,10,13,14`).
For each pair of representatives and each of ∧, ∨, ⊃ (and each
representative under ◯): shortlist the classes whose forcing vectors
agree with the combination on the whole confluent battery (vector
disagreement is a confluent countermodel, i.e. a PCLL separation), then
try to certify interderivability with a shortlisted representative
(both directions, tiers ≤ 2). -/

def classifyC (bat : Array FinCM) (rvecs : Array (Array (Array Bool)))
    (repFs : Array PLLFormula) (repNs : Array String)
    (nm : String) (F : PLLFormula) : IO Unit := do
  let out ← IO.getStdout
  let vF := bat.map fun M => vecOf M F
  let mut sl : List Nat := []
  for c in [0:repFs.size] do
    let mut ok := true
    for fi in [0:bat.size] do
      if ok && (rvecs.getD fi #[]).getD c #[] ≠ vF.getD fi #[] then
        ok := false
    if ok then sl := sl ++ [c]
  match sl with
  | [] => IO.println s!"  {nm}: NEW CLASS (vector-separated from every representative on the confluent battery)"
  | _ =>
    let mut done := false
    for c in sl do
      if !done then
        let d1 := decidePosT 2 F (repFs.getD c .falsePLL)
        let d2 := decidePosT 2 (repFs.getD c .falsePLL) F
        match d1, d2 with
        | .proved t1, .proved t2 =>
          IO.println s!"  {nm}: ≡ {repNs.getD c ""} (tiers {t1}/{t2})"
          done := true
        | _, _ => pure ()
    if !done then
      IO.println s!"  {nm}: OPEN, vector-shortlist {sl.map fun c => repNs.getD c ""}"
  out.flush

def phaseC (repIdx : List Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"=== (C) connective closure of the PCLL quotient, reps {repIdx.map fun i => cnames.getD i ""} ==="
  let bat := battery ++ framesRooted5.toArray
  let repFs : Array PLLFormula := (repIdx.map fun i => cands.getD i .falsePLL).toArray
  let repNs : Array String := (repIdx.map fun i => cnames.getD i "").toArray
  let rvecs := batVecs bat repFs
  let k := repFs.size
  for i in [0:k] do
    for j in [0:k] do
      let X := repFs.getD i .falsePLL
      let Y := repFs.getD j .falsePLL
      if i ≤ j then
        classifyC bat rvecs repFs repNs
          s!"{repNs.getD i ""} ∧ {repNs.getD j ""}" (X.and Y)
        classifyC bat rvecs repFs repNs
          s!"{repNs.getD i ""} ∨ {repNs.getD j ""}" (X.or Y)
      classifyC bat rvecs repFs repNs
        s!"{repNs.getD i ""} ⊃ {repNs.getD j ""}" (X.ifThen Y)
  for i in [0:k] do
    classifyC bat rvecs repFs repNs
      s!"◯{repNs.getD i ""}" (somehow (repFs.getD i .falsePLL))
  let tz ← IO.monoMsNow
  IO.println s!"=== phase C done in {tz - t0} ms ==="

def parseIdx (s : String) : List Nat :=
  (s.splitOn ",").filterMap (·.toNat?)

def parseCells (s : String) : List (Nat × Nat) :=
  (s.splitOn ",").filterMap fun c =>
    match c.splitOn "-" with
    | [a, b] =>
      match a.toNat?, b.toNat? with
      | some i, some j => some (i, j)
      | _, _ => none
    | _ => none

def phaseR (cells : List (Nat × Nat)) : IO Unit := do
  let t0 ← IO.monoMsNow
  let out ← IO.getStdout
  IO.println s!"=== (R) rooted 5-world confluent sweep, {cells.length} unknown cells ==="
  let fs := framesRooted5
  let t1 ← IO.monoMsNow
  IO.println s!"rooted 5-world confluent battery (canonical orbits): {fs.length} frames ({t1 - t0} ms)"
  out.flush
  let mut remaining := cells
  let mut idx := 0
  for M in fs do
    if !remaining.isEmpty then
      let mut still : List (Nat × Nat) := []
      for c in remaining do
        if M.forceB 0 (cands.getD c.1 .falsePLL) &&
            !(M.forceB 0 (cands.getD c.2 .falsePLL)) then
          IO.println s!"  {cnames.getD c.1 ""} ⊢ {cnames.getD c.2 ""}: REFUTED by rooted-5 frame ri={M.ri} rm={M.rm} fall={M.fall}"
          out.flush
        else
          still := still ++ [c]
      remaining := still
    idx := idx + 1
  let t2 ← IO.monoMsNow
  IO.println s!"sweep done in {t2 - t1} ms; {remaining.length} cells survive (no ≤5-world confluent countermodel)"
  out.flush
  -- big-budget positive push for the survivors
  for c in remaining do
    let X := cands.getD c.1 .falsePLL
    let Y := cands.getD c.2 .falsePLL
    if provedAt 100000 [X] Y then
      IO.println s!"  {cnames.getD c.1 ""} ⊢ {cnames.getD c.2 ""}: PROVED (plain PLL, budget 100000)"
    else if provedDist1 60000 X Y then
      IO.println s!"  {cnames.getD c.1 ""} ⊢ {cnames.getD c.2 ""}: PROVED (one dist application, budget 60000)"
    else if provedDist2 40000 X Y then
      IO.println s!"  {cnames.getD c.1 ""} ⊢ {cnames.getD c.2 ""}: PROVED (two dist applications, budget 40000)"
    else if (tier1 X Y).any (fun p => provedAt 60000 [X, ConfluentU.distF p.1 p.2] Y) then
      IO.println s!"  {cnames.getD c.1 ""} ⊢ {cnames.getD c.2 ""}: PROVED (single instance premise, budget 60000)"
    else if provedAt 100000 (X :: distsOf (tier1 X Y)) Y then
      IO.println s!"  {cnames.getD c.1 ""} ⊢ {cnames.getD c.2 ""}: PROVED (full tier-1 premise list, budget 100000)"
    else
      IO.println s!"  {cnames.getD c.1 ""} ⊢ {cnames.getD c.2 ""}: UNKNOWN (survives rooted ≤5-world sweep; unproved by all positive stages)"
    out.flush
  let tz ← IO.monoMsNow
  IO.println s!"=== phase R done in {tz - t0} ms ==="

/-! ## Phase P: pin emission — Lean source for the PCLL-proper proved
cells (`derivU_of_proved'` over an emitted G4iLL″ term), after
wip/rnDictGen.lean's `emitTm`. -/

def leanNameOf (i : Nat) : String := if i < 15 then s!"q{i}" else s!"w{i}"

partial def ppL (X : PLLFormula) : String :=
  match cands.findIdx? (· = X) with
  | some i => leanNameOf i
  | none =>
    match X with
    | .prop s => s!"(.prop \"{s}\")"
    | .falsePLL => ".falsePLL"
    | .and a b => s!"(.and {ppL a} {ppL b})"
    | .or a b => s!"(.or {ppL a} {ppL b})"
    | .ifThen a b => s!"(.ifThen {ppL a} {ppL b})"
    | .somehow a => s!"(.somehow {ppL a})"

def memIdx (X : PLLFormula) : List PLLFormula → Nat
  | [] => 0
  | Y :: R => if X = Y then 0 else memIdx X R + 1

def memStrN : Nat → String
  | 0 => "(.head _)"
  | n + 1 => s!"(.tail _ {memStrN n})"

def memS (X : PLLFormula) (Γ : List PLLFormula) : String :=
  memStrN (memIdx X Γ)

partial def emitTm : {Γ : List PLLFormula} → {C : PLLFormula} → G4cTm Γ C → String
  | _, _, @G4cTm.init Γ a _ => s!"(.init {memS (.prop a) Γ})"
  | _, _, @G4cTm.botL Γ _ _ => s!"(.botL {memS .falsePLL Γ})"
  | _, _, @G4cTm.andR _ _ _ t1 t2 => s!"(.andR {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.orR1 _ _ _ t => s!"(.orR1 {emitTm t})"
  | _, _, @G4cTm.orR2 _ _ _ t => s!"(.orR2 {emitTm t})"
  | _, _, @G4cTm.impR _ _ _ t => s!"(.impR {emitTm t})"
  | _, _, @G4cTm.laxR _ _ t => s!"(.laxR {emitTm t})"
  | _, _, @G4cTm.laxL Γ A _ _ t =>
      s!"(.laxL (A := {ppL A}) {memS A.somehow Γ} {emitTm t})"
  | _, _, @G4cTm.andL Γ A B _ _ t =>
      s!"(.andL (A := {ppL A}) (B := {ppL B}) {memS (A.and B) Γ} {emitTm t})"
  | _, _, @G4cTm.orL Γ A B _ _ t1 t2 =>
      s!"(.orL (A := {ppL A}) (B := {ppL B}) {memS (A.or B) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLProp Γ a B _ _ _ t =>
      s!"(.impLProp (a := \"{a}\") (B := {ppL B}) {memS ((PLLFormula.prop a).ifThen B) Γ} {memS (.prop a) Γ} {emitTm t})"
  | _, _, @G4cTm.impLAnd Γ A B D _ _ t =>
      s!"(.impLAnd (A := {ppL A}) (B := {ppL B}) (D := {ppL D}) {memS ((A.and B).ifThen D) Γ} {emitTm t})"
  | _, _, @G4cTm.impLOr Γ A B D _ _ t =>
      s!"(.impLOr (A := {ppL A}) (B := {ppL B}) (D := {ppL D}) {memS ((A.or B).ifThen D) Γ} {emitTm t})"
  | _, _, @G4cTm.impLImp Γ A B D _ _ t1 t2 =>
      s!"(.impLImp (A := {ppL A}) (B := {ppL B}) (D := {ppL D}) {memS ((A.ifThen B).ifThen D) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLLax Γ A B _ _ t1 t2 =>
      s!"(.impLLax (A := {ppL A}) (B := {ppL B}) {memS (A.somehow.ifThen B) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLLaxLax Γ A B X _ _ _ t1 t2 =>
      s!"(.impLLaxLax (A := {ppL A}) (B := {ppL B}) (X := {ppL X}) {memS (A.somehow.ifThen B) Γ} {memS X.somehow Γ} {emitTm t1} {emitTm t2})"

def ppPairs (ps : List (PLLFormula × PLLFormula)) : String :=
  "[" ++ String.intercalate ", "
    (ps.map fun p => s!"({ppL p.1}, {ppL p.2})") ++ "]"

def findTm (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    Option (G4cTm Γ C) :=
  (G4cTm.findBounded b Γ C).1

def phaseP (cells : List (Nat × Nat)) : IO Unit := do
  let out ← IO.getStdout
  for c in cells do
    let X := cands.getD c.1 .falsePLL
    let Y := cands.getD c.2 .falsePLL
    let nmX := leanNameOf c.1
    let nmY := leanNameOf c.2
    let mut done := false
    -- plain PLL term
    match findTm 300000 [X] Y with
    | some t =>
      IO.println s!"/-- `[{nmX}] ⊢ {nmY}` (plain PLL). -/"
      IO.println s!"theorem rnc_{c.1}_{c.2} : ConfluentU.DerivU [{nmX}] {nmY} :="
      IO.println s!"  (Search.proved_sound {emitTm t}).elim"
      IO.println s!"    ConfluentU.DerivU.of_nd"
      IO.println ""
      done := true
    | none => pure ()
    -- one dist application, cut-style: [X] ⊢ ◯(A∨B), then [◯A∨◯B, X] ⊢ Y
    if !done then
      for p in tier1 X Y do
        if !done then
          let mid := (somehow p.1).or (somehow p.2)
          match findTm 150000 [X] (somehow (p.1.or p.2)) with
          | some tA =>
            match findTm 150000 [mid, X] Y with
            | some tB =>
              IO.println s!"/-- `[{nmX}] ⊢ {nmY}` (PCLL, one application of distribution at `({ppL p.1}, {ppL p.2})`). -/"
              IO.println s!"theorem rnc_{c.1}_{c.2} : ConfluentU.DerivU [{nmX}] {nmY} :="
              IO.println s!"  (Search.proved_sound {emitTm tA}).elim fun pA =>"
              IO.println s!"  (Search.proved_sound {emitTm tB}).elim fun pB =>"
              IO.println s!"    ConfluentU.DerivU.mp (ConfluentU.DerivU.of_nd (.impIntro pB))"
              IO.println s!"      (ConfluentU.DerivU.mp (ConfluentU.DerivU.dist {ppL p.1} {ppL p.2})"
              IO.println s!"        (ConfluentU.DerivU.of_nd pA))"
              IO.println ""
              done := true
            | none => pure ()
          | none => pure ()
    -- instance-as-premise fallback
    if !done then
      let attempts : List (Nat × List (PLLFormula × PLLFormula)) :=
        ((tier1 X Y).map fun p => (1, [p])) ++ [(2, tier1 X Y)]
      for a in attempts do
        if !done then
          match findTm 200000 (X :: distsOf a.2) Y with
          | some t =>
            IO.println s!"/-- `[{nmX}] ⊢ {nmY}` (PCLL, instance premises, tier {a.1}). -/"
            IO.println s!"theorem rnc_{c.1}_{c.2} : ConfluentU.DerivU [{nmX}] {nmY} :="
            IO.println s!"  derivU_of_proved' {ppPairs a.2} (Search.proved_sound"
            IO.println s!"    {emitTm t})"
            IO.println ""
            done := true
          | none => pure ()
    if !done then
      IO.println s!"-- rnc_{c.1}_{c.2}: NO TERM within budget"
    out.flush

end RNC
end PLLND

def main (args : List String) : IO Unit :=
  match args with
  | "c" :: rest :: _ => PLLND.RNC.phaseC (PLLND.RNC.parseIdx rest)
  | "r" :: rest :: _ => PLLND.RNC.phaseR (PLLND.RNC.parseCells rest)
  | "p" :: rest :: _ => PLLND.RNC.phaseP (PLLND.RNC.parseCells rest)
  | _ => PLLND.RNC.mainLoop
