import LaxLogic.PLLSearch

/-!
# Probe: description-realisability on finite instances

The mechanised sandwich (`PLLSemUITrace.lean`) reduces each `BoxRowAmalg`
residue to one question per `(C, x)`: is some closure triple with the
right `◯φ`-placement `Realises`-related to `x`?  On finite instances
both sides are computable:

* the canonical worlds over `cl` are the consistent total triples
  `(val, cl∖val, mfal ⊆ cl∖val)` — consistency is ONE sequent per
  triple (`val ⊢ ⋁fal ∨ ◯⋁mfal`, maximal choice; `disjOf_mono` makes
  the maximal choice sufficient), decided by the two-sided search
  oracle with a node budget;
* `Realises` is the greatest fixpoint of the clause operator on
  `C.W × worlds(cl)`: seed with the safety clauses (atoms off `p`,
  fallibility), prune pairs failing a transfer clause, iterate.

Per proved row (φ, ψ = the value of the quantified φ) and per decorated
battery frame: for each point satisfying the row condition, count

* **candidates** — triples with `◯φ ∈ fal` (∀-side) / `◯φ ∈ val`
  (∃-side) whose p-free val/fal agree with the point (necessary for
  realisation, `realises_val_iff`);
* **realised candidates** — candidates alive in the gfp: `> 0` means
  the discharge `boxRowAmalg{All,Ex}_of_realises` closes this
  instance (GREEN);
* `candsPre` — candidates additionally honouring the pre-triple's
  promises (`pfmfal ⊆ mfal`, the lindenbaum shape);
* whether the FULL trace triple of the point survives the gfp.

`!!NO-CAND` = the pre-triple is inconsistent there — by
`preTripleAll_cons_of_residue` the RESIDUE ITSELF fails at that
instance.  `!!RED` = consistent candidates exist but none is realised —
the canonical-target route needs refinement at that instance.

Run compiled: `lake build descprobe && .lake/build/bin/descprobe`.
-/

open PLLFormula PLLND PLLND.Search

namespace DescProbe

/-! ## Rows: the proved values -/

def pV : PLLFormula := .prop "p"
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL
def gB : PLLFormula := PLLFormula.falsePLL.somehow

/-- (label, φ, ψ, ∀-side?) — ψ the PROVED value of `∀p.φ` resp `∃p.φ`. -/
def rows : List (String × PLLFormula × PLLFormula × Bool) :=
  [ ("A p      ", pV,                     .falsePLL, true)
  , ("A p∨¬p   ", pV.or (nF pV),          .falsePLL, true)
  , ("A ¬p     ", nF pV,                  .falsePLL, true)
  , ("A ¬¬p⊃p  ", (nF (nF pV)).ifThen pV, .falsePLL, true)
  , ("A ◯p⊃p   ", pV.somehow.ifThen pV,   .falsePLL, true)   -- the gap row
  , ("A ◯p     ", pV.somehow,             gB,        true)
  , ("E p      ", pV,                     truePLL,   false)
  , ("E ¬p     ", nF pV,                  truePLL,   false)
  , ("E ◯p     ", pV.somehow,             truePLL,   false) ]

/-! ## Closure (⊥ first, so the ⊥-index is 0) -/

def subFL : PLLFormula → List PLLFormula
  | .prop a => [.prop a]
  | .falsePLL => [.falsePLL]
  | .and a b => .and a b :: (subFL a ++ subFL b)
  | .or a b => .or a b :: (subFL a ++ subFL b)
  | .ifThen a b => .ifThen a b :: (subFL a ++ subFL b)
  | .somehow a => .somehow a :: subFL a

def dedupF (l : List PLLFormula) : List PLLFormula :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

def clOfRow (φ : PLLFormula) : List PLLFormula :=
  dedupF (.falsePLL :: subFL φ.somehow)

def hasP : PLLFormula → Bool
  | .prop a => a == "p"
  | .falsePLL => false
  | .and a b => hasP a || hasP b
  | .or a b => hasP a || hasP b
  | .ifThen a b => hasP a || hasP b
  | .somehow a => hasP a

/-! ## Masks over closure indices -/

def memM (m i : Nat) : Bool := (m >>> i) &&& 1 == 1
def subM (a b : Nat) : Bool := a &&& b == a

def listOfM (cl : List PLLFormula) (m : Nat) : List PLLFormula :=
  (List.range cl.length).filterMap fun i =>
    if memM m i then cl[i]? else none

def maskOf (cl : List PLLFormula) (P : PLLFormula → Bool) : Nat :=
  (List.range cl.length).foldl (fun acc i =>
    match cl[i]? with
    | some χ => if P χ then acc ||| (1 <<< i) else acc
    | none => acc) 0

/-! ## The oracle -/

/-- Extra refutation frames (the one-◯ sweep battery). -/
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

def cfg : Config :=
  { frames := defaultFrames ++ extraFrames, findBudget := some 40000 }

/-- Transitive closure of a frame's relations (some battery frames —
the onebox forks — are not closed as listed; instance-building needs
legal models). -/
def closeF (f : Frame) : Frame := Id.run do
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

/-- The C-side instance frames, closed. -/
def instFrames : List Frame := (defaultFrames ++ extraFrames).map closeF

inductive V3 | yes | no | unk

/-- Two-sided, budgeted, certificate-carrying. -/
def decPure (Γ : List PLLFormula) (Cc : PLLFormula) : V3 :=
  match decide cfg Γ Cc with
  | .proved _ => .yes
  | .refuted .. => .no
  | .unknown => .unk

/-! ## The canonical worlds -/

def bigOrL : List PLLFormula → PLLFormula
  | [] => .falsePLL
  | x :: r => x.or (bigOrL r)

def disjOfL : List PLLFormula → List PLLFormula → PLLFormula
  | Ds, [] => bigOrL Ds
  | [], K :: Ts => (bigOrL (K :: Ts)).somehow
  | D :: Ds, K :: Ts => (bigOrL (D :: Ds)).or ((bigOrL (K :: Ts)).somehow)

structure Trip where
  val : Nat
  mfal : Nat
  deriving BEq, Repr, Inhabited

def allM (cl : List PLLFormula) : Nat := (1 <<< cl.length) - 1
def falOf (cl : List PLLFormula) (t : Trip) : Nat := allM cl ^^^ t.val

/-- Enumerate the canonical worlds: total triples `(val, cl∖val, mfal ⊆
cl∖val)` that pass the (maximal-choice) consistency sequent.  Returns
`(worlds, unknown-count)`. -/
def canonWorlds (cl : List PLLFormula) : List Trip × Nat := Id.run do
  let L := cl.length
  let mut ws : List Trip := []
  let mut unk := 0
  for val in List.range (1 <<< L) do
    let fal := allM cl ^^^ val
    for mf in List.range (1 <<< L) do
      if subM mf fal then
        if fal == 0 && mf == 0 then
          ws := ws ++ [⟨val, mf⟩]
        else
          match decPure (listOfM cl val)
              (disjOfL (listOfM cl fal) (listOfM cl mf)) with
          | .yes => pure ()
          | .no => ws := ws ++ [⟨val, mf⟩]
          | .unk => unk := unk + 1
  return (ws, unk)

/-! ## C-side instances: decorated battery frames -/

def mkCM (f : Frame) (pmask : Nat) : FinCM :=
  ⟨f.n, f.ri, f.rm, f.fall,
   ((List.range f.n).filter (fun w => memM pmask w)).map (fun w => (w, "p"))⟩

/-- Hereditary p-decorations, full on the fallible worlds. -/
def heredMasks (f : Frame) : List Nat :=
  (List.range (1 <<< f.n)).filter fun m =>
    (f.fall.all fun w => memM m w) &&
    (f.ri.all fun e => !(memM m e.1) || memM m e.2)

/-! ## The gfp -/

structure GfpCtx where
  cm : FinCM
  cl : List PLLFormula
  ws : Array Trip

def canRi (a b : Trip) : Bool := subM a.val b.val
def canRm (a b : Trip) : Bool := subM a.val b.val && subM a.mfal b.mfal
def canF (t : Trip) : Bool := memM t.val 0

/-- Safety clauses: tracked non-p atoms agree, fallibility agrees. -/
def safeOK (ctx : GfpCtx) (w : Nat) (t : Trip) : Bool :=
  (ctx.cm.fallB w == canF t) &&
  ((List.range ctx.cl.length).all fun i =>
    match ctx.cl[i]? with
    | some (.prop a) =>
        if a == "p" then true else ctx.cm.valB w a == memM t.val i
    | _ => true)

def idx (ctx : GfpCtx) (w ti : Nat) : Nat := w * ctx.ws.size + ti

/-- The four transfer clauses at a pair, w.r.t. the current relation. -/
def clauseOK (ctx : GfpCtx) (alive : Array Bool) (w ti : Nat) : Bool :=
  Id.run do
  let t := ctx.ws[ti]!
  let n := ctx.cm.n
  -- iforth: every non-fallible Rᵢ-successor pairs above
  for v in List.range n do
    if ctx.cm.riB w v && !ctx.cm.fallB v then
      let mut ok := false
      for tj in List.range ctx.ws.size do
        if canRi t ctx.ws[tj]! && alive[idx ctx v tj]! then
          ok := true
      if !ok then return false
  -- kback: every canonical Rᵢ-extension is realised above
  for tj in List.range ctx.ws.size do
    if canRi t ctx.ws[tj]! then
      let mut ok := false
      for v in List.range n do
        if ctx.cm.riB w v && alive[idx ctx v tj]! then
          ok := true
      if !ok then return false
  -- mforth: every Rₘ-successor pairs (or falls fallibly, both sides)
  for u in List.range n do
    if ctx.cm.rmB w u then
      let mut ok := false
      for tj in List.range ctx.ws.size do
        if canRm t ctx.ws[tj]! &&
            (alive[idx ctx u tj]! || (ctx.cm.fallB u && canF ctx.ws[tj]!)) then
          ok := true
      if !ok then return false
  -- mback: every canonical Rₘ-extension is realised on the row (or
  -- escapes at a fallible row world)
  for tj in List.range ctx.ws.size do
    if canRm t ctx.ws[tj]! then
      let mut ok := false
      for u in List.range n do
        if ctx.cm.rmB w u && (alive[idx ctx u tj]! || ctx.cm.fallB u) then
          ok := true
      if !ok then return false
  return true

/-- A pair never pruned (alive at the fixpoint). -/
def IMMORTAL : Nat := 1000000

/-- Synchronous pruning rounds from the safety seed; returns each
pair's DEATH ROUND (1-based; `IMMORTAL` = survives to the gfp).
Round-`r` survival is the rank-`r` stratified relation `R_r`:
`R_{r+1}` = pairs satisfying the transfer clauses w.r.t. `R_r`. -/
def runRounds (ctx : GfpCtx) : Array Nat := Id.run do
  let n := ctx.cm.n
  let sz := n * ctx.ws.size
  let mut death : Array Nat := Array.replicate sz 0
  let mut alive : Array Bool := Array.replicate sz false
  for w in List.range n do
    for ti in List.range ctx.ws.size do
      if safeOK ctx w ctx.ws[ti]! then
        alive := alive.set! (idx ctx w ti) true
        death := death.set! (idx ctx w ti) IMMORTAL
  let mut round := 0
  let mut changed := true
  while changed do
    changed := false
    round := round + 1
    let prev := alive
    for w in List.range n do
      for ti in List.range ctx.ws.size do
        if prev[idx ctx w ti]! && !clauseOK ctx prev w ti then
          alive := alive.set! (idx ctx w ti) false
          death := death.set! (idx ctx w ti) round
          changed := true
  return death

/-! ## Per-row analysis -/

/-- Syntactic depth: the number of pruning rounds the stratified
forcing lemma consumes for a formula. -/
def depthF : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => 1 + max (depthF a) (depthF b)
  | .or a b => 1 + max (depthF a) (depthF b)
  | .ifThen a b => 1 + max (depthF a) (depthF b)
  | .somehow a => 1 + depthF a

structure RowStats where
  insts : Nat := 0
  pts : Nat := 0
  green : Nat := 0
  red : Nat := 0
  nocand : Nat := 0
  traceAlive : Nat := 0
  cands : Nat := 0
  candsAlive : Nat := 0
  candsPre : Nat := 0
  /-- `greenAt[d]` = points with some candidate surviving `d` pruning
  rounds (index 0 unused). -/
  greenAt : Array Nat := Array.replicate 8 0
  /-- points whose best candidate survives `depthF ◯φ` rounds. -/
  greenDepth : Nat := 0

def runRow (label : String) (φ ψ : PLLFormula) (isAll : Bool) :
    IO RowStats := do
  let cl := clOfRow φ
  let boxIdx := cl.findIdx (· == φ.somehow)
  let t0 ← IO.monoMsNow
  let (ws, unk) := canonWorlds cl
  let t1 ← IO.monoMsNow
  IO.println s!"row {label}: |cl|={cl.length} worlds={ws.length} unk={unk} ({t1-t0} ms)"
  if unk > 0 then
    IO.println "  !!UNKNOWN consistencies — world set incomplete, verdicts unreliable"
  let wsA := ws.toArray
  let boxBit := 1 <<< boxIdx
  let dNeed := depthF φ.somehow
  IO.println s!"  required depth d = {dNeed}"
  let mut st : RowStats := {}
  for f in instFrames do
    for pm in heredMasks f do
      let cm := mkCM f pm
      let ctx : GfpCtx := ⟨cm, cl, wsA⟩
      let death := runRounds ctx
      st := { st with insts := st.insts + 1 }
      for x in List.range cm.n do
        let qual :=
          if isAll then
            (List.range cm.n).all fun u => !(cm.rmB x u) || !(cm.forceB u ψ)
          else
            (List.range cm.n).all fun v => !(cm.riB x v) ||
              ((List.range cm.n).any fun u => cm.rmB v u && cm.forceB u ψ)
        if qual then
          let pfv := maskOf cl (fun χ => !hasP χ && cm.forceB x χ)
          let pff := maskOf cl (fun χ => !hasP χ && !(cm.forceB x χ))
          let pfm := maskOf cl (fun χ => !hasP χ &&
            ((List.range cm.n).all fun u => !(cm.rmB x u) || !(cm.forceB u χ)))
          let trv := maskOf cl (fun χ => cm.forceB x χ)
          let trm := maskOf cl (fun χ =>
            (List.range cm.n).all fun u => !(cm.rmB x u) || !(cm.forceB u χ))
          let trAlive := match wsA.findIdx? (fun t => t.val == trv && t.mfal == trm) with
            | some ti => death[idx ctx x ti]! == IMMORTAL
            | none => false
          let mut c := 0
          let mut ca := 0
          let mut cp := 0
          let mut best := 0   -- best candidate death round
          for ti in List.range wsA.size do
            let t := wsA[ti]!
            let placed :=
              if isAll then memM (falOf cl t) boxIdx else memM t.val boxIdx
            if placed && subM pfv t.val && subM pff (falOf cl t) then
              c := c + 1
              if subM pfm t.mfal then cp := cp + 1
              let dr := death[idx ctx x ti]!
              if dr > best then best := dr
              if dr == IMMORTAL then ca := ca + 1
          let mut ga := st.greenAt
          for d in List.range 8 do
            if d ≥ 1 && best > d then ga := ga.set! d (ga[d]! + 1)
          st := { st with
            pts := st.pts + 1
            cands := st.cands + c
            candsAlive := st.candsAlive + ca
            candsPre := st.candsPre + cp
            green := st.green + (if ca > 0 then 1 else 0)
            red := st.red + (if ca == 0 && c > 0 then 1 else 0)
            nocand := st.nocand + (if c == 0 then 1 else 0)
            traceAlive := st.traceAlive + (if trAlive then 1 else 0)
            greenAt := ga
            greenDepth := st.greenDepth + (if best > dNeed then 1 else 0) }
          if c == 0 then
            IO.println s!"  !!NO-CAND {label}: n={f.n} ri={f.ri} rm={f.rm} fall={f.fall} pmask={pm} x={x}"
          else if best ≤ dNeed then
            IO.println s!"  !!RED@d {label}: n={f.n} ri={f.ri} rm={f.rm} fall={f.fall} pmask={pm} x={x} cands={c} best={best}"
  let t2 ← IO.monoMsNow
  IO.println s!"  insts={st.insts} pts={st.pts} GREEN(gfp)={st.green} NO-CAND={st.nocand} traceAlive={st.traceAlive} cands={st.cands} alive={st.candsAlive} pre={st.candsPre} ({t2-t1} ms)"
  IO.println s!"  survive d rounds: d1={st.greenAt[1]!} d2={st.greenAt[2]!} d3={st.greenAt[3]!} d4={st.greenAt[4]!} d5={st.greenAt[5]!} d6={st.greenAt[6]!}  GREEN@depth({dNeed})={st.greenDepth}/{st.pts}"
  return st

def mainLoop : IO Unit := do
  IO.println "=== description-realisability probe ==="
  for (label, φ, ψ, isAll) in rows do
    let _ ← runRow label φ ψ isAll
  IO.println "=== done ==="

end DescProbe

def main : IO Unit := DescProbe.mainLoop
