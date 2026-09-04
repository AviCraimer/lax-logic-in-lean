import LaxLogic.PLLSearch

/-!
# Probe: the b.ii configuration of the amalgamation ◯-induction

Semantic-UI route, case b.ii of the ◯-case (route doc §0(hh); the
same-trace no-descent clause is REFUTED, so the induction must survive
the following residue).  Over a mutually confluent `K` and arbitrary
`M`, with layered E-bisimulation approximants `Z_n` (all atoms
protected) and closure traces `tr`, the configuration is:

  worlds `k', k, kv, κ ∈ K`, `m', m, u ∈ M`, `Δ := tr(k)`,
  `d := |cl| − |Δ|`, such that
  (1) `tr(k') = Δ`, `⊥ ∉ Δ`;
  (2) `Rᵢ m' m`, `Rₘ m u`, `u ∉ F_M`;
  (3) `(k',m') ∈ Z_{2d+1}`, `(k,m) ∈ Z_{2d}`;
  (4) `Rᵢ k' kv`, `(kv,u) ∈ Z_{2d}`, `Δ ⊊ tr(kv)`  (iback partner grew);
  (5) `Rₘ k κ`, `(κ,u) ∈ Z_{2d−1}`, `tr(κ) = Δ`     (mback partner did not).

RESOLUTION at a config:
  (R1) same-trace rescue: `kb` with `tr(kb) = Δ`, `(kb,u) ∈ Z_{2d}`;
  (R2) grown answer: `kb` with `T := tr(kb) ⊋ Δ`, `(kb,u) ∈ Z_{2·d(T)}`,
       the canonical Rₘ-condition `RmC(Δ,T)` (`Δ ⊆ T` and every `χ ∈ T`
       has `boxOf χ ∈ Δ`), plus a reservoir `(kr,mr)`: `tr(kr) = T`,
       `Rᵢ mr u`, `(kr,mr) ∈ Z_{2·d(T)+1}` (checked with `(kb,u)` itself
       first, `Rᵢ u u` reflexive).
A config with neither is a FAILURE (dumped in full).

NEGATIVE CONTROL: the machinery re-runs the REFUTED same-trace
no-descent clause — `(k,m) ∈ Z_n`, `Rᵢ k v`, `v ≠ k`,
`tr(v) = tr(k) = Δ`, `⊥ ∉ Δ` ⇒ some `m₂`, `Rᵢ m m₂`, `(v,m₂) ∈ Z_n`
— at every rank `n` BELOW the stabilisation level of the pair's
Z-chain (at and beyond stabilisation the clause holds vacuously: the
fixpoint's own iforth clause hands back a same-level partner whenever
`v ∉ F`, and `⊥ ∉ tr(v)` forces `v ∉ F`).  It must find failures,
else the approximants/traces are suspect.  Two supplementary
statistics: the financed-rank form (`n = 2d+1`, `d = |cl| − |Δ|`) and
the `Z_∞` form (the latter provably vacuous — a fixpoint sanity
check, expect 0).

Closures: the samval one-atom closures, each ◯-adequately extended
(`boxOf` of every member added; `boxOf(◯ψ) = ◯ψ`, else `◯φ`).
Battery: samval base frames (default + extra, transitively closed) ×
hereditary one-atom `q`-decorations (≤ 5 worlds/model).

Run: `lake build biiprobe && .lake/build/bin/biiprobe`.
-/

open PLLFormula PLLND PLLND.Search

namespace BiiProbe

def qV : PLLFormula := .prop "q"

/-- `boxOf(◯ψ) = ◯ψ`; `boxOf(φ) = ◯φ` otherwise. -/
def boxOf : PLLFormula → PLLFormula
  | .somehow ψ => .somehow ψ
  | φ => φ.somehow

/-- ◯-adequate extension: close under `boxOf` (one round suffices —
new members are `◯`-formulas, fixed by `boxOf`). -/
def extendBox (cl : List PLLFormula) : List PLLFormula := Id.run do
  let mut out := cl
  for φ in cl do
    let b := boxOf φ
    if !(out.contains b) then out := out ++ [b]
  return out

def closures : List (String × List PLLFormula) :=
  [("[⊥,q]∪boxOf", extendBox [.falsePLL, qV]),
   ("[⊥,q,◯q]∪boxOf", extendBox [.falsePLL, qV, qV.somehow]),
   ("Sub(◯q⊃q)∪{⊥}∪boxOf",
    extendBox [.falsePLL, qV, qV.somehow, qV.somehow.ifThen qV]),
   ("Sub(◯(◯q⊃q))∪{⊥}∪boxOf",
    extendBox [.falsePLL, qV, qV.somehow, qV.somehow.ifThen qV,
      (qV.somehow.ifThen qV).somehow]),
   -- rank-rich supplements: the b.ii window needs a growth witness of
   -- crank > 2d−1, so closures with deep towers widen the tested range
   ("Sub(◯◯◯q)∪{⊥}∪boxOf",
    extendBox [.falsePLL, qV, qV.somehow, qV.somehow.somehow,
      qV.somehow.somehow.somehow]),
   ("Sub(¬¬q)∪{⊥}∪boxOf",
    extendBox [.falsePLL, qV, qV.ifThen .falsePLL,
      (qV.ifThen .falsePLL).ifThen .falsePLL])]

def pf : PLLFormula → String
  | .prop a => a
  | .falsePLL => "⊥"
  | .and φ ψ => s!"({pf φ}∧{pf ψ})"
  | .or φ ψ => s!"({pf φ}∨{pf ψ})"
  | .ifThen φ ψ => s!"({pf φ}⊃{pf ψ})"
  | .somehow φ => s!"◯{pf φ}"

/-! ## Battery (as in `samval_probe`, one-atom phase, base frames) -/

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
   ⟨4, [(0,1),(0,2),(0,3),(1,3),(2,3)], [(0,1)], [3]⟩,
   ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], []⟩]

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

/-- Up-closed subsets of a closed frame (hereditary `q`-decorations),
capped per frame. -/
def upSets (f : Frame) : List (List Nat) := Id.run do
  let mut out : List (List Nat) := []
  for mask in List.range (2 ^ f.n) do
    let S := (List.range f.n).filter fun i => mask / 2 ^ i % 2 == 1
    let ok := f.ri.all fun e => !(S.contains e.1) || S.contains e.2
    if ok then out := out ++ [S]
    if out.length ≥ 16 then return out
  return out

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Random frames, as in `samval_probe` (restricted to ≤ 5 worlds). -/
def randFrame (seed n : Nat) : Frame := Id.run do
  let mut s := seed
  let mut ri : List (Nat × Nat) := []
  for i in List.range n do
    for j in List.range n do
      if i ≠ j then
        s := lcg s
        if s % 100 < 30 && i < j then
          ri := ri ++ [(i, j)]
  let riC := (closeF ⟨n, ri, [], []⟩).ri
  let mut rm : List (Nat × Nat) := []
  for e in riC do
    s := lcg s
    if s % 100 < 40 then
      rm := rm ++ [e]
  let rmC := (closeF ⟨n, [], rm, []⟩).rm
  let mut fall : List Nat := []
  for i in List.range n do
    s := lcg s
    if s % 100 < 25 then
      if !(fall.contains i) then fall := fall ++ [i]
  let mut changed := true
  while changed do
    changed := false
    for e in riC do
      if fall.contains e.1 && !(fall.contains e.2) then
        fall := fall ++ [e.2]
        changed := true
  return ⟨n, riC, rmC, fall⟩

def randFrames : List Frame :=
  ((List.range 40).map fun k => randFrame (k * 7919 + 13) (4 + k % 3)).filter
    (·.n ≤ 5)

/-! ### Supplementary deep frames (6–7 worlds, beyond the ≤5 spec cap)

The ≤5-world battery stabilises all Z-chains by level 3, while the
b.ii gates need `stab ≥ 2d ≥ 4` (see the output analysis): `d = 1` is
impossible outright (trace growth from a co-atomic `Δ` adds `⊥`,
i.e. fallibility, contradicting `Z_0`-matching with the infallible
`u`), and `d ≥ 2` needs a non-fixpoint `Z_{2d−1}`, `2d−1 ≥ 3`.  The
deep frames chase `stab ≥ 4`: Rieger–Nishimura-ladder truncations
(the canonical deep one-atom intuitionistic posets) and long chains
with alternating `Rₘ`. -/

/-- Chain `0 < 1 < … < n−1` with chosen `Rₘ`-edges and fallible set. -/
def chainFrame (n : Nat) (rmE : List (Nat × Nat)) (fall : List Nat) : Frame :=
  closeF ⟨n, (List.range (n - 1)).map (fun i => (i, i + 1)), rmE, fall⟩

/-- Rieger–Nishimura ladder truncation: worlds `0, 1` maximal, and
`i` (for `i ≥ 2`) lies immediately below `i−1` and `i−2`. -/
def rnFrame (n : Nat) (rmE : List (Nat × Nat)) (fall : List Nat) : Frame :=
  closeF ⟨n, (List.range n).flatMap (fun i =>
    if i ≥ 2 then [(i, i - 1), (i, i - 2)] else []), rmE, fall⟩

def deepRandFrames : List Frame :=
  (List.range 16).map fun k => randFrame (k * 31337 + 101) 6

def deepFrames : List Frame :=
  [ chainFrame 6 [(0,1),(2,3),(4,5)] [],
    chainFrame 6 [(0,1),(2,3),(4,5)] [5],
    chainFrame 6 [(1,2),(3,4)] [],
    chainFrame 6 [(1,2),(3,4)] [5],
    chainFrame 6 [] [5],
    chainFrame 6 [(4,5)] [5],
    chainFrame 7 [(1,2),(3,4),(5,6)] [],
    chainFrame 7 [(1,2),(3,4),(5,6)] [6],
    rnFrame 6 [] [],
    rnFrame 6 [] [0],
    rnFrame 6 [(2,1)] [],
    rnFrame 6 [(3,1),(4,2)] [],
    rnFrame 6 [(2,0),(3,1),(4,2),(5,3)] [1],
    rnFrame 7 [] [],
    rnFrame 7 [(2,1),(4,3),(6,5)] [],
    rnFrame 7 [(3,2),(5,4)] [0],
    rnFrame 7 [(2,0),(3,1),(4,2),(5,3),(6,4)] [] ] ++ deepRandFrames

def baseFrames : List Frame :=
  ((defaultFrames ++ extraFrames).map closeF) ++ randFrames ++ deepFrames

/-- Index of the first beyond-spec deep frame (for reading the class
table). -/
def deepStart : Nat :=
  (defaultFrames.length + extraFrames.length) + randFrames.length

/-! ## Prepared models -/

structure PM where
  cm : FinCM
  fi : Nat                    -- battery frame index (for the class table)
  riS : Array (Array Nat)     -- reflexive Rᵢ successor lists
  rmS : Array (Array Nat)     -- reflexive Rₘ successor lists
  fallA : Array Bool
  deriving Inhabited

def mkPM (fi : Nat) (cm : FinCM) : PM := Id.run do
  let n := cm.n
  let mut riS : Array (Array Nat) := #[]
  let mut rmS : Array (Array Nat) := #[]
  let mut fallA : Array Bool := #[]
  for w in List.range n do
    riS := riS.push ((List.range n).filter (fun v => cm.riB w v)).toArray
    rmS := rmS.push ((List.range n).filter (fun v => cm.rmB w v)).toArray
    fallA := fallA.push (cm.fallB w)
  return ⟨cm, fi, riS, rmS, fallA⟩

def models : List PM := Id.run do
  let mut out : List PM := []
  let mut fi := 0
  for f in baseFrames do
    for S in upSets f do
      let cm : FinCM := ⟨f.n, f.ri, f.rm, f.fall, S.map fun w => (w, "q")⟩
      out := out ++ [mkPM fi cm]
    fi := fi + 1
  return out

/-- MutuallyConfluent: `∀ x w v, Rₘ x w → Rᵢ x v → ∃y, Rᵢ w y ∧ Rₘ v y`. -/
def mutConf (P : PM) : Bool :=
  (List.range P.cm.n).all fun x =>
    (P.rmS[x]!).all fun w =>
      (P.riS[x]!).all fun v =>
        (List.range P.cm.n).any fun y => P.cm.riB w y && P.cm.rmB v y

/-! ## Layered approximants -/

structure ZData where
  levels : Array (Array Bool)  -- Z_0, Z_1, …, stabilised tail
  nM : Nat
  monoViol : Nat               -- violations of Z_{n+1} ⊆ Z_n (expect 0)

/-- Compute `Z_0, Z_1, …` until stabilisation (finite models ⇒ the
chain is eventually constant); check `Z_{n+1} ⊆ Z_n` at each step. -/
def zLevels (K M : PM) : ZData := Id.run do
  let nK := K.cm.n
  let nM := M.cm.n
  let mut z0 : Array Bool := Array.replicate (nK * nM) false
  for x in List.range nK do
    for y in List.range nM do
      if (K.cm.valB x "q") == (M.cm.valB y "q")
          && K.fallA[x]! == M.fallA[y]! then
        z0 := z0.set! (x * nM + y) true
  let mut levels := #[z0]
  let mut prev := z0
  let mut viol := 0
  let mut go := true
  while go do
    let mut cur : Array Bool := Array.replicate (nK * nM) false
    for x in List.range nK do
      for y in List.range nM do
        if z0[x * nM + y]! then
          let c1 := (K.riS[x]!).all fun v =>
            K.fallA[v]! || (M.riS[y]!).any fun v' => prev[v * nM + v']!
          let c2 := (M.riS[y]!).all fun v' =>
            M.fallA[v']! || (K.riS[x]!).any fun v => prev[v * nM + v']!
          let c3 := (K.rmS[x]!).all fun u =>
            (M.rmS[y]!).any fun u' =>
              prev[u * nM + u']! || (K.fallA[u]! && M.fallA[u']!)
          let c4 := (M.rmS[y]!).all fun u' =>
            (K.rmS[x]!).any fun u =>
              prev[u * nM + u']! || (K.fallA[u]! && M.fallA[u']!)
          if c1 && c2 && c3 && c4 then
            cur := cur.set! (x * nM + y) true
    for i in List.range (nK * nM) do
      if cur[i]! && !prev[i]! then viol := viol + 1
    if cur == prev then
      go := false
    else
      levels := levels.push cur
      prev := cur
  return ⟨levels, nM, viol⟩

/-- `(x,y) ∈ Z_lvl` (clamped: past stabilisation the chain is constant). -/
def zAt (zd : ZData) (lvl x y : Nat) : Bool :=
  (zd.levels[min lvl (zd.levels.size - 1)]!)[x * zd.nM + y]!

/-! ## Traces -/

def traceMasks (cl : Array PLLFormula) (P : PM) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for w in List.range P.cm.n do
    let mut m := 0
    for i in List.range cl.size do
      if P.cm.forceB w cl[i]! then m := m ||| (1 <<< i)
    out := out.push m
  return out

def popC (sz m : Nat) : Nat :=
  (List.range sz).foldl (fun a i => a + ((m >>> i) &&& 1)) 0

def maskFormulas (cl : Array PLLFormula) (m : Nat) : String :=
  String.intercalate "," (((List.range cl.size).filter
    (fun i => (m >>> i) &&& 1 == 1)).map (fun i => pf cl[i]!))

/-! ## Resolution -/

structure ClInfo where
  cl : Array PLLFormula
  botIdx : Nat
  boxIdx : Array Nat  -- boxIdx[i] = index of boxOf cl[i] in cl
  deriving Inhabited

def mkClInfo (cl : List PLLFormula) : ClInfo := Id.run do
  let a := cl.toArray
  let idxOf := fun (φ : PLLFormula) => Id.run do
    for i in List.range a.size do
      if a[i]! == φ then return i
    return a.size
  let mut bx : Array Nat := #[]
  for i in List.range a.size do
    bx := bx.push (idxOf (boxOf a[i]!))
  return ⟨a, idxOf .falsePLL, bx⟩

/-- `RmC(Δ,T)`: `Δ ⊆ T` and `∀χ ∈ T, boxOf χ ∈ Δ` (cl is ◯-adequate,
so the guard `boxOf χ ∈ cl` is vacuous). -/
def rmC (ci : ClInfo) (Δ T : Nat) : Bool :=
  (Δ &&& T == Δ) &&
  (List.range ci.cl.size).all fun i =>
    ((T >>> i) &&& 1 == 0) || ((Δ >>> ci.boxIdx[i]!) &&& 1 == 1)

structure Resolution where
  r1 : Bool
  r2 : Bool
  r2kb : Nat := 0      -- witness kb for R2
  r2T : Nat := 0       -- its trace
  r2self : Bool := false  -- reservoir was (kb,u) itself
  r2kr : Nat := 0
  r2mr : Nat := 0

def resolve (K M : PM) (zd : ZData) (ci : ClInfo) (tk : Array Nat)
    (Δ u : Nat) : Resolution := Id.run do
  let nK := K.cm.n
  let nM := M.cm.n
  let clSize := ci.cl.size
  let d := clSize - popC clSize Δ
  -- R1
  let r1 := (List.range nK).any fun kb =>
    tk[kb]! == Δ && zAt zd (2 * d) kb u
  -- R2
  let mut r2 := false
  let mut res : Resolution := { r1 := r1, r2 := false }
  for kb in List.range nK do
    if !r2 then
      let T := tk[kb]!
      if (Δ &&& T == Δ) && Δ != T && rmC ci Δ T then
        let dT := clSize - popC clSize T
        if zAt zd (2 * dT) kb u then
          -- reservoir: (kb,u) itself first
          if zAt zd (2 * dT + 1) kb u then
            r2 := true
            res := ⟨r1, true, kb, T, true, kb, u⟩
          else
            for kr in List.range nK do
              if !r2 && tk[kr]! == T then
                for mr in List.range nM do
                  if !r2 && M.cm.riB mr u && zAt zd (2 * dT + 1) kr mr then
                    r2 := true
                    res := ⟨r1, true, kb, T, false, kr, mr⟩
  return res

/-! ## Statistics -/

structure BiiStats where
  configs : Nat := 0
  r1ok : Nat := 0
  r2only : Nat := 0
  failures : Nat := 0
  r1failed : Nat := 0        -- configs where R1 fails (R2 may hold)
  r2selfRes : Nat := 0       -- R2 resolutions with self-reservoir
  deriving Inhabited

structure CtrlStats where
  needed : Nat := 0      -- all-ranks form, ranks below stabilisation
  fails : Nat := 0
  neededFin : Nat := 0   -- financed-rank form (n = 2d+1)
  failsFin : Nat := 0
  neededInf : Nat := 0   -- Z_∞ form (provably vacuous; sanity)
  failsInf : Nat := 0
  deriving Inhabited

structure Funnel where
  gA : Nat := 0   -- k' with ⊥ ∉ Δ
  gB : Nat := 0   -- + m' with (k',m') ∈ Z_{2d+1}
  gC : Nat := 0   -- + k with tr(k) = Δ
  gD : Nat := 0   -- + m: Rᵢ m' m ∧ (k,m) ∈ Z_{2d}
  gE : Nat := 0   -- + u: Rₘ m u ∧ u ∉ F
  gF : Nat := 0   -- candidates with ≥1 grown iback kv (Z_{2d}, Δ ⊊ tr)
  deriving Inhabited

/-- κ-gate decode at gF candidates: the mback partner set
`{κ₀ : Rₘ k κ₀ ∧ (κ₀,u) ∈ Z_{2d−1}}` classified by trace. -/
structure KDecode where
  mbEmpty : Nat := 0     -- no mback partner at all (mback clause says: expect 0)
  mbHasSame : Nat := 0   -- some partner has trace Δ (→ b.ii configs)
  mbAllGrown : Nat := 0  -- every partner's trace ⊋ Δ
  mbMixed : Nat := 0     -- partners exist, none with trace Δ, not all grown
  r1Avail : Nat := 0     -- counterfactual: R1's kb exists at (Δ,u)
  r2Avail : Nat := 0     -- counterfactual: R2's kb+reservoir exist at (Δ,u)
  neither : Nat := 0     -- neither rescue available (would-be failures)
  dumped : Nat := 0
  deriving Inhabited

def dumpModel (tag : String) (P : PM) : IO Unit := do
  IO.println s!"    {tag}: n={P.cm.n} ri={P.cm.ri} rm={P.cm.rm} fall={P.cm.fall} val={P.cm.val} (frame #{P.fi})"

def dumpTraces (tag : String) (ci : ClInfo) (P : PM) (t : Array Nat) :
    IO Unit := do
  for w in List.range P.cm.n do
    IO.println s!"    tr_{tag}({w}) = \{{maskFormulas ci.cl t[w]!}}"

/-! ## Main -/

def mainLoop : IO Unit := do
  let t0 ← IO.monoMsNow
  let ms := models
  let nMod := ms.length
  let msArr := ms.toArray
  let confl := msArr.map mutConf
  let nConfl := (List.range nMod).foldl
    (fun a i => if confl[i]! then a + 1 else a) 0
  IO.println s!"=== b.ii probe: {baseFrames.length} frames (deep supplementary frames start at #{deepStart}), {nMod} models ({nConfl} mutually confluent as K) ==="
  -- closure info + collapse note
  let cis := (closures.map fun c => (c.1, mkClInfo c.2)).toArray
  for i in List.range cis.size do
    let (nm, ci) := cis[i]!
    IO.println s!"closure {i} {nm}: |cl|={ci.cl.size} [{maskFormulas ci.cl ((1 <<< ci.cl.size) - 1)}]"
    for j in List.range i do
      let (nm', ci') := cis[j]!
      if ci.cl.toList.all (ci'.cl.toList.contains ·) &&
          ci'.cl.toList.all (ci.cl.toList.contains ·) then
        IO.println s!"  (note: set-equal to closure {j} {nm'} after ◯-adequate extension)"
  -- traces per closure per model
  let mut traces : Array (Array (Array Nat)) := #[]
  for ic in List.range cis.size do
    let ci := (cis[ic]!).2
    traces := traces.push (msArr.map fun P => traceMasks ci.cl P)
  -- global counters
  let mut bii : Array BiiStats := Array.replicate cis.size {}
  let mut ctrl : Array CtrlStats := Array.replicate cis.size {}
  let mut monoViol := 0
  let nFr := baseFrames.length
  -- per (K-frame, M-frame) per closure: (configs, failures)
  let mut classTab : Array (Nat × Nat) :=
    Array.replicate (cis.size * nFr * nFr) (0, 0)
  let mut failDumps : Array Nat := Array.replicate cis.size 0
  let mut r2onlyDumped : Array Bool := Array.replicate cis.size false
  let mut ctrlDumped : Array Nat := Array.replicate cis.size 0
  let mut funnels : Array Funnel := Array.replicate cis.size {}
  let mut kdecode : Array KDecode := Array.replicate cis.size {}
  let mut stabHist : Array Nat := Array.replicate 40 0
  -- (d, stab) occupancy at grown-kv candidates: ic*64 + min d 7 * 8 + min stab 7
  let mut dsHist : Array Nat := Array.replicate (cis.size * 64) 0
  for iK in List.range nMod do
    let K := msArr[iK]!
    for iM in List.range nMod do
      let M := msArr[iM]!
      let zd := zLevels K M
      monoViol := monoViol + zd.monoViol
      let stab := zd.levels.size - 1
      stabHist := stabHist.set! (min stab 39) (stabHist[min stab 39]! + 1)
      let nK := K.cm.n
      let nM := M.cm.n
      let zInf := zd.levels.size - 1
      for ic in List.range cis.size do
        let ci := (cis[ic]!).2
        let clSize := ci.cl.size
        let tk := (traces[ic]!)[iK]!
        /- ---- negative control: same-trace no-descent (REFUTED clause) -/
        for k in List.range nK do
          let Δ := tk[k]!
          if (Δ >>> ci.botIdx) &&& 1 == 0 then
            let d := clSize - popC clSize Δ
            for m in List.range nM do
              -- all ranks below stabilisation (the non-vacuous window)
              for n in List.range zInf do
                if zAt zd n k m then
                  for v in K.riS[k]! do
                    if v != k && tk[v]! == Δ then
                      let mut c := ctrl[ic]!
                      c := { c with needed := c.needed + 1 }
                      let ok := (M.riS[m]!).any fun m₂ => zAt zd n v m₂
                      if !ok then
                        c := { c with fails := c.fails + 1 }
                        if ctrlDumped[ic]! < 3 then
                          ctrlDumped := ctrlDumped.set! ic (ctrlDumped[ic]! + 1)
                          IO.println s!"  CTRL-FAIL[{(cis[ic]!).1}] rank n={n} (stab={zInf}): K#{iK}(fr{K.fi}) k={k} v={v} Δ=\{{maskFormulas ci.cl Δ}}  M#{iM}(fr{M.fi}) m={m}"
                      ctrl := ctrl.set! ic c
              -- financed-rank form (n = 2d+1)
              if zAt zd (2 * d + 1) k m then
                for v in K.riS[k]! do
                  if v != k && tk[v]! == Δ then
                    let mut c := ctrl[ic]!
                    c := { c with neededFin := c.neededFin + 1 }
                    let ok := (M.riS[m]!).any fun m₂ =>
                      zAt zd (2 * d + 1) v m₂
                    if !ok then
                      c := { c with failsFin := c.failsFin + 1 }
                    ctrl := ctrl.set! ic c
              -- Z_∞ form (fixpoint sanity: provably 0)
              if zAt zd zInf k m then
                for v in K.riS[k]! do
                  if v != k && tk[v]! == Δ then
                    let mut c := ctrl[ic]!
                    c := { c with neededInf := c.neededInf + 1 }
                    let ok := (M.riS[m]!).any fun m₂ => zAt zd zInf v m₂
                    if !ok then
                      c := { c with failsInf := c.failsInf + 1 }
                    ctrl := ctrl.set! ic c
        /- ---- the b.ii configuration (K mutually confluent) -/
        if confl[iK]! then
          -- memo for resolution keyed by Δ * nM + u
          let mut memo : Array (Option Resolution) :=
            Array.replicate ((1 <<< clSize) * nM) none
          for k' in List.range nK do
            let Δ := tk[k']!
            if (Δ >>> ci.botIdx) &&& 1 == 0 then
              let d := clSize - popC clSize Δ
              funnels := funnels.set! ic { funnels[ic]! with gA := (funnels[ic]!).gA + 1 }
              for m' in List.range nM do
                if zAt zd (2 * d + 1) k' m' then
                  funnels := funnels.set! ic { funnels[ic]! with gB := (funnels[ic]!).gB + 1 }
                  for k in List.range nK do
                    if tk[k]! == Δ then
                      funnels := funnels.set! ic { funnels[ic]! with gC := (funnels[ic]!).gC + 1 }
                      for m in M.riS[m']! do
                        if zAt zd (2 * d) k m then
                          funnels := funnels.set! ic { funnels[ic]! with gD := (funnels[ic]!).gD + 1 }
                          for u in M.rmS[m]! do
                            if !M.fallA[u]! then
                              funnels := funnels.set! ic { funnels[ic]! with gE := (funnels[ic]!).gE + 1 }
                              -- grown iback partners of k' at (kv,u) ∈ Z_2d
                              let kvs := (K.riS[k']!).filter fun kv =>
                                zAt zd (2 * d) kv u
                                  && (Δ &&& tk[kv]! == Δ) && tk[kv]! != Δ
                              if kvs.size > 0 then
                                funnels := funnels.set! ic { funnels[ic]! with gF := (funnels[ic]!).gF + 1 }
                                let dsKey := ic * 64 + (min d 7) * 8 +
                                  min (zd.levels.size - 1) 7
                                dsHist := dsHist.set! dsKey (dsHist[dsKey]! + 1)
                                -- decode the κ-gate: the mback partner set of (k,u)
                                let mbs := (K.rmS[k]!).filter fun κ₀ =>
                                  zAt zd (2 * d - 1) κ₀ u
                                let mbSame := mbs.filter fun κ₀ => tk[κ₀]! == Δ
                                let mbGrown := mbs.filter fun κ₀ =>
                                  (Δ &&& tk[κ₀]! == Δ) && tk[κ₀]! != Δ
                                let mut kd := kdecode[ic]!
                                if mbs.size == 0 then
                                  kd := { kd with mbEmpty := kd.mbEmpty + 1 }
                                else if mbSame.size > 0 then
                                  kd := { kd with mbHasSame := kd.mbHasSame + 1 }
                                else if mbGrown.size == mbs.size then
                                  kd := { kd with mbAllGrown := kd.mbAllGrown + 1 }
                                else
                                  kd := { kd with mbMixed := kd.mbMixed + 1 }
                                -- counterfactual R1/R2 availability at (Δ,u)
                                let mut rc : Resolution :=
                                  { r1 := false, r2 := false }
                                match memo[Δ * nM + u]! with
                                | some r0 => rc := r0
                                | none =>
                                    rc := resolve K M zd ci tk Δ u
                                    memo := memo.set! (Δ * nM + u) (some rc)
                                if rc.r1 then
                                  kd := { kd with r1Avail := kd.r1Avail + 1 }
                                if rc.r2 then
                                  kd := { kd with r2Avail := kd.r2Avail + 1 }
                                if !rc.r1 && !rc.r2 then
                                  kd := { kd with neither := kd.neither + 1 }
                                if mbSame.size == 0 && kd.dumped < 3 then
                                  kd := { kd with dumped := kd.dumped + 1 }
                                  IO.println s!"  κ-GATE KILL [{(cis[ic]!).1}] (grown iback exists, no same-trace mback):"
                                  dumpModel "K" K
                                  dumpModel "M" M
                                  IO.println s!"    k'={k'} k={k} m'={m'} m={m} u={u} d={d} stab={zd.levels.size - 1}  Δ=\{{maskFormulas ci.cl Δ}}"
                                  IO.println s!"    grown kv's: {kvs.toList.map fun kv => (kv, maskFormulas ci.cl tk[kv]!)}"
                                  IO.println s!"    mback partners (Rm k ∘, Z_{2*d-1} with u): {mbs.toList.map fun κ₀ => (κ₀, maskFormulas ci.cl tk[κ₀]!)}"
                                  IO.println s!"    tr_M(u) = \{{maskFormulas ci.cl ((traces[ic]!)[iM]!)[u]!}}  rigid-dead-end u:{(M.rmS[u]!).all (· == u)}"
                                  IO.println s!"    counterfactual rescues: R1={rc.r1} R2={rc.r2}{if rc.r2 then s!" (kb={rc.r2kb} T=\{{maskFormulas ci.cl rc.r2T}} selfReservoir={rc.r2self} kr={rc.r2kr} mr={rc.r2mr})" else ""}"
                                kdecode := kdecode.set! ic kd
                              for kv in kvs do
                                  for κ in K.rmS[k]! do
                                    if zAt zd (2 * d - 1) κ u && tk[κ]! == Δ then
                                      -- a b.ii config
                                      let mut r : Resolution :=
                                        { r1 := false, r2 := false }
                                      match memo[Δ * nM + u]! with
                                      | some r0 => r := r0
                                      | none =>
                                          r := resolve K M zd ci tk Δ u
                                          memo := memo.set! (Δ * nM + u) (some r)
                                      let mut s := bii[ic]!
                                      s := { s with configs := s.configs + 1 }
                                      let key := ic * nFr * nFr + K.fi * nFr + M.fi
                                      let (cc, cf) := classTab[key]!
                                      let mut cf' := cf
                                      if r.r1 then
                                        s := { s with r1ok := s.r1ok + 1 }
                                      else
                                        s := { s with r1failed := s.r1failed + 1 }
                                        if r.r2 then
                                          s := { s with r2only := s.r2only + 1 }
                                          if r.r2self then
                                            s := { s with r2selfRes := s.r2selfRes + 1 }
                                          if !r2onlyDumped[ic]! then
                                            r2onlyDumped := r2onlyDumped.set! ic true
                                            IO.println s!"  R2-ONLY EXAMPLE [{(cis[ic]!).1}] (R1 fails, R2 succeeds):"
                                            dumpModel "K" K
                                            dumpModel "M" M
                                            IO.println s!"    k'={k'} k={k} kv={kv} κ={κ}  m'={m'} m={m} u={u}  d={d}"
                                            IO.println s!"    Δ = \{{maskFormulas ci.cl Δ}}  tr(kv) = \{{maskFormulas ci.cl tk[kv]!}}"
                                            IO.println s!"    R2 witness kb={r.r2kb} T=\{{maskFormulas ci.cl r.r2T}} selfReservoir={r.r2self} kr={r.r2kr} mr={r.r2mr}"
                                        else
                                          s := { s with failures := s.failures + 1 }
                                          cf' := cf' + 1
                                          if failDumps[ic]! < 6 then
                                            failDumps := failDumps.set! ic (failDumps[ic]! + 1)
                                            IO.println s!"  !!FAILURE [{(cis[ic]!).1}] (neither R1 nor R2):"
                                            dumpModel "K" K
                                            dumpModel "M" M
                                            IO.println s!"    k'={k'} k={k} kv={kv} κ={κ}  m'={m'} m={m} u={u}  d={d}  levels: (k',m')∈Z_{2*d+1} (k,m)∈Z_{2*d} (kv,u)∈Z_{2*d} (κ,u)∈Z_{2*d-1}"
                                            IO.println s!"    Δ = \{{maskFormulas ci.cl Δ}}  tr(kv) = \{{maskFormulas ci.cl tk[kv]!}}"
                                            dumpTraces "K" ci K tk
                                            dumpTraces "M" ci M ((traces[ic]!)[iM]!)
                                            let deadU := (M.rmS[u]!).all (· == u)
                                            let deadκ := (K.rmS[κ]!).all (· == κ)
                                            IO.println s!"    rigid dead-end? u:{deadU} κ:{deadκ}  Rm-row(u)={M.rmS[u]!} Rm-row(κ)={K.rmS[κ]!} Ri-row(u)={M.riS[u]!}"
                                            IO.println s!"    Z-levels(K,M): stabilised at {zd.levels.size - 1}"
                                      classTab := classTab.set! key (cc + 1, cf')
                                      bii := bii.set! ic s
  let t1 ← IO.monoMsNow
  IO.println s!"=== monotonicity (Z_(n+1) ⊆ Z_n) violations: {monoViol} (expect 0) ==="
  IO.print "=== Z-chain stabilisation levels (level: pair count): "
  for l in List.range 40 do
    if stabHist[l]! > 0 then IO.print s!"{l}:{stabHist[l]!} "
  IO.println "==="
  IO.println "=== NEGATIVE CONTROL (refuted same-trace no-descent clause) ==="
  for ic in List.range cis.size do
    let c := ctrl[ic]!
    IO.println s!"  {(cis[ic]!).1}: all-ranks<stab needed={c.needed} FAILURES={c.fails} | financed n=2d+1 needed={c.neededFin} FAILURES={c.failsFin} | Z_∞ needed={c.neededInf} FAILURES={c.failsInf} (expect 0)"
  IO.println "=== b.ii CONFIGURATION COUNTS ==="
  for ic in List.range cis.size do
    let s := bii[ic]!
    let f := funnels[ic]!
    IO.println s!"  {(cis[ic]!).1}: configs={s.configs} R1-resolved={s.r1ok} R2-only={s.r2only} FAILURES={s.failures} | R1-failed={s.r1failed} (R2 self-reservoir among R2-only: {s.r2selfRes})"
    IO.println s!"    funnel: ⊥∉Δ k'={f.gA} → +m'∈Z_(2d+1)={f.gB} → +k same-tr={f.gC} → +m∈Z_2d={f.gD} → +u∉F={f.gE} → +grown-kv cands={f.gF} → configs={s.configs}"
    let kd := kdecode[ic]!
    IO.println s!"    κ-gate decode at grown-kv candidates: mback-set empty={kd.mbEmpty} (expect 0), has-same-trace={kd.mbHasSame}, all-grown={kd.mbAllGrown}, mixed-no-same={kd.mbMixed}"
    IO.println s!"    counterfactual rescues at those candidates: R1-available={kd.r1Avail}, R2-available={kd.r2Avail}, neither={kd.neither}"
    IO.print "    (d,stab) occupancy at grown-kv candidates: "
    for dd in List.range 8 do
      for ss in List.range 8 do
        let c := dsHist[ic * 64 + dd * 8 + ss]!
        if c > 0 then IO.print s!"(d={dd},stab={ss}):{c} "
    IO.println ""
  IO.println "=== per (K-frame, M-frame) class table (rows with configs > 0) ==="
  for ic in List.range cis.size do
    IO.println s!"  closure {(cis[ic]!).1}:"
    let mut rows := 0
    for fk in List.range nFr do
      for fm in List.range nFr do
        let (cc, cf) := classTab[ic * nFr * nFr + fk * nFr + fm]!
        if cc > 0 then
          rows := rows + 1
          if rows ≤ 60 then
            IO.println s!"    K-frame {fk} × M-frame {fm}: configs={cc} failures={cf}"
    if rows > 60 then IO.println s!"    … and {rows - 60} more rows"
    if rows == 0 then IO.println "    (no configs)"
  IO.println s!"=== done in {t1 - t0} ms ==="

end BiiProbe

def main : IO Unit := BiiProbe.mainLoop
