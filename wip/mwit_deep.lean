import LaxLogic.PLLSearch

/-!
# Deep-model probe: `MwitResidue`/`RankGap` in the DESCENDING regime

The small-battery probe (wip/mwit_probe.lean, PROGRESS §50) found the
live window — configurations whose financed levels sit BELOW the
stabilisation level of the link chain — empty: small models cannot
keep variable-free agreement descending.  This probe goes where the
ladder lives:

* battery = finite truncations of the LIFTED LADDER skeleton of
  wip/rnEmbed.lean: the Rieger–Nishimura frame on j ∈ {8,10,12} base
  worlds (`w Rᵢ v ↔ v + 2 ≤ w`; worlds 0,1 maximal) plus a fallible
  top `f`, with `Rₘ` = reflexive ∪ {(v,f) : v ∈ U} for an up-closed
  `U`, over several `U` and optional base `Rₘ`-chains — the very
  construction whose infinite form kernel-embeds the ladder;
* the ranked link's pool = the ◯⊥-alternation rungs to index 90
  (crank ≈ 47), computed by CACHED TRUTH MASKS (each rung's mask from
  its predecessors' masks — no formula-tree blowup), so the chain has
  genuine levels through `rslope 4 = 45`;
* the same configuration funnel and GIVEN/OTHER/FAIL verdicts as
  wip/mwit_probe.lean, now reporting the LIVE WINDOW occupancy and
  dumping the first live configuration reached — together with any
  failure, which would be a `RankGap` counterexample candidate.

Modes: Rdeep (ranked link, both models mutually confluent; the
harness's `valB` builds `full_F` in, so undecorated atoms have
`V a = F` exactly — the battery is genuinely `POnly`) and Gdeep (the
greatest-fixpoint layered family, p unprotected).

Run: `lake build mwitdeep && .lake/build/bin/mwitdeep`.
-/

open PLLFormula PLLND PLLND.Search

set_option maxRecDepth 16384

namespace MwitDeep

def pV : PLLFormula := .prop "p"
def qV : PLLFormula := .prop "q"

def boxOf : PLLFormula → PLLFormula
  | .somehow ψ => .somehow ψ
  | φ => φ.somehow

def extendBox (cl : List PLLFormula) : List PLLFormula := Id.run do
  let mut out := cl
  for φ in cl do
    let b := boxOf φ
    if !(out.contains b) then out := out ++ [b]
  return out

def closures : List (String × List PLLFormula) :=
  [("cl1={⊥,p,◯⊥,◯p}", extendBox [.falsePLL, pV]),
   ("cl3=Sub(◯(◯p⊃p))∪{⊥}∪boxOf",
    extendBox [.falsePLL, pV, pV.somehow, pV.somehow.ifThen pV,
      (pV.somehow.ifThen pV).somehow])]

def pf : PLLFormula → String
  | .prop a => a
  | .falsePLL => "⊥"
  | .and φ ψ => s!"({pf φ}∧{pf ψ})"
  | .or φ ψ => s!"({pf φ}∨{pf ψ})"
  | .ifThen φ ψ => s!"({pf φ}⊃{pf ψ})"
  | .somehow φ => s!"◯{pf φ}"

def hasP : PLLFormula → Bool
  | .prop a => a == "p"
  | .falsePLL => false
  | .and φ ψ => hasP φ || hasP ψ
  | .or φ ψ => hasP φ || hasP ψ
  | .ifThen φ ψ => hasP φ || hasP ψ
  | .somehow φ => hasP φ

def rnP : Nat → PLLFormula
  | 0 => .falsePLL
  | 1 => .somehow .falsePLL
  | 2 => (PLLFormula.somehow .falsePLL).ifThen .falsePLL
  | (n + 3) =>
    if n % 2 == 0 then (rnP (n + 1)).or (rnP (n + 2))
    else (rnP (n + 1)).ifThen (rnP (n - 1))

/-- ψ pool: closure members, an alternation prefix, `q`. -/
def psiPool (cl : List PLLFormula) : List PLLFormula := Id.run do
  let mut out := cl
  for φ in (PLLFormula.falsePLL.ifThen .falsePLL) ::
      (List.range 9).map rnP ++ [qV] do
    if !(out.contains φ) then out := out ++ [φ]
  return out

/-! ## Battery: lifted ladder truncations (+ deep chains/ladders) -/

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

/-- The lifted ladder: base worlds `0..j-1` with `w Rᵢ v ↔ v + 2 ≤ w`
(0, 1 maximal), fallible top `f = j` above everything;
`Rₘ` = {(v, f) : v ∈ U} plus optional base chains `rmE` (all inside
`Rᵢ`); `fall = {f}`. -/
def liftedLadder (j : Nat) (U : List Nat) (rmE : List (Nat × Nat)) : Frame :=
  closeF ⟨j + 1,
    ((List.range j).flatMap fun w =>
      ((List.range j).filter fun v => v + 2 ≤ w).map fun v => (w, v))
    ++ (List.range j).map (fun w => (w, j)),
    U.map (fun v => (v, j)) ++ rmE,
    [j]⟩

/-- Plain deep ladders/chains with a fallible top (mode-G fodder). -/
def rnFrame (n : Nat) (rmE : List (Nat × Nat)) (fall : List Nat) : Frame :=
  closeF ⟨n, (List.range n).flatMap (fun i =>
    if i ≥ 2 then [(i, i - 1), (i, i - 2)] else []), rmE, fall⟩

def chainFrame (n : Nat) (rmE : List (Nat × Nat)) (fall : List Nat) : Frame :=
  closeF ⟨n, (List.range (n - 1)).map (fun i => (i, i + 1)), rmE, fall⟩

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

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
    if s % 100 < 45 then
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

def deepFrames : List Frame := Id.run do
  let mut out : List Frame := []
  for j in [8, 10, 12] do
    for U in [[0], [1], [0, 1], [0, 1, 2], [0, 1, 2, 3]] do
      out := out ++ [liftedLadder j U []]
    -- base Rₘ-chains: descending ladder steps (all within Rᵢ)
    out := out ++ [liftedLadder j [0] (((List.range j).filter (· ≥ 2)).map
      fun w => (w, w - 2))]
    out := out ++ [liftedLadder j [0, 1] ([(2, 0), (3, 1), (4, 2)])]
    -- NON-ROW-RIGID variants: dense base Rₘ-chains (all drops by ≥ 2,
    -- inside Rᵢ), so infallible rows are genuinely non-reflexive —
    -- the battery class in which RankGapGrow's grow case can occur
    out := out ++ [liftedLadder j [0] (((List.range j).filter (· ≥ 2)).map
      fun w => (w, w - 2))]
    out := out ++ [liftedLadder j [0, 1, 2] (((List.range j).filter (· ≥ 3)).map
      fun w => (w, w - 3))]
  out := out ++
    [rnFrame 8 [] [0], rnFrame 8 [(2,0),(3,1),(4,2),(5,3)] [0],
     rnFrame 10 [] [0], rnFrame 10 [(2,0),(4,2),(6,4),(8,6)] [0],
     chainFrame 9 [(0,1),(2,3),(4,5),(6,7)] [8],
     chainFrame 9 [] [8]]
  -- random dense-Rₘ frames (7 worlds): confluence-filtered at scan time
  for k in List.range 16 do
    out := out ++ [randFrame (k * 104729 + 7) 7]
  return out

def upSets (f : Frame) : List (List Nat) := Id.run do
  let mut out : List (List Nat) := []
  for mask in List.range (2 ^ f.n) do
    let S := (List.range f.n).filter fun i => mask / 2 ^ i % 2 == 1
    let ok := f.ri.all fun e => !(S.contains e.1) || S.contains e.2
    if ok then out := out ++ [S]
    if out.length ≥ 6 then return out
  return out

structure PM where
  cm : FinCM
  fi : Nat
  riS : Array (Array Nat)
  rmS : Array (Array Nat)
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

/-- Decorations: hereditary p-sets only; `q` and all other atoms have
`V a = F` automatically (`valB` builds `full_F` in) — `POnly` holds. -/
def models : List PM := Id.run do
  let mut out : List PM := []
  let mut fi := 0
  for f in deepFrames do
    for P in (upSets f).take 6 do
      out := out ++ [mkPM fi ⟨f.n, f.ri, f.rm, f.fall, P.map (fun w => (w, "p"))⟩]
    fi := fi + 1
  return out

def mutConf (P : PM) : Bool :=
  (List.range P.cm.n).all fun x =>
    (P.rmS[x]!).all fun w =>
      (P.riS[x]!).all fun v =>
        (List.range P.cm.n).any fun y => P.cm.riB w y && P.cm.rmB v y

/-! ## The rung pool by cached truth masks -/

/-- `impMask A B` at `w`: every `Rᵢ`-successor in `A` is in `B`. -/
def impMask (P : PM) (A B : Nat) : Nat := Id.run do
  let mut m := 0
  for w in List.range P.cm.n do
    let ok := (P.riS[w]!).all fun v =>
      ((A >>> v) &&& 1 == 0) || ((B >>> v) &&& 1 == 1)
    if ok then m := m ||| (1 <<< w)
  return m

/-- `somehowMask A` at `w`: every `Rᵢ`-successor has an `Rₘ`-successor
in `A`. -/
def somehowMask (P : PM) (A : Nat) : Nat := Id.run do
  let mut m := 0
  for w in List.range P.cm.n do
    let ok := (P.riS[w]!).all fun v =>
      (P.rmS[v]!).any fun u => (A >>> u) &&& 1 == 1
    if ok then m := m ||| (1 <<< w)
  return m

/-- Rung truth masks and cranks, to index `count − 1`:
r0 = ⊥, r1 = ◯⊥, r2 = ¬◯⊥, r(n+3) = r(n+1) ∨ r(n+2) (n even),
r(n+3) = r(n+1) ⊃ r(n−1) (n odd).  Masks from cached masks — no
formula trees. -/
def rungData (P : PM) (count : Nat) : Array (Nat × Nat) := Id.run do
  let mut fallM := 0
  for w in List.range P.cm.n do
    if P.fallA[w]! then fallM := fallM ||| (1 <<< w)
  let oBot := somehowMask P fallM
  let mut out : Array (Nat × Nat) := #[(fallM, 0), (oBot, 2),
    (impMask P oBot fallM, 3)]
  for n in List.range (count - 3) do
    let r1 := out[n + 1]!
    let r2 := out[n + 2]!
    if n % 2 == 0 then
      out := out.push (r1.1 ||| r2.1, max r1.2 r2.2)
    else
      let r0 := out[n - 1]!
      out := out.push (impMask P r1.1 r0.1, max r1.2 r0.2 + 1)
  return out

def RUNGS : Nat := 90

/-! ## The two link families -/

structure ZData where
  levels : Array (Array Bool)
  nM : Nat
  deriving Inhabited

def rslope : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * rslope n + 3

/-- Ranked family over the deep rung pool (precomputed rung data). -/
def zRanked (K M : PM) (rK rM : Array (Nat × Nat)) : ZData := Id.run do
  let nK := K.cm.n
  let nM := M.cm.n
  let maxC := rK.foldl (fun a c => max a c.2) 0
  let mut levels : Array (Array Bool) := #[]
  let mut ℓ := 0
  let mut go := true
  while go do
    let r := rslope ℓ
    let mut cur : Array Bool := Array.replicate (nK * nM) false
    for x in List.range nK do
      for y in List.range nM do
        let mut ok := true
        for i in List.range rK.size do
          if (rK[i]!).2 ≤ r &&
              ((rK[i]!).1 >>> x) &&& 1 != ((rM[i]!).1 >>> y) &&& 1 then
            ok := false
        if ok then cur := cur.set! (x * nM + y) true
    levels := levels.push cur
    if r ≥ maxC then go := false
    ℓ := ℓ + 1
  return ⟨levels, nM⟩

/-- Greatest-fixpoint layered family, p unprotected (mode Gdeep). -/
def zGfp (K M : PM) : ZData := Id.run do
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
    if cur == prev then
      go := false
    else
      levels := levels.push cur
      prev := cur
  return ⟨levels, nM⟩

def zAt (zd : ZData) (lvl x y : Nat) : Bool :=
  (zd.levels[min lvl (zd.levels.size - 1)]!)[x * zd.nM + y]!

/-! ## Traces, closure info, answers (as in wip/mwit_probe.lean) -/

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

structure ClInfo where
  cl : Array PLLFormula
  botIdx : Nat
  boxIdx : Array Nat
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

def rmCB (ci : ClInfo) (Δ T : Nat) : Bool :=
  (Δ &&& T == Δ) &&
  (List.range ci.cl.size).all fun i =>
    ((T >>> i) &&& 1 == 0) || ((Δ >>> ci.boxIdx[i]!) &&& 1 == 1)

structure Ans where
  found : Bool := false
  kb : Nat := 0
  T : Nat := 0
  deriving Inhabited

def resolveAt (K M : PM) (zd : ZData) (ci : ClInfo) (tk : Array Nat)
    (Δ u : Nat) : Ans := Id.run do
  let nK := K.cm.n
  let nM := M.cm.n
  let clSize := ci.cl.size
  for kb in List.range nK do
    let T := tk[kb]!
    if (Δ &&& T) == Δ && rmCB ci Δ T then
      let dT := clSize - popC clSize T
      if zAt zd (2 * dT) kb u then
        if zAt zd (2 * dT + 1) kb u then
          return ⟨true, kb, T⟩
        else
          for kr in List.range nK do
            if tk[kr]! == T then
              for mr in List.range nM do
                if M.cm.riB mr u && zAt zd (2 * dT + 1) kr mr then
                  return ⟨true, kb, T⟩
  return {}

structure PStats where
  configs : Nat := 0
  cfgLive : Nat := 0
  instAll : Nat := 0
  instGiven : Nat := 0
  instOther : Nat := 0
  instFail : Nat := 0
  instLiveAll : Nat := 0
  instLiveGiven : Nat := 0
  instLiveOther : Nat := 0
  instLiveFail : Nat := 0
  cfgNR : Nat := 0          -- configs with a NON-REFLEXIVE witness (u' ≠ m)
  cfgNRLive : Nat := 0
  instNRAll : Nat := 0
  instNRGiven : Nat := 0
  instNROther : Nat := 0
  instNRFail : Nat := 0
  agAll : Nat := 0          -- (config,ψ) instances with the ALL-GROW flag
  agLive : Nat := 0
  agGiven : Nat := 0
  agOther : Nat := 0
  agFail : Nat := 0
  agKbK : Nat := 0          -- winning kb classification (GIVEN answers)
  agKbKp : Nat := 0
  agKbKappa : Nat := 0
  agKbKv : Nat := 0
  agKbOther : Nat := 0
  agTGrown : Nat := 0       -- winning answer used a grown trace
  deriving Inhabited

def dumpModel (tag : String) (P : PM) : IO Unit := do
  IO.println s!"    {tag}: n={P.cm.n} ri={P.cm.ri} rm={P.cm.rm} fall={P.cm.fall} val={P.cm.val} (frame #{P.fi})"

def runScan (tag : String) (ms : Array PM) (needMConf : Bool)
    (rdOf : Nat → Array (Nat × Nat))
    (zfun : Nat → Nat → ZData) : IO Unit := do
  let t0 ← IO.monoMsNow
  let nMod := ms.size
  let confl := ms.map mutConf
  let cis := (closures.map fun c => (c.1, mkClInfo c.2)).toArray
  let pools := (closures.map fun c =>
    ((psiPool c.2).map fun ψ => (ψ, !hasP ψ)).toArray).toArray
  IO.println s!"=== MODE {tag}: {nMod} models, {(ms.toList.filter mutConf).length} confluent ==="
  let mut traces : Array (Array (Array Nat)) := #[]
  for ic in List.range cis.size do
    let ci := (cis[ic]!).2
    traces := traces.push (ms.map fun P => traceMasks ci.cl P)
  let mut stats : Array PStats := Array.replicate cis.size {}
  let mut stabHist : Array Nat := Array.replicate 40 0
  let mut failDumps : Array Nat := Array.replicate cis.size 0
  let mut liveDumped : Array Bool := Array.replicate cis.size false
  let mut agDumped : Array Bool := Array.replicate cis.size false
  let mut pairsDone := 0
  for iK in List.range nMod do
    if confl[iK]! then
      let K := ms[iK]!
      let nK := K.cm.n
      for iM in List.range nMod do
        if !needMConf || confl[iM]! then
          let M := ms[iM]!
          let rdM := rdOf iM
          let zd := zfun iK iM
          pairsDone := pairsDone + 1
          let stab := zd.levels.size - 1
          stabHist := stabHist.set! (min stab 39) (stabHist[min stab 39]! + 1)
          let nM := M.cm.n
          for ic in List.range cis.size do
            let ci := (cis[ic]!).2
            let pool := pools[ic]!
            let clSize := ci.cl.size
            let tk := (traces[ic]!)[iK]!
            let ψtt : Array Nat := pool.map fun c => Id.run do
              let mut m := 0
              for w in List.range nM do
                if M.cm.forceB w c.1 then m := m ||| (1 <<< w)
              return m
            let full := (1 <<< clSize) - 1
            let mut memo : Array (Option Ans) :=
              Array.replicate ((1 <<< clSize) * nM) none
            for k' in List.range nK do
              let Δ := tk[k']!
              if (Δ >>> ci.botIdx) &&& 1 == 0 then
                let d := clSize - popC clSize Δ
                let topOK := rmCB ci Δ full
                for m' in List.range nM do
                  if zAt zd (2 * d + 1) k' m' then
                    for k in List.range nK do
                      if tk[k]! == Δ then
                        for m in M.riS[m']! do
                          if zAt zd (2 * d) k m then
                            for u in M.rmS[m]! do
                              if !M.fallA[u]! then
                                let kvs := (K.riS[k']!).filter fun kv =>
                                  zAt zd (2 * d) kv u
                                    && (Δ &&& tk[kv]! == Δ) && tk[kv]! != Δ
                                for kv in kvs do
                                  for κ in K.rmS[k]! do
                                    if zAt zd (2 * d - 1) κ u && tk[κ]! == Δ then
                                      let mut s := stats[ic]!
                                      s := { s with configs := s.configs + 1 }
                                      let nr := decide (u ≠ m)
                                      if nr then
                                        s := { s with cfgNR := s.cfgNR + 1 }
                                      let live := decide (2 * d - 1 < stab)
                                      if live then
                                        s := { s with cfgLive := s.cfgLive + 1 }
                                        if nr then
                                          s := { s with cfgNRLive := s.cfgNRLive + 1 }
                                        if !liveDumped[ic]! then
                                          liveDumped := liveDumped.set! ic true
                                          IO.println s!"  LIVE CONFIG reached [{tag}/{(cis[ic]!).1}]: d={d} stab={stab}"
                                          dumpModel "K" K
                                          dumpModel "M" M
                                          IO.println s!"    k'={k'} k={k} kv={kv} κ={κ} m'={m'} m={m} u'={u} Δ=\{{maskFormulas ci.cl Δ}} tr(kv)=\{{maskFormulas ci.cl tk[kv]!}}"
                                      let aGiven ← do
                                        match memo[Δ * nM + u]! with
                                        | some a => pure a
                                        | none =>
                                            let a := resolveAt K M zd ci tk Δ u
                                            memo := memo.set! (Δ * nM + u) (some a)
                                            pure a
                                      let r2 := rslope (2 * d)
                                      -- pool-agreement of m with a row world at crank ≤ r2
                                      let stableW : Nat → Bool := fun u2 =>
                                        (List.range rdM.size).all fun i =>
                                          ((rdM[i]!).2 > r2) ||
                                          (((rdM[i]!).1 >>> m) &&& 1 ==
                                            ((rdM[i]!).1 >>> u2) &&& 1)
                                      for j in List.range pool.size do
                                        if (ψtt[j]! >>> u) &&& 1 == 1 then
                                          -- ALL-GROW: every ψ-witness in m's row
                                          -- pool-visibly grows m's vf theory at r2
                                          let allGrow := (M.rmS[m]!).all fun u2 =>
                                            ((ψtt[j]! >>> u2) &&& 1 == 0) ||
                                            !(stableW u2)
                                          if allGrow then
                                            s := { s with agAll := s.agAll + 1 }
                                            if live then
                                              s := { s with agLive := s.agLive + 1 }
                                              if !agDumped[ic]! then
                                                agDumped := agDumped.set! ic true
                                                IO.println s!"  ALL-GROW LIVE instance [{tag}/{(cis[ic]!).1}]: ψ={pf (pool[j]!).1} d={d} stab={stab} u'={u} m={m}"
                                                dumpModel "K" K
                                                dumpModel "M" M
                                          s := { s with instAll := s.instAll + 1 }
                                          if nr then
                                            s := { s with instNRAll := s.instNRAll + 1 }
                                          if live then
                                            s := { s with instLiveAll := s.instLiveAll + 1 }
                                          if aGiven.found then
                                            if allGrow then
                                              s := { s with agGiven := s.agGiven + 1 }
                                              if aGiven.T != Δ then
                                                s := { s with agTGrown := s.agTGrown + 1 }
                                              else if aGiven.kb == k then
                                                s := { s with agKbK := s.agKbK + 1 }
                                              else if aGiven.kb == k' then
                                                s := { s with agKbKp := s.agKbKp + 1 }
                                              else if aGiven.kb == κ then
                                                s := { s with agKbKappa := s.agKbKappa + 1 }
                                              else if aGiven.kb == kv then
                                                s := { s with agKbKv := s.agKbKv + 1 }
                                              else
                                                s := { s with agKbOther := s.agKbOther + 1 }
                                            s := { s with instGiven := s.instGiven + 1 }
                                            if nr then
                                              s := { s with instNRGiven := s.instNRGiven + 1 }
                                            if live then
                                              s := { s with instLiveGiven := s.instLiveGiven + 1 }
                                          else
                                            let mut other := false
                                            for u2 in M.rmS[m]! do
                                              if !other && (ψtt[j]! >>> u2) &&& 1 == 1 then
                                                let a2 ← do
                                                  match memo[Δ * nM + u2]! with
                                                  | some a => pure a
                                                  | none =>
                                                      let a := resolveAt K M zd ci tk Δ u2
                                                      memo := memo.set! (Δ * nM + u2) (some a)
                                                      pure a
                                                if a2.found || (topOK && M.fallA[u2]!) then
                                                  other := true
                                            if other then
                                              if allGrow then
                                                s := { s with agOther := s.agOther + 1 }
                                              s := { s with instOther := s.instOther + 1 }
                                              if nr then
                                                s := { s with instNROther := s.instNROther + 1 }
                                              if live then
                                                s := { s with instLiveOther := s.instLiveOther + 1 }
                                            else
                                              s := { s with instFail := s.instFail + 1 }
                                              if allGrow then
                                                s := { s with agFail := s.agFail + 1 }
                                              if nr then
                                                s := { s with instNRFail := s.instNRFail + 1 }
                                              if live then
                                                s := { s with instLiveFail := s.instLiveFail + 1 }
                                              if failDumps[ic]! < 10 then
                                                failDumps := failDumps.set! ic (failDumps[ic]! + 1)
                                                IO.println s!"  !!FAIL [{tag}/{(cis[ic]!).1}] (RankGap counterexample candidate): ψ={pf (pool[j]!).1} live={live} d={d} stab={stab}"
                                                dumpModel "K" K
                                                dumpModel "M" M
                                                IO.println s!"    k'={k'} k={k} kv={kv} κ={κ} m'={m'} m={m} u'={u} Δ=\{{maskFormulas ci.cl Δ}} tr(kv)=\{{maskFormulas ci.cl tk[kv]!}}"
                                      stats := stats.set! ic s
      if iK % 25 == 0 then
        let t ← IO.monoMsNow
        IO.println s!"  [{tag} heartbeat] iK={iK}/{nMod} pairs={pairsDone} elapsed={t - t0}ms configs={(List.range cis.size).map fun ic => (stats[ic]!).configs} live={(List.range cis.size).map fun ic => (stats[ic]!).cfgLive} fails={(List.range cis.size).map fun ic => (stats[ic]!).instFail}"
        (← IO.getStdout).flush
  let t1 ← IO.monoMsNow
  IO.println s!"=== MODE {tag} RESULTS (pairs={pairsDone}) ==="
  IO.print s!"  stabilisation histogram: "
  for l in List.range 40 do
    if stabHist[l]! > 0 then IO.print s!"{l}:{stabHist[l]!} "
  IO.println ""
  for ic in List.range cis.size do
    let s := stats[ic]!
    IO.println s!"  {(cis[ic]!).1}:"
    IO.println s!"    configs={s.configs} (LIVE: {s.cfgLive}) | instances={s.instAll} GIVEN={s.instGiven} OTHER={s.instOther} FAIL={s.instFail}"
    IO.println s!"    LIVE-window instances={s.instLiveAll} GIVEN={s.instLiveGiven} OTHER={s.instLiveOther} FAIL={s.instLiveFail}"
    IO.println s!"    NON-RIGID (u' ≠ m): configs={s.cfgNR} (live {s.cfgNRLive}) | instances={s.instNRAll} GIVEN={s.instNRGiven} OTHER={s.instNROther} FAIL={s.instNRFail}"
    IO.println s!"    ALL-GROW instances={s.agAll} (live {s.agLive}) | GIVEN={s.agGiven} OTHER={s.agOther} FAIL={s.agFail}"
    IO.println s!"    ALL-GROW winning answers: same-trace kb=k:{s.agKbK} kb=k':{s.agKbKp} kb=κ:{s.agKbKappa} kb=kv:{s.agKbKv} kb=other:{s.agKbOther} | grown-T:{s.agTGrown}"
  IO.println s!"=== MODE {tag} done in {t1 - t0} ms ==="
  (← IO.getStdout).flush

def mainLoop : IO Unit := do
  IO.println "=== MwitResidue/RankGap DEEP probe: lifted ladder truncations, rung pool to 90 ==="
  let ms := models.toArray
  -- precompute rung data per model
  let rd : Array (Array (Nat × Nat)) := ms.map fun P => rungData P RUNGS
  let maxC := (rd[0]!).foldl (fun a c => max a c.2) 0
  IO.println s!"models={ms.size}; rung pool: {RUNGS} rungs, max crank {maxC}; rslope levels 0,3,9,21,45,…"
  runScan "Rdeep" ms true (fun i => rd[i]!)
    (fun iK iM => zRanked ms[iK]! ms[iM]! rd[iK]! rd[iM]!)
  runScan "Gdeep" ms false (fun i => rd[i]!)
    (fun iK iM => zGfp ms[iK]! ms[iM]!)

end MwitDeep

def main : IO Unit := MwitDeep.mainLoop
