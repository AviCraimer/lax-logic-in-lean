import LaxLogic.PLLSearch

/-!
# Probe: the WITNESS-FORM residue `MwitResidue`

Re-aim of `bii_p_probe.lean` (PROGRESS §§35–38) at the witness-form
residue of wip/witOut.lean — after the ranked ascent (PROGRESS §48)
the ONE open Prop of the route.  The Prop being probed (context
`B : LayeredBisimWit (≠p) K M`, `d := |cl| − |Δ|`):

  ∀ hK Δ k' k kv κ m' m u' ψ,
    SubClosed cl → ⊥ ∉ Δ →
    tr(k) = Δ → tr(k') = Δ →
    Rᵢ m' m → Rₘ m u' → M ⊨_{u'} ψ → u' ∉ F_M →
    (k',m') ∈ Z_{2d+1} → (k,m) ∈ Z_{2d} →
    Rᵢ k' kv → (kv,u') ∈ Z_{2d} → tr(kv) ≠ Δ →
    Rₘ k κ → (κ,u') ∈ Z_{2d−1} → tr(κ) = Δ →
    ∃ u'' Δ', Rₘ m u'' ∧ M ⊨_{u''} ψ ∧ RmC(Δ,Δ') ∧ WitTripleC Δ' u''

Differences from the `MforthResidue` probe: each configuration is
paired with every pool formula ψ forced at `u'`, and the conclusion
may answer with ANY ψ-witness in `m`'s row.  Verdicts per
(configuration, ψ):

* GIVEN — the supplied `u'` itself carries an answer (old-style);
* OTHER — `u'` carries none, but another row-witness `u''` of ψ does
  (THE WITNESS-FREEDOM GAIN of the re-typed pipeline);
* FAIL  — no row-witness of ψ carries an answer = an `MwitResidue`
  counterexample candidate (dumped in full).

Answers searched: proper triples realised as traces of K-worlds
(`kb` with `RmC(Δ,tr(kb))`, base `Z_{2d(T)}`, reservoir `Z_{2d(T)+1}`)
— a sound under-approximation of the canonical successor space — PLUS
the canonical-top answer (`RmC(Δ, cl)` with a fallible row-witness),
which the old probe omitted.

TWO LINK FAMILIES:

* mode G — the LARGEST lawful layered family (greatest-fixpoint
  approximants, p unprotected), as in `bii_p_probe`: the hard mode
  (most configurations).
* mode R — the RANKED family `Z n := ` variable-free agreement at
  rank `rslope n` (`rslope(n+1) = 2·rslope n + 3`) over a
  Rieger–Nishimura pool (`rn k [p := ◯⊥]`, k ≤ 12) — the EXACT link
  of the open Prop `MwitResidue cl (rankedB …)`; battery restricted
  to `POnly`-corrected decorations (`V q := F`) with BOTH models
  mutually confluent, per `rankedB`'s hypotheses.  Caveat recorded in
  the output: any finite pool truncates the ranked chain, so its
  stabilisation level is a floor, not a fact about the infinite
  fragment (which is infinite — wip/rnEmbed.lean).

Battery, funnel, Z-machinery, trace masks and the answer search are
`bii_p_probe`'s, verbatim where possible.

Run: `lake build mwitprobe && .lake/build/bin/mwitprobe`.
-/

open PLLFormula PLLND PLLND.Search

set_option maxRecDepth 16384

namespace MwitProbe

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
   ("cl2={⊥,p,q,◯⊥,◯p,◯q}", extendBox [.falsePLL, pV, qV]),
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

def hasAtom : PLLFormula → Bool
  | .prop _ => true
  | .falsePLL => false
  | .and φ ψ => hasAtom φ || hasAtom ψ
  | .or φ ψ => hasAtom φ || hasAtom ψ
  | .ifThen φ ψ => hasAtom φ || hasAtom ψ
  | .somehow φ => hasAtom φ

/-- `crank` (◯ costs 2) — the ranked family's measure. -/
def crank2 : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and φ ψ => max (crank2 φ) (crank2 ψ)
  | .or φ ψ => max (crank2 φ) (crank2 ψ)
  | .ifThen φ ψ => max (crank2 φ) (crank2 ψ) + 1
  | .somehow φ => crank2 φ + 2

/-! ## The ψ pool and the variable-free (ranked-link) pool

`rnP k`: a ladder-LIKE alternation family over ◯⊥ — rn 0 = ⊥,
rn 1 = ◯⊥, rn 2 = ¬◯⊥, rn (2k+3) = rn (2k+1) ∨ rn (2k+2),
rn (2k+4) = rn (2k+2) ⊃ rn (2k).  (Labelling note, post-run: the even
recursion differs from Nishimura's rn (2k+4) = rn (2k+3) ⊃ rn (2k+1)
from index 6 on — rn 4 = ¬¬◯⊥ agrees — so this is an alternation POOL
climbing in crank, not the exact rung enumeration of
wip/rnEmbed.lean.  As an agreement test set for the ranked link this
is equally sound: any variable-free pool under-approximates full
variable-free agreement, which is the recorded truncation caveat; the
run output prints the exact formulas used.) -/
def rnP : Nat → PLLFormula
  | 0 => .falsePLL
  | 1 => .somehow .falsePLL
  | 2 => (PLLFormula.somehow .falsePLL).ifThen .falsePLL
  | (n + 3) =>
    if n % 2 == 0 then (rnP (n + 1)).or (rnP (n + 2))
    else (rnP (n + 1)).ifThen (rnP (n - 1))

/-- The variable-free pool for the RANKED link: rungs 0–12 plus ⊤. -/
def vfPool : List PLLFormula :=
  (PLLFormula.falsePLL.ifThen .falsePLL) :: (List.range 13).map rnP

/-- The ψ pool: the closure members plus a ladder prefix plus the two
atoms' boxes — witnesses for these are what consumers push. -/
def psiPool (cl : List PLLFormula) : List PLLFormula := Id.run do
  let mut out := cl
  for φ in (PLLFormula.falsePLL.ifThen .falsePLL) ::
      (List.range 9).map rnP ++ [qV] do
    if !(out.contains φ) then out := out ++ [φ]
  return out

/-! ## Battery (bii_p_probe verbatim) -/

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

def upSets (f : Frame) : List (List Nat) := Id.run do
  let mut out : List (List Nat) := []
  for mask in List.range (2 ^ f.n) do
    let S := (List.range f.n).filter fun i => mask / 2 ^ i % 2 == 1
    let ok := f.ri.all fun e => !(S.contains e.1) || S.contains e.2
    if ok then out := out ++ [S]
    if out.length ≥ 16 then return out
  return out

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

def allRand : List Frame :=
  (List.range 40).map fun k => randFrame (k * 7919 + 13) (4 + k % 3)

def phaseAFrames : List Frame :=
  ((defaultFrames ++ extraFrames).map closeF).filter (·.n ≤ 4)

def phaseBFrames : List Frame :=
  ((extraFrames.filter (·.n == 5)).map closeF)
    ++ (allRand.filter (·.n == 4)).take 8
    ++ (allRand.filter (·.n == 5)).take 4

def chainFrame (n : Nat) (rmE : List (Nat × Nat)) (fall : List Nat) : Frame :=
  closeF ⟨n, (List.range (n - 1)).map (fun i => (i, i + 1)), rmE, fall⟩

def rnFrame (n : Nat) (rmE : List (Nat × Nat)) (fall : List Nat) : Frame :=
  closeF ⟨n, (List.range n).flatMap (fun i =>
    if i ≥ 2 then [(i, i - 1), (i, i - 2)] else []), rmE, fall⟩

def deepRandFrames : List Frame :=
  (List.range 16).map fun k => randFrame (k * 31337 + 101) 6

def phaseCFrames : List Frame :=
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

def allFrames : List Frame := phaseAFrames ++ phaseBFrames ++ phaseCFrames

/-! ## Prepared models -/

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

def deco (f : Frame) (fi : Nat) (P Q : List Nat) : PM :=
  mkPM fi ⟨f.n, f.ri, f.rm, f.fall,
    P.map (fun w => (w, "p")) ++ Q.map (fun w => (w, "q"))⟩

/-- Mode-G battery: frames × hereditary p×q decorations (capped as in
`bii_p_probe`). -/
def modelsG : List PM := Id.run do
  let mut out : List PM := []
  let mut fi := 0
  for f in phaseAFrames do
    let us := upSets f
    for P in us do
      for Q in us do
        out := out ++ [deco f fi P Q]
    fi := fi + 1
  for f in phaseBFrames ++ phaseCFrames do
    let us := upSets f
    for P in us.take 8 do
      for Q in us.take 3 do
        out := out ++ [deco f fi P Q]
    fi := fi + 1
  return out

/-- Mode-R battery: `POnly`-corrected decorations — `V q := F` exactly
(`pOnly_V_eq_F`), p free. -/
def modelsR : List PM := Id.run do
  let mut out : List PM := []
  let mut fi := 0
  for f in allFrames do
    let us := upSets f
    for P in us.take 12 do
      out := out ++ [deco f fi P f.fall]
    fi := fi + 1
  return out

def mutConf (P : PM) : Bool :=
  (List.range P.cm.n).all fun x =>
    (P.rmS[x]!).all fun w =>
      (P.riS[x]!).all fun v =>
        (List.range P.cm.n).any fun y => P.cm.riB w y && P.cm.rmB v y

/-! ## The two link families -/

structure ZData where
  levels : Array (Array Bool)
  nM : Nat
  monoViol : Nat
  deriving Inhabited

/-- Mode G: greatest-fixpoint layered approximants, p unprotected
(`bii_p_probe` verbatim). -/
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

def rslope : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * rslope n + 3

/-- Mode R: the RANKED family — `Z ℓ x y :=` agreement on every
variable-free pool member of crank ≤ `rslope ℓ`.  Decreasing by
construction; constant once `rslope ℓ` clears the pool's top crank
(the finite-pool truncation caveat). -/
def zRanked (K M : PM) : ZData := Id.run do
  let nK := K.cm.n
  let nM := M.cm.n
  let pool := vfPool.map fun φ => (crank2 φ, φ)
  let maxC := pool.foldl (fun a c => max a c.1) 0
  let tK := pool.map fun c => (List.range nK).map fun w => K.cm.forceB w c.2
  let tM := pool.map fun c => (List.range nM).map fun w => M.cm.forceB w c.2
  let mut levels : Array (Array Bool) := #[]
  let mut ℓ := 0
  let mut go := true
  while go do
    let r := rslope ℓ
    let mut cur : Array Bool := Array.replicate (nK * nM) false
    for x in List.range nK do
      for y in List.range nM do
        let mut ok := true
        for i in List.range pool.length do
          if (pool[i]!).1 ≤ r &&
              (tK[i]!)[x]! != (tM[i]!)[y]! then
            ok := false
        if ok then cur := cur.set! (x * nM + y) true
    levels := levels.push cur
    if r ≥ maxC then go := false
    ℓ := ℓ + 1
  return ⟨levels, nM, 0⟩

def zAt (zd : ZData) (lvl x y : Nat) : Bool :=
  (zd.levels[min lvl (zd.levels.size - 1)]!)[x * zd.nM + y]!

/-! ## Traces, closure info, RmC -/

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

/-! ## The answer search (per (Δ, u), ψ-independent, memoised) -/

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

/-! ## Statistics -/

structure PStats where
  configs : Nat := 0
  instAll : Nat := 0        -- (config, ψ) instances (ψ forced at u')
  instGiven : Nat := 0
  instOther : Nat := 0      -- the witness-freedom gain
  instFail : Nat := 0
  instPfree : Nat := 0      -- instances with ψ p-free
  givenPfree : Nat := 0
  otherPfree : Nat := 0
  failPfree : Nat := 0
  topUsed : Nat := 0        -- OTHER resolutions via the canonical top
  cfgLive : Nat := 0
  instLiveFail : Nat := 0
  deriving Inhabited

def dumpModel (tag : String) (P : PM) : IO Unit := do
  IO.println s!"    {tag}: n={P.cm.n} ri={P.cm.ri} rm={P.cm.rm} fall={P.cm.fall} val={P.cm.val} (frame #{P.fi})"

def dumpZ (zd : ZData) (nK : Nat) : IO Unit := do
  for l in List.range zd.levels.size do
    let lv := zd.levels[l]!
    let mut s := ""
    for x in List.range nK do
      for y in List.range zd.nM do
        if lv[x * zd.nM + y]! then s := s ++ s!"({x},{y}) "
    IO.println s!"      Z_{l} = [ {s}]"

/-! ## The generic scan (one mode) -/

def runScan (tag : String) (ms : Array PM) (needMConf : Bool)
    (zfun : PM → PM → ZData) : IO Unit := do
  let t0 ← IO.monoMsNow
  let nMod := ms.size
  let confl := ms.map mutConf
  let cis := (closures.map fun c => (c.1, mkClInfo c.2)).toArray
  let pools := (closures.map fun c =>
    ((psiPool c.2).map fun ψ => (ψ, !hasP ψ)).toArray).toArray
  IO.println s!"=== MODE {tag}: {nMod} models ==="
  let mut traces : Array (Array (Array Nat)) := #[]
  for ic in List.range cis.size do
    let ci := (cis[ic]!).2
    traces := traces.push (ms.map fun P => traceMasks ci.cl P)
  let mut stats : Array PStats := Array.replicate cis.size {}
  let mut monoViol := 0
  let mut stabHist : Array Nat := Array.replicate 40 0
  let mut failDumps : Array Nat := Array.replicate cis.size 0
  let mut otherDumped : Array Bool := Array.replicate cis.size false
  let mut pairsDone := 0
  for iK in List.range nMod do
    if confl[iK]! then
      let K := ms[iK]!
      let nK := K.cm.n
      for iM in List.range nMod do
        if !needMConf || confl[iM]! then
          let M := ms[iM]!
          let zd := zfun K M
          pairsDone := pairsDone + 1
          monoViol := monoViol + zd.monoViol
          let stab := zd.levels.size - 1
          stabHist := stabHist.set! (min stab 39) (stabHist[min stab 39]! + 1)
          let nM := M.cm.n
          for ic in List.range cis.size do
            let ci := (cis[ic]!).2
            let pool := pools[ic]!
            let clSize := ci.cl.size
            let tk := (traces[ic]!)[iK]!
            -- ψ truth masks over M's worlds
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
                                      -- an MwitResidue configuration core
                                      let mut s := stats[ic]!
                                      s := { s with configs := s.configs + 1 }
                                      let live := decide (2 * d - 1 < stab)
                                      if live then
                                        s := { s with cfgLive := s.cfgLive + 1 }
                                      -- answer at the GIVEN witness (memoised)
                                      let aGiven ← do
                                        match memo[Δ * nM + u]! with
                                        | some a => pure a
                                        | none =>
                                            let a := resolveAt K M zd ci tk Δ u
                                            memo := memo.set! (Δ * nM + u) (some a)
                                            pure a
                                      -- the ψ loop
                                      for j in List.range pool.size do
                                        if (ψtt[j]! >>> u) &&& 1 == 1 then
                                          let pfree := (pool[j]!).2
                                          s := { s with instAll := s.instAll + 1 }
                                          if pfree then
                                            s := { s with instPfree := s.instPfree + 1 }
                                          if aGiven.found then
                                            s := { s with instGiven := s.instGiven + 1 }
                                            if pfree then
                                              s := { s with givenPfree := s.givenPfree + 1 }
                                          else
                                            -- scan the other row-witnesses of ψ
                                            let mut other := false
                                            let mut viaTop := false
                                            let mut u2W := 0
                                            for u2 in M.rmS[m]! do
                                              if !other && (ψtt[j]! >>> u2) &&& 1 == 1 then
                                                let a2 ← do
                                                  match memo[Δ * nM + u2]! with
                                                  | some a => pure a
                                                  | none =>
                                                      let a := resolveAt K M zd ci tk Δ u2
                                                      memo := memo.set! (Δ * nM + u2) (some a)
                                                      pure a
                                                if a2.found then
                                                  other := true; u2W := u2
                                                else if topOK && M.fallA[u2]! then
                                                  other := true; viaTop := true; u2W := u2
                                            if other then
                                              s := { s with instOther := s.instOther + 1 }
                                              if viaTop then
                                                s := { s with topUsed := s.topUsed + 1 }
                                              if pfree then
                                                s := { s with otherPfree := s.otherPfree + 1 }
                                              if !otherDumped[ic]! then
                                                otherDumped := otherDumped.set! ic true
                                                IO.println s!"  EXAMPLE witness-freedom gain [{tag}/{(cis[ic]!).1}]: ψ={pf (pool[j]!).1} given u'={u} unresolvable, other witness u''={u2W}{if viaTop then " (via canonical top)" else ""}"
                                                dumpModel "K" K
                                                dumpModel "M" M
                                                IO.println s!"    k'={k'} k={k} kv={kv} κ={κ} m'={m'} m={m} d={d} Δ=\{{maskFormulas ci.cl Δ}}"
                                            else
                                              s := { s with instFail := s.instFail + 1 }
                                              if live then
                                                s := { s with instLiveFail := s.instLiveFail + 1 }
                                              if pfree then
                                                s := { s with failPfree := s.failPfree + 1 }
                                              if failDumps[ic]! < 10 then
                                                failDumps := failDumps.set! ic (failDumps[ic]! + 1)
                                                IO.println s!"  !!FAIL [{tag}/{(cis[ic]!).1}] (MwitResidue counterexample candidate): ψ={pf (pool[j]!).1} ({if pfree then "p-FREE" else "p-laden"})"
                                                dumpModel "K" K
                                                dumpModel "M" M
                                                IO.println s!"    M confluent: {confl[iM]!}  Z stabilised at {stab}  live={live}"
                                                IO.println s!"    k'={k'} k={k} kv={kv} κ={κ}  m'={m'} m={m} u'={u}  d={d}"
                                                IO.println s!"    Δ = \{{maskFormulas ci.cl Δ}}  tr(kv) = \{{maskFormulas ci.cl tk[kv]!}}"
                                                IO.println s!"    Rm-row(m)={M.rmS[m]!}  ψ-witnesses in row: {(M.rmS[m]!).filter (fun u2 => (ψtt[j]! >>> u2) &&& 1 == 1)}"
                                                dumpZ zd nK
                                      stats := stats.set! ic s
      if iK % 100 == 0 then
        let t ← IO.monoMsNow
        IO.println s!"  [{tag} heartbeat] iK={iK}/{nMod} pairs={pairsDone} elapsed={t - t0}ms configs={(List.range cis.size).map fun ic => (stats[ic]!).configs} fails={(List.range cis.size).map fun ic => (stats[ic]!).instFail}"
        (← IO.getStdout).flush
  let t1 ← IO.monoMsNow
  IO.println s!"=== MODE {tag} RESULTS (pairs={pairsDone}, monoViol={monoViol}) ==="
  IO.print s!"  Z stabilisation histogram: "
  for l in List.range 40 do
    if stabHist[l]! > 0 then IO.print s!"{l}:{stabHist[l]!} "
  IO.println ""
  for ic in List.range cis.size do
    let s := stats[ic]!
    IO.println s!"  {(cis[ic]!).1}:"
    IO.println s!"    configs={s.configs} (live window: {s.cfgLive}) | (config,ψ) instances={s.instAll} (p-free ψ: {s.instPfree})"
    IO.println s!"    GIVEN={s.instGiven} (p-free {s.givenPfree}) | OTHER={s.instOther} (p-free {s.otherPfree}; via top {s.topUsed}) | FAIL={s.instFail} (p-free {s.failPfree}; live {s.instLiveFail})"
  IO.println s!"=== MODE {tag} done in {t1 - t0} ms ==="
  (← IO.getStdout).flush

/-! ## The sanity control (mode G, the hand-built instance) -/

def ctrlCM : FinCM := ⟨2, [(0,1)], [(0,1)], [], [(1, "p")]⟩

def controlCheck : IO Bool := do
  IO.println "=== SANITY CONTROL (mode G): 2-chain, p at top, cl1, ψ=p ==="
  let ci := mkClInfo (closures[0]!).2
  let P := mkPM 9999 ctrlCM
  let zd := zLevels P P
  let tk := traceMasks ci.cl P
  let Δ := tk[0]!
  let d := ci.cl.size - popC ci.cl.size Δ
  let gates : List (String × Bool) :=
    [("tr(k'=0)=Δ ∧ ⊥∉Δ", tk[0]! == Δ && (Δ >>> ci.botIdx) &&& 1 == 0),
     ("(k'=0,m'=0)∈Z_2d+1 ∧ (k=0,m=0)∈Z_2d", zAt zd (2*d+1) 0 0 && zAt zd (2*d) 0 0),
     ("Rm 0 1 ∧ u'=1∉F ∧ 1⊨p", P.cm.rmB 0 1 && !P.fallA[1]! && P.cm.forceB 1 pV),
     ("kv=1: Ri 0 1 ∧ (1,1)∈Z_2d ∧ tr grows", P.cm.riB 0 1 && zAt zd (2*d) 1 1 && tk[1]! != Δ && (Δ &&& tk[1]! == Δ)),
     ("κ=0: Rm 0 0 ∧ (0,1)∈Z_2d−1 ∧ tr(0)=Δ", P.cm.rmB 0 0 && zAt zd (2*d-1) 0 1 && tk[0]! == Δ),
     ("K mutually confluent", mutConf P)]
  let mut ok := true
  for (nm, g) in gates do
    if !g then ok := false
    IO.println s!"  gate {nm}: {g}"
  let a := resolveAt P P zd ci tk Δ 1
  IO.println s!"  answer at the given witness u'=1: found={a.found} kb={a.kb} T=\{{maskFormulas ci.cl a.T}}"
  let pass := ok && a.found
  IO.println s!"=== CONTROL {if pass then "PASS" else "FAIL"} ==="
  return pass

def mainLoop : IO Unit := do
  IO.println "=== MwitResidue probe: witness-form residue, modes G (gfp family) and R (ranked family, POnly, both confluent) ==="
  let cis := closures.map fun c => (c.1, mkClInfo c.2)
  for (nm, ci) in cis do
    IO.println s!"closure {nm}: |cl|={ci.cl.size}"
  for (nm, cl) in closures do
    IO.println s!"ψ-pool[{nm}]: {String.intercalate " | " ((psiPool cl).map pf)}"
  IO.println s!"vf pool (ranked link): {String.intercalate " | " (vfPool.map fun φ => s!"{pf φ}(c{crank2 φ})")}"
  let ctrlPass ← controlCheck
  if !ctrlPass then
    IO.println "!! CONTROL FAILED — aborting"
    return
  runScan "R" modelsR.toArray true zRanked
  runScan "G" modelsG.toArray false zLevels

end MwitProbe

def main : IO Unit := MwitProbe.mainLoop
