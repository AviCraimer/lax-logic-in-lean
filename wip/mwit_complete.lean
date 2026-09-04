import LaxLogic.PLLSearch

/-!
# The CONFIG-COMPLETION probe: which hypothesis protects `kvInvisible`?

PROGRESS §57: the open kernel of the route is the grown partner's
variable-free invisibility — in every residue configuration,
`kv`'s vf theory at rank `rslope (2d)` equals `k`'s.  This probe runs
the funnel BACKWARDS: it enumerates the countermodel candidates —
K-pairs `(k, kv)` with `⊥ ∉ trace k`, `trace kv ⊋ trace k`, and a
VISIBLE variable-free difference at rank `rslope (2d)` (some
alternation rung below the rank separating them) — and then searches,
over every confluent `M`, for the rest of the configuration:

  S0: `k'` with `trace k' = trace k`, `k' Rᵢ k`, `k' Rᵢ kv`;
  S1: `m'` with rank-`rslope (2d+1)` agreement to `k'`;
  S2: `m`  with `m' Rᵢ m` and rank-`rslope (2d)` agreement to `k`;
  S3: `u'` infallible in `m`'s row with rank-`rslope (2d)` agreement
      to `kv`;
  S4: `κ` with `k Rₘ κ`, `trace κ = trace k`, rank-`rslope (2d−1)`
      agreement to `u'`;
  S5: COMPLETED — a configuration whose grown partner is vf-VISIBLE,
      refuting `kvInvisible` as a universal Prop.  For completions we
      further test the `StableWitness` and `RankGap` CONCLUSIONS per
      pool-ψ forced at `u'` (they may still hold through another
      witness) — a completion failing those too is a counterexample
      candidate to the route's open Prop itself.

The per-pair result is the DEEPEST stage reached over all `M`; the
blocking histogram says which hypothesis does the protecting.  Note
`internal_inclusion` (PROVED) already forces `type k ⊆ type kv` in
genuine configurations, so pairs whose visible difference has `kv`
DROPPING a rung must block at S3 or earlier — the probe tags the
difference direction (kv-adds / kv-drops / mixed) to check this
prediction.  Truncation caveat: for `d ≥ 2` the reservoir rank
`rslope (2d+1)` exceeds the pool ceiling, so S1 is pool-approximated
(completions there are candidates, not certificates).

Run: `lake build mwitcomplete && .lake/build/bin/mwitcomplete`.
-/

open PLLFormula PLLND PLLND.Search

set_option maxRecDepth 16384

namespace MwitComplete

def pV : PLLFormula := .prop "p"

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

def rnP : Nat → PLLFormula
  | 0 => .falsePLL
  | 1 => .somehow .falsePLL
  | 2 => (PLLFormula.somehow .falsePLL).ifThen .falsePLL
  | (n + 3) =>
    if n % 2 == 0 then (rnP (n + 1)).or (rnP (n + 2))
    else (rnP (n + 1)).ifThen (rnP (n - 1))

def psiPool (cl : List PLLFormula) : List PLLFormula := Id.run do
  let mut out := cl
  for φ in (PLLFormula.falsePLL.ifThen .falsePLL) ::
      (List.range 9).map rnP do
    if !(out.contains φ) then out := out ++ [φ]
  return out

/-! ## Battery (as wip/mwit_deep.lean) -/

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

def liftedLadder (j : Nat) (U : List Nat) (rmE : List (Nat × Nat)) : Frame :=
  closeF ⟨j + 1,
    ((List.range j).flatMap fun w =>
      ((List.range j).filter fun v => v + 2 ≤ w).map fun v => (w, v))
    ++ (List.range j).map (fun w => (w, j)),
    U.map (fun v => (v, j)) ++ rmE,
    [j]⟩

def rnFrame (n : Nat) (rmE : List (Nat × Nat)) (fall : List Nat) : Frame :=
  closeF ⟨n, (List.range n).flatMap (fun i =>
    if i ≥ 2 then [(i, i - 1), (i, i - 2)] else []), rmE, fall⟩

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
    out := out ++ [liftedLadder j [0] (((List.range j).filter (· ≥ 2)).map
      fun w => (w, w - 2))]
    out := out ++ [liftedLadder j [0, 1] ([(2, 0), (3, 1), (4, 2)])]
    out := out ++ [liftedLadder j [0, 1, 2] (((List.range j).filter (· ≥ 3)).map
      fun w => (w, w - 3))]
  out := out ++
    [rnFrame 8 [] [0], rnFrame 8 [(2,0),(3,1),(4,2),(5,3)] [0],
     rnFrame 10 [] [0], rnFrame 10 [(2,0),(4,2),(6,4),(8,6)] [0]]
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

/-! ## Rung data (cached masks) and rank agreement -/

def impMask (P : PM) (A B : Nat) : Nat := Id.run do
  let mut m := 0
  for w in List.range P.cm.n do
    let ok := (P.riS[w]!).all fun v =>
      ((A >>> v) &&& 1 == 0) || ((B >>> v) &&& 1 == 1)
    if ok then m := m ||| (1 <<< w)
  return m

def somehowMask (P : PM) (A : Nat) : Nat := Id.run do
  let mut m := 0
  for w in List.range P.cm.n do
    let ok := (P.riS[w]!).all fun v =>
      (P.rmS[v]!).any fun u => (A >>> u) &&& 1 == 1
    if ok then m := m ||| (1 <<< w)
  return m

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

def rslope : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * rslope n + 3

/-- Cross-model pool agreement at rank `r`. -/
def agreeAt (rdA rdB : Array (Nat × Nat)) (r x y : Nat) : Bool :=
  (List.range rdA.size).all fun i =>
    ((rdA[i]!).2 > r) ||
    (((rdA[i]!).1 >>> x) &&& 1 == ((rdB[i]!).1 >>> y) &&& 1)

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

structure ClInfo where
  cl : Array PLLFormula
  botIdx : Nat
  deriving Inhabited

def mkClInfo (cl : List PLLFormula) : ClInfo := Id.run do
  let a := cl.toArray
  let idxOf := fun (φ : PLLFormula) => Id.run do
    for i in List.range a.size do
      if a[i]! == φ then return i
    return a.size
  return ⟨a, idxOf .falsePLL⟩

structure CStats where
  pairsAll : Nat := 0        -- (k,kv): ⊥-free same-band, trace grows
  pairsVisible : Nat := 0    -- + vf-visible difference at rslope (2d)
  visAdds : Nat := 0         -- kv adds rungs only
  visDrops : Nat := 0        -- kv drops rungs only
  visMixed : Nat := 0
  blockS0 : Nat := 0         -- no k' (K-side)
  blockS1 : Nat := 0         -- no reservoir m' in any M
  blockS2 : Nat := 0         -- no base m
  blockS3 : Nat := 0         -- no witness u'
  blockS4 : Nat := 0         -- no κ-link
  completed : Nat := 0
  compStable : Nat := 0      -- completions where StableWitness's
                             -- conclusion holds for every pool-ψ at u'
  compRankGap : Nat := 0     -- ditto for RankGap's conclusion
  compBad : Nat := 0         -- completions where some ψ defeats BOTH
  deriving Inhabited

def dumpModel (tag : String) (P : PM) : IO Unit := do
  IO.println s!"    {tag}: n={P.cm.n} ri={P.cm.ri} rm={P.cm.rm} fall={P.cm.fall} val={P.cm.val} (frame #{P.fi})"

def mainLoop : IO Unit := do
  let t0 ← IO.monoMsNow
  let ms := models.toArray
  let nMod := ms.size
  let confl := ms.map mutConf
  let rd : Array (Array (Nat × Nat)) := ms.map fun P => rungData P RUNGS
  let cis := (closures.map fun c => (c.1, mkClInfo c.2)).toArray
  let pools := (closures.map fun c => (psiPool c.2).toArray).toArray
  IO.println s!"=== CONFIG-COMPLETION probe: {nMod} models ({(ms.toList.filter mutConf).length} confluent), rung pool {RUNGS} ==="
  let mut traces : Array (Array (Array Nat)) := #[]
  for ic in List.range cis.size do
    let ci := (cis[ic]!).2
    traces := traces.push (ms.map fun P => traceMasks ci.cl P)
  let mut stats : Array CStats := Array.replicate cis.size {}
  let mut compDumped : Array Bool := Array.replicate cis.size false
  for iK in List.range nMod do
    if confl[iK]! then
      let K := ms[iK]!
      let nK := K.cm.n
      let rdK := rd[iK]!
      for ic in List.range cis.size do
        let ci := (cis[ic]!).2
        let clSize := ci.cl.size
        let tk := (traces[ic]!)[iK]!
        for k in List.range nK do
          let Δ := tk[k]!
          if (Δ >>> ci.botIdx) &&& 1 == 0 then
            let d := clSize - popC clSize Δ
            let r1 := rslope (2 * d - 1)
            let r2 := rslope (2 * d)
            let rB := rslope (2 * d + 1)
            for kv in List.range nK do
              if tk[kv]! != Δ && (Δ &&& tk[kv]!) == Δ then
                let mut s := stats[ic]!
                s := { s with pairsAll := s.pairsAll + 1 }
                -- visible vf difference at r2?
                let mut adds := false
                let mut drops := false
                for i in List.range rdK.size do
                  if (rdK[i]!).2 ≤ r2 then
                    let bk := ((rdK[i]!).1 >>> k) &&& 1
                    let bv := ((rdK[i]!).1 >>> kv) &&& 1
                    if bk == 0 && bv == 1 then adds := true
                    if bk == 1 && bv == 0 then drops := true
                if adds || drops then
                  s := { s with pairsVisible := s.pairsVisible + 1 }
                  if adds && drops then s := { s with visMixed := s.visMixed + 1 }
                  else if adds then s := { s with visAdds := s.visAdds + 1 }
                  else s := { s with visDrops := s.visDrops + 1 }
                  -- K-side prefilter: k' below both, same trace
                  let kps := (List.range nK).filter fun kp =>
                    tk[kp]! == Δ && K.cm.riB kp k && K.cm.riB kp kv
                  if kps.isEmpty then
                    s := { s with blockS0 := s.blockS0 + 1 }
                  else
                    -- completion search over all M
                    let mut best := 1   -- deepest stage reached (1..5)
                    let mut done := false
                    for iM in List.range nMod do
                      if !done && confl[iM]! then
                        let M := ms[iM]!
                        let nM := M.cm.n
                        let rdM := rd[iM]!
                        for kp in kps do
                          if !done then
                            for m' in List.range nM do
                              if !done && agreeAt rdK rdM rB kp m' then
                                best := max best 2
                                for m in M.riS[m']! do
                                  if !done && agreeAt rdK rdM r2 k m then
                                    best := max best 3
                                    for u' in M.rmS[m]! do
                                      if !done && !M.fallA[u']! &&
                                          agreeAt rdK rdM r2 kv u' then
                                        best := max best 4
                                        let hasκ := (K.rmS[k]!).any fun κ =>
                                          tk[κ]! == Δ && agreeAt rdK rdM r1 κ u'
                                        if hasκ then
                                          best := 5
                                          done := true
                                          -- conclusions per pool-ψ at u'
                                          let mut allStable := true
                                          let mut allGap := true
                                          for ψ in pools[ic]! do
                                            if M.cm.forceB u' ψ then
                                              let hasStable := (M.rmS[m]!).any fun u2 =>
                                                M.cm.forceB u2 ψ &&
                                                agreeAt rdM rdM r2 m u2
                                              let hasGap := (List.range nK).any fun kb =>
                                                tk[kb]! == Δ && K.cm.riB kp kb &&
                                                (M.rmS[m]!).any fun u2 =>
                                                  M.cm.forceB u2 ψ &&
                                                  agreeAt rdK rdM r2 kb u2
                                              if !hasStable then allStable := false
                                              if !hasGap then allGap := false
                                          let mut s2 := stats[ic]!
                                          s2 := { s2 with completed := s2.completed + 1 }
                                          if allStable then
                                            s2 := { s2 with compStable := s2.compStable + 1 }
                                          if allGap then
                                            s2 := { s2 with compRankGap := s2.compRankGap + 1 }
                                          if !allStable && !allGap then
                                            s2 := { s2 with compBad := s2.compBad + 1 }
                                          stats := stats.set! ic s2
                                          s := stats[ic]!
                                          if !compDumped[ic]! then
                                            compDumped := compDumped.set! ic true
                                            IO.println s!"  COMPLETION [{(cis[ic]!).1}]: d={d} k={k} kv={kv} k'={kp} m'={m'} m={m} u'={u'} allStable={allStable} allGap={allGap}"
                                            dumpModel "K" K
                                            dumpModel "M" M
                                            IO.println s!"    Δ=\{{maskFormulas ci.cl Δ}} tr(kv)=\{{maskFormulas ci.cl tk[kv]!}} adds={adds} drops={drops}"
                    if !done then
                      match best with
                      | 1 => s := { s with blockS1 := s.blockS1 + 1 }
                      | 2 => s := { s with blockS2 := s.blockS2 + 1 }
                      | 3 => s := { s with blockS3 := s.blockS3 + 1 }
                      | _ => s := { s with blockS4 := s.blockS4 + 1 }
                stats := stats.set! ic s
      if iK % 25 == 0 then
        let t ← IO.monoMsNow
        IO.println s!"  [heartbeat] iK={iK}/{nMod} elapsed={t - t0}ms visible={(List.range cis.size).map fun ic => (stats[ic]!).pairsVisible} completed={(List.range cis.size).map fun ic => (stats[ic]!).completed}"
        (← IO.getStdout).flush
  let t1 ← IO.monoMsNow
  IO.println "=== CONFIG-COMPLETION RESULTS ==="
  for ic in List.range cis.size do
    let s := stats[ic]!
    IO.println s!"  {(cis[ic]!).1}:"
    IO.println s!"    pairs: all={s.pairsAll} vf-VISIBLE={s.pairsVisible} (kv-adds={s.visAdds} kv-drops={s.visDrops} mixed={s.visMixed})"
    IO.println s!"    blocking: S0-no-k'={s.blockS0} S1-no-m'={s.blockS1} S2-no-m={s.blockS2} S3-no-u'={s.blockS3} S4-no-κ={s.blockS4}"
    IO.println s!"    COMPLETED={s.completed} | StableWitness-conclusion-holds={s.compStable} RankGap-conclusion-holds={s.compRankGap} BOTH-FAIL={s.compBad}"
  IO.println s!"=== done in {t1 - t0} ms ==="

end MwitComplete

def main : IO Unit := MwitComplete.mainLoop
