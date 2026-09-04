import LaxLogic.PLLSearch

/-!
# Probe (corrected): the b.ii configuration with p-CONTAINING closures
# and p UNPROTECTED

Semantic-UI route, the `MforthResidue` residue of the amalgamation
◯-induction (route doc §0(ii), PROGRESS §34–36).  The previous probe
(`bii_probe.lean`) reported "0 configurations", an ARTIFACT: its
closures contained no occurrence of the quantified atom p, while
`residue_config_satisfiable` (PROVED) exhibits a configuration whose
growth is pure-p.  This probe corrects the design:

* the approximants' Z₀ atoms-clause protects only atoms OTHER than
  `p` — pairs may disagree on `p`; the fallibility clause is
  unchanged;
* models carry TWO hereditary atoms `p`, `q`;
* the closures contain `p` (◯-adequately extended, `⊥` included);
* at every found configuration the FULL conclusion of `MforthResidue`
  is tested by exhaustive search.

The configuration (over pairs `(K, M)` with `K` mutually confluent,
`M` arbitrary; `Δ := tr(k)`, `d := |cl| − |Δ|`):

  worlds `k', k, kv, κ ∈ K`, `m', m, u ∈ M` with
  (1) `tr(k') = Δ`, `⊥ ∉ Δ`;
  (2) `Rᵢ m' m`, `Rₘ m u`, `u ∉ F_M`;
  (3) `(k',m') ∈ Z_{2d+1}`, `(k,m) ∈ Z_{2d}`;
  (4) `Rᵢ k' kv`, `(kv,u) ∈ Z_{2d}`, `Δ ⊊ tr(kv)`  (iback partner grew);
  (5) `Rₘ k κ`, `(κ,u) ∈ Z_{2d−1}`, `tr(κ) = Δ`   (mback partner did not).

THE CONCLUSION TEST (exhaustive): an answer is ANY `kb ∈ K` with
`T := tr(kb) ⊇ Δ` such that
  (i)   `RmC(Δ,T)`: `Δ ⊆ T` and every `χ ∈ T` (with `boxOf χ ∈ cl` —
        vacuous, cl is ◯-adequate) has `boxOf χ ∈ Δ`;
  (ii)  base link `(kb,u) ∈ Z_{2·d(T)}`, `d(T) := |cl| − |T|`;
  (iii) a reservoir `(kr,mr)`: `tr(kr) = T`, `Rᵢ mr u`,
        `(kr,mr) ∈ Z_{2·d(T)+1}` — `(kb,u)` itself checked first
        (`Rᵢ u u` reflexive).
A configuration with NO answer is a FAILURE = a counterexample
candidate to `MforthResidue` (dumped in full).

SANITY CONTROL (must pass): the hand-built instance of
`residue_config_satisfiable` — `K = M =` the 2-point chain
(`Rᵢ = Rₘ` = the order, no fallible worlds, `p` at the top only, `q`
nowhere), closure `{⊥,p,◯⊥,◯p}`, `k'=k=κ=0`, `m'=m=0`, `u=kv=1` —
must be FOUND by the machinery and must RESOLVE (the grown answer
`T = tr(1)` is RmC-anticipated since `◯p ∈ tr(0)`).

GROWTH BOUNDARY BOOKKEEPING: `residue_growth_boundary` (PROVED)
says: over a RANKED link, every p-FREE member of the growth
`tr(kv)∖Δ` has `crankC > 2d−1` (◯ costs 1).  Rankedness at `crankC`
is delivered by `force_iff_of_layeredC` for pairs with BOTH models
mutually confluent; the approximants computed here are the LARGEST
lawful layered family, so on such pairs a protected growth member
with `crankC ≤ 2d−1` would contradict the theorem = a probe bug.
On pairs whose `M` is NOT confluent the theorem's hypothesis is not
in force and such members are merely recorded.  An empirical
rankedness check runs alongside: over cl, `(x,y) ∈ Z_{crankC χ}`
with `χ` p-free must force χ equally when both models are confluent
(expect 0 violations).

Battery: phase A = the ≤4-world base frames (default + extra,
transitively closed) with ALL hereditary p×q decorations; phase B =
a 5-world slice (the 5-world extra frames + random 4/5-world
frames) with capped decorations.

Run: `lake build biipprobe && .lake/build/bin/biipprobe`.
-/

open PLLFormula PLLND PLLND.Search

set_option maxRecDepth 16384

namespace BiiPProbe

def pV : PLLFormula := .prop "p"
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

/-- The three p-containing closures of the corrected design. -/
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

/-- Does the formula contain the quantified atom `p`?  (Growth members
with `p` are invisible to the protected-atoms clause.) -/
def hasP : PLLFormula → Bool
  | .prop a => a == "p"
  | .falsePLL => false
  | .and φ ψ => hasP φ || hasP ψ
  | .or φ ψ => hasP φ || hasP ψ
  | .ifThen φ ψ => hasP φ || hasP ψ
  | .somehow φ => hasP φ

/-- `crankC`: the ◯-costs-1 complexity (⊃ costs 1, ∧/∨ free), the
rank measure of `residue_growth_boundary`. -/
def crankC : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and φ ψ => max (crankC φ) (crankC ψ)
  | .or φ ψ => max (crankC φ) (crankC ψ)
  | .ifThen φ ψ => max (crankC φ) (crankC ψ) + 1
  | .somehow φ => crankC φ + 1

/-! ## Battery -/

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

/-- Up-closed subsets of a closed frame (hereditary decorations),
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

/-- Random frames, as in the previous probes. -/
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

/-- Phase A: the ≤4-world base frames, ALL hereditary p×q decorations. -/
def phaseAFrames : List Frame :=
  ((defaultFrames ++ extraFrames).map closeF).filter (·.n ≤ 4)

/-- Phase B (the runtime-permitting slice): 5-world extra frames plus
random 4/5-world frames, decorations capped (p-sets ≤ 8, q-sets ≤ 3). -/
def phaseBFrames : List Frame :=
  ((extraFrames.filter (·.n == 5)).map closeF)
    ++ (allRand.filter (·.n == 4)).take 8
    ++ (allRand.filter (·.n == 5)).take 4

/-! ### Phase C: deep frames (6–7 worlds), chasing the LIVE window

On the ≤5-world battery every configuration has `2d−1 > stab`: all
financed Z-levels sit at the fixpoint and rescue is easy.  The
contentful counterexample window needs the approximant chain still
strictly descending at the financed levels (`2d−1 < stab`), which
requires structural depth: long chains with alternating `Rₘ` and
Rieger–Nishimura-ladder truncations, as in the previous probe. -/

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

def nFrA : Nat := phaseAFrames.length
def nFrB : Nat := phaseBFrames.length
def nFr : Nat := nFrA + nFrB + phaseCFrames.length

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

/-- Decorate a frame with a hereditary p-set and q-set. -/
def deco (f : Frame) (fi : Nat) (P Q : List Nat) : PM :=
  mkPM fi ⟨f.n, f.ri, f.rm, f.fall,
    P.map (fun w => (w, "p")) ++ Q.map (fun w => (w, "q"))⟩

def models : List PM := Id.run do
  let mut out : List PM := []
  let mut fi := 0
  for f in phaseAFrames do
    let us := upSets f
    for P in us do
      for Q in us do
        out := out ++ [deco f fi P Q]
    fi := fi + 1
  for f in phaseBFrames do
    let us := upSets f
    for P in us.take 8 do
      for Q in us.take 3 do
        out := out ++ [deco f fi P Q]
    fi := fi + 1
  for f in phaseCFrames do
    let us := upSets f
    for P in us.take 8 do
      for Q in us.take 3 do
        out := out ++ [deco f fi P Q]
    fi := fi + 1
  return out

/-- MutuallyConfluent: `∀ x w v, Rₘ x w → Rᵢ x v → ∃y, Rᵢ w y ∧ Rₘ v y`. -/
def mutConf (P : PM) : Bool :=
  (List.range P.cm.n).all fun x =>
    (P.rmS[x]!).all fun w =>
      (P.riS[x]!).all fun v =>
        (List.range P.cm.n).any fun y => P.cm.riB w y && P.cm.rmB v y

/-! ## Layered approximants — p UNPROTECTED

Z₀ requires agreement on the protected atoms (here: `q` only, NOT
`p`) and on fallibility; the four zigzag clauses and the fallibility
escapes are unchanged from the previous probe. -/

structure ZData where
  levels : Array (Array Bool)  -- Z_0, Z_1, …, stabilised tail
  nM : Nat
  monoViol : Nat               -- violations of Z_{n+1} ⊆ Z_n (expect 0)

def zLevels (K M : PM) : ZData := Id.run do
  let nK := K.cm.n
  let nM := M.cm.n
  let mut z0 : Array Bool := Array.replicate (nK * nM) false
  for x in List.range nK do
    for y in List.range nM do
      if (K.cm.valB x "q") == (M.cm.valB y "q")   -- p NOT protected
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

/-! ## Closure info and the canonical Rₘ condition -/

structure ClInfo where
  cl : Array PLLFormula
  botIdx : Nat
  boxIdx : Array Nat  -- boxIdx[i] = index of boxOf cl[i] in cl
  protIdx : Array Bool -- protIdx[i] = cl[i] is p-free (protected)
  crk : Array Nat     -- crk[i] = crankC cl[i]
  deriving Inhabited

def mkClInfo (cl : List PLLFormula) : ClInfo := Id.run do
  let a := cl.toArray
  let idxOf := fun (φ : PLLFormula) => Id.run do
    for i in List.range a.size do
      if a[i]! == φ then return i
    return a.size
  let mut bx : Array Nat := #[]
  let mut pr : Array Bool := #[]
  let mut ck : Array Nat := #[]
  for i in List.range a.size do
    bx := bx.push (idxOf (boxOf a[i]!))
    pr := pr.push (!hasP a[i]!)
    ck := ck.push (crankC a[i]!)
  return ⟨a, idxOf .falsePLL, bx, pr, ck⟩

/-- `RmC(Δ,T)`: `Δ ⊆ T` and `∀χ ∈ T` (with `boxOf χ ∈ cl` — vacuous,
cl is ◯-adequate), `boxOf χ ∈ Δ`. -/
def rmC (ci : ClInfo) (Δ T : Nat) : Bool :=
  (Δ &&& T == Δ) &&
  (List.range ci.cl.size).all fun i =>
    ((T >>> i) &&& 1 == 0) || ((Δ >>> ci.boxIdx[i]!) &&& 1 == 1)

/-! ## The conclusion test (exhaustive answer search) -/

structure Ans where
  found : Bool := false
  same : Bool := false      -- an answer with T = Δ exists
  grown : Bool := false     -- an answer with T ⊋ Δ exists
  kb : Nat := 0             -- first witness
  T : Nat := 0
  selfRes : Bool := false   -- its reservoir was (kb,u) itself
  kr : Nat := 0
  mr : Nat := 0
  deriving Inhabited

/-- Exhaustive search for an answer at `(Δ,u)`: any `kb` with
`T := tr(kb) ⊇ Δ`, `RmC(Δ,T)`, `(kb,u) ∈ Z_{2d(T)}`, and a reservoir
`(kr,mr)` with `tr(kr) = T`, `Rᵢ mr u`, `(kr,mr) ∈ Z_{2d(T)+1}`
(`(kb,u)` itself checked first). -/
def resolveFull (K M : PM) (zd : ZData) (ci : ClInfo) (tk : Array Nat)
    (Δ u : Nat) : Ans := Id.run do
  let nK := K.cm.n
  let nM := M.cm.n
  let clSize := ci.cl.size
  let mut a : Ans := {}
  for kb in List.range nK do
    let T := tk[kb]!
    if (Δ &&& T) == Δ && rmC ci Δ T then
      let dT := clSize - popC clSize T
      if zAt zd (2 * dT) kb u then
        let mut hit := false
        let mut sr := false
        let mut krW := 0
        let mut mrW := 0
        if zAt zd (2 * dT + 1) kb u then
          hit := true; sr := true; krW := kb; mrW := u
        else
          for kr in List.range nK do
            if !hit && tk[kr]! == T then
              for mr in List.range nM do
                if !hit && M.cm.riB mr u && zAt zd (2 * dT + 1) kr mr then
                  hit := true; krW := kr; mrW := mr
        if hit then
          if !a.found then
            a := { a with found := true, kb := kb, T := T, selfRes := sr,
                          kr := krW, mr := mrW }
          if T == Δ then a := { a with same := true }
          else a := { a with grown := true }
  return a

/-- Reservoir existence at `(T,u)` alone (for the kv-as-answer check). -/
def resvScan (K M : PM) (zd : ZData) (tk : Array Nat) (clSize T u : Nat) :
    Bool :=
  let dT := clSize - popC clSize T
  (List.range K.cm.n).any fun kr => tk[kr]! == T &&
    (List.range M.cm.n).any fun mr =>
      M.cm.riB mr u && zAt zd (2 * dT + 1) kr mr

/-! ## Statistics -/

structure PStats where
  configs : Nat := 0
  cfgMConf : Nat := 0        -- configs whose M is also confluent
  resolved : Nat := 0
  failures : Nat := 0
  ansSame : Nat := 0         -- same-trace answer available
  ansGrown : Nat := 0        -- grown answer available
  ansSameOnly : Nat := 0
  ansGrownOnly : Nat := 0
  ansBoth : Nat := 0
  firstSelfRes : Nat := 0    -- first witness used the self-reservoir
  kvSelf : Nat := 0          -- kv itself is a valid answer
  antic : Nat := 0           -- RmC(Δ, tr(kv)) holds (growth ◯-anticipated)
  gPureP : Nat := 0          -- all growth members p-laden
  gMixed : Nat := 0          -- both p-laden and protected members
  gPureProt : Nat := 0       -- all growth members protected
  protMem : Nat := 0         -- protected growth member instances
  protLEc : Nat := 0         -- protected member crankC ≤ 2d−1, M confluent (BUG!)
  protLEn : Nat := 0         -- protected member crankC ≤ 2d−1, M non-confluent
  protHi : Nat := 0          -- protected member crankC ≥ 2d
  cells : Nat := 0           -- distinct (Δ,u) resolution cells computed
  cellFail : Nat := 0        -- distinct cells with no answer
  cfgLive : Nat := 0         -- configs in the LIVE window (2d−1 < stab:
                             -- financed levels below the fixpoint)
  liveFail : Nat := 0        -- failures among live configs
  rankViolC : Nat := 0       -- rankedness violations, both confluent (expect 0)
  rankViolN : Nat := 0       -- rankedness violations, M non-confluent (allowed)
  deriving Inhabited

structure Funnel where
  gA : Nat := 0   -- k' with ⊥ ∉ Δ
  gB : Nat := 0   -- + m' with (k',m') ∈ Z_{2d+1}
  gC : Nat := 0   -- + k with tr(k) = Δ
  gD : Nat := 0   -- + m: Rᵢ m' m ∧ (k,m) ∈ Z_{2d}
  gE : Nat := 0   -- + u: Rₘ m u ∧ u ∉ F
  gF : Nat := 0   -- candidates with ≥1 grown iback kv (Z_{2d}, Δ ⊊ tr)
  deriving Inhabited

def dumpModel (tag : String) (P : PM) : IO Unit := do
  IO.println s!"    {tag}: n={P.cm.n} ri={P.cm.ri} rm={P.cm.rm} fall={P.cm.fall} val={P.cm.val} (frame #{P.fi})"

def dumpTraces (tag : String) (ci : ClInfo) (P : PM) (t : Array Nat) :
    IO Unit := do
  for w in List.range P.cm.n do
    IO.println s!"    tr_{tag}({w}) = \{{maskFormulas ci.cl t[w]!}}"

def dumpZ (zd : ZData) (nK : Nat) : IO Unit := do
  for l in List.range zd.levels.size do
    let lv := zd.levels[l]!
    let mut s := ""
    for x in List.range nK do
      for y in List.range zd.nM do
        if lv[x * zd.nM + y]! then s := s ++ s!"({x},{y}) "
    IO.println s!"      Z_{l} = [ {s}]"

/-- Growth decode: each member with p-ladenness and crankC vs 2d−1. -/
def growthDecode (ci : ClInfo) (gm d : Nat) : String :=
  String.intercalate "; " (((List.range ci.cl.size).filter
    (fun i => (gm >>> i) &&& 1 == 1)).map (fun i =>
      let tagP := if ci.protIdx[i]! then
        s!"PROTECTED crankC={ci.crk[i]!} vs 2d−1={2*d-1}"
        else "p-laden"
      s!"{pf ci.cl[i]!} ({tagP})"))

/-! ## The sanity control (residue_config_satisfiable, hand-built) -/

def ctrlCM : FinCM := ⟨2, [(0,1)], [(0,1)], [], [(1, "p")]⟩

/-- Check the hand-built instance directly: gates at
`k'=k=κ=0, m'=m=0, u=kv=1` over cl1, then the conclusion search. -/
def controlCheck (ci : ClInfo) : IO Bool := do
  IO.println "=== SANITY CONTROL: 2-point chain, p at top, q nowhere, cl1 ==="
  let P := mkPM 9999 ctrlCM
  let zd := zLevels P P
  let tk := traceMasks ci.cl P
  let Δ := tk[0]!
  let d := ci.cl.size - popC ci.cl.size Δ
  IO.println s!"  tr(0) = \{{maskFormulas ci.cl tk[0]!}}  tr(1) = \{{maskFormulas ci.cl tk[1]!}}  d={d}  stab={zd.levels.size - 1}"
  dumpZ zd P.cm.n
  let z0total := (List.range 4).all fun i => (zd.levels[0]!)[i]!
  IO.println s!"  Z_0 total: {z0total} (p unprotected: expected true)"
  let gates : List (String × Bool) :=
    [("tr(k'=0)=Δ", tk[0]! == Δ),
     ("⊥∉Δ", (Δ >>> ci.botIdx) &&& 1 == 0),
     ("Ri m'=0 m=0", P.cm.riB 0 0),
     ("Rm m=0 u=1", P.cm.rmB 0 1),
     ("u=1∉F", !P.fallA[1]!),
     ("(k'=0,m'=0)∈Z_2d+1", zAt zd (2*d+1) 0 0),
     ("(k=0,m=0)∈Z_2d", zAt zd (2*d) 0 0),
     ("Ri k'=0 kv=1", P.cm.riB 0 1),
     ("(kv=1,u=1)∈Z_2d", zAt zd (2*d) 1 1),
     ("Δ⊊tr(kv=1)", (Δ &&& tk[1]! == Δ) && tk[1]! != Δ),
     ("Rm k=0 κ=0", P.cm.rmB 0 0),
     ("(κ=0,u=1)∈Z_2d−1", zAt zd (2*d-1) 0 1),
     ("tr(κ=0)=Δ", tk[0]! == Δ),
     ("K mutually confluent", mutConf P)]
  let mut ok := true
  for (nm, g) in gates do
    if !g then ok := false
    IO.println s!"  gate {nm}: {g}"
  let gm := tk[1]! &&& (((1 <<< ci.cl.size) - 1) ^^^ Δ)
  IO.println s!"  growth tr(kv)∖Δ = \{{maskFormulas ci.cl gm}}  [{growthDecode ci gm d}]"
  IO.println s!"  RmC(Δ,tr(kv)) (◯-anticipation): {rmC ci Δ tk[1]!}"
  let a := resolveFull P P zd ci tk Δ 1
  IO.println s!"  conclusion search: found={a.found} sameTraceAnswer={a.same} grownAnswer={a.grown}"
  if a.found then
    IO.println s!"  first witness: kb={a.kb} T=\{{maskFormulas ci.cl a.T}} selfReservoir={a.selfRes} kr={a.kr} mr={a.mr}"
  let pass := ok && a.found
  IO.println s!"=== CONTROL {if pass then "PASS" else "FAIL"} ==="
  return pass

/-! ## Main -/

def mainLoop : IO Unit := do
  let t0 ← IO.monoMsNow
  let ms := models
  let nMod := ms.length
  let msArr := ms.toArray
  let confl := msArr.map mutConf
  let nConfl := (List.range nMod).foldl
    (fun a i => if confl[i]! then a + 1 else a) 0
  let nModA := (List.range nMod).foldl
    (fun a i => if (msArr[i]!).fi < nFrA then a + 1 else a) 0
  let nModB := (List.range nMod).foldl
    (fun a i => if (msArr[i]!).fi ≥ nFrA && (msArr[i]!).fi < nFrA + nFrB
      then a + 1 else a) 0
  IO.println s!"=== b.ii probe, CORRECTED (p-containing closures, p unprotected) ==="
  IO.println s!"battery: phase A {nFrA} frames (≤4 worlds, ALL p×q decorations) = {nModA} models; phase B {nFrB} frames (5-world slice + random 4/5-world, p≤8 × q≤3 decorations) = {nModB} models; phase C {nFr - nFrA - nFrB} frames (deep 6/7-world chains, RN ladders, deep randoms; p≤8 × q≤3) = {nMod - nModA - nModB} models; total {nMod} models, {nConfl} mutually confluent (usable as K)"
  let cis := (closures.map fun c => (c.1, mkClInfo c.2)).toArray
  for i in List.range cis.size do
    let (nm, ci) := cis[i]!
    IO.println s!"closure {i} {nm}: |cl|={ci.cl.size} [{maskFormulas ci.cl ((1 <<< ci.cl.size) - 1)}]"
  -- the sanity control (must pass)
  let ctrlPass ← controlCheck (cis[0]!).2
  if !ctrlPass then
    IO.println "!! CONTROL FAILED — aborting (machinery suspect)"
    return
  -- control model present in the battery?
  let mut ctrlIdx : Option Nat := none
  for i in List.range nMod do
    if ctrlIdx.isNone && (msArr[i]!).cm == ctrlCM then
      ctrlIdx := some i
  IO.println s!"control model battery index: {ctrlIdx} (frame #{(msArr[ctrlIdx.getD 0]!).fi})"
  -- traces per closure per model
  let mut traces : Array (Array (Array Nat)) := #[]
  for ic in List.range cis.size do
    let ci := (cis[ic]!).2
    traces := traces.push (msArr.map fun P => traceMasks ci.cl P)
  -- global counters
  let mut stats : Array PStats := Array.replicate cis.size {}
  let mut funnels : Array Funnel := Array.replicate cis.size {}
  let mut monoViol := 0
  let mut stabHist : Array Nat := Array.replicate 40 0
  -- (d, stab) occupancy at configs: ic*64 + min d 7 * 8 + min stab 7
  let mut dsHist : Array Nat := Array.replicate (cis.size * 64) 0
  -- growth member counts per closure per formula index
  let mut gMem : Array Nat := Array.replicate (cis.size * 8) 0
  -- per (K-frame, M-frame) per closure: (configs, failures)
  let mut classTab : Array (Nat × Nat) :=
    Array.replicate (cis.size * nFr * nFr) (0, 0)
  -- dump budgets
  let mut failDumps : Array Nat := Array.replicate cis.size 0
  let mut exSameDumped : Array Bool := Array.replicate cis.size false
  let mut exGrownDumped : Array Bool := Array.replicate cis.size false
  let mut protLEDumps : Array Nat := Array.replicate cis.size 0
  let mut rankDumps := 0
  let mut pairsDone := 0
  for iK in List.range nMod do
    if confl[iK]! then
      let K := msArr[iK]!
      let nK := K.cm.n
      for iM in List.range nMod do
        let M := msArr[iM]!
        let mC := confl[iM]!
        let zd := zLevels K M
        pairsDone := pairsDone + 1
        monoViol := monoViol + zd.monoViol
        let stab := zd.levels.size - 1
        stabHist := stabHist.set! (min stab 39) (stabHist[min stab 39]! + 1)
        let nM := M.cm.n
        for ic in List.range cis.size do
          let ci := (cis[ic]!).2
          let clSize := ci.cl.size
          let tk := (traces[ic]!)[iK]!
          let tm := (traces[ic]!)[iM]!
          -- empirical rankedness check: (x,y) ∈ Z_{crankC χ}, χ p-free in cl
          -- ⇒ agree on χ (expect 0 violations when both models confluent)
          for i in List.range clSize do
            if ci.protIdx[i]! then
              let c := ci.crk[i]!
              for x in List.range nK do
                for y in List.range nM do
                  if zAt zd c x y &&
                      ((tk[x]! >>> i) &&& 1) != ((tm[y]! >>> i) &&& 1) then
                    let mut s := stats[ic]!
                    if mC then
                      s := { s with rankViolC := s.rankViolC + 1 }
                      if rankDumps < 5 then
                        rankDumps := rankDumps + 1
                        IO.println s!"  !!RANKEDNESS VIOLATION (both confluent) [{(cis[ic]!).1}]: χ={pf ci.cl[i]!} crankC={c} (x,y)=({x},{y}) K#{iK} M#{iM}"
                    else
                      s := { s with rankViolN := s.rankViolN + 1 }
                    stats := stats.set! ic s
          -- the b.ii configuration scan
          let mut memo : Array (Option Ans) :=
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
                              let kvs := (K.riS[k']!).filter fun kv =>
                                zAt zd (2 * d) kv u
                                  && (Δ &&& tk[kv]! == Δ) && tk[kv]! != Δ
                              if kvs.size > 0 then
                                funnels := funnels.set! ic { funnels[ic]! with gF := (funnels[ic]!).gF + 1 }
                              for kv in kvs do
                                for κ in K.rmS[k]! do
                                  if zAt zd (2 * d - 1) κ u && tk[κ]! == Δ then
                                    -- a b.ii configuration
                                    let mut s := stats[ic]!
                                    s := { s with configs := s.configs + 1 }
                                    if mC then
                                      s := { s with cfgMConf := s.cfgMConf + 1 }
                                    let live := 2 * d - 1 < stab
                                    if live then
                                      s := { s with cfgLive := s.cfgLive + 1 }
                                    dsHist := dsHist.set! (ic * 64 + (min d 7) * 8 + min stab 7)
                                      (dsHist[ic * 64 + (min d 7) * 8 + min stab 7]! + 1)
                                    -- growth composition
                                    let gm := tk[kv]! &&& (((1 <<< clSize) - 1) ^^^ Δ)
                                    let mut anyP := false
                                    let mut anyProt := false
                                    for i in List.range clSize do
                                      if (gm >>> i) &&& 1 == 1 then
                                        gMem := gMem.set! (ic * 8 + i) (gMem[ic * 8 + i]! + 1)
                                        if ci.protIdx[i]! then
                                          anyProt := true
                                          s := { s with protMem := s.protMem + 1 }
                                          if ci.crk[i]! + 1 ≤ 2 * d then  -- crankC ≤ 2d−1
                                            if mC then
                                              s := { s with protLEc := s.protLEc + 1 }
                                            else
                                              s := { s with protLEn := s.protLEn + 1 }
                                            if protLEDumps[ic]! < 4 then
                                              protLEDumps := protLEDumps.set! ic (protLEDumps[ic]! + 1)
                                              IO.println s!"  {if mC then "!!SUSPECT-BUG (both confluent)" else "sub-boundary protected growth (M NOT confluent — outside theorem)"} [{(cis[ic]!).1}]: member {pf ci.cl[i]!} crankC={ci.crk[i]!} ≤ 2d−1={2*d-1}, K#{iK}(fr{K.fi}) M#{iM}(fr{M.fi}) k'={k'} kv={kv} u={u} d={d}"
                                          else
                                            s := { s with protHi := s.protHi + 1 }
                                        else
                                          anyP := true
                                    if anyP && anyProt then
                                      s := { s with gMixed := s.gMixed + 1 }
                                    else if anyP then
                                      s := { s with gPureP := s.gPureP + 1 }
                                    else
                                      s := { s with gPureProt := s.gPureProt + 1 }
                                    -- ◯-anticipation of the config growth + kv-as-answer
                                    let Tv := tk[kv]!
                                    let anticB := rmC ci Δ Tv
                                    if anticB then
                                      s := { s with antic := s.antic + 1 }
                                    let dTv := clSize - popC clSize Tv
                                    if anticB && zAt zd (2 * dTv) kv u &&
                                        (zAt zd (2 * dTv + 1) kv u ||
                                          resvScan K M zd tk clSize Tv u) then
                                      s := { s with kvSelf := s.kvSelf + 1 }
                                    -- the conclusion test (memoised per (Δ,u))
                                    let mut a : Ans := {}
                                    let mut fresh := false
                                    match memo[Δ * nM + u]! with
                                    | some a0 => a := a0
                                    | none =>
                                        a := resolveFull K M zd ci tk Δ u
                                        memo := memo.set! (Δ * nM + u) (some a)
                                        fresh := true
                                        s := { s with cells := s.cells + 1 }
                                        if !a.found then
                                          s := { s with cellFail := s.cellFail + 1 }
                                    let key := ic * nFr * nFr + K.fi * nFr + M.fi
                                    let (cc, cf) := classTab[key]!
                                    let mut cf' := cf
                                    if a.found then
                                      s := { s with resolved := s.resolved + 1 }
                                      if a.same then s := { s with ansSame := s.ansSame + 1 }
                                      if a.grown then s := { s with ansGrown := s.ansGrown + 1 }
                                      if a.same && a.grown then
                                        s := { s with ansBoth := s.ansBoth + 1 }
                                      else if a.same then
                                        s := { s with ansSameOnly := s.ansSameOnly + 1 }
                                        if !exSameDumped[ic]! then
                                          exSameDumped := exSameDumped.set! ic true
                                          IO.println s!"  EXAMPLE same-trace-only resolution [{(cis[ic]!).1}]:"
                                          dumpModel "K" K
                                          dumpModel "M" M
                                          IO.println s!"    k'={k'} k={k} kv={kv} κ={κ} m'={m'} m={m} u={u} d={d} Δ=\{{maskFormulas ci.cl Δ}} tr(kv)=\{{maskFormulas ci.cl Tv}}"
                                          IO.println s!"    answer kb={a.kb} T=\{{maskFormulas ci.cl a.T}} selfRes={a.selfRes} kr={a.kr} mr={a.mr}"
                                      else
                                        s := { s with ansGrownOnly := s.ansGrownOnly + 1 }
                                        if !exGrownDumped[ic]! then
                                          exGrownDumped := exGrownDumped.set! ic true
                                          IO.println s!"  EXAMPLE grown-only resolution [{(cis[ic]!).1}]:"
                                          dumpModel "K" K
                                          dumpModel "M" M
                                          IO.println s!"    k'={k'} k={k} kv={kv} κ={κ} m'={m'} m={m} u={u} d={d} Δ=\{{maskFormulas ci.cl Δ}} tr(kv)=\{{maskFormulas ci.cl Tv}}"
                                          IO.println s!"    answer kb={a.kb} T=\{{maskFormulas ci.cl a.T}} selfRes={a.selfRes} kr={a.kr} mr={a.mr}"
                                      if a.selfRes then
                                        s := { s with firstSelfRes := s.firstSelfRes + 1 }
                                    else
                                      s := { s with failures := s.failures + 1 }
                                      if live then
                                        s := { s with liveFail := s.liveFail + 1 }
                                      cf' := cf' + 1
                                      if fresh && failDumps[ic]! < 10 then
                                        failDumps := failDumps.set! ic (failDumps[ic]! + 1)
                                        IO.println s!"  !!FAILURE [{(cis[ic]!).1}] (no answer at all — MforthResidue counterexample candidate):"
                                        dumpModel "K" K
                                        dumpModel "M" M
                                        IO.println s!"    M confluent: {mC}  Z stabilised at {stab}"
                                        IO.println s!"    k'={k'} k={k} kv={kv} κ={κ}  m'={m'} m={m} u={u}  d={d}  levels: (k',m')∈Z_{2*d+1} (k,m)∈Z_{2*d} (kv,u)∈Z_{2*d} (κ,u)∈Z_{2*d-1}"
                                        IO.println s!"    Δ = \{{maskFormulas ci.cl Δ}}  tr(kv) = \{{maskFormulas ci.cl Tv}}"
                                        IO.println s!"    growth: [{growthDecode ci gm d}]"
                                        IO.println s!"    RmC(Δ,tr(kv)): {anticB}"
                                        dumpTraces "K" ci K tk
                                        dumpTraces "M" ci M tm
                                        dumpZ zd nK
                                        IO.println s!"    Rm-row(u)={M.rmS[u]!} Ri-row(u)={M.riS[u]!} rigid-dead-end u: {(M.rmS[u]!).all (· == u)}"
                                    classTab := classTab.set! key (cc + 1, cf')
                                    stats := stats.set! ic s
      if iK % 100 == 0 then
        let t ← IO.monoMsNow
        IO.println s!"  [heartbeat] iK={iK}/{nMod} pairs={pairsDone} elapsed={t - t0}ms configs={(List.range cis.size).map fun ic => (stats[ic]!).configs} failures={(List.range cis.size).map fun ic => (stats[ic]!).failures}"
        (← IO.getStdout).flush
  let t1 ← IO.monoMsNow
  IO.println s!"=== monotonicity (Z_(n+1) ⊆ Z_n) violations: {monoViol} (expect 0) ==="
  IO.print "=== Z-chain stabilisation levels (level: pair count): "
  for l in List.range 40 do
    if stabHist[l]! > 0 then IO.print s!"{l}:{stabHist[l]!} "
  IO.println "==="
  IO.println "=== EMPIRICAL RANKEDNESS (p-free χ ∈ cl agree across Z_{crankC χ}) ==="
  for ic in List.range cis.size do
    let s := stats[ic]!
    IO.println s!"  {(cis[ic]!).1}: violations both-confluent={s.rankViolC} (expect 0) | M-non-confluent={s.rankViolN} (allowed: crankC transfer needs both confluent)"
  IO.println "=== b.ii CONFIGURATIONS AND THE CONCLUSION TEST ==="
  for ic in List.range cis.size do
    let s := stats[ic]!
    let f := funnels[ic]!
    IO.println s!"  {(cis[ic]!).1}:"
    IO.println s!"    funnel: ⊥∉Δ k'={f.gA} → +m'∈Z_2d+1={f.gB} → +k same-tr={f.gC} → +m∈Z_2d={f.gD} → +u∉F={f.gE} → +grown-kv cands={f.gF}"
    IO.println s!"    configs={s.configs} (M also confluent: {s.cfgMConf}) | RESOLVED={s.resolved} FAILURES={s.failures} | distinct (Δ,u) cells={s.cells} failing cells={s.cellFail}"
    IO.println s!"    LIVE window (2d−1 < stab, financed levels below the fixpoint): configs={s.cfgLive} failures={s.liveFail}"
    IO.println s!"    answer shapes: same-trace available={s.ansSame} grown available={s.ansGrown} | same-only={s.ansSameOnly} grown-only={s.ansGrownOnly} both={s.ansBoth} | first-witness self-reservoir={s.firstSelfRes}"
    IO.println s!"    growth anticipation: RmC(Δ,tr(kv))={s.antic}/{s.configs} | kv itself is an answer={s.kvSelf}"
    IO.println s!"    growth composition: pure-p={s.gPureP} mixed={s.gMixed} pure-protected={s.gPureProt}"
    IO.println s!"    protected growth members: total={s.protMem} | crankC ≤ 2d−1: both-confluent={s.protLEc} (BUG if >0) M-non-confluent={s.protLEn} | crankC ≥ 2d: {s.protHi}"
    IO.print s!"    growth member counts: "
    for i in List.range (cis[ic]!).2.cl.size do
      if gMem[ic * 8 + i]! > 0 then
        IO.print s!"{pf (cis[ic]!).2.cl[i]!}:{gMem[ic * 8 + i]!} "
    IO.println ""
    IO.print "    (d,stab) occupancy at configs: "
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
          if rows ≤ 50 then
            IO.println s!"    K-frame {fk} × M-frame {fm}: configs={cc} failures={cf}"
    if rows > 50 then IO.println s!"    … and {rows - 50} more rows"
    if rows == 0 then IO.println "    (no configs)"
  IO.println s!"=== pairs processed: {pairsDone} (K confluent × all M) ==="
  IO.println s!"=== done in {t1 - t0} ms ==="

end BiiPProbe

def main : IO Unit := BiiPProbe.mainLoop
