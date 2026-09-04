import LaxLogic.PLLSearch

/-!
# Probe: the ∀-residue DIRECTLY, by small-variant search

`BoxRowAmalgAll p φ ⊥` says: for every `(C, x)` whose m-row avoids the
fallible set, some p-variant of `C` kills `◯φ` over `x`.  For the gap
row `φ = ◯p⊃p` (and the discharged rows, as calibration) this probe
measures the residue itself on the battery:

* an instance is a pair `(frame, x)` with `row(x) ∩ F = ∅` — the
  p-decoration of `C` is irrelevant throughout: the p-blind
  bisimulation clauses never mention it, so one variant serves every
  decoration of the frame simultaneously;
* the variant family: the frame with `k ≤ 2` points adjoined above
  `x` (`x ≤ a ≤ b`), with chosen `Rᵢ`-exits into the cone of `x`,
  chosen `Rₘ`-exits (the sideways promises), and a free hereditary
  p-decoration of the WHOLE variant (`k = 0` = pure redecoration);
* legality is by construction (exits confined to the cone of `x`,
  `out(b) ⊆ out(a)`, no entries except from the down-set of `x`);
* the p-blind bisimulation is computed as a greatest fixpoint on
  `frame × variant` pairs (safety = matching fallibility; the four
  zigzag clauses); success needs `(x, x)` surviving AND
  `¬ force_N x ◯φ`.

`FAIL` = the whole family is exhausted at that instance — a lead
towards refuting the residue (or towards larger gadgets), to be
studied by hand.

Run compiled: `lake build residprobe && .lake/build/bin/residprobe`.
-/

open PLLFormula PLLND PLLND.Search

namespace ResidProbe

def pV : PLLFormula := .prop "p"
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

/-- The rows: (label, φ) with proved-or-conjectured ∀p-value ⊥, so the
row condition is `row(x) ∩ F = ∅`. -/
def rows : List (String × PLLFormula) :=
  [ ("A p      ", pV)
  , ("A p∨¬p   ", pV.or (nF pV))
  , ("A ¬¬p⊃p  ", (nF (nF pV)).ifThen pV)
  , ("A ◯p⊃p   ", pV.somehow.ifThen pV) ]   -- the gap row

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

/-- Transitive closure of a frame's relations (some battery frames —
the onebox forks — are not closed as listed; the `Frame` contract
assumes closure). -/
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

def allFrames : List Frame := (defaultFrames ++ extraFrames).map closeF

def memM (m i : Nat) : Bool := (m >>> i) &&& 1 == 1

/-! ## Variants as FinCMs -/

/-- Build the variant: `f` plus a CHAIN of `k ≤ 3` new points above
`x` (`x ≤ a ≤ b ≤ c`).  `outs[i]` are the base `Rᵢ`-exits of the i-th
new point (⊆ reflexive cone of `x`, nested downward for
transitivity); `ms[i] ⊆ outs[i]` its base `Rₘ`-exits; `mNew` three
bits for the in-chain `Rₘ`-edges (a→b, a→c, b→c); `pmask` the
p-decoration over `f.n + k` worlds. -/
def mkVariant (f : Frame) (x : Nat) (k : Nat) (outs ms : List Nat)
    (mNew pmask : Nat) : FinCM := Id.run do
  let n := f.n
  let mut ri := f.ri
  let mut rm := f.rm
  -- entries: from the reflexive down-set of x, to every new point
  for w in List.range n do
    if w == x || decide ((w, x) ∈ f.ri) then
      for i in List.range k do
        ri := ri ++ [(w, n + i)]
  -- the chain, and in-chain m-edges
  for i in List.range k do
    for j in List.range k do
      if i < j then
        ri := ri ++ [(n + i, n + j)]
  if k ≥ 2 && memM mNew 0 then rm := rm ++ [(n, n+1)]
  if k ≥ 3 && memM mNew 1 then rm := rm ++ [(n, n+2)]
  if k ≥ 3 && memM mNew 2 then rm := rm ++ [(n+1, n+2)]
  -- exits into the cone of x
  for i in List.range k do
    let o := outs.getD i 0
    let m := ms.getD i 0
    for y in List.range n do
      if memM o y then
        ri := ri ++ [(n + i, y)]
        if memM m y then rm := rm ++ [(n + i, y)]
  let val := ((List.range (n + k)).filter (fun w => memM pmask w)).map
    (fun w => (w, "p"))
  return ⟨n + k, ri, rm, f.fall, val⟩

/-- Reflexive cone of `x` as a mask (base worlds). -/
def coneM (f : Frame) (x : Nat) : Nat :=
  (List.range f.n).foldl (fun acc y =>
    if y == x || decide ((x, y) ∈ f.ri) then acc ||| (1 <<< y) else acc) 0

/-- Up-closed submasks of the cone (so exits keep transitivity). -/
def upClosedSubs (f : Frame) (x : Nat) : List Nat :=
  (List.range (1 <<< f.n)).filter fun m =>
    (m &&& coneM f x == m) &&
    ((List.range f.n).all fun y => !(memM m y) ||
      ((List.range f.n).all fun z => !(decide ((y, z) ∈ f.ri)) || memM m z))

/-- Hereditary p-masks of a FinCM (fallible worlds forced in). -/
def heredP (M : FinCM) : List Nat :=
  (List.range (1 <<< M.n)).filter fun m =>
    (M.fall.all fun w => memM m w) &&
    (M.ri.all fun e => !(memM m e.1) || memM m e.2)

/-! ## The p-blind bisimulation gfp -/

/-- Largest p-blind bisimulation between base `B` and variant `N`;
returns whether `(x, x)` survives.  Safety: matching fallibility (no
protected atoms in the 1-variable rows).  Clauses: the four zigzags. -/
def bisimOK (B N : FinCM) (x : Nat) : Bool := Id.run do
  let nb := B.n
  let nn := N.n
  let mut alive : Array Bool := Array.replicate (nb * nn) false
  for w in List.range nb do
    for w' in List.range nn do
      if B.fallB w == N.fallB w' then
        alive := alive.set! (w * nn + w') true
  let mut changed := true
  while changed do
    changed := false
    for w in List.range nb do
      for w' in List.range nn do
        if alive[w * nn + w']! then
          let ok := Id.run do
            -- iforth
            for v in List.range nb do
              if B.riB w v then
                if !((List.range nn).any fun v' =>
                    N.riB w' v' && alive[v * nn + v']!) then
                  return false
            -- iback
            for v' in List.range nn do
              if N.riB w' v' then
                if !((List.range nb).any fun v =>
                    B.riB w v && alive[v * nn + v']!) then
                  return false
            -- mforth
            for u in List.range nb do
              if B.rmB w u then
                if !((List.range nn).any fun u' =>
                    N.rmB w' u' && alive[u * nn + u']!) then
                  return false
            -- mback
            for u' in List.range nn do
              if N.rmB w' u' then
                if !((List.range nb).any fun u =>
                    B.rmB w u && alive[u * nn + u']!) then
                  return false
            return true
          if !ok then
            alive := alive.set! (w * nn + w') false
            changed := true
  return alive[x * nn + x]!

/-! ## The search -/

/-- A base FinCM for the frame with NO p (the bisimulation ignores p,
so any decoration gives the same verdict). -/
def baseCM (f : Frame) : FinCM := ⟨f.n, f.ri, f.rm, f.fall, []⟩

/-- Try one gadget shape over all hereditary p-decorations. -/
def tryShape (B : FinCM) (f : Frame) (x : Nat) (target : PLLFormula)
    (k : Nat) (outs ms : List Nat) (mNew : Nat) : Option String :=
  Id.run do
  let N0 := mkVariant f x k outs ms mNew 0
  for pm in heredP N0 do
    let N := mkVariant f x k outs ms mNew pm
    if !(N.forceB x target) && bisimOK B N x then
      return some s!"outs={outs} ms={ms} mNew={mNew} pmask={pm}"
  return none

/-- Search the variant family at `(f, x)` for a kill of `◯φ`.
Returns `some (k, description)` on success. -/
def search (f : Frame) (x : Nat) (φ : PLLFormula) : Option (Nat × String) :=
  Id.run do
  let B := baseCM f
  let target := φ.somehow
  -- k = 0: pure redecoration
  for pm in heredP B do
    let N : FinCM := ⟨f.n, f.ri, f.rm, f.fall,
      ((List.range f.n).filter (fun w => memM pm w)).map (fun w => (w, "p"))⟩
    if !(N.forceB x target) && bisimOK B N x then
      return some (0, s!"pmask={pm}")
  -- k = 1, 2: nested base exits
  for outA in upClosedSubs f x do
    for mA in List.range (1 <<< f.n) do
      if mA &&& outA == mA then
        if let some d := tryShape B f x target 1 [outA] [mA] 0 then
          return some (1, d)
  for outA in upClosedSubs f x do
    for mA in List.range (1 <<< f.n) do
      if mA &&& outA == mA then
        for outB in (upClosedSubs f x).filter (fun m => m &&& outA == m) do
          for mB in (List.range (1 <<< f.n)).filter (fun m => m &&& outB == m) do
            for mNew in [0, 1] do
              if let some d := tryShape B f x target 2 [outA, outB] [mA, mB] mNew then
                return some (2, d)
  -- k = 3: nested exits (outC ⊆ outB ⊆ outA), base m-exits on `a` only
  for outA in upClosedSubs f x do
    for outB in (upClosedSubs f x).filter (fun m => m &&& outA == m) do
      for outC in (upClosedSubs f x).filter (fun m => m &&& outB == m) do
        for mA in (List.range (1 <<< f.n)).filter (fun m => m &&& outA == m) do
          for mNew in List.range 8 do
            if let some d := tryShape B f x target 3 [outA, outB, outC]
                [mA, 0, 0] mNew then
              return some (3, d)
  return none

def runRow (label : String) (φ : PLLFormula) (verbose : Bool := false) :
    IO Unit := do
  let t0 ← IO.monoMsNow
  let mut pts := 0
  let mut ok0 := 0
  let mut ok1 := 0
  let mut ok2 := 0
  let mut ok3 := 0
  let mut fails := 0
  for f in allFrames do
    for x in List.range f.n do
      let B := baseCM f
      -- row condition: the m-row of x avoids F
      let qual := (List.range f.n).all fun u => !(B.rmB x u) || !(B.fallB u)
      if qual then
        pts := pts + 1
        match search f x φ with
        | some (k, d) =>
            if k == 0 then ok0 := ok0 + 1
            else if k == 1 then ok1 := ok1 + 1
            else if k == 2 then ok2 := ok2 + 1
            else ok3 := ok3 + 1
            if verbose then
              IO.println s!"  k{k} n={f.n} ri={f.ri} rm={f.rm} fall={f.fall} x={x}: {d}"
        | none =>
            fails := fails + 1
            IO.println s!"  !!FAIL {label}: n={f.n} ri={f.ri} rm={f.rm} fall={f.fall} x={x}"
  let t1 ← IO.monoMsNow
  IO.println s!"row {label}: pts={pts} k0={ok0} k1={ok1} k2={ok2} k3={ok3} FAIL={fails} ({t1-t0} ms)"

def mainLoop : IO Unit := do
  IO.println "=== direct ∀-residue probe (variant search) ==="
  for (label, φ) in rows do
    runRow label φ (verbose := label == "A ◯p⊃p   ")
  IO.println "=== done ==="

end ResidProbe

def main : IO Unit := ResidProbe.mainLoop
