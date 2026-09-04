import LaxLogic.PLLSearch

/-!
# Probe: the same-trace no-descent clause

The open case of the amalgamation ◯-induction (PLLSemUIHenkin design
ledger; route doc §0(hh)): when a world `v` above `k` along `Rᵢ` has
the SAME closure-description as `k`, the amalgam needs an
`Rᵢ`-successor of `k`'s rank-`n` partner `m` agreeing with `v` at the
SAME rank `n` — the proved clause `agree_iforth` descends to `n − 1`,
one level short exactly there.

CONJECTURE (same-trace no-descent): if `k` and `m` agree on all
p-free formulas of crank ≤ n, and `Rᵢ k v` with `v`, `k` forcing the
same members of a subformula-closed set `cl`, then some `m₂` with
`Rᵢ m m₂` agrees with `v` on all p-free formulas of crank ≤ n.

Surrogate (same discipline as `wip/mforth_probe.lean`): agreement =
fingerprint equality on a systematic variable-free formula list `L`
(90 formulas, depth ~4); closure-description equality = fingerprint
equality on a small subformula-closed `cl ⊆ L`; the rank-grading is
dropped (list agreement on both sides).  A violation is a candidate
counterexample (its ranks would need checking); a clean pass is
supporting, not conclusive, evidence.  Cases with `v` fully
`L`-equivalent to `k` are trivial (`m₂ := m` by transitivity) and
counted separately — the interesting cases are `cl`-equal but
`L`-distinct.

Run: `lake build samvalprobe && .lake/build/bin/samvalprobe`.
-/

open PLLFormula PLLND PLLND.Search

namespace SamValProbe

def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

/-- Systematic variable-free formulas (as in `mforth_probe`). -/
def genF : Nat → List PLLFormula
  | 0 => [.falsePLL]
  | n + 1 => Id.run do
      let prev := genF n
      let mut out := prev
      for φ in prev do
        for ψ in [φ.somehow, nF φ] do
          if !(out.contains ψ) then out := out ++ [ψ]
      for φ in prev.take 8 do
        for χ in prev.take 8 do
          for ψ in [φ.ifThen χ, φ.or χ] do
            if !(out.contains ψ) then out := out ++ [ψ]
      return out.take 90

def formulas : List PLLFormula := genF 3

/-- The subformula-closed closures probed (variable-free shapes of the
adequate sets in play).  Smaller closure = weaker same-trace
hypothesis = stronger clause. -/
def closures : List (String × List PLLFormula) :=
  [("cl=[⊥]", [.falsePLL]),
   ("cl=[⊥,◯⊥]", [.falsePLL, PLLFormula.somehow .falsePLL]),
   ("cl=[⊥,◯⊥,¬◯⊥]",
    [.falsePLL, PLLFormula.somehow .falsePLL,
     nF (PLLFormula.somehow .falsePLL)])]

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

def randFrames : List Frame :=
  (List.range 240).map fun k => randFrame (k * 7919 + 13) (4 + k % 3)

def allCMs : List FinCM :=
  (((defaultFrames ++ extraFrames).map closeF) ++ randFrames).map fun f =>
    ⟨f.n, f.ri, f.rm, f.fall, []⟩

/-! ### Phase 2: one-atom decorations (the gap-row closure has `p`) -/

/-- Systematic formulas over the single atom `q`. -/
def genFA : Nat → List PLLFormula
  | 0 => [.falsePLL, .prop "q"]
  | n + 1 => Id.run do
      let prev := genFA n
      let mut out := prev
      for φ in prev do
        for ψ in [φ.somehow, nF φ] do
          if !(out.contains ψ) then out := out ++ [ψ]
      for φ in prev.take 8 do
        for χ in prev.take 8 do
          for ψ in [φ.ifThen χ, φ.or χ] do
            if !(out.contains ψ) then out := out ++ [ψ]
      return out.take 70

def formulasA : List PLLFormula := genFA 3

/-- One-atom closures, up to the gap row's own adequate set. -/
def closuresA : List (String × List PLLFormula) :=
  [("cl=[⊥,q]", [.falsePLL, .prop "q"]),
   ("cl=[⊥,q,◯q]",
    [.falsePLL, .prop "q", PLLFormula.somehow (.prop "q")]),
   ("cl=Sub(◯q⊃q)+⊥",
    [.falsePLL, .prop "q", PLLFormula.somehow (.prop "q"),
     (PLLFormula.somehow (.prop "q")).ifThen (.prop "q")])]

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

def allCMsA : List FinCM :=
  ((((defaultFrames ++ extraFrames).map closeF) ++ randFrames.take 40).flatMap
    fun f => (upSets f).map fun S =>
      (⟨f.n, f.ri, f.rm, f.fall, S.map fun w => (w, "q")⟩ : FinCM))

/-! ### The generic pass -/

/-- Truth fingerprint of a point on a formula list. -/
def fingerOn (L : List PLLFormula) (M : FinCM) (w : Nat) : List Bool :=
  L.map fun φ => M.forceB w φ

/-- One probe pass: formula list `L`, closure family `cls`, models. -/
def runPass (label : String) (L : List PLLFormula)
    (cls : List (String × List PLLFormula)) (cms : List FinCM) :
    IO Unit := do
  IO.println s!"=== {label}: {L.length} formulas, {cms.length} models, {cls.length} closures ==="
  let tabs := cms.map fun M =>
    (M, (List.range M.n).map (fingerOn L M),
      cls.map fun c => (List.range M.n).map (fingerOn c.2 M))
  let pts := tabs.flatMap fun (M, fs, cfs) =>
    (List.range M.n).map fun w => (M, fs, cfs, w)
  let mut pairs := 0
  let mut trivial := 0
  let mut needed : Array Nat := Array.replicate cls.length 0
  let mut fails : Array Nat := Array.replicate cls.length 0
  for (M, fsM, cfsM, w) in pts do
    let fw := fsM.getD w []
    for (N, fsN, _, w') in pts do
      if fw == fsN.getD w' [] then
        pairs := pairs + 1
        for v in List.range M.n do
          if M.riB w v && v != w then
            let fv := fsM.getD v []
            if fv == fw then
              trivial := trivial + 1
            else
              for i in List.range cls.length do
                let cfM := cfsM.getD i []
                if cfM.getD v [] == cfM.getD w [] then
                  needed := needed.set! i (needed[i]! + 1)
                  let ok := (List.range N.n).any fun s =>
                    N.riB w' s && fsN.getD s [] == fv
                  if !ok then
                    fails := fails.set! i (fails[i]! + 1)
                    if fails[i]! ≤ 4 then
                      let nm := (cls.getD i ("?", [])).1
                      IO.println s!"  !!FAIL[{nm}]: M=(n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} val={M.val}) w={w} v={v}  vs  N=(n={N.n} ri={N.ri} rm={N.rm} fall={N.fall} val={N.val}) w'={w'}"
  IO.println s!"=== {label}: agreeing pairs={pairs} trivial i-moves={trivial} ==="
  for i in List.range cls.length do
    let nm := (cls.getD i ("?", [])).1
    IO.println s!"=== {label} {nm}: needed={needed[i]!} FAILURES={fails[i]!} ==="

def mainLoop : IO Unit := do
  runPass "variable-free" formulas closures allCMs
  runPass "one-atom" formulasA closuresA allCMsA

end SamValProbe

def main : IO Unit := SamValProbe.mainLoop
