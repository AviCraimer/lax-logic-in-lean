import LaxLogic.PLLSearch

/-!
# Probe: is forth-m derivable from fragment-agreement?

The one open clause of the pillar-2 redesign (route doc §0(ff)):
given two pointed models agreeing on all variable-free formulas up to
some rank, and a non-fallible Rₘ-successor u of the first point, must
the second point's row contain a successor agreeing with u (or a
fallible escape)?

Probe: battery frames (transitively closed), no atom decoration (the
variable-free question), a systematically generated formula list to
modal/implication depth ~4; for every pair of pointed models agreeing
on the WHOLE list, test forth-m with successor-agreement on the same
list.  Since the genuine clause grades the successor agreement at a
LOWER rank, a violation here is a fortiori a counterexample
candidate; a clean pass is supporting (not conclusive) evidence.

Run: `lake build mforthprobe && .lake/build/bin/mforthprobe`.
-/

open PLLFormula PLLND PLLND.Search

namespace MForthProbe

def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

/-- Systematic variable-free formulas: close {⊥} under ◯, ¬ and a
capped set of implications/disjunctions, three rounds. -/
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
   -- the F-free 3-chain with rigid bottom (the battery-gap find)
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

/-- Deterministic pseudo-random frames (LCG): random Rᵢ-edges closed
transitively, a random Rₘ-subset of them closed transitively (stays
inside the closed Rᵢ), a random up-closed fallible set. -/
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
  -- close fall upward along riC
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

/-- Truth fingerprint of a pointed model on the formula list. -/
def finger (M : FinCM) (w : Nat) : List Bool :=
  formulas.map fun φ => M.forceB w φ

def mainLoop : IO Unit := do
  IO.println s!"=== forth-m from agreement probe: {formulas.length} formulas, {allCMs.length} frames ==="
  let mut pairs := 0
  let mut cands := 0
  let mut fcands := 0
  -- precompute fingerprints once per point
  let pts := allCMs.flatMap fun M =>
    (List.range M.n).map fun w => (M, w, finger M w)
  for (M, w, fw) in pts do
    for (N, w', fw') in pts do
      if fw == fw' then
        pairs := pairs + 1
        for u in List.range M.n do
          if M.rmB w u && !M.fallB u then
            -- forth-m at a NON-fallible row-member: agreeing partner?
            let fu := finger M u
            let ok := (List.range N.n).any fun s =>
              N.rmB w' s && finger N s == fu
            if !ok then
              cands := cands + 1
              IO.println s!"  !!CANDIDATE: M=(n={M.n} ri={M.ri} rm={M.rm} fall={M.fall}) w={w} u={u}  vs  N=(n={N.n} ri={N.ri} rm={N.rm} fall={N.fall}) w'={w'}"
          if M.rmB w u && M.fallB u then
            -- the PAIR escape: does the other row even contain a
            -- fallible member?
            let ok := (List.range N.n).any fun s =>
              N.rmB w' s && N.fallB s
            if !ok then
              fcands := fcands + 1
              if fcands ≤ 5 then
                IO.println s!"  !!FALLIBLE-PAIR FAILS: M=(n={M.n} ri={M.ri} rm={M.rm} fall={M.fall}) w={w} u={u}  vs  N=(n={N.n} ri={N.ri} rm={N.rm} fall={N.fall}) w'={w'}"
  IO.println s!"=== agreeing pairs={pairs} forth-m candidates={cands} fallible-pair failures={fcands} ==="

end MForthProbe

def main : IO Unit := MForthProbe.mainLoop
