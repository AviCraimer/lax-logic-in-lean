import LaxLogic.PLLG4Dec

/-!
# Lattice comparison: RN(◯,{}) vs RN({p})

Scratch computation (not part of the library).  Decide, via the G4c
proof-search oracle `PLLND.search`, whether the closed lax fragment
`RN(◯,{})` (formulas over `⊥` with `∧ ∨ ⊃ ◯`, no atoms) is isomorphic as a
Heyting algebra to `RN({p})`, the free Heyting algebra on one generator
(formulas over one atom `p` and `⊥` with `∧ ∨ ⊃`, no `◯`) — both truncated
to formulas of weight ≤ N, for increasing N.

Method: enumerate formulas of each fragment by exact Dyckhoff weight
(memoized table, bottom-up), then INCREMENTALLY dedup by oracle-checked
equivalence (`entails` both ways) to get the count of equivalence classes
= size of the truncated lattice.  Then test whether `On := ◯(¬◯⊥)` is
equivalent to any G-class, and whether anything sits strictly between
`p∨¬p` and `¬¬p⊃p` in G (mirroring the known strict L-side gap around
`On`).
-/

open PLLFormula PLLND

/-! ## The oracle -/

/-- Fuel for the search oracle — ample for the small formulas here. -/
def FUEL : Nat := 3000

/-- `provF fuel Γ C` — does G4c derive `Γ ⊢ C`, searched with an explicit
fuel budget?  Kernel-sound via `search_sound` in EITHER direction: `true`
is unconditionally a genuine derivation.  `false` only means "not found
within this fuel" — the mechanised completeness theorem needs fuel up to
the astronomical `decideFuel` pigeonhole bound to be UNCONDITIONALLY safe,
which is far more than we use.  We rely instead on the empirical fact
(confirmed below by rerunning the crux checks at ~7x fuel) that actual
derivation heights for formulas this small are nowhere near that ceiling. -/
def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

def entailsF (fuel : Nat) (X Y : PLLFormula) : Bool := provF fuel [X] Y
def equivF (fuel : Nat) (X Y : PLLFormula) : Bool := entailsF fuel X Y && entailsF fuel Y X

/-- `prov Γ C` at the main working fuel. -/
def prov (Γ : List PLLFormula) (C : PLLFormula) : Bool := provF FUEL Γ C

/-- `X ⊢ Y`, i.e. `[X] ⊢ Y` — the Lindenbaum order `X ≤ Y`. -/
def entails (X Y : PLLFormula) : Bool := prov [X] Y

/-- Oracle-checked Heyting-algebra equivalence `X ≡ Y` (`X ≤ Y ≤ X`). -/
def equiv (X Y : PLLFormula) : Bool := entails X Y && entails Y X

/-- Readable pretty-printer (reuses the library's symbol choice). -/
def pf (F : PLLFormula) : String := F.toString

/-! ## Sanity checks against the known `PLLG4Dec` demos -/

#eval prov [] (PLLFormula.falsePLL.ifThen PLLFormula.falsePLL)   -- expect true
#eval prov [] (PLLFormula.prop "p")                               -- expect false
#eval prov [(PLLFormula.prop "p")] (PLLFormula.prop "p").somehow  -- expect true
#eval prov [(PLLFormula.prop "p").somehow] (PLLFormula.prop "p")  -- expect false

/-! ## Distinguished formulas -/

def p : PLLFormula := PLLFormula.prop "p"
def negp : PLLFormula := p.ifThen PLLFormula.falsePLL
def negnegp : PLLFormula := negp.ifThen PLLFormula.falsePLL
def loG : PLLFormula := p.or negp          -- p ∨ ¬p
def hiG : PLLFormula := negnegp.ifThen p   -- ¬¬p ⊃ p

def g : PLLFormula := PLLFormula.falsePLL.somehow   -- ◯⊥
def negg : PLLFormula := g.ifThen PLLFormula.falsePLL
def negnegg : PLLFormula := negg.ifThen PLLFormula.falsePLL
def On : PLLFormula := negg.somehow                 -- ◯(¬◯⊥)
def loL : PLLFormula := negg.or g          -- ¬g ∨ g
def hiL : PLLFormula := negnegg.ifThen g   -- ¬¬g ⊃ g

#eval s!"p={pf p}  loG={pf loG}  hiG={pf hiG}"
#eval s!"g={pf g}  On={pf On}  loL={pf loL}  hiL={pf hiL}"

/-! ## Formula generation, memoized by exact weight

`buildTable leaves useSomehow maxW` returns an array indexed `0..maxW`,
where index `w` holds every formula of *exactly* weight `w` (Dyckhoff
weight, `and = +2`, `or/ifThen = +1`, `somehow = +1`, leaves `= 1`), built
bottom-up from `leaves` using previously-computed lower entries — so no
formula is regenerated, unlike naively unfolding `PLLND.enum` (which
re-derives its own argument several times per level with no memoization
and would blow up combinatorially). -/
def buildTable (leaves : List PLLFormula) (useSomehow : Bool) (maxW : Nat) :
    Array (List PLLFormula) := Id.run do
  let mut tbl : Array (List PLLFormula) := #[[]]
  for n in List.range maxW do
    let w := n + 1
    let mut acc : List PLLFormula := []
    if w = 1 then
      acc := leaves
    else
      -- and : weight A + weight B + 2 = w
      for i in List.range (w - 1) do
        let a := i
        let b := w - 2 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < tbl.size ∧ b < tbl.size then
          for x in tbl[a]! do
            for y in tbl[b]! do
              acc := (x.and y) :: acc
      -- or, ifThen : weight A + weight B + 1 = w
      for i in List.range w do
        let a := i
        let b := w - 1 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < tbl.size ∧ b < tbl.size then
          for x in tbl[a]! do
            for y in tbl[b]! do
              acc := (x.or y) :: acc
              acc := (x.ifThen y) :: acc
      -- somehow : weight A + 1 = w
      if useSomehow ∧ w ≥ 2 ∧ w - 1 < tbl.size then
        for x in tbl[w-1]! do
          acc := x.somehow :: acc
    tbl := tbl.push acc
  return tbl

/-! ## Incremental semantic dedup -/

/-- Add `φ` to `reps` unless it is `equiv` to something already there. -/
def addRep (reps : List PLLFormula) (φ : PLLFormula) : List PLLFormula :=
  if reps.any (fun ψ => equiv φ ψ) then reps else φ :: reps

/-- Run incremental dedup over weight-levels `1..maxW`, printing per-level
and checkpoint stats.  Returns the final representative list (one formula
per equivalence class reached by weight `maxW`). -/
def dedupReport (label : String) (tbl : Array (List PLLFormula)) (maxW : Nat)
    (checkpoints : List Nat) : IO (List PLLFormula) := do
  let mut reps : List PLLFormula := []
  let mut raw : Nat := 0
  IO.println s!"-- {label} --"
  for n in List.range maxW do
    let w := n + 1
    let level := tbl[w]!
    let t0 ← IO.monoMsNow
    for φ in level do
      raw := raw + 1
      reps := addRep reps φ
    let t1 ← IO.monoMsNow
    IO.println
      s!"  weight {w}: level raw={level.length}  cumulative raw={raw}  \
classes so far={reps.length}  ({t1 - t0} ms)"
    if checkpoints.contains w then
      IO.println s!"  >>> CHECKPOINT N={w}: raw={raw}  classes={reps.length}"
  return reps

/-! ## Part 2 / Part 3 helpers -/

def findEquivClass (reps : List PLLFormula) (φ : PLLFormula) : Option PLLFormula :=
  reps.find? (fun ψ => equiv φ ψ)

/-- `X` with `lo < X < hi` strictly (Lindenbaum order via `entails`). -/
def intervalWitnesses (reps : List PLLFormula) (lo hi : PLLFormula) : List PLLFormula :=
  reps.filter (fun x =>
    entails lo x && !(equiv lo x) && entails x hi && !(equiv x hi))

/-! ## Main driver -/

def maxW : Nat := 8
def checkpoints : List Nat := [4, 5, 6, 7, 8]

def main : IO Unit := do
  let startTime ← IO.monoMsNow

  let tblG := buildTable [p, PLLFormula.falsePLL] false maxW
  let repsG ← dedupReport
    s!"Fragment G = RN(p)  (and/or/implies, atom p, bot, NO diamond) up to weight {maxW}"
    tblG maxW checkpoints

  let tblL := buildTable [PLLFormula.falsePLL] true maxW
  let repsL ← dedupReport
    s!"Fragment L = RN(diamond, no atoms)  (and/or/implies/diamond, bot only) up to weight {maxW}"
    tblL maxW checkpoints

  IO.println ""
  IO.println "== Part 2: is On = O(not O bot) expressible in fragment G? =="
  match findEquivClass repsG On with
  | some ψ =>
      IO.println s!"YES: On == {pf ψ}  (found among G's {repsG.length} classes at N={maxW})"
  | none =>
      IO.println s!"NO: On is not equiv to any of G's {repsG.length} classes at N={maxW}"

  IO.println ""
  IO.println "== Part 3: gap between p-or-notp and notnotp-implies-p in fragment G =="
  IO.println s!"  entails loG hiG = {entails loG hiG}  (sanity: expect true)"
  IO.println s!"  equiv  loG hiG = {equiv loG hiG}  (sanity: expect false)"
  let witnesses := intervalWitnesses repsG loG hiG
  if witnesses.isEmpty then
    IO.println "  NO witness: nothing strictly between p-or-notp and notnotp-implies-p among G's classes."
  else
    IO.println s!"  WITNESS(ES): {witnesses.map pf}"

  IO.println ""
  IO.println "== Part 3b: replay the cited L-side facts (sanity check) =="
  IO.println s!"  entails loL On = {entails loL On},  equiv loL On = {equiv loL On}"
  IO.println s!"  entails On hiL = {entails On hiL},  equiv On hiL = {equiv On hiL}"

  IO.println ""
  IO.println "== Part 3c (bonus): L-side interval witnesses, cross-check =="
  let witnessesL := intervalWitnesses repsL loL hiL
  IO.println s!"  L witnesses strictly between loL and hiL (among L's {repsL.length} classes): \
{witnessesL.map pf}"
  match findEquivClass repsL On with
  | some ψ =>
      IO.println s!"  On's class IS represented in L's list by: {pf ψ}"
  | none =>
      IO.println s!"  On's class has no representative in L's list up to weight {maxW}"

  IO.println ""
  IO.println "== Robustness recheck: crux NO-findings replayed at ~7x fuel (20000) =="
  let hiFuel : Nat := 20000
  let onRecheck := repsG.map (fun ψ => (pf ψ, equivF hiFuel On ψ))
  IO.println s!"  On vs each G-class @ fuel={hiFuel} (all should stay false): {onRecheck}"
  let gapRecheck := repsG.map (fun x =>
    (pf x,
     entailsF hiFuel loG x && !(equivF hiFuel loG x)
       && entailsF hiFuel x hiG && !(equivF hiFuel x hiG)))
  IO.println s!"  strictly-between(loG,hiG) vs each G-class @ fuel={hiFuel} (all should stay false): \
{gapRecheck}"

  let endTime ← IO.monoMsNow
  IO.println ""
  IO.println s!"TOTAL RUNTIME: {endTime - startTime} ms"

#eval main
