import LaxLogic.PLLG4Dec

/-!
# Probe: the one-variable quantifier value table

For every one-variable formula `M` (atoms ⊆ {p}) up to a weight cap,
compute — via the G4c search oracle, sound on `true` — the CANDIDATE
values of the two bisimulation quantifiers, and search for the
certificates that the criteria of `LaxLogic/PLLSemUI.lean` turn into Lean
proofs:

* candidate ∀p-value  = the maximum of { closed ξ : ξ ⊢ M }  (Pitts'
  universal property forces the value there if it exists and is closed);
* candidate ∃p-value  = the minimum of { closed ξ : M ⊢ ξ };
* ∀-certificate: a finite family χ₁…χₖ with  M[p:=χ₁],…,M[p:=χₖ] ⊢ candA
  (then `isSemAll_of_certificates` proves `IsSemAll p M candA`);
* ∃-certificate: a single χ with  candE ⊢ M[p:=χ]
  (then `isSemEx_of_certificates` proves `IsSemEx p M candE`);
* essentiality: inessential if M ≡ some closed ξ (witness printed);
  else certified essential if two substitution instances separate
  (`essential_of_separation`); else UNKNOWN.

Certificate-less rows are the SURGERY FRONTIER: values (like
∀p.(p∨¬p) = ⊥, proved by the doubling) needing frame-changing variants.

Run with  `lake env lean --run wip/semui_probe.lean`  (never `#eval`:
IO buffers until completion).
-/

open PLLFormula PLLND

namespace SemUIProbe

/-! ## Oracle (as in `wip/lattice_cmp.lean`) -/

def FUEL : Nat := 500

def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

def prov (Γ : List PLLFormula) (C : PLLFormula) : Bool := provF FUEL Γ C

def entails (X Y : PLLFormula) : Bool := prov [X] Y

def equivO (X Y : PLLFormula) : Bool := entails X Y && entails Y X

def pf (F : PLLFormula) : String := F.toString

/-! ## Substitution (mirror of `SemUI.substP`) -/

def substP (p : String) (χ : PLLFormula) : PLLFormula → PLLFormula
  | .prop a     => if a = p then χ else .prop a
  | .falsePLL   => .falsePLL
  | .and A B    => .and (substP p χ A) (substP p χ B)
  | .or A B     => .or (substP p χ A) (substP p χ B)
  | .ifThen A B => .ifThen (substP p χ A) (substP p χ B)
  | .somehow A  => .somehow (substP p χ A)

/-! ## Formula generation (memoized by exact Dyckhoff weight) -/

def buildTable (leaves : List PLLFormula) (useSomehow : Bool) (maxW : Nat) :
    Array (List PLLFormula) := Id.run do
  let mut tbl : Array (List PLLFormula) := #[[]]
  for n in List.range maxW do
    let w := n + 1
    let mut acc : List PLLFormula := []
    if w = 1 then
      acc := leaves
    else
      for i in List.range (w - 1) do
        let a := i
        let b := w - 2 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < tbl.size ∧ b < tbl.size then
          for x in tbl[a]! do
            for y in tbl[b]! do
              acc := (x.and y) :: acc
      for i in List.range w do
        let a := i
        let b := w - 1 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < tbl.size ∧ b < tbl.size then
          for x in tbl[a]! do
            for y in tbl[b]! do
              acc := (x.or y) :: acc
              acc := (x.ifThen y) :: acc
      if useSomehow ∧ w ≥ 2 ∧ w - 1 < tbl.size then
        for x in tbl[w-1]! do
          acc := x.somehow :: acc
    tbl := tbl.push acc
  return tbl

def addRep (reps : List PLLFormula) (φ : PLLFormula) : List PLLFormula :=
  if reps.any (fun ψ => equivO φ ψ) then reps else φ :: reps

/-! ## Lattice helpers (Lindenbaum order via `entails`) -/

/-- Maximal elements: no strictly larger companion in the list. -/
def maximals (xs : List PLLFormula) : List PLLFormula :=
  xs.filter (fun x => xs.all (fun y => !(entails x y) || entails y x))

/-- Minimal elements. -/
def minimals (xs : List PLLFormula) : List PLLFormula :=
  xs.filter (fun x => xs.all (fun y => !(entails y x) || entails x y))

def orAll : List PLLFormula → PLLFormula
  | [] => .falsePLL
  | [x] => x
  | x :: xs => x.or (orAll xs)

def andAll : List PLLFormula → PLLFormula
  | [] => truePLL
  | [x] => x
  | x :: xs => x.and (andAll xs)

def pairsOf (xs : List PLLFormula) : List (PLLFormula × PLLFormula) :=
  xs.flatMap (fun a => xs.filterMap (fun b => some (a, b)))

/-! ## Certificate search -/

/-- The lower transform (mirror of `SemUI.lowT`): forcing of `M` at the
generic lower point of the decorated double. -/
def lowT (p : String) : PLLFormula → PLLFormula
  | .prop a     => if a = p then .falsePLL else .prop a
  | .falsePLL   => .falsePLL
  | .and A B    => (lowT p A).and (lowT p B)
  | .or A B     => (lowT p A).or (lowT p B)
  | .ifThen A B => ((lowT p A).ifThen (lowT p B)).and
      ((substP p truePLL A).ifThen (substP p truePLL B))
  | .somehow A  => (substP p truePLL A).somehow

/-- The level-0 transform of the sideways-witness (Löb) model:
`sideT(◯A) = ◯(sideT A) ∧ ◯(A[⊤])`, implication collects all levels. -/
def sideT (p : String) : PLLFormula → PLLFormula
  | .prop a     => if a = p then .falsePLL else .prop a
  | .falsePLL   => .falsePLL
  | .and A B    => (sideT p A).and (sideT p B)
  | .or A B     => (sideT p A).or (sideT p B)
  | .ifThen A B => ((sideT p A).ifThen (sideT p B)).and (lowT p (A.ifThen B))
  | .somehow A  => ((sideT p A).somehow).and ((substP p truePLL A).somehow)

/-- Reduced fuel for the *failing* certificate probes (the successful
certificates we mechanise are re-checked at full fuel anyway). -/
def CFUEL : Nat := 200

def provC (Γ : List PLLFormula) (C : PLLFormula) : Bool := provF CFUEL Γ C

/-- Pair searches are the expensive tail; off for the fast sweep. -/
def TRY_PAIRS : Bool := false

/-- Tiny fuel for the big-but-shallow sideT attempts: failing searches
at weight ~40 are pathologically slow, succeeding ones are instant. -/
def SFUEL : Nat := 60

/-- Skip failing-prone oracle calls on oversized sequents: per-iteration
search cost grows steeply with total weight. -/
def WCAP : Nat := 13

/-- Combination premises restricted to the safe low chain: failing
searches against ¬◯⊥-instance combos have chaotic (non-monotone-in-
fuel) cost. -/
def comboPool : List PLLFormula :=
  [.falsePLL, PLLFormula.falsePLL.somehow, truePLL]

/-- ∀-side: substitution singletons (full fuel), then the lower
transform alone / with a single, then substitution pairs, then
lowT + pair (reduced fuel). -/
def certAllX (p : String) (M ψ : PLLFormula) (pool poolSmall : List PLLFormula) :
    String :=
  match pool.find? (fun χ =>
      let i := substP p χ M
      i.weight + ψ.weight ≤ WCAP && provC [i] ψ) with
  | some χ => s!"CERT-SUBST[{pf χ}]"
  | none =>
  let lw := lowT p M
  let sw := sideT p M
  if lw.weight > 20 then "LOW-SKIPPED(weight)"
  else if provC [lw] ψ then "CERT-LOW[]"
  else if sw.weight ≤ 100 && provF SFUEL [sw] ψ then "CERT-SIDE[]"
  else match comboPool.find? (fun χ =>
      let i := substP p χ M
      i.weight ≤ WCAP && provC [lw, i] ψ) with
  | some χ => s!"CERT-LOW[{pf χ}]"
  | none =>
  match comboPool.find? (fun χ =>
      let i := substP p χ M
      sw.weight ≤ 100 && i.weight ≤ WCAP && provF SFUEL [sw, i] ψ) with
  | some χ => s!"CERT-SIDE[{pf χ}]"
  | none =>
  if !TRY_PAIRS then "NO-CERT(singles+low+side)"
  else match (pairsOf poolSmall).find?
      (fun ab => provC [substP p ab.1 M, substP p ab.2 M] ψ) with
  | some ab => s!"CERT-SUBST[{pf ab.1}, {pf ab.2}]"
  | none =>
  match (pairsOf poolSmall).find?
      (fun ab => provC [lw, substP p ab.1 M, substP p ab.2 M] ψ) with
  | some ab => s!"CERT-LOW[{pf ab.1}, {pf ab.2}]"
  | none => "NO-CERT"

/-- ∃-side: a single substitution instance, then the lower transform. -/
def certExX (p : String) (M ψ : PLLFormula) (pool : List PLLFormula) :
    String :=
  match pool.find? (fun χ =>
      let i := substP p χ M
      i.weight + ψ.weight ≤ WCAP && provC [ψ] i) with
  | some χ => s!"CERT-SUBST[{pf χ}]"
  | none =>
  let lw := lowT p M
  if lw.weight > 20 then "LOW-SKIPPED(weight)"
  else if provC [ψ] lw then "CERT-LOW"
  else
  let sw := sideT p M
  if sw.weight > 100 then "NO-CERT(side-skipped)"
  else if provF SFUEL [ψ] sw then "CERT-SIDE"
  else "NO-CERT"

/-- Essentiality by separation of two instances. -/
def equivC (X Y : PLLFormula) : Bool := provC [X] Y && provC [Y] X

def sepWitness (p : String) (M : PLLFormula) (pool : List PLLFormula) :
    Option (PLLFormula × PLLFormula) :=
  (pairsOf pool).find?
    (fun ab =>
      let i₁ := substP p ab.1 M
      let i₂ := substP p ab.2 M
      i₁.weight + i₂.weight ≤ 20 && !(equivC i₁ i₂))

/-! ## Main driver -/

def LADDER_W : Nat := 8
def MPOOL_W : Nat := 5

def pVar : PLLFormula := .prop "p"
def negF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL
def gBot : PLLFormula := PLLFormula.falsePLL.somehow

/-- Interesting one-variable formulas beyond the weight cap. -/
def extras : List PLLFormula :=
  [ (negF (negF pVar)).ifThen pVar                  -- ¬¬p ⊃ p
  , negF (negF pVar)                                -- ¬¬p
  , (pVar.or (negF pVar)).somehow                   -- ◯(p ∨ ¬p)
  , gBot.or pVar                                    -- ◯⊥ ∨ p
  , (negF gBot).or pVar                             -- ¬◯⊥ ∨ p
  , (negF gBot).somehow.or pVar                     -- ◯¬◯⊥ ∨ p
  , (pVar.somehow).ifThen gBot                      -- ◯p ⊃ ◯⊥
  , ((pVar.somehow).ifThen pVar).somehow            -- ◯(◯p ⊃ p)
  , (negF (pVar.somehow)).or (pVar.somehow)         -- ¬◯p ∨ ◯p
  ]

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== semantic-UI 1-pv value-table probe =="
  pl s!"oracle fuel {FUEL}; ladder weight ≤ {LADDER_W}; M weight ≤ {MPOOL_W}"

  -- closed ladder
  let ladderTbl := buildTable [.falsePLL] true LADDER_W
  let mut ladder : List PLLFormula := []
  for n in List.range LADDER_W do
    let w := n + 1
    let t0 ← IO.monoMsNow
    for φ in ladderTbl[w]! do
      ladder := addRep ladder φ
    let t1 ← IO.monoMsNow
    pl s!"ladder weight {w}: raw level={ (ladderTbl[w]!).length }  classes so far={ladder.length}  ({t1 - t0} ms)"
  let ladderL := ladder.reverse   -- lowest weight first
  pl s!"closed ladder classes (≤ w{LADDER_W}): {ladderL.length}"
  for ξ in ladderL do
    pl s!"  ladder rep: {pf ξ}"

  -- substitution pool: closed reps of low weight, plus ⊤ and ¬p
  let pool := (ladderL.filter (fun ξ => ξ.weight ≤ 6)) ++ [negF pVar]
  pl s!"substitution pool size: {pool.length}"

  -- one-variable formula classes
  let mTbl := buildTable [pVar, .falsePLL] true MPOOL_W
  let mut mreps : List PLLFormula := []
  for n in List.range MPOOL_W do
    let w := n + 1
    let t0 ← IO.monoMsNow
    for φ in mTbl[w]! do
      mreps := addRep mreps φ
    let t1 ← IO.monoMsNow
    pl s!"M-pool weight {w}: raw level={ (mTbl[w]!).length }  classes so far={mreps.length}  ({t1 - t0} ms)"
  for φ in extras do
    mreps := addRep mreps φ
  let mrepsL := mreps.reverse
  pl s!"one-variable classes (incl. extras): {mrepsL.length}"
  pl ""

  -- the table
  let p := "p"
  let poolSmall := pool.filter (fun ξ => ξ.weight ≤ 5)
  pl s!"pair-search pool size: {poolSmall.length}"
  for M in mrepsL do
    pl s!"M = {pf M}"
    let t0 ← IO.monoMsNow
    let low := ladderL.filter (fun ξ => entails ξ M)
    let maxs := maximals low
    let candA := orAll maxs
    let okA := entails candA M
    let up := ladderL.filter (fun ξ => entails M ξ)
    let mins := minimals up
    let candE := andAll mins
    let okE := entails M candE
    let sA := certAllX p M candA pool poolSmall
    let sE := certExX p M candE pool
    let iness := ladderL.find? (fun ξ => equivO M ξ)
    let sep := if iness.isSome then none else sepWitness p M pool
    let t1 ← IO.monoMsNow
    let sI := match iness, sep with
      | some ξ, _ => s!"INESSENTIAL (≡ {pf ξ})"
      | none, some ab => s!"ESSENTIAL (sep {pf ab.1} vs {pf ab.2})"
      | none, none => "ESSENTIALITY-UNKNOWN"
    pl s!"  ∀p-cand = {pf candA}  (max of {maxs.length}/{low.length} lower; sound={okA})  {sA}"
    pl s!"  ∃p-cand = {pf candE}  (min of {mins.length}/{up.length} upper; sound={okE})  {sE}"
    pl s!"  {sI}  ({t1 - t0} ms)"
  pl ""
  pl "== done =="

end SemUIProbe

def main : IO Unit := SemUIProbe.main
