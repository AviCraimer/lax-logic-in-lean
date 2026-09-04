import wip.towerkit

/-!
# `towertest` — run the syntactic tower on the semantic ladder's battery

Computes the tower's quantifier tables (`itpE`/`itpA`, the ones
`wip/packaging.lean` packages as `existsP`/`forallP`) at the prescribed
space and fuel and at a *range of budgets*, and decides agreement with the
ladder's machine-checked values two-sidedly with `PLLND.Search.settle`.

See `wip/towerkit.lean` for why a budget range is both necessary (the
prescribed budget denotes an astronomically large formula) and sufficient
(the verdict transfers upward by the sorry-free `itp_budget_mono_le`).

Run:

    scripts/probe <sec> towertest sizes  <bmax>
    scripts/probe <sec> towertest agree  <bmax> <findBudget>
    scripts/probe <sec> towertest spade  <bmax> <findBudget>
-/

open PLLFormula PLLND PLLND.RNEmbed PLLND.Search TowerKit

def cfgOf (fb : Nat) : Config := { findBudget := some fb }

/-- One-line verdict tag. -/
def tag {Γ : List PLLFormula} {C : PLLFormula} : Verdict Γ C → String
  | .proved _      => "PROVED"
  | .refuted _ _ _ => "REFUTED"
  | .unknown r     => "UNDECIDED (" ++ r.describe ++ ")"

/-- Countermodel render, when there is one. -/
def cmOf {Γ : List PLLFormula} {C : PLLFormula} : Verdict Γ C → String
  | .refuted M w _ => renderCM M (some w)
  | _              => ""

def decideSeq (fb : Nat) (Γ : List PLLFormula) (C : PLLFormula) : String × String :=
  let v := settleWhy (cfgOf fb) Γ C
  (tag v, cmOf v)

/-- Variable-free reference points for placing an answer in `RN(◯,{})`. -/
def refPoints : List (String × PLLFormula) :=
  [ ("bot", PLLFormula.falsePLL)
  , ("oBot", oBot)
  , ("n oBot", nt oBot)
  , ("nn oBot", nt (nt oBot))
  , ("nn oBot > oBot", psiClub)
  , ("rnSub 3", rnSub 3)
  , ("rnSub 4", rnSub 4)
  , ("rnSub 5", rnSub 5)
  , ("rnSub 6", rnSub 6)
  , ("rnSub 7", rnSub 7)
  , ("top", truePLL) ]

def hdr (s : String) : IO Unit := do
  IO.println ""
  IO.println ("=== " ++ s ++ " ===")

def sizesMode (bmax : Nat) : IO Unit := do
  hdr "sizes: tower output node count per row per budget"
  IO.println "row | side | |S| | kcap+1 (prescribed budget) | fuel | sizes b=0.."
  for r in battery do
    let S := pieceClosure r.subj
    let bud := if r.side = "E" then eBudget r.subj else aBudget r.subj
    let fu  := if r.side = "E" then eFuel r.subj else aFuel r.subj
    let mut line := s!"{r.name} | {r.side} | {S.card} | {bud} | {fu} |"
    for b in List.range (bmax + 1) do
      line := line ++ s!" b{b}={sz (rowTower r b)}"
    IO.println line

def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- Run one sequent, unless the antecedent/goal is bigger than `cap` nodes. -/
def run1 (cap fb : Nat) (lbl : String) (Γ : List PLLFormula) (C : PLLFormula) :
    IO Unit := do
  let n := (Γ.map sz).foldl (· + ·) 0 + sz C
  if n > cap then
    say s!"     {lbl}: NOT ATTEMPTED (sequent has {n} nodes, cap {cap})"
  else
    let t0 ← IO.monoMsNow
    let (v, cm) := decideSeq fb Γ C
    let t1 ← IO.monoMsNow
    say s!"     {lbl}: {v}   [{t1 - t0} ms]"
    if cm != "" then say ("       countermodel:\n" ++ cm)

def agreeMode (bmax fb cap : Nat) : IO Unit := do
  hdr "agreement: tower output vs pinned semantic value"
  say "For E rows the FREE direction is  v |- T  (itp_sound + minimality of v);"
  say "the TEST direction is  T |- v.  For A rows: free is  U |- w, test is  w |- U."
  for r in battery do
    match r.val with
    | none => say s!"\n-- {r.name} [{r.side}]: value OPEN ({r.pin}) -- see spade mode"
    | some v =>
      say s!"\n-- {r.name} [{r.side}] pinned value from {r.pin}"
      for b in List.range (bmax + 1) do
        let T := rowTower r b
        say s!"   b={b} sz={sz T}"
        if r.side = "E" then
          run1 cap fb s!"TEST  T{b} |- v" [T] v
          run1 cap fb s!"FREE  v |- T{b}" [v] T
        else
          run1 cap fb s!"TEST  w |- U{b}" [v] T
          run1 cap fb s!"FREE  U{b} |- w" [T] v

def spadeMode (bmax fb cap : Nat) : IO Unit := do
  hdr "phiSpade: the tower's PREDICTION for the semantically OPEN row"
  let φ := phiSpade
  say s!"|S| = {(pieceClosure φ).card}, prescribed budget = {eBudget φ}, fuel = {eFuel φ}"
  for b in List.range (bmax + 1) do
    let T := eTower φ b
    say s!"\n b={b}  sz={sz T}"
    run1 cap fb s!"phiSpade |- T{b}  (itp_sound predicts PROVED)" [φ] T
    run1 cap fb s!"T{b} |- bot        (consistency: expect REFUTED)" [T] PLLFormula.falsePLL
    for (nm, w) in refPoints do
      run1 cap fb s!"T{b} |- {nm}" [T] w
      run1 cap fb s!"{nm} |- T{b}" [w] T

def selfMode (bmax fb cap : Nat) : IO Unit := do
  hdr "budget stability: is the tower's answer already stable at low budgets?"
  say "T(b+1) |- T(b) is a theorem (itp_budget_mono_le); the test is T(b) |- T(b+1)."
  for r in battery do
    say s!"\n-- {r.name} [{r.side}]"
    for b in List.range bmax do
      let T0 := rowTower r b
      let T1 := rowTower r (b + 1)
      let same := if T0 == T1 then "SYNTACTICALLY EQUAL" else "differ"
      say s!"   b={b}->{b+1}: {same}"
      if r.side = "E" then run1 cap fb s!"T{b} |- T{b+1}" [T0] T1
      else run1 cap fb s!"U{b+1} |- U{b}" [T1] T0

/-! ## Decomposed agreement

The tower's ∃-answer is an `andAll` and its ∀-answer an `orAll`
(`LaxLogic/PLLG4UI.lean`), i.e. `c₁ ∧ (c₂ ∧ (… ∧ ⊤))` resp.
`d₁ ∨ (d₂ ∨ (… ∨ ⊥))`.  That structure decomposes both agreement
directions into searches on the *components*, which are one to three
orders of magnitude smaller than the whole:

* `v ⊢ andAll cs`  **iff**  `v ⊢ cᵢ` for every `i`  (∧-introduction /
  ∧-elimination; `G4c.andAll_intro`);
* `andAll cs ⊢ v`  **if**   `cᵢ ⊢ v` for some `i` (∧-elimination) — a
  sufficient condition, and the one that fires in practice;
* `orAll ds ⊢ w`   **iff**  `dᵢ ⊢ w` for every `i` (∨-elimination);
* `w ⊢ orAll ds`   **if**   `w ⊢ dᵢ` for some `i` (∨-introduction).

Each is a *derived rule of the calculus*, so a decomposed verdict is a
verdict about the whole. -/

def conjuncts : PLLFormula → List PLLFormula
  | .and a b => conjuncts a ++ conjuncts b
  | φ => if φ == truePLL then [] else [φ]

def disjuncts : PLLFormula → List PLLFormula
  | .or a b => disjuncts a ++ disjuncts b
  | φ => if φ == PLLFormula.falsePLL then [] else [φ]

/-- Run a sequent, returning the verdict tag (no printing). -/
def quiet (fb : Nat) (Γ : List PLLFormula) (C : PLLFormula) : String :=
  (decideSeq fb Γ C).1

def decompMode (bmax fb cap : Nat) : IO Unit := do
  hdr "decomposed agreement: componentwise verdicts"
  say "E rows: T = andAll cs.  'v |- T' iff v |- c for EVERY c (complete);"
  say "        'T |- v' if c |- v for SOME c (sufficient)."
  say "A rows: U = orAll ds.   'U |- w' iff d |- w for EVERY d (complete);"
  say "        'w |- U' if w |- d for SOME d (sufficient)."
  for r in battery do
    match r.val with
    | none => say s!"\n-- {r.name} [{r.side}]: OPEN"
    | some v =>
      for b in List.range (bmax + 1) do
        let T := rowTower r b
        let comps := if r.side = "E" then conjuncts T else disjuncts T
        let big := comps.filter (fun c => sz c > cap)
        say s!"\n-- {r.name} [{r.side}] b={b} sz={sz T}: {comps.length} components, \
sizes {(comps.map sz)}, {big.length} over cap"
        let t0 ← IO.monoMsNow
        -- complete direction, componentwise
        let mut allOk := true
        let mut anyFail := false
        let mut unk := 0
        let mut i := 0
        for c in comps do
          if sz c > cap then
            unk := unk + 1
            allOk := false
          else
            let res := if r.side = "E" then quiet fb [v] c else quiet fb [c] v
            if res == "PROVED" then pure ()
            else if res == "REFUTED" then
              anyFail := true
              allOk := false
              say s!"     component #{i} (sz {sz c}) REFUTES the complete direction"
            else
              unk := unk + 1
              allOk := false
              say s!"     component #{i} (sz {sz c}) undecided: {res}"
          i := i + 1
        let lblC := if r.side = "E" then s!"v |- T{b}" else s!"U{b} |- w"
        let verdictC :=
          if allOk then "PROVED (every component)"
          else if anyFail then "REFUTED (a component fails)"
          else s!"UNDECIDED ({unk} components unresolved)"
        say s!"   COMPLETE {lblC}: {verdictC}"
        -- sufficient direction, componentwise
        let mut hit : Option (Nat × Nat) := none
        let mut j := 0
        for c in comps do
          if hit.isNone && sz c ≤ cap then
            let res := if r.side = "E" then quiet fb [c] v else quiet fb [v] c
            if res == "PROVED" then hit := some (j, sz c)
          j := j + 1
        let lblS := if r.side = "E" then s!"T{b} |- v" else s!"w |- U{b}"
        let t1 ← IO.monoMsNow
        match hit with
        | some (k, n) => say s!"   SUFFICIENT {lblS}: PROVED via component #{k} \
(sz {n})   [{t1 - t0} ms total]"
        | none => say s!"   SUFFICIENT {lblS}: no single component works \
[{t1 - t0} ms total]"

/-! ## The PLL-equivalence normaliser, iterated

`PLLND.Search.nf` (`LaxLogic/PLLSearch.lean` §0) is a bottom-up pass of
Heyting `⊥`/`⊤` laws plus `◯⊤ ≡ ⊤`, `◯◯ ≡ ◯` — all PLL equivalences.
Iterating it to a fixpoint is what makes the big tower outputs legible. -/

partial def nfStar (φ : PLLFormula) : PLLFormula :=
  let ψ := nf φ
  if ψ == φ then φ else nfStar ψ

def nfMode (bmax fb cap : Nat) : IO Unit := do
  hdr "normalised tower outputs (PLLND.Search.nf iterated to a fixpoint)"
  for r in battery do
    for b in List.range (bmax + 1) do
      let T := rowTower r b
      let t0 ← IO.monoMsNow
      let N := nfStar T
      let t1 ← IO.monoMsNow
      say s!"\n-- {r.name} [{r.side}] b={b}: {sz T} -> {sz N} nodes  [{t1 - t0} ms]"
      if sz N ≤ 400 then say s!"     nf = {repr N}"
      match r.val with
      | none => pure ()
      | some v =>
        if r.side = "E" then
          run1 cap fb s!"nf T{b} |- v" [N] v
          run1 cap fb s!"v |- nf T{b}" [v] N
        else
          run1 cap fb s!"w |- nf U{b}" [v] N
          run1 cap fb s!"nf U{b} |- w" [N] v

/-- `φ♠`'s prediction, on the normalised answer. -/
def spadeNfMode (bmax fb cap : Nat) : IO Unit := do
  hdr "phiSpade: the tower's PREDICTION, normalised"
  let φ := phiSpade
  say s!"|S| = {(pieceClosure φ).card}, prescribed budget = {eBudget φ}, fuel = {eFuel φ}"
  for b in List.range (bmax + 1) do
    let T := eTower φ b
    let N := nfStar T
    say s!"\n b={b}  sz={sz T} -> nf {sz N}"
    if sz N ≤ 500 then say s!"     nf = {repr N}"
    run1 cap fb s!"nf T{b} |- bot   (consistency: expect REFUTED)" [N] PLLFormula.falsePLL
    for (nm, w) in refPoints do
      run1 cap fb s!"nf T{b} |- {nm}" [N] w
      run1 cap fb s!"{nm} |- nf T{b}" [w] N

/-- Placement of a row's answer among the variable-free reference points. -/
def placeMode (bmax fb cap : Nat) : IO Unit := do
  hdr "placement: where each answer sits in the variable-free lattice"
  for r in battery do
    for b in List.range (bmax + 1) do
      let T := rowTower r b
      say s!"\n-- {r.name} [{r.side}] b={b} sz={sz T}"
      for (nm, w) in refPoints do
        run1 cap fb s!"T |- {nm}" [T] w
        run1 cap fb s!"{nm} |- T" [w] T

/-! ## The `φ♠` circle

`§53` proved `IsPostInterp φ♠ ψ♣` with `ψ♣ = ¬¬◯⊥ ⊃ ◯⊥`.  `§54` computed the
tower's `b = 1` answer `T♠1` and certified facts *about* it.  The remaining
check is the direct one: is `nf^* T♠1` interderivable with `ψ♣`?

The two directions are run separately (`dir = 1` / `dir = 2`) so that a
generous `findBudget` can be spent on one of them at a time; `dir = 0` runs
both.  The iteration count `k` of `nf` to its fixpoint is reported, because
the Lean-side cut needs it (`nfIter_interd k`). -/

partial def nfCount (n : Nat) (φ : PLLFormula) : Nat × PLLFormula :=
  let ψ := nf φ
  if ψ == φ then (n, φ) else nfCount (n + 1) ψ

def circleMode (b fb dir : Nat) : IO Unit := do
  hdr "phiSpade circle: Interd (nf^k T b) psiClub"
  let T := eTower phiSpade b
  let (k, N) := nfCount 0 T
  say s!"b={b}  sz T = {sz T}  ->  nf^{k} T, sz = {sz N}"
  if sz N ≤ 800 then say s!"  nf^k T = {repr N}"
  say s!"  psiClub sz = {sz psiClub}, findBudget = {fb}"
  if dir == 0 || dir == 1 then do
    let t0 ← IO.monoMsNow
    let (v, cm) := decideSeq fb [N] psiClub
    let t1 ← IO.monoMsNow
    say s!"  FORWARD   nf^k T{b} |- psiClub : {v}   [{t1 - t0} ms]"
    if cm != "" then say ("    countermodel:\n" ++ cm)
  if dir == 0 || dir == 2 then do
    let t0 ← IO.monoMsNow
    let (v, cm) := decideSeq fb [psiClub] N
    let t1 ← IO.monoMsNow
    say s!"  BACKWARD  psiClub |- nf^k T{b} : {v}   [{t1 - t0} ms]"
    if cm != "" then say ("    countermodel:\n" ++ cm)

def main (args : List String) : IO Unit := do
  let mode := args.getD 0 "sizes"
  let bmax := (args.getD 1 "2").toNat!
  let fb   := (args.getD 2 "200000").toNat!
  let cap  := (args.getD 3 "40000").toNat!
  let dir  := (args.getD 4 "0").toNat!
  say s!"towertest mode={mode} bmax={bmax} findBudget={fb} sizeCap={cap} dir={dir}"
  match mode with
  | "circle" => circleMode bmax fb dir
  | "sizes" => sizesMode bmax
  | "agree" => agreeMode bmax fb cap
  | "spade" => spadeMode bmax fb cap
  | "self"  => selfMode bmax fb cap
  | "place" => placeMode bmax fb cap
  | "decomp" => decompMode bmax fb cap
  | "nf" => nfMode bmax fb cap
  | "spadenf" => spadeNfMode bmax fb cap
  | _       => say "modes: sizes | agree | spade | self | place"
