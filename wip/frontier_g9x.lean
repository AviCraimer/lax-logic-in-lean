import frontier

/-!
# ROUND 9, PHASE 1x — does the fresh-row refutation lift THROUGH the box?

`wip/frontier_g9y.lean` established, at `Γ = []` (where the ambient is `⊤`
and every `itpAenv` table is empty):

* the fresh row descends nowhere: `[row(2)] ⊬ row(1)` at inner fuel ≥ 3,
  refuted by the two-world chain `M2`;
* the UNBOXED room-free descent `A@(f,2)([],D) ⊢ A@(f,1)([],D)` is refuted
  at fuel ≥ 4 by the same model.

`Round4.BoxDesc`'s target is the BOXED table

    A@(f+1, β)([], ◯D) = ◯(⊤ ⊃ A@(f,β)([],D)) ∨ ◯(⊤ ⊃ ◯(⊤ ⊃ A@(f,β)([],D)))

and `M2` does not refute it: `M2`'s modal successor is its top world, where
`z` holds, so both target disjuncts are satisfied there.  What a refutation
needs is a world whose modal successors ALL see the unboxed failure — i.e.
`M2` (or `AscRefute.Mr`) with a modal PREDECESSOR prefixed.  These are the
three- and four-world chains that do that.

Durable output: `wip/frontier_g9x.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g9xLedger : Ledger := { path := "wip/frontier_g9x.txt" }

def xx : PLLFormula := prop "x"
def xy : PLLFormula := prop "y"
def xz : PLLFormula := prop "z"
def xC1 : PLLFormula := (xx.somehow).ifThen xy
def xD : PLLFormula := xC1.ifThen xz
def xSl : List PLLFormula := [xD.somehow, xD, xC1, xx.somehow, xx, xy, xz]
def xS : Finset PLLFormula := xSl.toFinset

/-- Candidate models: chains whose TOP world forces `x`, `y` (never `z`), so
that the unboxed failure sits strictly above every modal step. -/
def cands : List (String × FinCM) :=
  [ ("M2  2-chain, x y z at top",
     ⟨2, [(0,1)], [(0,1)], [], [(1,"x"),(1,"y"),(1,"z")]⟩)
  , ("N2  2-chain, x y at top, no z",
     ⟨2, [(0,1)], [(0,1)], [], [(1,"x"),(1,"y")]⟩)
  , ("N3a 3-chain, rm full, x y at top",
     ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2),(0,2)], [], [(2,"x"),(2,"y")]⟩)
  , ("N3b 3-chain, rm step-only, x y at top",
     ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2)], [], [(2,"x"),(2,"y")]⟩)
  , ("N3c 3-chain, rm=[(0,1),(1,2)], x y at 1 and 2",
     ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2)], [], [(1,"x"),(1,"y"),(2,"x"),(2,"y")]⟩)
  , ("N4a 4-chain, rm full, x y at top",
     ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],
        [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], [(3,"x"),(3,"y")]⟩)
  , ("N4b 4-chain, rm step-only, x y at top",
     ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],
        [(0,1),(1,2),(2,3)], [], [(3,"x"),(3,"y")]⟩)
  , ("N4c 4-chain, rm step-only, x y at 2 and 3",
     ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],
        [(0,1),(1,2),(2,3)], [], [(2,"x"),(2,"y"),(3,"x"),(3,"y")]⟩)
  , ("N5a 5-chain, rm step-only, x y at top",
     ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],
        [(0,1),(1,2),(2,3),(3,4)], [], [(4,"x"),(4,"y")]⟩) ]

def g9xAll : IO Unit := do
  g9xLedger.comment "=== round-9 lift-through-the-box probe (g9x) ==="
  -- 1. the unboxed row and the unboxed table, per model, at inner fuel 3/4
  for (nm, M) in cands do
    let row (f bb : Nat) : PLLFormula :=
      (itpE pv xS f bb [xC1]).ifThen (itpA pv xS f bb [xC1] xz)
    let r3 ← IO.lazyPure (fun _ => FinCM.checkB M 0 [row 3 2] (row 3 1))
    let u4 ← IO.lazyPure (fun _ =>
      FinCM.checkB M 0 [itpA pv xS 4 2 [] xD, itpE pv xS 4 2 []]
        (itpA pv xS 4 1 [] xD))
    g9xLedger.comment s!"{nm}: ROW f=3 refuted={r3}  UNBOXED f=4 refuted={u4}"
  -- 2. `Round4.BoxDesc` at Γ = [], b = 1, per model, fuels 4..7
  for (nm, M) in cands do
    let mut line := s!"{nm}: BD b=1"
    for f in [4, 5, 6, 7] do
      let v ← IO.lazyPure (fun _ =>
        FinCM.checkB M 0 [itpA pv xS f 2 [] xD.somehow, itpE pv xS f 2 []]
          (itpA pv xS f 1 [] xD.somehow))
      line := line ++ s!" f{f}={v}"
    g9xLedger.comment line
  -- 3. `Round8.GoalRowAbsorb` at Γ = [], b = 2, c = 1, per model, fuels 4..7
  --    Gsrc = ◯(E@(f,1)([]) ⊃ A@(f,2)([],D)),  target A@(f+1,1)([],◯D)
  for (nm, M) in cands do
    let mut line := s!"{nm}: GRA b=2 c=1"
    for f in [3, 4, 5, 6] do
      let gsrc := ((itpE pv xS f 1 []).ifThen (itpA pv xS f 2 [] xD)).somehow
      let amb := itpE pv xS (f + 1) 3 []
      let tgt := itpA pv xS (f + 1) 1 [] xD.somehow
      let v ← IO.lazyPure (fun _ => FinCM.checkB M 0 [gsrc, amb] tgt)
      line := line ++ s!" f{f}={v}"
    g9xLedger.comment line
  -- 4. the certified battery on the two instances the fixed models leave open
  for f in [5, 6] do
    let src := itpA pv xS f 2 [] xD.somehow
    let amb := itpE pv xS f 2 []
    let tgt := itpA pv xS f 1 [] xD.somehow
    let n ← IO.lazyPure (fun _ =>
      TowerKit.sz src + TowerKit.sz amb + TowerKit.sz tgt)
    g9xLedger.comment s!"BATTERY BD f={f} b=1 sz={n}"
    let v ← IO.lazyPure (fun _ => refute? cfgCM [src, amb] tgt)
    match v with
    | some ⟨M, w, _⟩ => g9xLedger.comment s!"  R! w={w} M={reprStr M}"
    | none => g9xLedger.comment "  battery quiet"
  g9xLedger.comment "=== g9x done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g9xAll
