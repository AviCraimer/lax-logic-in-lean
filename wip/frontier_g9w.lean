import frontier

/-!
# ROUND 9, PHASE 1w — the fresh-row refutation with a modal PREDECESSOR

`M2 = ⟨2, [(0,1)], [(0,1)], [], [(1,"x"),(1,"y"),(1,"z")]⟩` refutes the
fresh row descent at world `0`: `row(2)` holds there, `row(1)` fails.  To
lift that through the `◯` of `Round4.BoxDesc`'s target one needs a world
whose modal successors are all `M2`-world-`0`-like — i.e. `M2` with a modal
predecessor prefixed, TOP WORLD STILL FORCING `z` (the `g9x` chains dropped
`z` and therefore refuted nothing).

Durable output: `wip/frontier_g9w.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g9wLedger : Ledger := { path := "wip/frontier_g9w.txt" }

def wx : PLLFormula := prop "x"
def wy : PLLFormula := prop "y"
def wz : PLLFormula := prop "z"
def wC1 : PLLFormula := (wx.somehow).ifThen wy
def wD : PLLFormula := wC1.ifThen wz
def wSl : List PLLFormula := [wD.somehow, wD, wC1, wx.somehow, wx, wy, wz]
def wS : Finset PLLFormula := wSl.toFinset

/-- `M2` with a modal predecessor, in every plausible `rm` shape, and the
same with two predecessors.  The top world always forces `x`, `y`, `z`. -/
def wcands : List (String × FinCM) :=
  [ ("P3a 3-chain rm=[(0,1),(1,2)] xyz@2",
     ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2)], [], [(2,"x"),(2,"y"),(2,"z")]⟩)
  , ("P3b 3-chain rm full xyz@2",
     ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2),(0,2)], [], [(2,"x"),(2,"y"),(2,"z")]⟩)
  , ("P3c 3-chain rm=[(1,2)] xyz@2",
     ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], [(2,"x"),(2,"y"),(2,"z")]⟩)
  , ("P3d 3-chain rm=[(0,1),(1,2)] xyz@1,2",
     ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2)], [],
      [(1,"x"),(1,"y"),(1,"z"),(2,"x"),(2,"y"),(2,"z")]⟩)
  , ("P4a 4-chain rm=[(0,1),(1,2),(2,3)] xyz@3",
     ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(0,1),(1,2),(2,3)], [],
      [(3,"x"),(3,"y"),(3,"z")]⟩)
  , ("P4b 4-chain rm full xyz@3",
     ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],
        [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], [(3,"x"),(3,"y"),(3,"z")]⟩)
  , ("P4c 4-chain rm=[(0,1),(1,2),(2,3)] xyz@2,3",
     ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(0,1),(1,2),(2,3)], [],
      [(2,"x"),(2,"y"),(2,"z"),(3,"x"),(3,"y"),(3,"z")]⟩)
  , ("P4d 4-chain rm=[(0,1),(1,2),(1,3),(2,3)] xyz@3",
     ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(0,1),(1,2),(1,3),(2,3)], [],
      [(3,"x"),(3,"y"),(3,"z")]⟩) ]

def g9wAll : IO Unit := do
  g9wLedger.comment "=== round-9 modal-predecessor probe (g9w) ==="
  let row (f bb : Nat) : PLLFormula :=
    (itpE pv wS f bb [wC1]).ifThen (itpA pv wS f bb [wC1] wz)
  for (nm, M) in wcands do
    let mut line := s!"{nm}:"
    -- the unboxed row at each world (where does the failure sit?)
    for w in [0, 1] do
      let r ← IO.lazyPure (fun _ => FinCM.checkB M w [row 3 2] (row 3 1))
      line := line ++ s!" ROW@w{w}={r}"
    -- the BOXED row: the shape the absorption really has to produce
    let rb ← IO.lazyPure (fun _ =>
      FinCM.checkB M 0 [(row 3 2).somehow] ((row 3 1).somehow))
    let rb2 ← IO.lazyPure (fun _ =>
      FinCM.checkB M 0 [row 3 2] ((row 3 1).somehow))
    line := line ++ s!" ◯ROW={rb} ROW⊢◯={rb2}"
    g9wLedger.comment line
  -- `Round4.BoxDesc` at Γ = [], b = 1, fuels 4..7
  for (nm, M) in wcands do
    let mut line := s!"{nm}: BD b=1"
    for f in [4, 5, 6, 7] do
      let v ← IO.lazyPure (fun _ =>
        FinCM.checkB M 0 [itpA pv wS f 2 [] wD.somehow, itpE pv wS f 2 []]
          (itpA pv wS f 1 [] wD.somehow))
      line := line ++ s!" f{f}={v}"
    g9wLedger.comment line
  -- `Round8.GoalRowAbsorb` at Γ = [], b = 2, c = 1, fuels 3..6
  for (nm, M) in wcands do
    let mut line := s!"{nm}: GRA b=2 c=1"
    for f in [3, 4, 5, 6] do
      let gsrc := ((itpE pv wS f 1 []).ifThen (itpA pv wS f 2 [] wD)).somehow
      let amb := itpE pv wS (f + 1) 3 []
      let tgt := itpA pv wS (f + 1) 1 [] wD.somehow
      let v ← IO.lazyPure (fun _ => FinCM.checkB M 0 [gsrc, amb] tgt)
      line := line ++ s!" f{f}={v}"
    g9wLedger.comment line
  g9wLedger.comment "=== g9w done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g9wAll
