import frontier

/-!
# ROUND 9, PHASE 1v — the refuting instances, exactly as they will be pinned

`P3c` (`wip/frontier_g9w.lean`) refutes `Round4.BoxDesc` and
`Round8.GoalRowAbsorb` at `Γ = []` over the piece-closure of
`◯((◯x ⊃ y) ⊃ z)`.  This file prints the verdict of every instance the pin
file will carry, together with the arithmetic that places the refuted cell
strictly BELOW the room (so `Round4.BoxDescR` and `cascade_boxgoal_pos` are
untouched).

Durable output: `wip/frontier_g9v.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g9vLedger : Ledger := { path := "wip/frontier_g9v.txt" }

def vx : PLLFormula := prop "x"
def vy : PLLFormula := prop "y"
def vz : PLLFormula := prop "z"
def vC1 : PLLFormula := (vx.somehow).ifThen vy
def vD : PLLFormula := vC1.ifThen vz
def vSl : List PLLFormula := [vD.somehow, vD, vC1, vx.somehow, vx, vy, vz]
def vS : Finset PLLFormula := vSl.toFinset

def P3c : FinCM :=
  ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], [(2,"x"),(2,"y"),(2,"z")]⟩
def M2 : FinCM := ⟨2, [(0,1)], [(0,1)], [], [(1,"x"),(1,"y"),(1,"z")]⟩

def g9vAll : IO Unit := do
  g9vLedger.comment "=== round-9 pin candidates (g9v) ==="
  g9vLedger.comment s!"pieceClosed={Round5Refute.pieceClosedB vSl} \
|S|={vSl.length} defect={PLLND.defect vS []} J={(jumpGoals vS).card} \
room={PLLND.defect vS [] * ((jumpGoals vS).card + 2)}"
  g9vLedger.comment s!"◯D ∈ S = {vSl.contains vD.somehow}"
  -- BoxDesc: fs = ft = f, b = 1, Γ = []
  for f in [3, 4, 5, 6] do
    let src := itpA "p" vS f 2 [] vD.somehow
    let amb := itpE "p" vS f 2 []
    let tgt := itpA "p" vS f 1 [] vD.somehow
    let n ← IO.lazyPure (fun _ =>
      TowerKit.sz src + TowerKit.sz amb + TowerKit.sz tgt)
    let v ← IO.lazyPure (fun _ => FinCM.checkB P3c 0 [src, amb] tgt)
    g9vLedger.comment s!"BoxDesc fs=ft={f} b=1 sz={n}: checkB P3c 0 = {v}"
  -- GoalRowAbsorb: f, b = 2, c = 1, Γ = []
  for f in [3, 4, 5] do
    let gsrc := ((itpE "p" vS f 1 []).ifThen (itpA "p" vS f 2 [] vD)).somehow
    let amb := itpE "p" vS (f + 1) 3 []
    let tgt := itpA "p" vS (f + 1) 1 [] vD.somehow
    let n ← IO.lazyPure (fun _ =>
      TowerKit.sz gsrc + TowerKit.sz amb + TowerKit.sz tgt)
    let v ← IO.lazyPure (fun _ => FinCM.checkB P3c 0 [gsrc, amb] tgt)
    g9vLedger.comment s!"GoalRowAbsorb f={f} b=2 c=1 sz={n}: checkB P3c 0 = {v}"
  -- CompProd: fs = ft = f, b = 2, c = 1, Γ = []
  for f in [3, 4, 5] do
    let cmp (bb : Nat) : PLLFormula :=
      ((itpE "p" vS f bb []).ifThen (itpA "p" vS f bb [] vD.somehow)).somehow
    let amb := itpE "p" vS f 3 []
    let n ← IO.lazyPure (fun _ =>
      TowerKit.sz (cmp 2) + TowerKit.sz amb + TowerKit.sz (cmp 1))
    let v ← IO.lazyPure (fun _ => FinCM.checkB P3c 0 [cmp 2, amb] (cmp 1))
    g9vLedger.comment s!"CompProd f={f} b=2 c=1 sz={n}: checkB P3c 0 = {v}"
  -- the fresh row (M2) and the unboxed same-context descent at Γ = [] (M2)
  for f in [3, 4] do
    let row (bb : Nat) : PLLFormula :=
      (itpE "p" vS f bb [vC1]).ifThen (itpA "p" vS f bb [vC1] vz)
    let n ← IO.lazyPure (fun _ => TowerKit.sz (row 2) + TowerKit.sz (row 1))
    let v ← IO.lazyPure (fun _ => FinCM.checkB M2 0 [row 2] (row 1))
    let v3 ← IO.lazyPure (fun _ => FinCM.checkB P3c 0 [row 2] (row 1))
    g9vLedger.comment s!"freshRow f={f} sz={n}: M2={v} P3c={v3}"
  for f in [4, 5] do
    let src := itpA "p" vS f 2 [] vD
    let amb := itpE "p" vS f 2 []
    let tgt := itpA "p" vS f 1 [] vD
    let n ← IO.lazyPure (fun _ =>
      TowerKit.sz src + TowerKit.sz amb + TowerKit.sz tgt)
    let v ← IO.lazyPure (fun _ => FinCM.checkB M2 0 [src, amb] tgt)
    g9vLedger.comment s!"unboxed f={f} b=1 sz={n}: M2={v}"
  g9vLedger.comment "=== g9v done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g9vAll
