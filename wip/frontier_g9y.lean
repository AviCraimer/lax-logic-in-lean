import frontier

/-!
# ROUND 9, PHASE 1y — does the fresh-row refutation propagate to `BoxDesc`?

`wip/frontier_g9z.lean` refuted the fresh-row descent at the empty context:

    row(β) := E@(3,β)([◯x ⊃ y]) ⊃ A@(3,β)([◯x ⊃ y], z)
    [row(2)] ⊬ row(1)            — `M2` at world 0, kernel-checkable

At `Γ = []` the ambient is `⊤` and `itpAenv` is empty, so

    A@(f+1, β)([], ◯D) = ◯(⊤ ⊃ A@(f,β)([],D)) ∨ ◯(⊤ ⊃ ◯(⊤ ⊃ A@(f,β)([],D)))

and `A@(f,β)([], C₁ ⊃ C₂)` is the row at inner fuel `f − 1`.  So
`Round4.BoxDesc` at `Γ = []`, `b = 1` should read the row two fuel levels
down — which is why the fuel-3 and fuel-4 `BD` instances (rows at fuel 1 and
2) were provable/quiet while the fuel-3 ROW was refuted.  This file checks
the matched instance directly against the model the battery produced,
by `FinCM.checkB` at a FIXED model (no search).

Durable output: `wip/frontier_g9y.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g9yLedger : Ledger := { path := "wip/frontier_g9y.txt" }

/-- The model `wip/frontier_g9z.lean`'s battery produced for the fuel-3 row:
the two-world chain `0 ⊑ 1`, `0 ⊳ 1`, infallible, `x`, `y`, `z` exactly at
world `1`.  (`AscRefute.Mk` with the atoms renamed.) -/
def M2 : FinCM :=
  ⟨2, [(0, 1)], [(0, 1)], [], [(1, "x"), (1, "y"), (1, "z")]⟩

/-- `wip/frontier_g9z.lean`'s space, cloned (that file is a concurrent
recorded artifact, not an import). -/
def yx : PLLFormula := prop "x"
def yy : PLLFormula := prop "y"
def yz : PLLFormula := prop "z"
def zC1 : PLLFormula := (yx.somehow).ifThen yy
def zD : PLLFormula := zC1.ifThen yz
def zSl : List PLLFormula := [zD.somehow, zD, zC1, yx.somehow, yx, yy, yz]
def zS : Finset PLLFormula := zSl.toFinset
def zz : PLLFormula := yz

def g9yAll : IO Unit := do
  g9yLedger.comment "=== round-9 BoxDesc-at-Γ=[] propagation check (g9y) ==="
  -- the row itself, at every fuel: where does the refutation start?
  for f in [1, 2, 3, 4, 5] do
    let row (bb : Nat) : PLLFormula :=
      (itpE pv zS f bb [zC1]).ifThen (itpA pv zS f bb [zC1] zz)
    let v ← IO.lazyPure (fun _ => FinCM.checkB M2 0 [row 2] (row 1))
    let v2 ← IO.lazyPure (fun _ => FinCM.checkB M2 0 [row 3] (row 1))
    let v3 ← IO.lazyPure (fun _ => FinCM.checkB M2 0 [row 3] (row 2))
    g9yLedger.comment s!"ROW f={f}: [row2]|-row1 refuted={v}  \
[row3]|-row1 refuted={v2}  [row3]|-row2 refuted={v3}"
  -- `Round4.BoxDesc` at Γ = [], b = 1 (source b+1 = 2), every fuel
  for f in [3, 4, 5, 6, 7] do
    let src := itpA pv zS f 2 [] zD.somehow
    let amb := itpE pv zS f 2 []
    let tgt := itpA pv zS f 1 [] zD.somehow
    let n ← IO.lazyPure (fun _ =>
      TowerKit.sz src + TowerKit.sz amb + TowerKit.sz tgt)
    let v ← IO.lazyPure (fun _ => FinCM.checkB M2 0 [src, amb] tgt)
    g9yLedger.comment s!"BD f={f} b=1 sz={n}: refuted={v}"
  -- and at b = 2 (source 3, target 2)
  for f in [4, 5, 6, 7] do
    let src := itpA pv zS f 3 [] zD.somehow
    let amb := itpE pv zS f 3 []
    let tgt := itpA pv zS f 2 [] zD.somehow
    let v ← IO.lazyPure (fun _ => FinCM.checkB M2 0 [src, amb] tgt)
    g9yLedger.comment s!"BD f={f} b=2: refuted={v}"
  -- the unboxed body, for reference (`AscRefute.not_roomFreeDescent`'s shape)
  for f in [3, 4, 5, 6] do
    let src := itpA pv zS f 2 [] zD
    let amb := itpE pv zS f 2 []
    let tgt := itpA pv zS f 1 [] zD
    let v ← IO.lazyPure (fun _ => FinCM.checkB M2 0 [src, amb] tgt)
    g9yLedger.comment s!"UNBOXED f={f} b=1: refuted={v}"
  g9yLedger.comment "=== g9y done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g9yAll
