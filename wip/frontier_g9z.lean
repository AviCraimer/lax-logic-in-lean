import frontier

/-!
# ROUND 9, PHASE 1z — the fresh-antecedent residue at a NEAR-EMPTY CONTEXT

The corpus never samples this regime.  `genDrop` removes `defectTarget`
(one or two) members of the space, so every recorded cell has a context that
is almost all of `S`; July's witness (`Gk` a singleton, defect 8) is the one
high-defect instance in the inventory, and it is the one place where the
unboxed room-free descent is REFUTED (`AscRefute.not_roomFreeDescent`).

At `Γ = []` the tables collapse: `itpE p S f β [] = ⊤`, every `itpAenv`
table is empty, and

    A@(f+1, β)([], ◯D)  =  ◯( ⊤ ⊃ A@(f, β)([], D) )  ∨  (truncation of the
                                                          same disjunct)
    A@(f+1, β)([], C₁ ⊃ C₂)  =  E@(f, β)(C₁::[]) ⊃ A@(f, β)(C₁::[], C₂)

— so `Round4.BoxDesc` at `Γ = []`, `b = 1`, `D = (◯x ⊃ y) ⊃ z` IS the
fresh-row descent `row@2 ⊢ row@1`, boxed, with a trivial ambient.  Every
hypothesis of `BoxDesc` holds at `Γ = []` (`∀ X ∈ Γ, X ∈ S` is vacuous), so
a countermodel here refutes `BoxDesc` outright and, with it, the whole
room-free route.

The instances are tiny, so the certified battery runs in seconds and the
closure emitter (complete over the subformula closure) is affordable.

Durable output: `wip/frontier_g9z.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g9zLedger : Ledger := { path := "wip/frontier_g9z.txt" }

def runInstZ (nm : String) (prems : List PLLFormula) (tgt : PLLFormula)
    (pbudget : Nat) : IO Unit := do
  let n ← IO.lazyPure (fun _ =>
    (prems.map TowerKit.sz).foldl (· + ·) 0 + TowerKit.sz tgt)
  g9zLedger.comment s!"{nm} sz={n}"
  let v ← IO.lazyPure (fun _ => refute? cfgCM prems tgt)
  match v with
  | some ⟨M, w, _⟩ =>
      g9zLedger.comment s!"  R! w={w} M={reprStr M}"
  | none =>
      let d ← IO.lazyPure (fun _ => prove?Bounded pbudget prems tgt)
      match d with
      | some t =>
          g9zLedger.comment s!"  P (proved, budget {pbudget})"
          let s ← IO.lazyPure (fun _ => t.pretty)
          g9zLedger.comment s!"  TERM {s.take 4000}"
      | none => g9zLedger.comment s!"  ~ (quiet, unproved at {pbudget})"

/-- `x`, `y`, `z` — and `p` is the eliminated variable, absent from the
space, so no `p`-clause of the tables is live. -/
def zx : PLLFormula := prop "x"
def zy : PLLFormula := prop "y"
def zz : PLLFormula := prop "z"

/-- The fresh antecedent: a `⊃◯`-clause, the shape that makes the grown
context's guard budget-GATED (`AscRefute.Xr` verbatim, renamed). -/
def zC1 : PLLFormula := (zx.somehow).ifThen zy

/-- The goal body: `D = (◯x ⊃ y) ⊃ z`, July's `gk` shape. -/
def zD : PLLFormula := zC1.ifThen zz

/-- The piece-closure of `◯D`. -/
def zSl : List PLLFormula := [zD.somehow, zD, zC1, zx.somehow, zx, zy, zz]
def zS : Finset PLLFormula := zSl.toFinset

/-- The same space with a chained γ-clause, so the context is a singleton
exactly as `Gk` is. -/
def zw : PLLFormula := prop "w"
def zGam : PLLFormula := (zw.somehow).ifThen zx
def zSl2 : List PLLFormula :=
  [zD.somehow, zD, zC1, zx.somehow, zx, zy, zz, zGam, zw.somehow, zw]
def zS2 : Finset PLLFormula := zSl2.toFinset

def g9zAll : IO Unit := do
  g9zLedger.comment "=== round-9 near-empty-context probe (g9z) ==="
  g9zLedger.comment s!"zS piece-closed = {Round5Refute.pieceClosedB zSl}"
  g9zLedger.comment s!"zS2 piece-closed = {Round5Refute.pieceClosedB zSl2}"
  g9zLedger.comment s!"defect zS [] = {PLLND.defect zS []} J = {(jumpGoals zS).card}"
  -- BoxDesc at Γ = [], b = 1: source at budget 2, target at budget 1
  for f in [2, 3, 4] do
    runInstZ s!"g9z BD-{f}  [A@({f},2)([],◯D), E@({f},2)([])] |- A@({f},1)([],◯D)"
      [itpA pv zS f 2 [] zD.somehow, itpE pv zS f 2 []]
      (itpA pv zS f 1 [] zD.somehow) 40000
  -- BoxDesc at Γ = [], b = 2
  runInstZ "g9z BD2-4 [A@(4,3)([],◯D), E@(4,3)([])] |- A@(4,2)([],◯D)"
    [itpA pv zS 4 3 [] zD.somehow, itpE pv zS 4 3 []]
    (itpA pv zS 4 2 [] zD.somehow) 40000
  -- the bare fresh-row descent, unboxed, no ambient (Γ = [] makes it ⊤)
  for f in [2, 3, 4] do
    let row (bb : Nat) : PLLFormula :=
      (itpE pv zS f bb [zC1]).ifThen (itpA pv zS f bb [zC1] zz)
    runInstZ s!"g9z ROW-{f} [row@2] |- row@1" [row 2] (row 1) 40000
    runInstZ s!"g9z ROWB-{f} [◯row@2] |- ◯row@1" [(row 2).somehow] ((row 1).somehow) 40000
  -- the same at the singleton context Γ = [γ-clause] (July's shape, minimal)
  for f in [3, 4] do
    runInstZ s!"g9z BDγ-{f} [A@({f},2)([γ],◯D), E@({f},2)([γ])] |- A@({f},1)([γ],◯D)"
      [itpA pv zS2 f 2 [zGam] zD.somehow, itpE pv zS2 f 2 [zGam]]
      (itpA pv zS2 f 1 [zGam] zD.somehow) 40000
  g9zLedger.comment "=== g9z done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g9zAll
