import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch

/-!
# The positive side at the low-budget cells that decide the recursion

`wip/ascprobe.lean` measured the descent at *jump goals* countermodel-first
and found no certified failure at budget `0` for atom goals (there it found
proofs) and for `⊃`-shaped jump goals (there it found neither — the cell
reads `~`, "no countermodel in the battery", which is evidence and not a
verdict).

Those `~` cells are exactly the ones that decide whether a **goal-shape**
budget law can finance the descent's recursion.  The clause table says the
budget tier is entered only at jump goals, and only ever one step: to build
a target gated environment clause at budget `b` the proof needs the
universal component at `b−1`, at goals `A`, `A ⊃ B` or `◯A`.  So the law
can be a function of the goal shape provided the shapes reached at the
bottom need `0`.

This probe runs the **positive** side hard on precisely those cells: proof
search with a large budget on the descent at each jump-goal shape at
budgets `0` and `1`.  A `P` here is a found proof (certified derivable) and
settles the cell; `~` after a large budget is a stronger statement than `~`
after a token spot-check, but still not a verdict.

Run: `lake build jumpprobe && .lake/build/bin/jumpprobe`.
-/

open PLLFormula PLLND PLLND.Search

namespace JumpProbe

def atomAt : Nat → PLLFormula
  | 0 => prop "p" | 1 => prop "r" | 2 => prop "s" | 3 => prop "t"
  | 4 => prop "u" | 5 => prop "v" | _ => prop "w"

def chainPieces (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i => ((atomAt i).somehow).ifThen (atomAt (i + 1)))

def chainClosure (n : Nat) : List PLLFormula :=
  (List.range (n + 1)).flatMap (fun i => [atomAt i, (atomAt i).somehow])

def goalPiece (n : Nat) : PLLFormula :=
  (((atomAt (n - 1)).somehow).ifThen (atomAt n)).ifThen (prop "z")

def chainList (n : Nat) : List PLLFormula :=
  (chainPieces n ++ chainClosure n ++ [goalPiece n, prop "z"]).dedup

def chainSpace (n : Nat) : Finset PLLFormula := (chainList n).toFinset

/-- The `⊃⊃`-gated chain, whose jump goals are `⊃`-shaped. -/
def chainPiecesII (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i =>
    ((atomAt (2 * i)).ifThen (atomAt (2 * i + 1))).ifThen (atomAt (2 * i + 2)))

def chainListII (n : Nat) : List PLLFormula :=
  (chainPiecesII n ++ (List.range (2 * n + 1)).map atomAt
    ++ (List.range (2 * n + 1)).map (fun i => (atomAt i).ifThen (atomAt (i + 1)))
    ++ [prop "z"]).dedup

def chainSpaceII (n : Nat) : Finset PLLFormula := (chainListII n).toFinset

def descHyps (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : List PLLFormula :=
  [itpA p S fuel (c + 1) Γ g, itpE p S fuel (c + 1) Γ]

def descGoal (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : PLLFormula :=
  itpA p S fuel c Γ g

/-- The positive side, run hard. -/
def cfgHard (n : Nat) : Config := { findBudget := some n, emitClosureCap := 0 }

def verdictStr (cf : Config) (hyps : List PLLFormula) (goal : PLLFormula) :
    String :=
  match settleWhy cf hyps goal with
  | .proved _ => "PROVED"
  | .refuted _ _ _ => "REFUTED!"
  | .unknown (.budgetExhausted k) => s!"~ (budget {k} exhausted)"
  | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > cap {cap})"
  | .unknown .allStagesMissed => "~ (all stages missed)"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== the positive side at the deciding low-budget cells =="
  pl ""
  pl "-- ◯-gated chain: jump goals are atoms aᵢ and boxed atoms ◯aᵢ --"
  for n in [2, 3] do
    let S := chainSpace n
    let Γ := [chainPieces n |>.headD (prop "p")]
    let goals : List (String × PLLFormula) :=
      ((List.range n).flatMap (fun i =>
        [(s!"a{i}", atomAt i), (s!"◯a{i}", (atomAt i).somehow)]))
      ++ [("last⊃", ((atomAt (n - 1)).somehow).ifThen (atomAt n))]
    for (nm, g) in goals do
      for c in [0, 1] do
        for bud in [20000, 200000] do
          let t0 ← IO.monoMsNow
          let v ← IO.lazyPure (fun _ =>
            verdictStr (cfgHard bud) (descHyps "p" S (n + 2) c Γ g)
              (descGoal "p" S (n + 2) c Γ g))
          let _ ← IO.lazyPure (fun _ => v.length)
          let t1 ← IO.monoMsNow
          pl s!"chain{n} goal={nm} c={c} findBudget={bud}: {v}  ({t1 - t0} ms)"
  pl ""
  pl "-- ⊃⊃-gated chain: jump goals are ⊃-shaped (aᵢ ⊃ aᵢ₊₁) --"
  for n in [1, 2] do
    let S := chainSpaceII n
    let head := chainPiecesII n |>.headD (prop "p")
    let Γ := [head, (atomAt (2 * n - 1)).ifThen (atomAt (2 * n))]
    let goals : List (String × PLLFormula) :=
      (List.range n).map (fun i =>
        (s!"(a{2*i}⊃a{2*i+1})",
          (atomAt (2 * i)).ifThen (atomAt (2 * i + 1))))
    for (nm, g) in goals do
      for c in [0, 1] do
        for bud in [20000, 200000] do
          let t0 ← IO.monoMsNow
          let v ← IO.lazyPure (fun _ =>
            verdictStr (cfgHard bud) (descHyps "p" S (n + 3) c Γ g)
              (descGoal "p" S (n + 3) c Γ g))
          let _ ← IO.lazyPure (fun _ => v.length)
          let t1 ← IO.monoMsNow
          pl s!"chainII{n} goal={nm} c={c} findBudget={bud}: {v}  ({t1 - t0} ms)"
  pl ""
  pl "== done =="

end JumpProbe

def main : IO Unit := JumpProbe.main
