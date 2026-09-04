import wip.rnDict
import LaxLogic.PLLSearchConf
import LaxLogic.PLLCountermodelEmit

/-!
# Which valuations of `(◯⊥, ◯¬◯⊥)` are realisable?

A two-generator transfer theorem would say: for ◯-free `A` in variables
`p, q`, forcing `A[p := ◯⊥, q := ◯¬◯⊥]` is IPC forcing over a skeleton
with `V(p) = F := {w : w ⊨ ◯⊥}` and `V(q) = G := {w : w ⊨ ◯¬◯⊥}`.

The transfer direction is the easy half — the induction on ◯-free `A`
never meets a `◯`.  The half that decides whether the theorem is USEFUL
is realisation: which pairs of upsets `(F, G)` actually occur?  If every
pair with `F ⊆ G` occurs, the two-generator logic is IPC plus the single
axiom `p ⊃ q`, and the fragment is decidable by IPC.  If fewer pairs
occur, the logic is stronger and the extra axioms are what a transfer
theorem has to carry.

`F ⊆ G` is forced, since `◯⊥ ⊢ ◯X` for every `X`.  This probe scans the
rooted five-world battery and reports which (F, G) shapes occur, as the
IPC-relevant invariant: the isomorphism type of the pair of upsets.

Run: `scripts/probe 300 twogen > wip/twogen_out.txt`.
-/

open PLLFormula PLLND PLLND.SemUI.RND

namespace TwoGen

def c : PLLFormula := falsePLL.somehow                     -- ◯⊥
def d : PLLFormula := (falsePLL.somehow.ifThen falsePLL).somehow  -- ◯¬◯⊥

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => let r := subsets as; r ++ r.map (a :: ·)

def pairsOf (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)

def memP (r : List (Nat × Nat)) (a b : Nat) : Bool := r.contains (a, b)

def transL (r : List (Nat × Nat)) : Bool :=
  r.all fun p => r.all fun q => !(decide (p.2 = q.1)) || memP r p.1 q.2

def antisymL (r : List (Nat × Nat)) : Bool :=
  r.all fun p => !(memP r p.2 p.1) || decide (p.1 = p.2)

def upClosedL (r : List (Nat × Nat)) (s : List Nat) : Bool :=
  s.all fun w => r.all fun p => !(decide (p.1 = w)) || decide (p.2 ∈ s)

/-- Every rooted `n`-world mutually-confluent model, `n = 3, 4, 5`. -/
def battery (n : Nat) : List FinCM :=
  let inner := (pairsOf (n - 1)).map fun q => (q.1 + 1, q.2 + 1)
  ((subsets inner).filter fun ri' => transL ri' && antisymL ri').flatMap
    fun ri' =>
      let ri := ((List.range (n - 1)).map fun k => (0, k + 1)) ++ ri'
      ((subsets ri).filter transL).flatMap fun rm =>
        ((subsets (List.range n)).filter (upClosedL ri)).filterMap fun fall =>
          let M : FinCM := ⟨n, ri, rm, fall, []⟩
          if M.wellB && RNC.confB M then some M else none

/-- The pair of upsets `(F, G)` a model realises, as bit-lists. -/
def fg (M : FinCM) : List Bool × List Bool :=
  ((List.range M.n).map fun w => M.forceB w c,
   (List.range M.n).map fun w => M.forceB w d)

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (x : String) : IO Unit := do out.putStrLn x; out.flush
  pl "=== realisable (F, G) pairs for (◯⊥, ◯¬◯⊥) ==="
  pl ""
  for n in [3, 4, 5] do
    let B := battery n
    let mut seen : List (List Bool × List Bool) := []
    let mut viol := 0
    for M in B do
      let p := fg M
      if !(seen.contains p) then seen := seen ++ [p]
      -- check the forced containment F ⊆ G
      if !((List.range M.n).all fun w => !(M.forceB w c) || M.forceB w d) then
        viol := viol + 1
    let all := (2 ^ n) * (2 ^ n)
    pl s!"n = {n}: {B.length} models, {seen.length} distinct (F,G) pairs \
(of {all} bit-pairs); F ⊆ G violations: {viol}"
    -- how many pairs have F = G?  and how many have F strictly inside G?
    let eq := seen.filter fun p => p.1 == p.2
    pl s!"        F = G in {eq.length} of them, F ⊊ G in {seen.length - eq.length}"
    if n ≤ 4 then
      for p in seen do pl s!"        F={p.1}  G={p.2}"
  pl ""
  pl "=== done ==="

end TwoGen

def main : IO Unit := TwoGen.main
