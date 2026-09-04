import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnDict
import LaxLogic.PLLSearchConf

/-!
# What IS `◯q11`?  The two surviving candidates, and placement

`wip/boxTop.lean` refutes the `⊤` candidate for `cBox_11` by inversion.
The survivors from the dictionary's shortlist are `q11` and `q13`, plus
"a new class".  This probe tests both directions of each against the
exhaustive rooted five-world battery (refutations; pure `checkB`, no
search) and the searcher (proofs), and places `◯q11` against `q12`
(strictness of the ◯-chain) and `q9`, `q14`.

Run: `scripts/probe 600 boxq11probe > wip/boxq11probe_out.txt`.
-/

open PLLFormula PLLND PLLND.Search PLLND.SemUI.RND

namespace BoxQ11

open PLLND.RNC (confB)

/-! ## The rooted five-world battery, copied from `wip/rnc_probe.lean`
(that module declares its own top-level `main`, so it cannot be imported). -/

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => (subsets as) ++ (subsets as).map (a :: ·)

def pairsOf (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun a =>
    (List.range n).filterMap fun b => if a = b then none else some (a, b)

def memP (r : List (Nat × Nat)) (p : Nat × Nat) : Bool := decide (p ∈ r)

def transL (r : List (Nat × Nat)) : Bool :=
  r.all fun p => r.all fun q =>
    !(decide (p.2 = q.1)) || memP r (p.1, q.2)

def antisymL (r : List (Nat × Nat)) : Bool :=
  r.all fun p => !(memP r (p.2, p.1))

def upClosedL (r : List (Nat × Nat)) (s : List Nat) : Bool :=
  s.all fun w => r.all fun p =>
    !(decide (p.1 = w)) || decide (p.2 ∈ s)

def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true else if b < a then false else ltKey as bs

def keyOf (r : List (Nat × Nat)) : List Nat :=
  (r.map fun q => q.1 * 16 + q.2).mergeSort (fun a b => a ≤ b)

def pairKey (ri rm : List (Nat × Nat)) : List Nat :=
  keyOf ri ++ [999] ++ keyOf rm

def applyPerm (p : List Nat) (k : Nat) : Nat :=
  if k = 0 then 0 else p.getD (k - 1) k

def isCanon (ri4 rm : List (Nat × Nat)) : Bool :=
  let k0 := pairKey ri4 rm
  ([1, 2, 3, 4].permutations).all fun p =>
    let ri' := ri4.map fun q => (applyPerm p q.1, applyPerm p q.2)
    let rm' := rm.map fun q => (applyPerm p q.1, applyPerm p q.2)
    !(ltKey (pairKey ri' rm') k0)

def framesRooted5 : List FinCM :=
  let inner := (pairsOf 4).map fun q => (q.1 + 1, q.2 + 1)
  ((subsets inner).filter fun ri4 => transL ri4 && antisymL ri4).flatMap
    fun ri4 =>
      let ri := ((List.range 4).map fun k => (0, k + 1)) ++ ri4
      (((subsets ri).filter transL).filter (isCanon ri4)).flatMap fun rm =>
        if confB ⟨5, ri, rm, [], []⟩ then
          ((subsets (List.range 5)).filter (upClosedL ri)).filterMap
            fun fall =>
              let M : FinCM := ⟨5, ri, rm, fall, []⟩
              if M.wellB && confB M then some M else none
        else []

open PLLND.RNC (confB)


def bq : PLLFormula := q11.somehow

def scan (A B : PLLFormula) : Option (FinCM × Nat) := Id.run do
  for M in framesRooted5 do
    for w in List.range 5 do
      if FinCM.checkB M w [A] B then return some (M, w)
  return none

def cfg : Config := { findBudget := some 120000, emitClosureCap := 40 }

def cell (out : IO.FS.Stream) (nm : String) (A B : PLLFormula) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure (fun _ => scan A B)
  let _ ← IO.lazyPure (fun _ => (r.map (·.2)).getD 0)
  let t1 ← IO.monoMsNow
  match r with
  | some (M, w) =>
      out.putStrLn s!"  {nm}: REFUTED at 5 worlds — M={repr M} w={w}  ({t1-t0} ms)"
  | none =>
      let v ← IO.lazyPure (fun _ =>
        match settleWhy cfg [A] B with
        | .proved t => s!"PROVED ({t.size} nodes)\npaste: {t.toLeanSrc}"
        | .refuted M w _ => s!"REFUTED by searcher battery M={repr M} w={w}"
        | .unknown _ => "OPEN (no 5-world countermodel, searcher inconclusive)")
      let _ ← IO.lazyPure (fun _ => v.length)
      let t2 ← IO.monoMsNow
      out.putStrLn s!"  {nm}: {v}  ({t2-t0} ms)"
  out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s!"battery size: {framesRooted5.length}"
  out.putStrLn ""
  out.putStrLn "== candidate q11 (fixed point?) =="
  cell out "◯q11 ⊢ q11" bq q11
  out.putStrLn "  (q11 ⊢ ◯q11 is the unit, free)"
  out.putStrLn ""
  out.putStrLn "== candidate q13 =="
  cell out "◯q11 ⊢ q13" bq q13
  cell out "q13 ⊢ ◯q11" q13 bq
  out.putStrLn ""
  out.putStrLn "== placement =="
  cell out "◯q11 ⊢ q12" bq q12
  cell out "q12 ⊢ ◯q11" q12 bq
  cell out "◯q11 ⊢ q9 " bq q9
  cell out "q9 ⊢ ◯q11 " q9 bq
  cell out "◯q11 ⊢ q14" bq q14
  cell out "q14 ⊢ ◯q11" q14 bq
  out.putStrLn "done"

end BoxQ11

def main : IO Unit := BoxQ11.main
