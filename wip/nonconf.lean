import LaxLogic.PLLSearch
import wip.rnDict
import wip.rungPinned
import LaxLogic.PLLSearchConf

/-!
# The five remaining open cells against the NON-confluent five-world battery

Correction run.  `wip/five.lean`'s battery was copied from the PCLL
probe and keeps only MUTUALLY CONFLUENT models — right for PCLL, but
PLL does not require confluence, so its "no 5-world countermodel"
verdicts only covered the confluent part.  The ◯q11 fixed-point cell
fell to a non-confluent five-world model found by hand; this probe
re-runs the five cells still open after the confluent scan.

Run: `scripts/probe 900 nonconf > wip/nonconf_out.txt`.
-/

open PLLFormula PLLND PLLND.SemUI.RND

namespace NonConf

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

def framesAll5 : List FinCM :=
  let inner := (pairsOf 4).map fun q => (q.1 + 1, q.2 + 1)
  ((subsets inner).filter fun ri4 => transL ri4 && antisymL ri4).flatMap
    fun ri4 =>
      let ri := ((List.range 4).map fun k => (0, k + 1)) ++ ri4
      (((subsets ri).filter transL).filter (isCanon ri4)).flatMap fun rm =>
        ((subsets (List.range 5)).filter (upClosedL ri)).filterMap
          fun fall =>
            let M : FinCM := ⟨5, ri, rm, fall, []⟩
            if M.wellB then some M else none

open PLLND.RNC (confB)



def scan (A B : PLLFormula) : Option (FinCM × Nat) := Id.run do
  for M in framesAll5 do
    for w in List.range 5 do
      if FinCM.checkB M w [A] B then return some (M, w)
  return none

def cells : List (String × PLLFormula × PLLFormula) :=
  [("q12 ⊢ q11", q12, q11), ("q14 ⊢ q13", q14, q13),
   ("q8 ⊢ t9", q8, PLLND.RNEmbed.t9), ("q13 ⊢ t9", q13, PLLND.RNEmbed.t9),
   ("q14 ⊢ t9", q14, PLLND.RNEmbed.t9)]

def main : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s!"non-confluent rooted 5-world battery: {framesAll5.length} models"
  out.flush
  for (nm, A, B) in cells do
    let t0 ← IO.monoMsNow
    let r ← IO.lazyPure (fun _ => scan A B)
    let _ ← IO.lazyPure (fun _ => (r.map (·.2)).getD 0)
    let t1 ← IO.monoMsNow
    match r with
    | some (M, w) => out.putStrLn s!"  {nm}: REFUTED — M={repr M} w={w}  ({t1-t0} ms)"
    | none => out.putStrLn s!"  {nm}: no countermodel at 5 worlds, confluent or not  ({t1-t0} ms)"
    out.flush
  out.putStrLn "done"

end NonConf

def main : IO Unit := NonConf.main
