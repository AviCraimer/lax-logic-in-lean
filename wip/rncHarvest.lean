import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnEmbed
import wip.rnDict

/-!
# Harvesting the PCLL closure cells into certificates

`wip/rnc_c_out.txt` records 347 settled cells of the connective closure
of the PCLL quotient (and 133 it could not settle).  They are probe
output: verdicts, not theorems.  This generator re-derives each one and
emits Lean source for the ones that close, so the cell becomes a
kernel-checked `InterdU`.

Route: search in PLL, pin the proof term, lift with `DerivU.of_nd`.  A
cell that genuinely needs distribution will NOT close this way — those
are reported separately, and they are the interesting ones, since they
are exactly where PCLL is doing work PLL cannot.

Run: `lake build rncHarvest && .lake/build/bin/rncHarvest > wip/rncHarvest_out.lean`.
-/

open PLLFormula PLLND PLLND.Search

namespace RncHarvest

open PLLND.RNEmbed
open PLLND.SemUI.RND

def cfg : Config := { findBudget := some 50000, emitClosureCap := 30 }

def w15 : PLLFormula := q8.and q10

def rep : Nat -> PLLFormula
  | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3 | 4 => q4 | 5 => q5 | 6 => q6
  | 7 => q7 | 8 => q8 | 9 => q9 | 10 => q10 | 11 => q11 | 12 => q12
  | 13 => q13 | 14 => q14 | _ => w15

def repName : Nat -> String
  | 15 => "w15" | n => s!"q{n}"

def opName : Nat -> String
  | 0 => "And" | 1 => "Or" | 2 => "Imp" | _ => "Box"

def lhs (op i j : Nat) : PLLFormula :=
  match op with
  | 0 => (rep i).and (rep j)
  | 1 => (rep i).or (rep j)
  | 2 => (rep i).ifThen (rep j)
  | _ => (rep i).somehow

def lhsSrc (op i j : Nat) : String :=
  match op with
  | 0 => s!"({repName i}.and {repName j})"
  | 1 => s!"({repName i}.or {repName j})"
  | 2 => s!"({repName i}.ifThen {repName j})"
  | _ => s!"({repName i}.somehow)"

/-- The cells recorded settled in `wip/rnc_c_out.txt`, as `(op, i, j, k)`. -/
def CELLS : List (Nat × Nat × Nat × Nat) :=
  [(0,0,0,0),
   (1,0,0,0),
   (2,0,0,1),
   (0,0,1,0),
   (1,0,1,1),
   (2,0,1,1),
   (0,0,2,0),
   (1,0,2,2),
   (2,0,2,1),
   (0,0,3,0),
   (1,0,3,3),
   (2,0,3,1),
   (0,0,4,0),
   (1,0,4,4),
   (2,0,4,1),
   (0,0,5,0),
   (1,0,5,5),
   (2,0,5,1),
   (0,0,6,0),
   (1,0,6,6),
   (2,0,6,1),
   (0,0,7,0),
   (1,0,7,7),
   (2,0,7,1),
   (0,0,8,0),
   (1,0,8,8),
   (2,0,8,1),
   (0,0,9,0),
   (1,0,9,9),
   (2,0,9,1),
   (0,0,10,0),
   (1,0,10,10),
   (2,0,10,1),
   (0,0,11,0),
   (1,0,11,11),
   (2,0,11,1),
   (0,0,13,0),
   (2,0,13,1),
   (0,0,14,0),
   (2,0,14,1),
   (0,0,15,0),
   (2,0,15,1),
   (2,1,0,0),
   (0,1,1,1),
   (1,1,1,1),
   (2,1,1,1),
   (0,1,2,2),
   (1,1,2,1),
   (2,1,2,2),
   (0,1,3,3),
   (1,1,3,1),
   (2,1,3,3),
   (0,1,4,4),
   (1,1,4,1),
   (2,1,4,4),
   (0,1,5,5),
   (1,1,5,1),
   (2,1,5,5),
   (0,1,6,6),
   (1,1,6,1),
   (2,1,6,6),
   (0,1,7,7),
   (1,1,7,1),
   (2,1,7,7),
   (0,1,8,8),
   (1,1,8,1),
   (2,1,8,8),
   (0,1,9,9),
   (1,1,9,1),
   (2,1,9,9),
   (0,1,10,10),
   (1,1,10,1),
   (2,1,10,10),
   (0,1,11,11),
   (1,1,11,1),
   (2,1,11,11),
   (1,1,13,1),
   (1,1,14,1),
   (1,1,15,1),
   (2,2,0,3),
   (2,2,1,1),
   (0,2,2,2),
   (1,2,2,2),
   (2,2,2,1),
   (0,2,3,0),
   (1,2,3,4),
   (2,2,3,3),
   (0,2,4,2),
   (1,2,4,4),
   (2,2,4,1),
   (0,2,5,2),
   (1,2,5,5),
   (2,2,5,1),
   (0,2,6,2),
   (1,2,6,6),
   (2,2,6,1),
   (0,2,7,2),
   (1,2,7,7),
   (2,2,7,1),
   (0,2,8,2),
   (1,2,8,8),
   (2,2,8,1),
   (0,2,9,2),
   (1,2,9,9),
   (2,2,9,1),
   (0,2,10,2),
   (1,2,10,10),
   (2,2,10,1),
   (0,2,11,2),
   (1,2,11,11),
   (2,2,11,1),
   (0,2,13,2),
   (2,2,13,1),
   (0,2,14,2),
   (2,2,14,1),
   (0,2,15,2),
   (2,2,15,1),
   (2,3,0,6),
   (2,3,1,1),
   (2,3,2,6),
   (0,3,3,3),
   (1,3,3,3),
   (2,3,3,1),
   (0,3,4,3),
   (1,3,4,4),
   (2,3,4,1),
   (0,3,5,3),
   (1,3,5,5),
   (2,3,5,1),
   (0,3,6,0),
   (1,3,6,7),
   (2,3,6,6),
   (0,3,7,3),
   (1,3,7,7),
   (2,3,7,1),
   (0,3,8,3),
   (1,3,8,8),
   (2,3,8,1),
   (0,3,9,3),
   (1,3,9,9),
   (2,3,9,1),
   (0,3,10,3),
   (1,3,10,10),
   (2,3,10,1),
   (0,3,11,3),
   (1,3,11,11),
   (2,3,11,1),
   (0,3,13,3),
   (2,3,13,1),
   (0,3,14,3),
   (2,3,14,1),
   (0,3,15,3),
   (2,3,15,1),
   (2,4,0,0),
   (2,4,1,1),
   (2,4,2,6),
   (2,4,3,3),
   (0,4,4,4),
   (1,4,4,4),
   (2,4,4,1),
   (0,4,5,4),
   (1,4,5,5),
   (2,4,5,1),
   (0,4,6,2),
   (1,4,6,7),
   (2,4,6,6),
   (0,4,7,4),
   (1,4,7,7),
   (2,4,7,1),
   (0,4,8,4),
   (1,4,8,8),
   (2,4,8,1),
   (0,4,9,4),
   (1,4,9,9),
   (2,4,9,1),
   (0,4,10,4),
   (1,4,10,10),
   (2,4,10,1),
   (0,4,11,4),
   (1,4,11,11),
   (2,4,11,1),
   (0,4,13,4),
   (2,4,13,1),
   (0,4,14,4),
   (2,4,14,1),
   (0,4,15,4),
   (2,4,15,1),
   (2,5,0,0),
   (2,5,1,1),
   (2,5,2,6),
   (2,5,3,3),
   (2,5,4,8),
   (0,5,5,5),
   (1,5,5,5),
   (2,5,5,1),
   (0,5,6,2),
   (1,5,6,9),
   (2,5,6,6),
   (0,5,7,4),
   (1,5,7,9),
   (2,5,7,8),
   (0,5,8,4),
   (0,5,9,5),
   (1,5,9,9),
   (2,5,9,1),
   (0,5,10,5),
   (1,5,10,10),
   (2,5,10,1),
   (0,5,11,5),
   (1,5,11,11),
   (2,5,11,1),
   (0,5,13,5),
   (2,5,13,1),
   (0,5,14,5),
   (2,5,14,1),
   (2,6,0,3),
   (2,6,1,1),
   (2,6,2,10),
   (2,6,3,3),
   (2,6,4,10),
   (2,6,5,10),
   (0,6,6,6),
   (1,6,6,6),
   (2,6,6,1),
   (0,6,7,6),
   (1,6,7,7),
   (2,6,7,1),
   (0,6,8,6),
   (2,6,8,1),
   (0,6,9,6),
   (1,6,9,9),
   (2,6,9,1),
   (0,6,10,2),
   (1,6,10,11),
   (2,6,10,10),
   (0,6,11,6),
   (1,6,11,11),
   (2,6,11,1),
   (0,6,13,6),
   (2,6,13,1),
   (0,6,14,6),
   (2,6,14,1),
   (0,6,15,2),
   (2,7,0,0),
   (2,7,1,1),
   (2,7,2,2),
   (2,7,3,3),
   (2,7,4,10),
   (2,7,5,10),
   (2,7,6,6),
   (0,7,7,7),
   (1,7,7,7),
   (2,7,7,1),
   (0,7,8,7),
   (2,7,8,1),
   (0,7,9,7),
   (1,7,9,9),
   (2,7,9,1),
   (0,7,10,4),
   (1,7,10,11),
   (2,7,10,10),
   (0,7,11,7),
   (1,7,11,11),
   (2,7,11,1),
   (0,7,13,7),
   (2,7,13,1),
   (0,7,14,7),
   (2,7,14,1),
   (2,8,0,0),
   (2,8,1,1),
   (2,8,2,2),
   (2,8,3,3),
   (2,8,6,6),
   (0,8,8,8),
   (1,8,8,8),
   (2,8,8,1),
   (0,8,9,7),
   (0,8,10,15),
   (0,8,13,8),
   (2,8,13,1),
   (2,9,0,0),
   (2,9,1,1),
   (2,9,2,2),
   (2,9,3,3),
   (2,9,5,10),
   (2,9,6,6),
   (0,9,9,9),
   (1,9,9,9),
   (2,9,9,1),
   (0,9,10,5),
   (1,9,10,11),
   (2,9,10,10),
   (0,9,11,9),
   (2,9,11,1),
   (0,9,13,9),
   (2,9,13,1),
   (0,9,14,9),
   (2,9,14,1),
   (2,10,0,0),
   (2,10,1,1),
   (2,10,2,6),
   (2,10,3,3),
   (2,10,6,6),
   (0,10,10,10),
   (1,10,10,10),
   (2,10,10,1),
   (0,10,11,10),
   (1,10,11,11),
   (2,10,11,1),
   (2,11,0,0),
   (2,11,1,1),
   (2,11,2,2),
   (2,11,3,3),
   (2,11,6,6),
   (0,11,11,11),
   (1,11,11,11),
   (2,11,11,1),
   (2,13,0,0),
   (2,13,1,1),
   (2,13,2,2),
   (2,13,3,3),
   (2,13,6,6),
   (2,13,13,1),
   (2,14,0,0),
   (2,14,1,1),
   (2,14,2,2),
   (2,14,3,3),
   (2,14,6,6),
   (2,15,0,0),
   (2,15,1,1),
   (2,15,2,6),
   (2,15,3,3),
   (2,15,6,6),
   (2,15,10,1),
   (2,15,11,1),
   (2,15,15,1),
   (3,0,0,2),
   (3,1,0,1),
   (3,2,0,2),
   (3,3,0,5),
   (3,4,0,5),
   (3,5,0,5),
   (3,6,0,6),
   (3,7,0,9),
   (3,8,0,13),
   (3,9,0,9),
   (3,10,0,10)]

def findTerm (A B : PLLFormula) : Option String :=
  match settleWhy cfg [A] B with
  | .proved t => some t.toLeanSrc
  | _ => none

def main : IO Unit := do
  let out <- IO.getStdout
  let pl (t : String) : IO Unit := do out.putStrLn t; out.flush
  let mut ok := 0
  let mut miss : List String := []
  pl "-- GENERATED by wip/rncHarvest.lean -- do not edit by hand."
  pl "import wip.rnEmbed"
  pl "import wip.rnDict"
  pl "import wip.rnDictBase"
  pl ""
  pl "open PLLFormula"
  pl "namespace PLLND"
  pl "namespace RNEmbed"
  pl "open SemUI ConfluentU PLLND.SemUI.RND"
  pl ""
  pl "def w15 : PLLFormula := q8.and q10"
  pl ""
  pl "theorem liftU {G : List PLLFormula} {C : PLLFormula} (h : Deriv G C) :"
  pl "    DerivU G C := h.elim fun d => DerivU.of_nd d"
  pl ""
  for (op, i, j, k) in CELLS do
    let L := lhs op i j
    let R := rep k
    let t1 <- IO.lazyPure (fun _ => findTerm L R)
    let _ <- IO.lazyPure (fun _ => (t1.getD "").length)
    let t2 <- IO.lazyPure (fun _ => findTerm R L)
    let _ <- IO.lazyPure (fun _ => (t2.getD "").length)
    match t1, t2 with
    | some a, some b =>
        ok := ok + 1
        pl s!"theorem cU{opName op}_{i}_{j} : InterdU {lhsSrc op i j} {repName k} :="
        pl s!"  ⟨liftU (ofG4 {a}),"
        pl s!"   liftU (ofG4 {b})⟩"
        pl ""
    | _, _ =>
        miss := miss ++ [s!"{opName op} {repName i} {repName j} = {repName k}"]
  pl "end RNEmbed"
  pl "end PLLND"
  pl ""
  pl s!"-- HARVESTED {ok} of {CELLS.length} cells."
  pl s!"-- {miss.length} did NOT close by a PLL proof (candidates for genuine PCLL content):"
  for m in miss do pl s!"--   {m}"

end RncHarvest

def main : IO Unit := RncHarvest.main
