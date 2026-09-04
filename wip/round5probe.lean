import wip.towerkit
import LaxLogic.PLLSearch

/-!
# ROUND 5 — `cascade_boxgoal_pos` at the ROOM FLOOR

`wip/round4probe2.lean` screened the `◯`-goal descent at budgets `b ∈ {1,2,3}`
over the `gam` family, whose room is `defect · (J+2) = 1 · 4 = 4` — i.e. every
screened cell sits BELOW the room floor, in the room-free regime.  The
statement to be proved (`cascade_boxgoal_pos`) carries
`hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ b`, so its own regime starts
at `b = 4` on this family, and the financing analysis (PROGRESS §59, §60(d))
says the only open question lives exactly there: at `b = room` the γ-head
descent one budget down (`b → b-1`) has no room left to finance it.

This probe covers:

* the MAIN statement at `b = 4` (the floor) and `b = 5` (slack 1), fuels
  `(3,3)` and `(4,4)` — deep enough for two/three nested γ-head unfoldings;
* the γ-HEAD RESIDUE at the floor: from the boxed γ-head component and the
  ambient, the same component one budget down — the one obligation every
  mapping design reduces to at a `◯`-involving γ-row.

Atomic-body rows are controls (theorems: `boxDesc_atom_all`).
-/

open PLLFormula PLLND PLLND.Search

namespace Round5Probe

def jumpGoals (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

def roomProduct (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  defect S Γ * ((jumpGoals S).card + 2)

inductive V4 | prov | refCert | clean deriving BEq

def V4.tag : V4 → String
  | .prov => "P " | .refCert => "R!" | .clean => "~ "

def frames' : List Frame :=
  [ ⟨2, [(0,1)], [(0,1)], []⟩
  , ⟨2, [(0,1)], [(0,1)], [1]⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [], []⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [], [2]⟩
  , ⟨3, [(0,1),(0,2)], [], []⟩
  , ⟨1, [], [], []⟩
  , ⟨1, [], [], [0]⟩ ]

def cfg : Config :=
  { frames := frames' ++ defaultFrames
  , findBudget := some 400
  , emitClosureCap := 0 }

def verdictOf (hyps : List PLLFormula) (goal : PLLFormula) : V4 :=
  match settleWhy cfg hyps goal with
  | .proved _ => .prov
  | .refuted _ _ _ => .refCert
  | .unknown _ => .clean

def aA : PLLFormula := prop "a"
def bA : PLLFormula := prop "b"
def cA : PLLFormula := prop "c"

structure BInst where
  name : String
  Sl : List PLLFormula
  ctx : List PLLFormula
  body : PLLFormula
deriving Inhabited

def BInst.S (i : BInst) : Finset PLLFormula := i.Sl.toFinset

/-- `◯D ⊃ c` with its whole subformula set (probe-2's family): live γ-gate,
`defect = 1`, `J = 2`, room `4`. -/
def gam (D : PLLFormula) (nm : String) : BInst :=
  { name := nm
  , Sl := ((D.somehow.ifThen cA) :: D.somehow :: D :: cA ::
      (match D with
       | .ifThen X Y => [X, Y]
       | .and X Y => [X, Y]
       | .somehow X => [X]
       | _ => [])).dedup
  , ctx := ((D.somehow.ifThen cA) :: D.somehow :: D ::
      (match D with
       | .ifThen X Y => [X, Y]
       | .and X Y => [X, Y]
       | .somehow X => [X]
       | _ => [])).dedup
  , body := D }

def insts : List BInst :=
  [ gam aA             "ATOM-CONTROL ◯a "
  , gam (aA.ifThen bA) "IMP  ◯(a⊃b)"
  , gam (aA.and bA)    "AND  ◯(a∧b)"
  , gam aA.somehow     "BOX  ◯◯a  " ]

/-- The MAIN statement's sequent at `(fs, ft, b)`. -/
def mainCell (i : BInst) (fs ft b : Nat) : V4 :=
  verdictOf
    [itpA "p" i.S fs (b + 1) i.ctx i.body.somehow,
     itpE "p" i.S ft (b + 1) i.ctx]
    (itpA "p" i.S ft b i.ctx i.body.somehow)

/-- The γ-HEAD RESIDUE at `(F, fl, b)`: source component of the γ-row of
`◯D ⊃ c` (budget `b`), ambient at `b + 1`, target component at `b - 1`. -/
def gammaCell (i : BInst) (F fl b : Nat) : V4 :=
  verdictOf
    [((itpE "p" i.S F b i.ctx).ifThen
        (itpA "p" i.S F b i.ctx i.body.somehow)).somehow,
     itpE "p" i.S fl (b + 1) i.ctx]
    (((itpE "p" i.S fl (b - 1) i.ctx).ifThen
        (itpA "p" i.S fl (b - 1) i.ctx i.body.somehow)).somehow)

def mainGrid : List (Nat × Nat × Nat) :=
  [(3,3,4), (4,4,4), (3,3,5), (4,4,5)]

def gammaGrid : List (Nat × Nat × Nat) :=
  [(3,3,4), (4,4,4), (3,3,5)]

def mainRow (i : BInst) : String :=
  let cells := mainGrid.map (fun c =>
    (mainCell i c.1 c.2.1 c.2.2).tag)
  s!"MAIN  {i.name} d={defect i.S i.ctx} J={(jumpGoals i.S).card} room={roomProduct i.S i.ctx}   " ++
    String.intercalate "  " cells

def gammaRow (i : BInst) : String :=
  let cells := gammaGrid.map (fun c =>
    (gammaCell i c.1 c.2.1 c.2.2).tag)
  s!"GHEAD {i.name} d={defect i.S i.ctx} J={(jumpGoals i.S).card} room={roomProduct i.S i.ctx}   " ++
    String.intercalate "  " cells

def header : String :=
  "cells (fs/F, ft/fl, b): MAIN " ++
    String.intercalate "  " (mainGrid.map (fun c => s!"{c.1},{c.2.1},{c.2.2}")) ++
  " | GHEAD " ++
    String.intercalate "  " (gammaGrid.map (fun c => s!"{c.1},{c.2.1},{c.2.2}"))

end Round5Probe

#eval IO.println Round5Probe.header
#eval IO.println (Round5Probe.mainRow (Round5Probe.insts[0]!))
#eval IO.println (Round5Probe.mainRow (Round5Probe.insts[1]!))
#eval IO.println (Round5Probe.mainRow (Round5Probe.insts[2]!))
#eval IO.println (Round5Probe.mainRow (Round5Probe.insts[3]!))
#eval IO.println (Round5Probe.gammaRow (Round5Probe.insts[0]!))
#eval IO.println (Round5Probe.gammaRow (Round5Probe.insts[1]!))
#eval IO.println (Round5Probe.gammaRow (Round5Probe.insts[2]!))
#eval IO.println (Round5Probe.gammaRow (Round5Probe.insts[3]!))
