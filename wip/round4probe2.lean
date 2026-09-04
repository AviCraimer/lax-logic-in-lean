import wip.towerkit
import LaxLogic.PLLSearch

/-!
# ROUND 4, Task 1(b) — `BoxDesc` at COMPOUND bodies

`wip/round4Free.lean` proves `Round4.BoxDesc` at an **atomic** body.  What the
three sealed sites need is an arbitrary body `D` with `◯D ∈ S`.  This probe
screens the compound-body statement, countermodel-first, before any attempt is
made to prove it — and carries the atomic rows as a **control**: those are
theorems (`Round4Free.boxDesc_atom_all`), so an `R!` on an atomic row would
indicate a broken probe, not a broken statement.

Rows are small on purpose (low fuels, small spaces): a countermodel to a
`◯`-goal descent, if one exists, shows up at the floor, which is where every
refutation in the repository's inventory sits.
-/

open PLLFormula PLLND PLLND.Search

namespace Round4Probe2

def jumpGoals (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

def roomProduct (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  defect S Γ * ((jumpGoals S).card + 2)

def bdHyps (p : String) (S : Finset PLLFormula) (fs ft b : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) : List PLLFormula :=
  [itpA p S fs (b + 1) Γ D.somehow, itpE p S ft (b + 1) Γ]

def bdGoal (p : String) (S : Finset PLLFormula) (ft b : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) : PLLFormula :=
  itpA p S ft b Γ D.somehow

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

def bdVerdict (p : String) (S : Finset PLLFormula)
    (fs ft b : Nat) (Γ : List PLLFormula) (D : PLLFormula) : V4 :=
  match settleWhy cfg (bdHyps p S fs ft b Γ D) (bdGoal p S ft b Γ D) with
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

def BInst.S (i : BInst) : Finset PLLFormula := i.Sl.toFinset

def admissible (i : BInst) : Bool :=
  i.Sl.contains i.body.somehow && i.ctx.all (fun F => i.Sl.contains F)

/-- `◯D ⊃ c` with its whole subformula set: the minimal `◯`-band space with a
live γ-gate (`c` missing from `Γ`, so `defect = 1`), parameterised by the
body. -/
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
  [ gam aA          "ATOM-CONTROL ◯a"        -- theorem: boxDesc_atom_all
  , gam (aA.ifThen bA)   "IMP  ◯(a⊃b)"
  , gam (aA.and bA)      "AND  ◯(a∧b)"
  , gam aA.somehow       "BOX  ◯◯a"
  , gam falsePLL         "BOT  ◯⊥"
  , gam (bA.ifThen cA)   "IMP2 ◯(b⊃c)" ]

def grid : List (Nat × Nat) := [(2,2), (2,3), (3,3)]

def row (i : BInst) (b : Nat) : String :=
  let S := i.S
  let adm := if admissible i then "adm  " else "INADM"
  let rm := roomProduct S i.ctx
  let cells := grid.map (fun fp =>
    (bdVerdict "p" S fp.1 fp.2 b i.ctx i.body).tag)
  s!"{i.name}  b={b} {adm} d={defect S i.ctx} J={(jumpGoals S).card} room={rm}   " ++
    String.intercalate "  " cells

def budgets : List Nat := [1, 2, 3]

def table : String :=
  "instance                 b  adm   d/J/room     " ++
    String.intercalate "  " (grid.map (fun fp => s!"{fp.1}→{fp.2}")) ++ "\n" ++
  String.intercalate "\n"
    (insts.flatMap (fun i => budgets.map (fun b => row i b)))

end Round4Probe2

#eval IO.println Round4Probe2.table
