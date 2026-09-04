import wip.towerkit
import LaxLogic.PLLSearch

/-!
# ROUND 4, Task 1 — semantic pre-verification of `BoxDesc`

`wip/round4Comp.lean` reduces all three sealed sites of `cascade_main` to one
obligation:

    BoxDesc :  E@(ft, b+1)(Γ)  ⟶  A@(fs, b+1)(Γ, ◯D)  ⟶  A@(ft, b)(Γ, ◯D)
               (fs ≤ ft,  1 ≤ b,  ◯D ∈ S,  Γ ⊆ S)

This probe screens that obligation, countermodel-first, **on the spaces of the
repository's own refutation inventory** — the configurations at which the
room-free descent (`AscRefute.not_roomFreeDescent`, space `Sk`), the ambient
guard ascent (`not_ambGuardAscent`, space `Sr`), the floor descent
(`FloorRefute.not_floorDescent`, space `Sz`) and the ledger dilemma
(`SealLedger.no_ledger`, space `Sγ`) are all FALSE — plus the room-floor
instances of `wip/roomPin.lean`.

A `R!` verdict at any admissible instance would kill the round-4 architecture.
-/

open PLLFormula PLLND PLLND.Search

namespace Round4Probe

/-- `jumpGoals`, verbatim from `wip/absorb_base.lean`:37 (that file is not a
Lake target). -/
def jumpGoals (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

def roomProduct (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  defect S Γ * ((jumpGoals S).card + 2)

/-! ## The instance -/

def bdHyps (p : String) (S : Finset PLLFormula) (fs ft b : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) : List PLLFormula :=
  [itpA p S fs (b + 1) Γ D.somehow, itpE p S ft (b + 1) Γ]

def bdGoal (p : String) (S : Finset PLLFormula) (ft b : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) : PLLFormula :=
  itpA p S ft b Γ D.somehow

inductive V4 | prov | refCert | clean deriving BEq

def V4.tag : V4 → String
  | .prov => "P " | .refCert => "R!" | .clean => "~ "

def ladderFrames : List Frame :=
  [ ⟨3, [(0,1),(1,2),(0,2)], [], []⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [], [2]⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],
       [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], []⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], []⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(0,1)], []⟩
  , ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],
       [], [4]⟩
  , ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],
       [(3,4)], []⟩
  , ⟨3, [(0,1),(0,2)], [], []⟩
  , ⟨3, [(0,1),(0,2)], [(0,1),(0,2)], []⟩
    -- the two models of the refutation inventory, as frames
  , ⟨2, [(0,1)], [(0,1)], []⟩
  , ⟨1, [], [], []⟩
  , ⟨1, [], [], [0]⟩ ]

def cfgHunt : Config :=
  { frames := ladderFrames ++ defaultFrames
  , findBudget := some 900
  , emitClosureCap := 0 }

def bdVerdict (cf : Config) (p : String) (S : Finset PLLFormula)
    (fs ft b : Nat) (Γ : List PLLFormula) (D : PLLFormula) : V4 :=
  match settleWhy cf (bdHyps p S fs ft b Γ D) (bdGoal p S ft b Γ D) with
  | .proved _ => .prov
  | .refuted _ _ _ => .refCert
  | .unknown _ => .clean

/-! ## The spaces of the refutation inventory -/

/-- `AscRefute.Sk` — the space at which the ROOM-FREE descent is refuted. -/
def SkL : List PLLFormula :=
  [((prop "p").somehow).ifThen (prop "r"), (prop "p").somehow, prop "p",
   prop "r", (((prop "r").somehow).ifThen (prop "s")).ifThen (prop "t"),
   ((prop "r").somehow).ifThen (prop "s"), (prop "r").somehow, prop "s",
   prop "t"]
def GkL : List PLLFormula := [((prop "p").somehow).ifThen (prop "r")]

/-- `AscRefute.Sr` — the space at which `AmbGuardAscent` is refuted. -/
def SrL : List PLLFormula :=
  [((prop "p").somehow).ifThen (prop "r"), prop "r",
   ((prop "r").somehow).ifThen (prop "s"), prop "s"]
def GrL : List PLLFormula := [((prop "p").somehow).ifThen (prop "r")]

/-- `SealLedger.Sγ` — the budget-sensitive instance inside the kernel's band
at which `no_ledger_survives_gamma_seal` bites (room `4 ≤ c`). -/
def SgL : List PLLFormula :=
  [((prop "a").somehow).ifThen (prop "b"), (prop "a").somehow,
   prop "a", prop "b"]
def GgL : List PLLFormula :=
  [((prop "a").somehow).ifThen (prop "b"), (prop "a").somehow, prop "a"]

/-- `SealRefute.Sq` — the space of the seal-route refutations. -/
def SqL : List PLLFormula :=
  [((prop "r").somehow).ifThen (prop "s"), (prop "r").somehow, prop "r",
   prop "s", prop "z"]
def GqL : List PLLFormula := [((prop "r").somehow).ifThen (prop "s")]

/-- `RoomPin.Sbox` — the `◯`-band room FLOOR (`defect = 1`, `J = 2`,
`room = 4`). -/
def SboxL : List PLLFormula :=
  [((prop "p").somehow).ifThen (prop "z"), prop "z"]
def GboxL : List PLLFormula := [((prop "p").somehow).ifThen (prop "z")]

structure BInst where
  name : String
  Sl : List PLLFormula
  ctx : List PLLFormula
  body : PLLFormula          -- `D`; the goal is `◯D`

def BInst.S (i : BInst) : Finset PLLFormula := i.Sl.toFinset

/-- Every instance's goal `◯D` must be in `S` and `Γ ⊆ S` — `BoxDesc`'s own
side conditions.  Reported per row so no inadmissible row is ever counted. -/
def admissible (i : BInst) : Bool :=
  i.Sl.contains i.body.somehow && i.ctx.all (fun F => i.Sl.contains F)

def insts : List BInst :=
  [ ⟨"Sk/◯p", SkL, GkL, prop "p"⟩
  , ⟨"Sk/◯r", SkL, GkL, prop "r"⟩
  , ⟨"Sr/◯p", SrL, GrL, prop "p"⟩
  , ⟨"Sγ/◯a", SgL, GgL, prop "a"⟩
  , ⟨"Sq/◯r", SqL, GqL, prop "r"⟩
  , ⟨"Sbox/◯p", SboxL, GboxL, prop "p"⟩ ]

/-- The fuel/budget grid.  `(fs, ft)` covers the two calibrations the sites
use — matched (`F = fl`) and gapped (`F < fl`) — plus a deliberately
under-fuelled source. -/
def grid : List (Nat × Nat) := [(2,2), (3,3), (4,4), (2,4), (3,4), (1,3)]

def row (i : BInst) (b : Nat) : String :=
  let S := i.S
  let adm := if admissible i then "adm" else "INADM"
  let rm := roomProduct S i.ctx
  let vac := if b < rm then "vac" else "LIVE"
  let cells := grid.map (fun fp =>
    (bdVerdict cfgHunt "p" S fp.1 fp.2 b i.ctx i.body).tag)
  s!"{i.name}  b={b}  {adm}  defect={defect S i.ctx} J={(jumpGoals S).card} room={rm} [{vac}]   " ++
    String.intercalate " " cells

def budgets : List Nat := [1, 2, 3, 4, 5]

def table : String :=
  "instance          b  adm  defect/J/room [band]   " ++
    String.intercalate " " (grid.map (fun fp => s!"{fp.1}→{fp.2}")) ++ "\n" ++
  String.intercalate "\n"
    (insts.flatMap (fun i => budgets.map (fun b => row i b)))

end Round4Probe

#eval IO.println Round4Probe.table
