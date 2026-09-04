import wip.towerkit
import LaxLogic.PLLSearch

/-!
# ROUND 5, probe 2 — the fresh-⊃-antecedent × γ-head corner

`wip/round5probe.lean` proved every floor cell of the `gam` family, but that
family's context contains every proper subformula of the body, so the body's
`⊃`-antecedent is always PRESENT in the grown context and the fresh-antecedent
guard ascent (the `AmbGuardAscent`-shaped step, room-consuming, refuted
room-free by `AscRefute.not_ambGuardAscent`) never fires inside a γ-head
chain.  The financing analysis says the room `defect·(J+2) ≤ b` is exactly ONE
short of the guard ascent's demand at the first γ-head crossing when the
body's antecedent is MISSING from the context.  This probe puts the decisive
cells on the record:

* body `x ⊃ y` with `x ∉ Γ`, `x ∈ S` — the fresh-antecedent corner;
* `defect = 2` (`c` and `x` missing), `J = 2`, room floor `b = 8`;
* also the slack-1 cell `b = 9` and the sub-floor cell `b = 4` (room-free
  regime, for continuity with round-4's screens).

A refutation at the floor cell would show `cascade_boxgoal_pos` FALSE as
stated; a proof closes the last configuration the analysis flags.
-/

open PLLFormula PLLND PLLND.Search

namespace Round5Probe2

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

def xA : PLLFormula := prop "x"
def yA : PLLFormula := prop "y"
def cA : PLLFormula := prop "c"

/-- The body: `x ⊃ y`. -/
def D0 : PLLFormula := xA.ifThen yA

/-- The space: the γ-clause `◯(x⊃y) ⊃ c` with its subformula closure. -/
def Sl : List PLLFormula :=
  [D0.somehow.ifThen cA, D0.somehow, D0, xA, yA, cA]

def S : Finset PLLFormula := Sl.toFinset

/-- The context: clause, boxed body, body, `y` — with `x` and `c` MISSING.
`defect = 2`, and the body's antecedent is fresh. -/
def ctx : List PLLFormula := [D0.somehow.ifThen cA, D0.somehow, D0, yA]

/-- Control context: `x` present (defect 1, floor 4) — the probe-1 regime. -/
def ctxP : List PLLFormula := [D0.somehow.ifThen cA, D0.somehow, D0, xA, yA]

def mainCell (Γ : List PLLFormula) (fs ft b : Nat) : V4 :=
  verdictOf
    [itpA "p" S fs (b + 1) Γ D0.somehow, itpE "p" S ft (b + 1) Γ]
    (itpA "p" S ft b Γ D0.somehow)

def gammaCell (Γ : List PLLFormula) (F fl b : Nat) : V4 :=
  verdictOf
    [((itpE "p" S F b Γ).ifThen (itpA "p" S F b Γ D0.somehow)).somehow,
     itpE "p" S fl (b + 1) Γ]
    (((itpE "p" S fl (b - 1) Γ).ifThen
        (itpA "p" S fl (b - 1) Γ D0.somehow)).somehow)

def row (nm : String) (Γ : List PLLFormula)
    (cells : List (String × V4)) : String :=
  s!"{nm} d={defect S Γ} J={(jumpGoals S).card} room={roomProduct S Γ}   " ++
    String.intercalate "  " (cells.map (fun c => s!"{c.1}:{c.2.tag}"))

end Round5Probe2

open Round5Probe2 in
#eval IO.println (row "MAIN  fresh-x " ctx
  [ ("3,3,8", mainCell ctx 3 3 8)
  , ("4,4,8", mainCell ctx 4 4 8)
  , ("3,3,9", mainCell ctx 3 3 9)
  , ("3,3,4", mainCell ctx 3 3 4) ])
open Round5Probe2 in
#eval IO.println (row "GHEAD fresh-x " ctx
  [ ("3,3,8", gammaCell ctx 3 3 8)
  , ("4,4,8", gammaCell ctx 4 4 8)
  , ("3,3,4", gammaCell ctx 3 3 4)
  , ("3,3,2", gammaCell ctx 3 3 2) ])
open Round5Probe2 in
#eval IO.println (row "MAIN  pres-x  " ctxP
  [ ("3,3,4", mainCell ctxP 3 3 4)
  , ("4,4,4", mainCell ctxP 4 4 4) ])
open Round5Probe2 in
#eval IO.println (row "GHEAD pres-x  " ctxP
  [ ("3,3,4", gammaCell ctxP 3 3 4)
  , ("4,4,4", gammaCell ctxP 4 4 4) ])
