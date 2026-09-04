import LaxLogic.PLLCtxCompleteness
import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4Term

/-! Shared core of the constraint-commutation probes (models, Lemma-7
constraints, nf, piece closure, relative towers) — no `main`, so the
certifier can import it alongside wip.oracle2. -/

open PLLFormula PLLND PLLND.Ctx

namespace CtxRel

def prov (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  (G4cTm.find Γ C).isSome

def pf (F : PLLFormula) : String := F.toString

/-! ## Normaliser (verbatim from the ctx probe) -/

def isTop : PLLFormula → Bool
  | .ifThen .falsePLL .falsePLL => true
  | _ => false

def smash : PLLFormula → PLLFormula
  | .and A B =>
      if A == .falsePLL || B == .falsePLL then .falsePLL
      else if isTop A then B else if isTop B then A
      else if A == B then A
      else .and A B
  | .or A B =>
      if isTop A || isTop B then truePLL
      else if A == .falsePLL then B else if B == .falsePLL then A
      else if A == B then A
      else .or A B
  | .ifThen A B =>
      if A == .falsePLL || isTop B then truePLL
      else if isTop A then B
      else if A == B then truePLL
      else .ifThen A B
  | .somehow A =>
      if isTop A then truePLL
      else match A with
        | .somehow B => .somehow B
        | _ => .somehow A
  | F => F

def nf : PLLFormula → PLLFormula
  | .and A B    => smash (.and (nf A) (nf B))
  | .or A B     => smash (.or (nf A) (nf B))
  | .ifThen A B => smash (.ifThen (nf A) (nf B))
  | .somehow A  => smash (.somehow (nf A))
  | F => F

/-! ## Piece closure (verbatim from wip/packaging.lean) -/

def pieceClosure : PLLFormula → Finset PLLFormula
  | .prop a => {PLLFormula.prop a}
  | .falsePLL => {falsePLL}
  | .and A B => insert (A.and B) (pieceClosure A ∪ pieceClosure B)
  | .or A B => insert (A.or B) (pieceClosure A ∪ pieceClosure B)
  | .ifThen (.prop a) D =>
      insert ((PLLFormula.prop a).ifThen D)
        (pieceClosure (PLLFormula.prop a) ∪ pieceClosure D)
  | .ifThen .falsePLL D =>
      insert (falsePLL.ifThen D) (pieceClosure falsePLL ∪ pieceClosure D)
  | .ifThen (.and A B) D =>
      insert ((A.and B).ifThen D)
        (pieceClosure (A.and B) ∪ pieceClosure D
          ∪ pieceClosure (A.ifThen (B.ifThen D)))
  | .ifThen (.or A B) D =>
      insert ((A.or B).ifThen D)
        (pieceClosure (A.or B) ∪ pieceClosure D
          ∪ pieceClosure (A.ifThen D) ∪ pieceClosure (B.ifThen D))
  | .ifThen (.ifThen A B) D =>
      insert ((A.ifThen B).ifThen D)
        (pieceClosure (A.ifThen B) ∪ pieceClosure D
          ∪ pieceClosure (B.ifThen D))
  | .ifThen (.somehow X) D =>
      insert ((somehow X).ifThen D)
        (pieceClosure (somehow X) ∪ pieceClosure D)
  | .somehow χ => insert χ.somehow (pieceClosure χ)
termination_by φ => φ.weight
decreasing_by all_goals (simp only [PLLFormula.weight]; omega)

/-! ## Finite models and Lemma 7's constraint (verbatim) -/

structure FinModel where
  n : Nat
  ri : Nat → Nat → Bool
  rm : Nat → Nat → Bool
  fal : Nat → Bool

def worlds (m : FinModel) : List Nat := List.range m.n

def name (i : Nat) : PLLFormula := .prop s!"a{i}"

def stable (m : FinModel) (u : Nat) : Bool :=
  (worlds m).all (fun t => !(m.rm u t) || m.rm t u)

def iSuccB (m : FinModel) (u v : Nat) : Bool :=
  m.ri u v && !(m.ri v u) &&
    (worlds m).all (fun t => !(m.ri u t) || !(m.ri t v) || (m.ri t u || m.ri v t))

def c0Of (m : FinModel) : StdCtx :=
  ((worlds m).filter (stable m)).map (fun u =>
    (name u, Ctx.bigOr (((worlds m).filter (iSuccB m u)).map name)))

def mChain2 : FinModel where
  n := 2
  ri := fun a b => a ≤ b
  rm := fun a b => a ≤ b
  fal := fun a => a == 1

def mChain3 : FinModel where
  n := 3
  ri := fun a b => a ≤ b
  rm := fun a b => a == b || (a == 1 && b == 2)
  fal := fun a => a == 2

def mFork : FinModel where
  n := 4
  ri := fun a b => a == b || (a == 0) || (a == 2 && b == 3)
  rm := fun a b => a == b || (a == 2 && b == 3)
  fal := fun a => a == 3

/-- The frame theory: fallibility axioms `α_w ⊃ ⊥` for fallible `w`. -/
def falAxioms (m : FinModel) : List PLLFormula :=
  ((worlds m).filter m.fal).map (fun w => (name w).ifThen .falsePLL)

/-! ## Targets -/

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

/-- (name, M, PLL ∀p-value). -/
def targets : List (String × PLLFormula × PLLFormula) :=
  [ ("p∨¬p (control)", pV.or (nF pV), .falsePLL)
  , ("◯p⊃p          ", (pV.somehow).ifThen pV, .falsePLL)
  , ("◯(◯p⊃p)       ", ((pV.somehow).ifThen pV).somehow, gB)
  ]

/-! ## The relative tower -/

def TFUEL : Nat := 200
def WCAP : Nat := 200

def spaceOf (Θ : List PLLFormula) (T : PLLFormula) : Finset PLLFormula :=
  Θ.foldl (fun S θ => S ∪ pieceClosure θ) (pieceClosure T)

def towerARel (Θ : List PLLFormula) (T : PLLFormula) (b : Nat) : PLLFormula :=
  nf (itpA "p" (spaceOf Θ T) TFUEL b Θ T)

def equivRel (Θ : List PLLFormula) (X Y : PLLFormula) : Bool :=
  prov (X :: Θ) Y && prov (Y :: Θ) X

end CtxRel
