import LaxLogic.FormattingUtils
import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom
-- import Mathlib.Tactic

open PLLFormula

inductive  PLLProof where
 | emptyProof
 | axiomStep (prev:  PLLProof) (ax: PLLAxiom)
 | modusPonens (prev:  PLLProof) (conditional: Conditional)
  deriving Inhabited, DecidableEq, BEq

namespace PLLProof
-- Gets a list of PLL formulas that are in the proof, no validation here

@[simp]
def  formulas (proof:  PLLProof): List PLLFormula :=
  match proof with
  | emptyProof => []
  | axiomStep prev ax =>  prev.formulas ++ [ax.get]
  | modusPonens prev conditional =>  prev.formulas ++ [conditional.consequent]

-- TODO: Make formualsOf to be a set. Better for proofs.

-- It is convinient to provide steps in a non-nested format
inductive ProofStepInstruction where
  | axiomInstruction (ax: PLLAxiom)
  | modusPonensInstruction (c: Conditional)
deriving DecidableEq, BEq

open ProofStepInstruction

@[simp]
def toInstructions (proof: PLLProof) : List ProofStepInstruction :=
  match proof with
  | emptyProof => []
  | axiomStep prev ax => toInstructions prev ++  [axiomInstruction ax]
  | modusPonens prev c => toInstructions prev ++  [modusPonensInstruction c]

@[simp]
def fromInstructions (list: List ProofStepInstruction) :=
  fromReverse list.reverse where @[simp] fromReverse (reverseList: List  ProofStepInstruction): PLLProof :=
  match reverseList  with
  | [] => emptyProof
  | x::prev =>  match x with
    | axiomInstruction ax => axiomStep (fromReverse prev) ax
    | modusPonensInstruction c => modusPonens (fromReverse prev) c


-- TODO: Prove these are inverses


open ProofStepInstruction

/-- Repr (printing) for proofs -/

def stepsToString (steps: List ProofStepInstruction): String :=
    match steps  with
    | [] => ""
    | (axiomInstruction ax)::next =>  "\n" ++ ax.get.toString ++ " |  " ++ ax.getName ++ stepsToString next
    | (modusPonensInstruction c)::next =>   "\n" ++ c.consequent.toString  ++ " |  MP" ++ stepsToString next


def toString (proof: PLLProof) : String :=
  let steps := proof.toInstructions
  let stepsString :=  stepsToString steps
  let dot :=
    match stepsString with
    | "" =>  "."
    | _ => ""

  "⊢" ++ dot ++ stepsString


/-- `Repr` instance that first prints with `reprAux` and then
    strips one pair of outer parentheses. -/
instance : Repr PLLProof  where
  reprPrec := getReprFn toString


-- Proposition that a proof is valid
@[simp]
def  isValid (proof:  PLLProof) : Prop :=
  match proof with
  | emptyProof => True
  -- Any axiom step is valid
  | axiomStep prev _  => isValid prev
  -- Modus ponens is valid if both the antecedant and the consequent at in the previous steps.
  | modusPonens prev conditional => conditional.antecedant ∈ prev.formulas ∧ conditional.val ∈ prev.formulas

@[simp]
def  isEmpty (proof:  PLLProof):= proof = emptyProof

lemma  non_empty_formulas (proof:  PLLProof) (h: ¬proof.isEmpty) : proof.formulas ≠ [] := by
    induction proof with
    | emptyProof => contradiction
    | axiomStep prev ax => simp [formulas]
    | modusPonens prev conditional => simp [formulas]

def  NonEmpty := {p: PLLProof // ¬ p.isEmpty}

@[simp]
def  NonEmpty.conclusion (p: NonEmpty) : PLLFormula :=
    let h := non_empty_formulas p.val p.prop
    p.val.formulas.getLast h


-- Helper for when the proof is non-empty
@[simp]
private def  isProofOf_ (proof : NonEmpty) (target: PLLFormula)   : Prop :=
  proof.conclusion = target ∧ proof.val.isValid


-- Check that a given proof is a proof of a given formula
@[simp]
def  isProofOf (proof :  PLLProof)  (target: PLLFormula)  : Prop :=
  match proof with
  | emptyProof => False
  | axiomStep prev ax => isProofOf_  ⟨ axiomStep prev ax, by simp [isEmpty]⟩ target
  | modusPonens prev ax => isProofOf_  ⟨ modusPonens prev ax, by simp [isEmpty] ⟩ target

inductive ValidProof where
  | mk (proof: PLLProof)(target: PLLFormula) (valid: proof.isProofOf target)

def ValidProof.proof (vp: ValidProof): PLLProof :=
  match vp with
  |mk proof _ _ => proof

def ValidProof.conclusion (vp: ValidProof): PLLFormula :=
  match vp with
  |mk _ target _ => target

def ValidProof.validation (vp: ValidProof): vp.proof.isProofOf vp.conclusion :=
  match vp with
  |mk _ _ h => h

-- Remove the last formula from a proof
@[simp]
def undoStep (proof: PLLProof): PLLProof :=
  match proof with
  | emptyProof => emptyProof
  | axiomStep prev _ => prev
  | modusPonens prev _ => prev



--*********************
--*********************
-- Tests
--*********************
--*********************

-- Prove (A -> A) -> (A -> A)
open PLLAxiom

def cc: Conditional := ⟨ (impS (PLLFormula.prop "A") (PLLFormula.prop "A") (PLLFormula.prop "A")).get, by simp [PLLAxiom.get]⟩

#eval cc.consequent
#eval (impS (PLLFormula.prop "A") (PLLFormula.prop "A") (PLLFormula.prop "A")).get
#eval (impS (PLLFormula.prop "A") (PLLFormula.prop "A") (PLLFormula.prop "A")).get


def steps1 (A: PLLFormula) : List ProofStepInstruction := [
    axiomInstruction (impK A A),
    axiomInstruction (impS A A A),
    modusPonensInstruction ⟨ (impS A A A).get, by simp [PLLAxiom.get]⟩
  ]

#eval PLLProof.fromInstructions (steps1 (prop "A"))

-- Prove (A ⊃  A) ⊃  (A ⊃  A)
@[simp]
def test1 (A: PLLFormula): PLLProof :=
  let c : Conditional := ⟨ (impS A A A).get, by simp [PLLAxiom.get]⟩
  let steps : List ProofStepInstruction := [
    axiomInstruction (impK A A),
    axiomInstruction (impS A A A),
    modusPonensInstruction c
  ]

  PLLProof.fromInstructions steps

lemma test1b (A: PLLFormula) : ¬ (test1 A).isEmpty := by
simp [isEmpty, test1, fromInstructions, fromInstructions.fromReverse]

def A := prop ("A")
#eval PLLProof.NonEmpty.conclusion ⟨ (test1 A), by exact test1b A⟩
#eval  (test1 A).formulas

-- Returns a valid proof
def test1c (A: PLLFormula): ValidProof :=
  let proof := test1 A
  let nonEmpty : PLLProof.NonEmpty := ⟨proof, (by exact test1b A)⟩
  let target := nonEmpty.conclusion
  ValidProof.mk proof target (by
  simp  [proof, target, nonEmpty ]  )

lemma test1d (A: PLLFormula) : (test1 A).isProofOf (ifThen (ifThen A A )  (ifThen A A ) ) := by simp
