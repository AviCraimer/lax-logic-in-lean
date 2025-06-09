import LaxLogic.FormattingUtils
import Mathlib.Tactic
inductive PLLFormula where
| prop (constantName: String)
| falsePLL
| and (a: PLLFormula)(b: PLLFormula)
| or (a: PLLFormula)(b: PLLFormula)
| ifThen (antecedant: PLLFormula)(consequent: PLLFormula)
| somehow (a: PLLFormula)
deriving Inhabited, DecidableEq, BEq

open Std (Format)
namespace PLLFormula


abbrev notPLL (F: PLLFormula) : PLLFormula := ifThen F falsePLL

-- We use false implies false to as our cannoncial true value.
abbrev truePLL := ifThen falsePLL falsePLL

def PropositionalConstant := {F: PLLFormula // ∃ (name:String ), F =  prop name }

-- I originally used a sub-type for this, but I could not figure out how to derive DecidableEq
inductive Conditional where
| mk (F: PLLFormula) (h: ∃ (P Q:PLLFormula), F = ifThen P Q)
deriving DecidableEq

@[simp]
def Conditional.val (C: Conditional) :=
match C with
 | mk F _ => F

@[simp]
def Conditional.prop (C: Conditional):  ∃ P Q, C.val = ifThen P Q :=
match C with
 | mk _ h => h

instance : BEq Conditional where
  beq c1 c2 :=  c1.val == c2.val

@[simp]
def Conditional.antecedant (F: Conditional) :=
 match F with
  | ⟨ifThen P _, _ ⟩  => P
  | ⟨PLLFormula.prop _, p⟩ => by simp_all only [reduceCtorEq, exists_const]
  | ⟨falsePLL, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨and a b, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨or a b, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨somehow a, p⟩ => by simp_all only [reduceCtorEq, exists_const]

@[simp]
def Conditional.consequent (F: Conditional) :=
 match F with
 | ⟨ifThen _ Q, _ ⟩  => Q
 | ⟨PLLFormula.prop _, p⟩ => by simp_all only [reduceCtorEq, exists_const]
  | ⟨falsePLL, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨and a b, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨or a b, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨somehow a, p⟩ => by simp_all only [reduceCtorEq, exists_const]


/-- Pretty-printer using the required logical symbols. -/
def toString (F: PLLFormula) : String :=
(stripParens printF) F where printF (F: PLLFormula) :=
  match F with
  | prop s  =>  s
  | falsePLL =>  "False"
  | and p q => addParens (printF p  ++  " ∧ " ++ printF q )
  | or p q => addParens (printF p  ++  " ∨ " ++ printF q )
  | ifThen falsePLL falsePLL =>  "True"
  | ifThen p q => addParens (printF p  ++  " ⊃ " ++ printF q ) -- Symbol shortcut is \ssup
  | somehow p => addParens ( "◯" ++ printF p )

/-- `Repr` instance that first prints with `reprAux` and then
    strips one pair of outer parentheses. -/
instance : Repr PLLFormula where
  reprPrec := getReprFn  toString

-- Demontstrating Repr
#eval (ifThen (prop "P") (somehow (and (prop "Q") falsePLL))) -- removes outer parents form
#eval prop "P" -- deals with no parens
#eval and truePLL (prop "P") -- True ∧ P

end PLLFormula
