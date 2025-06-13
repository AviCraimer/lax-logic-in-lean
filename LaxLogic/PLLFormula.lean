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


def subformulasOf (F: PLLFormula) : Set PLLFormula :=
    match F with
    | PLLFormula.prop str   => {PLLFormula.prop str }
    | falsePLL => {falsePLL}
    | somehow P =>   {somehow P} ∪ P.subformulasOf
    | ifThen P Q   =>  {ifThen P Q} ∪ P.subformulasOf ∪ Q.subformulasOf
    | and P Q =>  {and P Q} ∪ P.subformulasOf ∪ Q.subformulasOf
    | or P Q => {or P Q} ∪ P.subformulasOf ∪ Q.subformulasOf


@[simp] -- Predicate
def isSomehowFormula (F: PLLFormula) : Prop := ∃(P: PLLFormula), F = somehow P
-- Subtype
def SomehowFormula := {F: PLLFormula // isSomehowFormula F}

@[simp] -- If all subformulas of F are not somehow formuas then F is somehowFree
def isSomehowFree (F: PLLFormula): Prop := ∀ (P: F.subformulasOf), ¬ isSomehowFormula P

def SomehowFree := {F: PLLFormula // isSomehowFree F}

def setIsSomehowFree (S: Set PLLFormula) : Prop := ∀ (F:S),  F.val.isSomehowFree

@[simp]
private def eraseSomehowRaw (F: PLLFormula) : PLLFormula   :=
    match F with

    | PLLFormula.prop str   => PLLFormula.prop str
    | falsePLL => falsePLL
    | somehow P =>  P.eraseSomehowRaw
    | ifThen P Q   =>  ifThen P.eraseSomehowRaw Q.eraseSomehowRaw
    | and P Q =>  and P.eraseSomehowRaw Q.eraseSomehowRaw
    | or P Q => or P.eraseSomehowRaw Q.eraseSomehowRaw

lemma somehow_is_erased (F: PLLFormula) : ∀ (F_erased: PLLFormula ), F_erased = F.eraseSomehowRaw → ∀ (P: F_erased.subformulasOf), ¬ isSomehowFormula P := by
    simp
    intro P Q hP hEq
    subst hEq
    induction F with
    | prop str =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q

    | falsePLL =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
    | and P' Q' ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | or P Q ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | ifThen P Q ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | somehow P ihP =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, not_true_eq_false]



-- This returns an erased PLLFormula packaged with a proof of the property that it is somehow free.
def eraseSomehow (F: PLLFormula) : SomehowFree :=
    let P := F.eraseSomehowRaw
    ⟨P, by
        simp
        have h := somehow_is_erased F P (by rfl)
        intro a b x
        simp_all only [isSomehowFormula, not_exists, Subtype.forall, not_false_eq_true, P]
    ⟩














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
