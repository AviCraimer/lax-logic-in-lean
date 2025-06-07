import Mathlib.Tactic
--import Mathlib.Data.Basic

import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom

open PLLFormula

section Contexts

def Context := Finset PLLFormula
open Finset

instance : Membership PLLFormula Context :=
  inferInstanceAs (Membership PLLFormula (Finset PLLFormula))
instance : Union Context := inferInstanceAs (Union (Finset PLLFormula))
instance : Singleton PLLFormula Context :=
  inferInstanceAs (Singleton PLLFormula (Finset PLLFormula))
instance : EmptyCollection Context := inferInstanceAs (EmptyCollection (Finset PLLFormula))

section Utilities

lemma move_singletons {Γ : Finset PLLFormula} {φ ψ : PLLFormula} :
  Γ ∪ {φ} ∪ {ψ} = Γ ∪ {ψ} ∪ {φ} := by
  apply union_right_comm

lemma image_add_singleton (Γ : Context) (φ : PLLFormula) (f : PLLFormula → PLLFormula)
  : image f (Γ ∪ {φ}) = image f Γ ∪ {f φ} := by
      simp[image_union] -- done!

-- Define what it means for a formula to be in IPL (no somehow modality)
def isIPLFormula : PLLFormula → Prop
  | PLLFormula.prop _  => true
  | falsePLL    => true
  | ifThen φ ψ  => isIPLFormula φ ∧ isIPLFormula ψ
  | PLLFormula.and φ ψ => isIPLFormula φ ∧ isIPLFormula ψ
  | PLLFormula.or φ ψ  => isIPLFormula φ ∧ isIPLFormula ψ
  | somehow _   => false

@[simp]
def eraseSomehow : PLLFormula → PLLFormula
  | PLLFormula.prop a => prop a
  | falsePLL    => falsePLL
  | ifThen φ ψ  => ifThen (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.and φ ψ     => and (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.or φ ψ      => or (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.somehow φ   => eraseSomehow φ

lemma eraseOuter (φ : PLLFormula) : eraseSomehow (somehow φ) = eraseSomehow φ := by
      simp[eraseSomehow]

@[simp]
lemma isIPLerase (φ : PLLFormula) : isIPLFormula (eraseSomehow φ) := by
  induction φ
  all_goals simp [isIPLFormula]
  constructor; assumption; assumption
  constructor; assumption; assumption
  constructor; assumption; assumption
  assumption
theorem map_append_distrib {α β : Type} (f : α → β) (xs ys : List α) (z : α):
  List.map f (xs ++ z :: ys) = List.map f xs ++ f z :: List.map f ys := by
  simp [List.map_append]
end Utilities

inductive LaxND : Context → PLLFormula → Type -- Natural deduction for PLL
  | iden (Γ : Context)  (φ : PLLFormula) /- (h : φ ∈ Γ) -/ : LaxND (Γ ∪ {φ}) φ
  | falsoElim {Γ : Context}  (φ : PLLFormula)  (p : LaxND Γ falsePLL) : LaxND Γ φ
  | impIntro  {Γ : Context}  {φ ψ : PLLFormula}
      (p : LaxND (Γ ∪ {φ}) ψ) : LaxND Γ (ifThen φ ψ)
  | impElim   {Γ : Context}  {φ ψ : PLLFormula}
      (p1 : LaxND Γ (ifThen φ ψ))  (p2 : LaxND Γ φ) : LaxND Γ ψ
  | andIntro  {Γ : Context}  {φ ψ : PLLFormula}
      (p1 : LaxND Γ φ)  (p2 : LaxND Γ ψ) : LaxND Γ (and φ ψ)
  | andElim1  {Γ : Context}  {φ ψ : PLLFormula}
      (p : LaxND Γ (and φ ψ)) : LaxND Γ φ
  | andElim2  {Γ : Context}  {φ ψ : PLLFormula}
      (p : LaxND Γ (and φ ψ)) : LaxND Γ ψ
  | orIntro1  {Γ : Context}  {φ ψ : PLLFormula}
      (p : LaxND Γ φ) : LaxND Γ (or φ ψ)
  | orIntro2  {Γ : Context}  {φ ψ : PLLFormula}
      (p : LaxND Γ ψ) : LaxND Γ (or φ ψ)
  | orElim    {Γ: Context}  {φ ψ χ : PLLFormula}
      (p1 : LaxND (Γ ∪ {φ}) χ)  (p2 : LaxND (Γ ∪ {ψ}) χ) : LaxND Γ χ
  | laxIntro  {Γ : Context}  {φ : PLLFormula}
      (p : LaxND Γ φ) : LaxND Γ (somehow φ)
  | laxElim   {Γ : Context}  {φ ψ : PLLFormula}
      (p1 : LaxND Γ (somehow φ))  (p2 : LaxND (Γ ∪ {φ}) (somehow ψ)) : LaxND Γ (somehow ψ)

infix:70 " ⊢- " => LaxND -- turnstile

def LaxValid (φ : PLLFormula) : Prop := Nonempty (({} : Context) ⊢- φ)

open LaxND

@[match_pattern]
def impInContext : {Γ : Context} → {φ ψ : PLLFormula} → -- too general to be useful?
      LaxND (Γ) φ → LaxND (Γ ∪ {φ}) ψ → LaxND (Γ) ψ := by
      intros Γ φ ψ prf1 prf2
      apply @impElim _ φ ψ
      apply impIntro; /- rw [union_right_comm] ; -/ exact prf2
      exact prf1

def OI (Γ : Context) (φ : PLLFormula) : Γ ⊢- ifThen φ (somehow φ) := impIntro (laxIntro (iden Γ φ))

lemma OItrue (φ : PLLFormula) : LaxValid <| ifThen φ (somehow φ) := by constructor; apply OI

def OSL (Γ : Context) (φ ψ : PLLFormula) : LaxND Γ (ifThen (somehow (and φ ψ)) (and (somehow φ) (somehow ψ))) := by
  apply impIntro
  apply andIntro
  apply @laxElim _ (φ.and ψ)
  apply iden ; apply laxIntro
  apply andElim1 ; apply iden
  apply @laxElim _ (φ.and ψ)
  apply iden ; apply laxIntro
  apply andElim2 ; apply iden

lemma OSLtrue (φ ψ : PLLFormula) : LaxValid <| ifThen (somehow (and φ ψ)) (and (somehow φ) (somehow ψ)) := by
    constructor; apply OSL

def OSR (Γ : Context) (φ ψ : PLLFormula) : Γ ⊢- ifThen (and (somehow φ) (somehow ψ)) (somehow (and φ ψ)) := by
  apply impIntro
  apply @laxElim _ φ
  apply andElim1; apply iden
  apply @laxElim _ ψ
  apply @andElim2 _ φ.somehow ψ.somehow
  rw [union_right_comm] -- rw [move_singletons] -- also works but less general
  apply iden
  apply laxIntro
  apply andIntro
  rw [union_right_comm] -- rw [move_singletons] -- also works but less general
  apply iden ; apply iden

def OM (Γ : Context){φ : PLLFormula} : Γ ⊢- ifThen (somehow (somehow φ)) (somehow φ) := by
  apply impIntro ; apply laxElim
  apply iden Γ ; apply iden

-- Define what it means for a PLL proof to be an IPL proof        s
@[simp]
def isIPLProof : {Γ : Context} → {φ : PLLFormula} → (prf : LaxND Γ φ) → Prop
  | _, _,  iden Γ φ         => isIPLFormula φ -- only you could have a proof in IPL using lax formulae
  | _, _,  falsoElim _ prf  => isIPLProof prf
  | _, _,  impIntro prf     => isIPLProof prf
  | _, _,  impElim  prf1 prf2  => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  andIntro prf1 prf2  => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  andElim1 prf => isIPLProof prf
  | _, _,  andElim2 prf => isIPLProof prf
  | _, _,  orIntro1 prf => isIPLProof prf
  | _, _,  orIntro2 prf => isIPLProof prf
  | _, _,  orElim prf1 prf2 => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  laxIntro _  => false
  | _, _,  laxElim _ _ => false

def erasePLLProof {Γ : Context} {φ : PLLFormula} (h : LaxND Γ φ) :
  LaxND (image eraseSomehow Γ) (eraseSomehow φ) :=
  match h with
  | iden Γ φ =>
    -- Handle identity rule: Γ ++ φ :: Δ ⊢ φ becomes erase(Γ) ++ erase(φ) :: erase(Δ) ⊢ erase(φ)
    -- let Γ' := image eraseSomehow Γ
    -- let Δ' := image eraseSomehow Δ
    -- let φ' := eraseSomehow φ
    cast (congrArg (fun x => LaxND x _) (Eq.symm (image_add_singleton Γ φ eraseSomehow))) <|
        (iden (image eraseSomehow Γ) (eraseSomehow φ))

  | @impIntro Γ φ ψ prf =>
    -- Implication introduction: Γ ++ Δ ⊢ φ → ψ becomes erase(Γ) ++ erase(Δ) ⊢ erase(φ) → erase(ψ)
    let prf' := erasePLLProof prf
    let prf_fix := cast (congrArg (fun x => LaxND x _) (image_add_singleton Γ φ eraseSomehow)) <|
        prf' --(iden (image eraseSomehow Γ) (eraseSomehow φ))
    impIntro prf_fix

  | falsoElim φ prf =>
    -- False elimination: Γ ⊢ ⊥ → Γ ⊢ φ becomes erase(Γ) ⊢ ⊥ → erase(Γ) ⊢ erase(φ)
    falsoElim (eraseSomehow φ) (erasePLLProof prf)

  | impElim prf1 prf2 =>
    -- Implication elimination: Combine erased proofs
    impElim (erasePLLProof prf1) (erasePLLProof prf2)

  | andIntro prf1 prf2 =>
    -- Conjunction introduction: Combine erased proofs
    andIntro (erasePLLProof prf1) (erasePLLProof prf2)

  | andElim1 prf =>
    -- Conjunction elimination (left)
    andElim1 (erasePLLProof prf)

  | andElim2 prf =>
    -- Conjunction elimination (right)
    andElim2 (erasePLLProof prf)

  | orIntro1 prf =>
    -- Disjunction introduction (left)
    orIntro1 (erasePLLProof prf)

  | orIntro2 prf =>
    -- Disjunction introduction (right)
    orIntro2 (erasePLLProof prf)

  | @orElim Γ φ ψ χ prf1 prf2 =>
    -- Disjunction elimination: Combine erased proofs
    let prf1' := erasePLLProof prf1
    let prf2' := erasePLLProof prf2
    have h1 : image eraseSomehow (Γ ∪ {φ}) =
      image eraseSomehow Γ ∪ {eraseSomehow φ}  := by
      apply image_add_singleton -- simp [eraseSomehow, image_append]
    let prf1_cxt_fix := cast (congrArg (fun x => LaxND x _) h1) prf1'
    have h2 : image eraseSomehow (Γ ∪ {ψ}) =
      image eraseSomehow Γ ∪ {eraseSomehow ψ} := by
      apply image_add_singleton
    let prf2_cxt_fix := cast (congrArg (fun x => LaxND x _) h2) prf2'
    let ans := orElim prf1_cxt_fix prf2_cxt_fix
    ans

  | @laxIntro Γ φ prf =>
    -- Lax introduction: Erase the inner somehow
    @erasePLLProof Γ φ prf

  | @laxElim Γ φ ψ prf1 prf2 =>
  -- For laxElim, we need multiple casts
  let prf1' := erasePLLProof prf1
  let prf2' := erasePLLProof prf2

/-   -- First, handle the context equality -- um no longer needed
  have h_context1 (Δ : Context):
    image eraseSomehow (Γ ∪ Δ) = image eraseSomehow Γ ∪ image eraseSomehow Δ := by
    simp[image_union] -- simp [image_append]
 -/
  -- handle the formula equality for the first premise
  have h_formula1 : eraseSomehow (somehow φ) = eraseSomehow φ := by
    simp [eraseSomehow]
  -- let prf1_ctx_fix := cast (congrArg (fun x => LaxND x _) h_context1) prf1'
  -- Cast the first premise to match the expected type
  let prf1_fix := cast (congrArg (fun x => LaxND _ x) h_formula1) prf1'

  -- For prf2', we need to handle the context transformation
  -- The context in prf2' is (Γ ++ φ :: Δ), which needs to be transformed to
  -- (image eraseSomehow Γ ++ eraseSomehow φ :: image eraseSomehow Δ)
  have h_context2 : image eraseSomehow (Γ ∪ {φ}) =
                    image eraseSomehow Γ ∪ {eraseSomehow φ} := by
    simp [image_union, image_add_singleton]
  have h_formula2 : eraseSomehow (somehow ψ) = eraseSomehow ψ := by
    simp [eraseSomehow]

  -- Cast prf2' to fix its context
  let prf2_cxt_fix := cast (congrArg (fun x => LaxND x _) h_context2) prf2'
  let prf2_fix := cast (congrArg (fun x => LaxND _ x) h_formula2) prf2_cxt_fix

   -- Now we can use impInContext with the properly cast arguments
  let ans := @impInContext _ (eraseSomehow φ) (eraseSomehow ψ) prf1_fix prf2_fix -- notice no laxElim
  let ans_fix := cast (congrArg (fun x => LaxND _ x) (Eq.symm h_formula2)) ans

  ans_fix

universe u -- for the next theorem
-- this is the main theorem
theorem PLLconservative : {Γ : Context} → {φ : PLLFormula} → (prf : LaxND Γ φ) →
  isIPLProof (erasePLLProof prf) := by
  intros Γ φ prf; -- unfold isIPLProofList
  -- let tmp := erasePLLProof prf -- no we have this already
  -- simp
  induction prf
  case iden Γ' φ' =>
    -- unfold isIPLProofList
    simp [eraseSomehow, erasePLLProof, isIPLFormula, isIPLProof/- , cast_eq -/];
    have h : isIPLProof (iden (image eraseSomehow Γ') (eraseSomehow φ')) := by
      simp
    norm_cast at h; -- did nothing but didn't fail
    have k {α β : Sort u}{casting : α = β}(f : α)(g : β) : -- totally unsound!
      /- (iden (image eraseSomehow Γ') (eraseSomehow φ')) -/ g =
      (cast casting /- (iden (image eraseSomehow Γ') (eraseSomehow φ')) -/ f) := by sorry
    let dodgy := k (iden (image eraseSomehow Γ') (eraseSomehow φ')) ((iden (image eraseSomehow Γ') (eraseSomehow φ'))
    )
    let tmp := isIPLProofList_cast _ _ h
    -- apply isIPLProofList_cast
  --  simp[h]
  --  simp only [cast_eq]
    sorry

  -- unfold isIPLFormula
  -- simp; unfold erasePLLProof; simp
  all_goals sorry
end Contexts

/-- change the definition of LaxNDList to make casts less necessary and ... -/
inductive LaxNDList : (List PLLFormula) → PLLFormula → Prop -- Natural deduction for PLL
  | move (Γ Δ : List PLLFormula)  (φ ψ : PLLFormula) -- exchange as a "move to the middle" rule
      (p : LaxNDList (φ :: (Γ ++ Δ)) ψ) : LaxNDList (Γ ++ φ :: Δ) ψ  -- make φ and ψ implicit?
  | iden (Γ : List PLLFormula)  (φ : PLLFormula) : LaxNDList (φ :: Γ) φ
  | falsoElim {Γ : List PLLFormula}  (φ : PLLFormula)  (p : LaxNDList Γ falsePLL) : LaxNDList Γ φ
  | impIntro  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDList (φ :: Γ) ψ) : LaxNDList Γ (ifThen φ ψ)
  | impElim   {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p1 : LaxNDList Γ (ifThen φ ψ))  (p2 : LaxNDList Γ φ) : LaxNDList Γ ψ
  | andIntro  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p1 : LaxNDList Γ φ)  (p2 : LaxNDList Γ ψ) : LaxNDList Γ (and φ ψ)
  | andElim1  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDList Γ (and φ ψ)) : LaxNDList Γ φ
  | andElim2  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDList Γ (and φ ψ)) : LaxNDList Γ ψ
  | orIntro1  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDList Γ φ) : LaxNDList Γ (or φ ψ)
  | orIntro2  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDList Γ ψ) : LaxNDList Γ (or φ ψ)
  | orElim    {Γ Δ : List PLLFormula}  {φ ψ χ : PLLFormula}
      (p1 : LaxNDList (φ :: Γ) χ)  (p2 : LaxNDList (ψ :: Γ) χ) : LaxNDList Γ χ
  | laxIntro  {Γ : List PLLFormula}  {φ : PLLFormula}
      (p : LaxNDList Γ φ) : LaxNDList Γ (somehow φ)
  | laxElim   {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p1 : LaxNDList Γ (somehow φ))  (p2 : LaxNDList (φ :: Γ) (somehow ψ)) : LaxNDList Γ (somehow ψ)

open LaxNDList

lemma OIList (Γ : List PLLFormula) (φ : PLLFormula) : LaxNDList Γ <| ifThen φ (somehow φ) := impIntro (laxIntro (iden Γ φ))
def LaxValidList (φ : PLLFormula) : Prop := LaxNDList [] φ

lemma OIListTrue (φ : PLLFormula) : LaxValidList <| ifThen φ (somehow φ) := by apply OIList

lemma OSLList (Γ : List PLLFormula) (φ ψ : PLLFormula) : LaxNDList Γ (ifThen (somehow (and φ ψ)) (and (somehow φ) (somehow ψ))) := by
  apply impIntro
  apply andIntro
  apply @laxElim _ (φ.and ψ)
  apply iden ; apply laxIntro
  apply andElim1 ; apply iden
  apply @laxElim _ (φ.and ψ)
  apply iden ; apply laxIntro
  apply andElim2 ; apply iden

lemma OSLListTrue (φ ψ : PLLFormula) : LaxValidList <| ifThen (somehow (and φ ψ)) (and (somehow φ) (somehow ψ)) := by apply OSLList

lemma OSRList (Γ : List PLLFormula) (φ ψ : PLLFormula) : LaxNDList Γ <| ifThen (and (somehow φ) (somehow ψ)) (somehow (and φ ψ)) := by
  apply impIntro
  apply @laxElim _ φ
  apply andElim1; apply iden
  apply @laxElim _ ψ
  apply @andElim2 _ φ.somehow ψ.somehow
  apply move [φ] ; apply iden
  apply laxIntro
  apply andIntro
  apply move [ψ] ; apply iden ; apply iden

lemma OSRtrue (φ ψ : PLLFormula) : LaxValidList <| ifThen (and (somehow φ) (somehow ψ)) (somehow (and φ ψ)) := by apply OSRList

lemma OMok {Γ : List PLLFormula} (φ : PLLFormula) : LaxNDList Γ <| ifThen (somehow (somehow φ)) (somehow φ) :=
  impIntro (laxElim (iden Γ φ.somehow.somehow) (iden (φ.somehow.somehow :: Γ) φ.somehow))

lemma OMList (Γ : List PLLFormula){φ : PLLFormula} : LaxNDList Γ <| ifThen (somehow (somehow φ)) (somehow φ) := by
  apply impIntro ; apply laxElim
  apply iden Γ ; apply iden

lemma OMtrue (φ : PLLFormula) : LaxValidList <| ifThen (somehow (somehow φ)) (somehow φ) := by apply OMList

section Conservativity

@[match_pattern] -- is this needed, and if so, why?
inductive LaxNDListτ : (List PLLFormula) → PLLFormula → Type -- Natural deduction for PLL
  | moveτ (Γ Δ : List PLLFormula)  (φ ψ : PLLFormula) -- exchange as a "move to the middle" rule
      (p : LaxNDListτ (φ :: (Γ ++ Δ)) ψ) : LaxNDListτ (Γ ++ φ :: Δ) ψ  -- make φ and ψ implicit?
  | idenτ (Γ : List PLLFormula)  (φ : PLLFormula) : LaxNDListτ (φ :: Γ) φ -- simplified identity rule
  | falsoElimτ {Γ : List PLLFormula}  (φ : PLLFormula)  (p : LaxNDListτ Γ falsePLL) : LaxNDListτ Γ φ
  | impIntroτ  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDListτ (φ :: Γ) ψ) : LaxNDListτ Γ (ifThen φ ψ)
  | impElimτ   {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p1 : LaxNDListτ Γ (ifThen φ ψ))  (p2 : LaxNDListτ Γ φ) : LaxNDListτ Γ ψ
  | andIntroτ  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p1 : LaxNDListτ Γ φ)  (p2 : LaxNDListτ Γ ψ) : LaxNDListτ Γ (and φ ψ)
  | andElim1τ  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDListτ Γ (and φ ψ)) : LaxNDListτ Γ φ
  | andElim2τ  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDListτ Γ (and φ ψ)) : LaxNDListτ Γ ψ
  | orIntro1τ  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDListτ Γ φ) : LaxNDListτ Γ (or φ ψ)
  | orIntro2τ  {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p : LaxNDListτ Γ ψ) : LaxNDListτ Γ (or φ ψ)
  | orElimτ    {Γ : List PLLFormula}  {φ ψ χ : PLLFormula}
      (p1 : LaxNDListτ (φ :: Γ) χ)  (p2 : LaxNDListτ (ψ :: Γ) χ) : LaxNDListτ Γ χ
  | laxIntroτ  {Γ : List PLLFormula}  {φ : PLLFormula}
      (p : LaxNDListτ Γ φ) : LaxNDListτ Γ (somehow φ)
  | laxElimτ   {Γ : List PLLFormula}  {φ ψ : PLLFormula}
      (p1 : LaxNDListτ Γ (somehow φ))  (p2 : LaxNDListτ (φ :: Γ) (somehow ψ)) : LaxNDListτ Γ (somehow ψ)

infix:70 " ⊢τ " => LaxNDListτ -- turnstile for Type version
def LaxValidτ (φ : PLLFormula) : Prop := Nonempty (([] : List PLLFormula) ⊢τ φ)

open LaxNDListτ

-- this next is a kind of Cut rule incorporating exchange, contraction (?), weakening
@[match_pattern]
def impInContextList : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDListτ (Γ ++ Δ) φ → LaxNDListτ (Γ ++ φ :: Δ) ψ → LaxNDListτ (Γ ++ Δ) ψ := by
      intros Γ Δ φ ψ prf1 prf2
      apply @impElimτ _ φ ψ
      apply impIntroτ; sorry -- apply moveτ [] Γ ; exact prf2 -- calculus fails here
      -- we see the need for an exchange rule now but in both directions :-( )
      -- it might have been a derived rule, but then we'd have to show it by an induction on proofs...
      exact prf1

-- Define what it means for a PLL proof to be an IPL proof
-- more inference could be requested
@[simp]
def isIPLProofList : {Γ : List PLLFormula} → {φ : PLLFormula} → (prf : LaxNDListτ Γ φ) → Prop
  | _, _,  moveτ Γ Δ φ ψ prf => isIPLProofList prf -- exchange rule
  | _, _,  idenτ Γ φ       => isIPLFormula φ -- only you could have a proof in IPL using lax formulae
  | _, _,  falsoElimτ _ prf  => isIPLProofList prf
  | _, _,  impIntroτ prf => isIPLProofList prf
  | _, _,  impElimτ prf1 prf2  => isIPLProofList prf1 ∧ isIPLProofList prf2
  | _, _,  andIntroτ prf1 prf2 => isIPLProofList prf1 ∧ isIPLProofList prf2
  | _, _,  andElim1τ prf => isIPLProofList prf
  | _, _,  andElim2τ prf => isIPLProofList prf
  | _, _,  orIntro1τ prf => isIPLProofList prf
  | _, _,  orIntro2τ prf => isIPLProofList prf
  | _, _,  orElimτ prf1 prf2 => isIPLProofList prf1 ∧ isIPLProofList prf2
  | _, _,  laxIntroτ _  => false
  | _, _,  laxElimτ _ _ => false

def isIPLProof_robust {Γ : List PLLFormula} {φ : PLLFormula} (prf : LaxNDListτ Γ φ) : Prop :=
  match prf with
  | idenτ Γ φ => isIPLFormula φ
  | _ => false -- very incomplete and next fails
 -- | cast _ prf' => isIPLProof_robust prf'
  -- Other cases

-- @[simp]
theorem isIPLProofList_cast {Γ₁ Γ₂ : List PLLFormula} {φ₁ φ₂ : PLLFormula}
  {prf₁ : LaxNDListτ Γ₁ φ₁} {prf₂ : LaxNDListτ Γ₂ φ₂}
  (h_ctx : Γ₁ = Γ₂) (h_form : φ₁ = φ₂) (h_cast : cast (by simp [h_ctx, h_form]) prf₁ = prf₂) :
  isIPLProofList prf₁ = isIPLProofList prf₂ := by
  subst h_ctx
  subst h_form
  subst h_cast
  rfl

section recursors

def erasePLLProofList {Γ : List PLLFormula} {φ : PLLFormula} (h : LaxNDListτ Γ φ) :
  LaxNDListτ (List.map eraseSomehow Γ) (eraseSomehow φ) :=
  match h with
  | idenτ Γ φ =>
    -- Handle identity rule: Γ ++ φ :: Δ ⊢ φ becomes erase(Γ) ++ erase(φ) :: erase(Δ) ⊢ erase(φ)
    let Γ' := List.map eraseSomehow Γ
    -- let Δ' := List.map eraseSomehow Δ
    let φ' := eraseSomehow φ
    -- how do we actually use definitions above to simplify statement of h1?
    have h1 : List.map eraseSomehow (Γ ++ φ :: Δ) = List.map eraseSomehow Γ ++ eraseSomehow φ :: List.map eraseSomehow Δ := by
      simp[List.map_append, List.map_cons]
    cast (congrArg (fun x => LaxNDListτ x _) (Eq.symm h1))
        (idenτ (List.map eraseSomehow Γ) (eraseSomehow φ))

  | @impIntroτ Γ φ ψ prf =>
    -- Implication introduction: Γ ++ Δ ⊢ φ → ψ becomes erase(Γ) ++ erase(Δ) ⊢ erase(φ) → erase(ψ)
    impIntroτ (erasePLLProofList prf)

  | falsoElimτ φ prf =>
    -- False elimination: Γ ⊢ ⊥ → Γ ⊢ φ becomes erase(Γ) ⊢ ⊥ → erase(Γ) ⊢ erase(φ)
    falsoElimτ (eraseSomehow φ) (erasePLLProofList prf)

  | impElimτ prf1 prf2 =>
    -- Implication elimination: Combine erased proofs
    impElimτ (erasePLLProofList prf1) (erasePLLProofList prf2)

  | andIntroτ prf1 prf2 =>
    -- Conjunction introduction: Combine erased proofs
    andIntroτ (erasePLLProofList prf1) (erasePLLProofList prf2)

  | andElim1τ prf =>
    -- Conjunction elimination (left)
    andElim1τ (erasePLLProofList prf)

  | andElim2τ prf =>
    -- Conjunction elimination (right)
    andElim2τ (erasePLLProofList prf)

  | orIntro1τ prf =>
    -- Disjunction introduction (left)
    orIntro1τ (erasePLLProofList prf)

  | orIntro2τ prf =>
    -- Disjunction introduction (right)
    orIntro2τ (erasePLLProofList prf)

  | @orElimτ Γ φ ψ χ prf1 prf2 =>
    -- Disjunction elimination: Combine erased proofs
    let prf1' := erasePLLProofList prf1
    let prf2' := erasePLLProofList prf2
    have h1 : List.map eraseSomehow (φ :: Γ) =
      eraseSomehow φ ::List.map eraseSomehow Γ := by
      simp [eraseSomehow, List.map_append]
    let prf1_cxt_fix := cast (congrArg (fun x => LaxNDListτ x _) h1) prf1'
    have h2 : List.map eraseSomehow (ψ :: Γ) =
      eraseSomehow ψ :: List.map eraseSomehow Γ := by
      simp [eraseSomehow, List.map_append]
    let prf2_cxt_fix := cast (congrArg (fun x => LaxNDListτ x _) h2) prf2'
    let ans := orElimτ prf1_cxt_fix prf2_cxt_fix
    ans

  | @laxIntroτ Γ φ prf =>
    -- Lax introduction: Erase the inner somehow
    @erasePLLProofList Γ φ prf

  | @laxElimτ Γ φ ψ prf1 prf2 =>
  -- For laxElimτ, we need multiple casts
  let prf1' := erasePLLProofList prf1
  let prf2' := erasePLLProofList prf2

  -- First, handle the context equality -- um no longer needed
  have h_context1 (Δ : List PLLFormula): List.map eraseSomehow (Γ ++ Δ) = List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
    simp [List.map_append]

  -- Then, handle the formula equality for the first premise
  have h_formula1 : eraseSomehow (somehow φ) = eraseSomehow φ := by
    simp [eraseSomehow]
  -- let prf1_ctx_fix := cast (congrArg (fun x => LaxNDListτ x _) h_context1) prf1'
  -- Cast the first premise to match the expected type
  let prf1_fix := cast (congrArg (fun x => LaxNDListτ _ x) h_formula1) prf1'

  -- For prf2', we need to handle the context transformation
  -- The context in prf2' is (Γ ++ φ :: Δ), which needs to be transformed to
  -- (List.map eraseSomehow Γ ++ eraseSomehow φ :: List.map eraseSomehow Δ)
  have h_context2 : List.map eraseSomehow (Γ ++ φ :: Δ) =
                    List.map eraseSomehow Γ ++ eraseSomehow φ :: List.map eraseSomehow Δ := by
    simp [List.map_append]
  have h_formula2 : eraseSomehow (somehow ψ) = eraseSomehow ψ := by
    simp [eraseSomehow]

  -- Cast prf2' to fix its context
  let prf2_cxt_fix := cast (congrArg (fun x => LaxNDListτ x _) h_context2) prf2'
  let prf2_fix := cast (congrArg (fun x => LaxNDListτ _ x) h_formula2) prf2_cxt_fix

   -- Now we can use impInContext with the properly cast arguments
  let ans := impInContextList prf1_fix prf2_fix -- notice no laxElimτ
  -- imvert h1_contezt and h_formula2 and put them together
  let ans_cxt_fix := cast (congrArg (fun x => LaxNDListτ x _) (Eq.symm h_context1)) ans
  let ans_fix := cast (congrArg (fun x => LaxNDListτ _ x) (Eq.symm h_formula2)) ans_cxt_fix

  ans_fix

end recursors

-- the construction below would show conservativity but for the issue with recursor 'LaxNDListτ.rec'
/- def erasePLLProofFail {Γ : List PLLFormula} {φ : PLLFormula}
  (h : LaxNDListτ Γ φ) :
  LaxNDListτ (List.map eraseSomehow Γ) (eraseSomehow φ) := by
  induction h
  case idenτ Γ Δ φ =>
    simp [map_append_distrib] -- Use simp to handle the equality
    apply idenτ
  case impIntroτ prf =>
    simp
    apply impIntroτ
    simp[map_append_distrib] at prf
    exact prf
  case falsoElimτ prf =>
    apply falsoElimτ; exact prf
  case impElimτ prf1 prf2 =>
    apply impElimτ; exact prf1; exact prf2
  case andIntroτ prf1 prf2 =>
    apply andIntroτ; exact prf1; exact prf2
  case andElim1τ prf =>
    apply andElim1τ; exact prf
  case andElim2τ prf =>
    apply andElim2τ; exact prf
  case orIntro1τ prf =>
    apply orIntro1τ; exact prf
  case orIntro2τ prf =>
    apply orIntro2τ; exact prf
  case orElimτ prf1 prf2 =>
    simp
    apply orElimτ
    simp[map_append_distrib] at prf1
    exact prf1
    simp[map_append_distrib] at prf2
    exact prf2
  case laxIntroτ prf =>
    simp; exact prf  -- the somehow has somehow gone :-)
  case laxElimτ prf1 prf2 =>
    simp[map_append_distrib] at prf1
    simp[map_append_distrib] at prf2
    simp
    apply impInContext
    exact prf1; exact prf2
 -/

section Casting



-- variable (α β : Sort)
@[norm_cast] theorem eraseSomehow_context (Γ Δ : List PLLFormula) :
  List.map eraseSomehow (Γ ++ Δ) = List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
  simp [List.map_append]

@[norm_cast] theorem eraseSomehow_somehow (φ : PLLFormula) :
  eraseSomehow (somehow φ) = eraseSomehow φ := by
  simp [eraseSomehow]

theorem isIPLProofList_cast_eq {Γ₁ Γ₂ : List PLLFormula} {φ₁ φ₂ : PLLFormula}
  {prf : LaxNDListτ Γ₁ φ₁} (h : Γ₁ = Γ₂ ∧ φ₁ = φ₂) :
  isIPLProofList (cast (by simp [h.1, h.2]) prf) = isIPLProofList prf := by
  cases h
  subst h_left
  subst h_right
  simp

end Casting

-- this is the main theorem
theorem PLLconservative : {Γ : List PLLFormula} → {φ : PLLFormula} → (prf : LaxNDListτ Γ φ) →
  isIPLProofList (erasePLLProof prf) := by
  intros Γ φ prf; -- unfold isIPLProofList
  -- let tmp := erasePLLProof prf -- no we have this already
  -- simp
  induction prf
  case idenτ Γ' Δ' φ' =>
    -- unfold isIPLProofList
    simp [eraseSomehow, erasePLLProof, isIPLFormula, isIPLProofList/- , cast_eq -/];
    have h : isIPLProofList (idenτ (List.map eraseSomehow Γ') (List.map eraseSomehow Δ') (eraseSomehow φ')) := by
      simp
    norm_cast at h;
    have k {α β : Sort}{casting : α = β} :
      (idenτ (List.map eraseSomehow Γ') (List.map eraseSomehow Δ') (eraseSomehow φ')) =
      (cast casting (idenτ (List.map eraseSomehow Γ') (List.map eraseSomehow Δ') (eraseSomehow φ')))
    let tmp := isIPLProofList_cast _ _ h
    -- apply isIPLProofList_cast
  --  simp[h]
  --  simp only [cast_eq]
    sorry

  -- unfold isIPLFormula
  -- simp; unfold erasePLLProof; simp
  all_goals sorry

end Conservativity
