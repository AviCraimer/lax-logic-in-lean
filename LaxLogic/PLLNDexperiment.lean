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
#check union_insert
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
def zapSomehow : PLLFormula → PLLFormula
  | PLLFormula.prop a => prop a
  | falsePLL    => falsePLL
  | ifThen φ ψ  => ifThen (zapSomehow φ) (zapSomehow ψ)
  | PLLFormula.and φ ψ     => and (zapSomehow φ) (zapSomehow ψ)
  | PLLFormula.or φ ψ      => or (zapSomehow φ) (zapSomehow ψ)
  | PLLFormula.somehow φ   => zapSomehow φ

lemma zapOuter (φ : PLLFormula) : zapSomehow (somehow φ) = zapSomehow φ := by
      simp[zapSomehow]

@[simp]
lemma isIPLzap (φ : PLLFormula) : isIPLFormula (zapSomehow φ) := by
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

def zapPLLProof {Γ : Context} {φ : PLLFormula} (h : LaxND Γ φ) :
  LaxND (image zapSomehow Γ) (zapSomehow φ) :=
  match h with
  | iden Γ φ =>
    -- Handle identity rule: Γ ++ φ :: Δ ⊢ φ becomes zap(Γ) ++ zap(φ) :: zap(Δ) ⊢ zap(φ)
    -- let Γ' := image zapSomehow Γ
    -- let Δ' := image zapSomehow Δ
    -- let φ' := zapSomehow φ
    cast (congrArg (fun x => LaxND x _) (Eq.symm (image_add_singleton Γ φ zapSomehow))) <|
        (iden (image zapSomehow Γ) (zapSomehow φ))

  | @impIntro Γ φ ψ prf =>
    -- Implication introduction: Γ ++ Δ ⊢ φ → ψ becomes zap(Γ) ++ zap(Δ) ⊢ zap(φ) → zap(ψ)
    let prf' := zapPLLProof prf
    let prf_fix := cast (congrArg (fun x => LaxND x _) (image_add_singleton Γ φ zapSomehow)) <|
        prf' --(iden (image zapSomehow Γ) (zapSomehow φ))
    impIntro prf_fix

  | falsoElim φ prf =>
    -- False elimination: Γ ⊢ ⊥ → Γ ⊢ φ becomes zap(Γ) ⊢ ⊥ → zap(Γ) ⊢ zap(φ)
    falsoElim (zapSomehow φ) (zapPLLProof prf)

  | impElim prf1 prf2 =>
    -- Implication elimination: Combine zapd proofs
    impElim (zapPLLProof prf1) (zapPLLProof prf2)

  | andIntro prf1 prf2 =>
    -- Conjunction introduction: Combine zapd proofs
    andIntro (zapPLLProof prf1) (zapPLLProof prf2)

  | andElim1 prf =>
    -- Conjunction elimination (left)
    andElim1 (zapPLLProof prf)

  | andElim2 prf =>
    -- Conjunction elimination (right)
    andElim2 (zapPLLProof prf)

  | orIntro1 prf =>
    -- Disjunction introduction (left)
    orIntro1 (zapPLLProof prf)

  | orIntro2 prf =>
    -- Disjunction introduction (right)
    orIntro2 (zapPLLProof prf)

  | @orElim Γ φ ψ χ prf1 prf2 =>
    -- Disjunction elimination: Combine zapd proofs
    let prf1' := zapPLLProof prf1
    let prf2' := zapPLLProof prf2
    have h1 : image zapSomehow (Γ ∪ {φ}) =
      image zapSomehow Γ ∪ {zapSomehow φ}  := by
      apply image_add_singleton -- simp [zapSomehow, image_append]
    let prf1_cxt_fix := cast (congrArg (fun x => LaxND x _) h1) prf1'
    have h2 : image zapSomehow (Γ ∪ {ψ}) =
      image zapSomehow Γ ∪ {zapSomehow ψ} := by
      apply image_add_singleton
    let prf2_cxt_fix := cast (congrArg (fun x => LaxND x _) h2) prf2'
    let ans := orElim prf1_cxt_fix prf2_cxt_fix
    ans

  | @laxIntro Γ φ prf =>
    -- Lax introduction: zap the inner somehow
    @zapPLLProof Γ φ prf

  | @laxElim Γ φ ψ prf1 prf2 =>
  -- For laxElim, we need multiple casts
  let prf1' := zapPLLProof prf1
  let prf2' := zapPLLProof prf2

/-   -- First, handle the context equality -- um no longer needed
  have h_context1 (Δ : Context):
    image zapSomehow (Γ ∪ Δ) = image zapSomehow Γ ∪ image zapSomehow Δ := by
    simp[image_union] -- simp [image_append]
 -/
  -- handle the formula equality for the first premise
  have h_formula1 : zapSomehow (somehow φ) = zapSomehow φ := by
    simp [zapSomehow]
  -- let prf1_ctx_fix := cast (congrArg (fun x => LaxND x _) h_context1) prf1'
  -- Cast the first premise to match the expected type
  let prf1_fix := cast (congrArg (fun x => LaxND _ x) h_formula1) prf1'

  -- For prf2', we need to handle the context transformation
  -- The context in prf2' is (Γ ++ φ :: Δ), which needs to be transformed to
  -- (image zapSomehow Γ ++ zapSomehow φ :: image zapSomehow Δ)
  have h_context2 : image zapSomehow (Γ ∪ {φ}) =
                    image zapSomehow Γ ∪ {zapSomehow φ} := by
    simp [image_union, image_add_singleton]
  have h_formula2 : zapSomehow (somehow ψ) = zapSomehow ψ := by
    simp [zapSomehow]

  -- Cast prf2' to fix its context
  let prf2_cxt_fix := cast (congrArg (fun x => LaxND x _) h_context2) prf2'
  let prf2_fix := cast (congrArg (fun x => LaxND _ x) h_formula2) prf2_cxt_fix

   -- Now we can use impInContext with the properly cast arguments
  let ans := @impInContext _ (zapSomehow φ) (zapSomehow ψ) prf1_fix prf2_fix -- notice no laxElim
  let ans_fix := cast (congrArg (fun x => LaxND _ x) (Eq.symm h_formula2)) ans

  ans_fix

section Casting

-- 0) good this checks; can we use it?
def congrArg2 {α β γ : Sort*} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
  (ha : a₁ = a₂) (hb : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ :=
by cases ha; cases hb; rfl

-- 1) checks but is useless
lemma cast_congrArg_context_id
  {Γ₁ Γ₂ : Context} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxND Γ₁ φ) :
  cast (congrArg (fun Γ => LaxND Γ φ) h) x = (cast (congrArg (fun Γ => LaxND Γ φ) h) x : LaxND Γ₂ φ) :=
rfl

/- -- 1) nope
lemma cast_congrArg_context_inv
  {Γ₁ Γ₂ : Context} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxND Γ₁ φ) :
  cast (congrArg (fun Γ => LaxND Γ φ) h) x = (cast h x : LaxND Γ₂ φ) :=
by cases h; rfl

-- 2) nope
lemma cast_congrArg_formula_inv
  {Γ : Context} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂) (x : LaxND Γ φ₁) :
  cast (congrArg (fun φ => LaxND Γ φ) h) x = (cast h x : LaxND Γ φ₂) :=
by cases h; rfl
 -/

-- 3) good this works
lemma cast_congrArg_context_cancel
  {Γ₁ Γ₂ : Context} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxND Γ₁ φ) :
  cast (congrArg (fun Γ => LaxND Γ φ) (h.symm)) (cast (congrArg (fun Γ => LaxND Γ φ) h) x) = x :=
by cases h; rfl

-- 4) fixed
lemma cast_congrArg_formula_cancel
  {Γ : Context} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂) (x : LaxND Γ φ₁) :
  cast (congrArg (fun φ => LaxND Γ φ) h.symm) (cast (congrArg (fun φ => LaxND Γ φ) h) x) = x :=
by cases h; rfl

-- 6) good this works
lemma cast_congrArg2_cancel_left
  {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula} (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂)
  (x : LaxND Γ₁ φ₁) :
  cast (congrArg2 LaxND hΓ.symm hφ.symm) (cast (congrArg2 LaxND hΓ hφ) x) = x :=
by cases hΓ; cases hφ; rfl
-- and conversely:
lemma cast_congrArg2_cancel_right
  {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula}
  (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (x : LaxND Γ₂ φ₂) :
  cast (congrArg2 LaxND hΓ hφ) (cast (congrArg2 LaxND hΓ.symm hφ.symm) x) = x :=
by cases hΓ; cases hφ; rfl

-- 5a) good this works
lemma isIPLProof_cast_eq {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula}
  {prf : LaxND Γ₁ φ₁} (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) :
  isIPLProof (cast (congrArg2 LaxND hΓ hφ) prf) = isIPLProof prf :=
by cases hΓ; cases hφ; rfl

/- -- 5b) not yet
theorem isIPLProof_cast_eq {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula}
  {prf : LaxND Γ₁ φ₁} (h : Γ₁ = Γ₂ ∧ φ₁ = φ₂) :
  isIPLProof (cast (congrArg2 LaxND h.1 h.2) prf) = isIPLProof prf := by
  cases h with | h_left h_right =>
  subst h_left
  subst h_right
  simp

-- 5c) nope
theorem isIPLProof_cast_eq {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula}
  {prf : LaxND Γ₁ φ₁} (h : Γ₁ = Γ₂ ∧ φ₁ = φ₂) :
  isIPLProof (cast (by simp [h.1, h.2]) prf) = isIPLProof prf := by
  cases h
  subst h_left
  subst h_right
  simp
 -/

def cast_ctx {Γ₁ Γ₂ : Context} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxND Γ₁ φ) : LaxND Γ₂ φ :=
  cast (congrArg (fun Γ => LaxND Γ φ) h) x

def cast_formula {Γ : Context} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂) (x : LaxND Γ φ₁) : LaxND Γ φ₂ :=
  cast (congrArg (fun φ => LaxND Γ φ) h) x

def cast_both {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula} (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (x : LaxND Γ₁ φ₁) : LaxND Γ₂ φ₂ :=
  cast (congrArg2 LaxND hΓ hφ) x

@[simp]
lemma cast_ctx_cancel {Γ₁ Γ₂ : Context} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxND Γ₁ φ) :
  cast_ctx h.symm (cast_ctx h x) = x :=
by cases h; rfl

@[simp]
lemma cast_formula_cancel {Γ : Context} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂) (x : LaxND Γ φ₁) :
  cast_formula h.symm (cast_formula h x) = x :=
by cases h; rfl

@[simp]
lemma cast_both_cancel_left {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula}
  (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (x : LaxND Γ₁ φ₁) :
  cast_both hΓ.symm hφ.symm (cast_both hΓ hφ x) = x :=
by cases hΓ; cases hφ; rfl

@[simp]
lemma cast_both_cancel_right {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula}
  (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (x : LaxND Γ₂ φ₂) :
  cast_both hΓ hφ (cast_both hΓ.symm hφ.symm x) = x :=
by cases hΓ; cases hφ; rfl

@[simp]
lemma isIPLProof_cast_ctx_eq {Γ₁ Γ₂ : Context} {φ : PLLFormula}
  {prf : LaxND Γ₁ φ} (hΓ : Γ₁ = Γ₂) :
  isIPLProof (cast_ctx hΓ prf) = isIPLProof prf :=
by cases hΓ; rfl

@[simp]
lemma isIPLProof_cast_formula_eq {Γ : Context} {φ₁ φ₂ : PLLFormula}
  {prf : LaxND Γ φ₁} (hφ : φ₁ = φ₂) :
  isIPLProof (cast_formula hφ prf) = isIPLProof prf :=
by cases hφ; rfl

@[simp]
lemma isIPLProof_cast_both_eq {Γ₁ Γ₂ : Context} {φ₁ φ₂ : PLLFormula}
  {prf : LaxND Γ₁ φ₁} (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) :
  isIPLProof (cast_both hΓ hφ prf) = isIPLProof prf :=
by cases hΓ; cases hφ; rfl

@[simp]
lemma cast_iden {Γ Γ' : Context} {φ φ' : PLLFormula}
   (hφ : φ = φ') (hΓ : Γ ∪ {φ} = Γ' ∪ {φ'}) :
  cast (congrArg2 LaxND hΓ hφ) (iden Γ φ) = iden Γ' φ' :=
  sorry -- by cases hΓ; cases hφ; rfl
end Casting

-- universe u -- for the next theorem, will be deleted later

-- this is the main theorem
theorem PLLconservative : {Γ : Context} → {φ : PLLFormula} → (prf : LaxND Γ φ) →
  isIPLProof (zapPLLProof prf) := by
  intros Γ φ prf; -- unfold isIPLProofList
  -- let tmp := zapPLLProof prf -- no we have this already
  -- simp
  induction prf
  case iden Γ' φ' =>
    -- unfold isIPLProofList
    simp [zapSomehow, zapPLLProof, isIPLFormula, isIPLProof/- , cast_eq -/];
    have h : isIPLProof (iden (image zapSomehow Γ') (zapSomehow φ')) := by
      simp
    norm_cast at h; -- did nothing but didn't fail
    simp at h -- [isIPLProof_cast_formula_eq, isIPLProof_cast_ctx_eq] -- already in simp
    -- well that did something to the context but not the goal which is what we want
    have k {α β : Sort}{casting : α = β}(f : α)(g : β) : -- totally unsound!
      /- (iden (image zapSomehow Γ') (zapSomehow φ')) -/ g =
      (cast casting /- (iden (image zapSomehow Γ') (zapSomehow φ')) -/ f) := by sorry
    -- let dodgy := k (iden (image zapSomehow Γ') (zapSomehow φ')) ((iden (image zapSomehow Γ') (zapSomehow φ')))

    -- let tmp := isIPLProofList_cast _ _ h
    -- apply isIPLProofList_cast
  --  simp[h]
  --  simp only [cast_eq]
    sorry

  -- unfold isIPLFormula
  -- simp; unfold zapPLLProof; simp
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
def impInContextList : {Γ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDListτ Γ φ → LaxNDListτ (φ :: Γ) ψ → LaxNDListτ Γ ψ := by
      intros Γ φ ψ prf1 prf2
      apply @impElimτ _ φ ψ
      apply impIntroτ prf2;
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

def zapPLLProofList {Γ : List PLLFormula} {φ : PLLFormula} (h : LaxNDListτ Γ φ) :
  LaxNDListτ (List.map zapSomehow Γ) (zapSomehow φ) :=
  match h with
  | moveτ Γ Δ φ ψ prf =>
    -- Handle the move/exchange rule by recursively erasing the inner proof
    let prf' := zapPLLProofList prf
    have mapCxt : List.map zapSomehow (φ :: Γ ++ Δ) =
      zapSomehow φ :: List.map zapSomehow Γ ++ List.map zapSomehow Δ := by
      simp [List.map_append, List.map_cons]
    let castingPush := cast (congrArg (fun x => LaxNDListτ x _) mapCxt)
    let prfCxtFix := castingPush prf'
    have reduced : (zapSomehow φ :: List.map zapSomehow Γ ++ List.map zapSomehow Δ) ⊢τ zapSomehow ψ := prfCxtFix
    let mover := moveτ (List.map zapSomehow Γ) (List.map zapSomehow Δ) (zapSomehow φ) (zapSomehow ψ)
    let moved := mover reduced
    have mapInvCxt : (List.map zapSomehow Γ ++ zapSomehow φ :: List.map zapSomehow Δ) =
      List.map zapSomehow (Γ ++ φ :: Δ) := by
      simp [List.map_append, List.map_cons]
    let castingPull := cast (congrArg (fun x => LaxNDListτ x _) mapInvCxt)
    let final := castingPull moved
    final

  | idenτ Γ φ =>
    -- Handle identity rule: Γ ++ φ :: Δ ⊢ φ becomes zap(Γ) ++ zap(φ) :: zap(Δ) ⊢ zap(φ)
    let Γ' := List.map zapSomehow Γ
    -- let Δ' := List.map zapSomehow Δ
    let φ' := zapSomehow φ
    -- how do we actually use definitions above to simplify statement of h1?
    have h1 : List.map zapSomehow (φ ::Γ) = zapSomehow φ :: List.map zapSomehow Γ := by
      simp[List.map_append, List.map_cons]
    cast (congrArg (fun x => LaxNDListτ x _) (Eq.symm h1))
        (idenτ (List.map zapSomehow Γ) (zapSomehow φ))

  | @impIntroτ Γ φ ψ prf =>
    -- Implication introduction: Γ ++ Δ ⊢ φ → ψ becomes zap(Γ) ++ zap(Δ) ⊢ zap(φ) → zap(ψ)
    impIntroτ (zapPLLProofList prf)

  | falsoElimτ φ prf =>
    -- False elimination: Γ ⊢ ⊥ → Γ ⊢ φ becomes zap(Γ) ⊢ ⊥ → zap(Γ) ⊢ zap(φ)
    falsoElimτ (zapSomehow φ) (zapPLLProofList prf)

  | impElimτ prf1 prf2 =>
    -- Implication elimination: Combine zapd proofs
    impElimτ (zapPLLProofList prf1) (zapPLLProofList prf2)

  | andIntroτ prf1 prf2 =>
    -- Conjunction introduction: Combine zapd proofs
    andIntroτ (zapPLLProofList prf1) (zapPLLProofList prf2)

  | andElim1τ prf =>
    -- Conjunction elimination (left)
    andElim1τ (zapPLLProofList prf)

  | andElim2τ prf =>
    -- Conjunction elimination (right)
    andElim2τ (zapPLLProofList prf)

  | orIntro1τ prf =>
    -- Disjunction introduction (left)
    orIntro1τ (zapPLLProofList prf)

  | orIntro2τ prf =>
    -- Disjunction introduction (right)
    orIntro2τ (zapPLLProofList prf)

  | @orElimτ Γ φ ψ χ prf1 prf2 =>
    -- Disjunction elimination: Combine zapd proofs
    let prf1' := zapPLLProofList prf1
    let prf2' := zapPLLProofList prf2
    have h1 : List.map zapSomehow (φ :: Γ) =
      zapSomehow φ ::List.map zapSomehow Γ := by
      simp [zapSomehow, List.map_append]
    let prf1_cxt_fix := cast (congrArg (fun x => LaxNDListτ x _) h1) prf1'
    have h2 : List.map zapSomehow (ψ :: Γ) =
      zapSomehow ψ :: List.map zapSomehow Γ := by
      simp [zapSomehow, List.map_append]
    let prf2_cxt_fix := cast (congrArg (fun x => LaxNDListτ x _) h2) prf2'
    let ans := orElimτ prf1_cxt_fix prf2_cxt_fix
    ans

  | @laxIntroτ Γ φ prf =>
    -- Lax introduction: zap the inner somehow
    @zapPLLProofList Γ φ prf

  | @laxElimτ Γ φ ψ prf1 prf2 =>
  -- For laxElimτ, we need multiple casts
  let prf1' := zapPLLProofList prf1
  let prf2' := zapPLLProofList prf2

  -- Handle the formula equality for the first premise
  have h_formula1 : zapSomehow (somehow φ) = zapSomehow φ := by
    simp [zapSomehow]
  -- Cast the first premise to match the expected type
  let prf1_fix := cast (congrArg (fun x => LaxNDListτ _ x) h_formula1) prf1'

  -- For prf2', we need to handle the context transformation
  -- The context in prf2' is List.map zapSomehow (φ :: Γ),
  -- which needs to be transformed to
  -- zapSomehow φ :: List.map zapSomehow Γ
  have h_context2 : List.map zapSomehow (φ :: Γ) =
                    zapSomehow φ :: List.map zapSomehow Γ := by
    simp [List.map_append]
  have h_formula2 : zapSomehow (somehow ψ) = zapSomehow ψ := by
    simp [zapSomehow]

  -- Cast prf2' to fix its context
  let prf2_cxt_fix := cast (congrArg (fun x => LaxNDListτ x _) h_context2) prf2'
  let prf2_fix := cast (congrArg (fun x => LaxNDListτ _ x) h_formula2) prf2_cxt_fix

   -- Now we can use impInContext with the properly cast arguments
  let ans := impInContextList prf1_fix prf2_fix -- notice no laxElimτ
  -- imvert h_formula2 and apply the cast
  let ans_fix := cast (congrArg (fun x => LaxNDListτ _ x) (Eq.symm h_formula2)) ans

  ans_fix

end recursors

-- the construction below would show conservativity but for the issue with recursor 'LaxNDListτ.rec'
/- def zapPLLProofFail {Γ : List PLLFormula} {φ : PLLFormula}
  (h : LaxNDListτ Γ φ) :
  LaxNDListτ (List.map zapSomehow Γ) (zapSomehow φ) := by
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
-- @[norm_cast]
theorem zapSomehow_context (Γ Δ : List PLLFormula) :
  List.map zapSomehow (Γ ++ Δ) = List.map zapSomehow Γ ++ List.map zapSomehow Δ := by
  simp [List.map_append]

-- @[norm_cast]
theorem zapSomehow_somehow (φ : PLLFormula) :
  zapSomehow (somehow φ) = zapSomehow φ := by
  simp [zapSomehow]

/- theorem isIPLProofList_cast_eq {Γ₁ Γ₂ : List PLLFormula} {φ₁ φ₂ : PLLFormula}
  {prf : LaxNDListτ Γ₁ φ₁} (h : Γ₁ = Γ₂ ∧ φ₁ = φ₂) :
  isIPLProofList (cast (by simp [h.1, h.2]) prf) = isIPLProofList prf := by
  cases h
  subst h_left
  subst h_right
  simp -/

end Casting

-- this is the main theorem; not working yet
theorem PLLconservative2 : {Γ : List PLLFormula} → {φ : PLLFormula} → (prf : LaxNDListτ Γ φ) →
  isIPLProofList (zapPLLProofList prf) := by
  intros Γ φ prf; -- unfold isIPLProofList
  -- let tmp := zapPLLProof prf -- no we have this already
  -- simp
  induction prf
  case idenτ Γ' φ' =>
    -- unfold isIPLProofList
    simp [zapSomehow, zapPLLProof, isIPLFormula, isIPLProofList/- , cast_eq -/]
    have h : isIPLProofList (idenτ (List.map zapSomehow Γ') (zapSomehow φ')) := by
      simp
    exact h
    -- norm_cast at h -- THIS SOLVED THE GOAL!! but so did exact h

  case falsoElimτ Γ' φ' p =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    exact p

  case moveτ Γ Δ  φ ψ  p ih  =>

    have hEq :  p = (moveτ Γ Δ φ ψ p) := by sorry
    rw [← hEq]





  --  | moveτ (Γ Δ : List PLLFormula)  (φ ψ : PLLFormula)
  --     (p : LaxNDListτ (φ :: (Γ ++ Δ)) ψ) : LaxNDListτ (Γ ++ φ :: Δ) ψ

    have hEq : Γ' = moveτ φ Δ prf ψ Γ' := by sorry







    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList, cast,   moveτ, List.map, zapSomehow  ]





  case impIntroτ =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    trivial

  case impElimτ prf1 prf2 =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    trivial

  case andIntroτ prf1 prf2 =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    trivial

  case andElim1τ prf =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    exact prf

  case andElim2τ prf =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    exact prf

  case orIntro1τ prf =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    exact prf

  case orIntro2τ prf =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    exact prf

  case orElimτ prf1 prf2 =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    trivial

  case laxIntroτ prf =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    exact prf

  case laxElimτ prf1 prf2 =>
    simp [zapSomehow, zapPLLProofList, isIPLFormula, isIPLProofList]
    constructor;exact prf2; exact prf1

end Conservativity
