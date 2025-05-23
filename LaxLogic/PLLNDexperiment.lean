
-- import Mathlib.Tactic.Core
import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom

open PLLFormula

inductive LaxND : (List PLLFormula)→ PLLFormula → Prop -- Natural deduction for PLL
--  | atom : (Γ Δ : List PLLFormula) → (a : String) → LaxND (Γ ++ [prop a] ++ Δ) (prop a)
-- this first is not sufficiently general
  | iden : (Γ Δ : List PLLFormula) → (φ : PLLFormula) → LaxND (Γ ++ φ :: Δ) φ
  | falsoElim : {Γ : List PLLFormula} → (φ : PLLFormula) → LaxND Γ falsePLL → LaxND Γ φ
  | impIntro : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxND (Γ ++ φ :: Δ) ψ → LaxND (Γ ++ Δ) (ifThen φ ψ)
  | impElim  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (ifThen φ ψ) → LaxND Γ φ → LaxND Γ ψ
  | andIntro : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ φ → LaxND Γ ψ → LaxND Γ (and φ ψ)
  | andElim1 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (and φ ψ) → LaxND Γ φ
  | andElim2 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (and φ ψ) → LaxND Γ ψ
  | orIntro1 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ φ → LaxND Γ (or φ ψ)
  | orIntro2 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ ψ → LaxND Γ (or φ ψ)
  | orElim   : {Γ Δ : List PLLFormula} → {φ ψ χ : PLLFormula} →
      LaxND (Γ ++ φ :: Δ) χ →
      LaxND (Γ ++ ψ :: Δ) χ → LaxND (Γ ++ Δ) χ
  | laxIntro : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ φ → LaxND Γ (somehow φ)
  | laxElim : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxND (Γ ++ Δ) (somehow φ) → LaxND (Γ ++ φ :: Δ) (somehow ψ) → LaxND (Γ ++ Δ) (somehow ψ)
--  | laxFlatten : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ (somehow (somehow φ)) → LaxND Γ (somehow φ)
-- this last is derivable

infix:70 " ⊢- " => LaxND -- turnstile

def LaxValid (φ : PLLFormula) : Prop := ([] : List PLLFormula) ⊢- φ

open LaxND

lemma OI (φ : PLLFormula) : [] ⊢- ifThen φ (somehow φ) := impIntro (laxIntro (iden [] [] φ))
lemma OItrue (φ : PLLFormula) : LaxValid <| ifThen φ (somehow φ) := by apply OI

lemma OSL (φ ψ : PLLFormula) : [] ⊢- ifThen (somehow (and φ ψ)) (and (somehow φ) (somehow ψ)) := by
  apply @impIntro [] [] ;
  apply @andIntro;
  apply @laxElim [(φ.and ψ).somehow] [] (φ.and ψ);
  apply iden [] ; apply laxIntro
  apply andElim1 ; apply iden
  apply @laxElim [(φ.and ψ).somehow] [] (φ.and ψ);
  apply iden [] ; apply laxIntro
  apply andElim2 ; apply iden
lemma OSLtrue (φ ψ : PLLFormula) : LaxValid <| ifThen (somehow (and φ ψ)) (and (somehow φ) (somehow ψ)) := by apply OSL

lemma OSR (φ ψ : PLLFormula) : [] ⊢- ifThen (and (somehow φ) (somehow ψ)) (somehow (and φ ψ)) := by
  apply @impIntro [] [] ; -- simp -- makes progress but not needed
  apply @laxElim [φ.somehow.and ψ.somehow] [] φ ; -- simp
  apply andElim1; apply iden []; -- simp
  apply @laxElim [φ.somehow.and ψ.somehow] [φ] ψ ; -- simp
  apply andElim2; apply iden []; -- simp
  apply laxIntro; apply andIntro
  apply iden [φ.somehow.and ψ.somehow, ψ] [] φ
  apply iden [φ.somehow.and ψ.somehow] [φ] ψ   -- note it looks "out of order" but makes same context as above
lemma OSRtrue (φ ψ : PLLFormula) : LaxValid <| ifThen (and (somehow φ) (somehow ψ)) (somehow (and φ ψ)) := by apply OSR

lemma OMoops {Γ : List PLLFormula} {φ : PLLFormula} : (Γ ++ []) /- awk -/⊢- ifThen (somehow (somehow φ)) (somehow φ) :=
  impIntro (
    laxElim
      (iden Γ [] (somehow (somehow φ)))
      (iden Γ [φ.somehow.somehow] (somehow φ))
  )
-- well I did think that way of permuting contexts might throw up problems! simp helps interactively
lemma OM {φ : PLLFormula} : [] ⊢- ifThen (somehow (somehow φ)) (somehow φ) := by
  apply @impIntro [] ; simp;  apply @laxElim [(somehow (somehow φ))] [] (somehow φ) ; simp;
  apply iden [] ; apply iden
lemma OMtrue (φ : PLLFormula) : LaxValid <| ifThen (somehow (somehow φ)) (somehow φ) := by apply OM

section Conservativity

-- Define what it means for a formula to be in IPL (no somehow modality)
def isIPLFormula : PLLFormula → Prop
  | PLLFormula.prop _  => true
  | falsePLL    => true
  | ifThen φ ψ  => isIPLFormula φ ∧ isIPLFormula ψ
  | PLLFormula.and φ ψ => isIPLFormula φ ∧ isIPLFormula ψ
  | PLLFormula.or φ ψ  => isIPLFormula φ ∧ isIPLFormula ψ
  | somehow _   => false

@[match_pattern] -- is this needed, and if so, why?
inductive LaxNDτ: (List PLLFormula)→ PLLFormula → Type -- ND for PLL, proof term version
  | idenτ : (Γ Δ : List PLLFormula) → (φ : PLLFormula) → LaxNDτ (Γ ++ φ :: Δ) φ
  | falsoElimτ  : {Γ : List PLLFormula} → (φ : PLLFormula) → LaxNDτ Γ falsePLL → LaxNDτ Γ φ
  | impIntroτ  : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDτ (Γ ++ φ :: Δ) ψ → LaxNDτ (Γ ++ Δ) (ifThen φ ψ)
  | impElimτ   : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (ifThen φ ψ) → LaxNDτ Γ φ → LaxNDτ Γ ψ
  | andIntroτ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ ψ → LaxNDτ Γ (and φ ψ)
  | andElim1τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (and φ ψ) → LaxNDτ Γ φ
  | andElim2τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (and φ ψ) → LaxNDτ Γ ψ
  | orIntro1τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ (or φ ψ)
  | orIntro2τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ ψ → LaxNDτ Γ (or φ ψ)
  | orElimτ    : {Γ Δ : List PLLFormula} → {φ ψ χ : PLLFormula} →
      LaxNDτ (Γ ++ φ :: Δ) χ →
      LaxNDτ (Γ ++ ψ :: Δ) χ → LaxNDτ (Γ ++ Δ) χ
  | laxIntroτ  : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ (somehow φ)
  | laxElimτ  : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDτ (Γ ++ Δ) (somehow φ) → LaxNDτ (Γ ++ φ :: Δ) (somehow ψ) → LaxNDτ (Γ ++ Δ) (somehow ψ)

open LaxNDτ

-- this next is a kind of Cut rule
def impInContext : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDτ (Γ ++ Δ) φ → LaxNDτ (Γ ++ φ :: Δ) ψ → LaxNDτ (Γ ++ Δ) ψ := by
      intros Γ Δ φ ψ prf1 prf2
      apply @impElimτ _ φ ψ
      apply impIntroτ; exact prf2; exact prf1

-- Define what it means for a PLL proof to be an IPL proof
-- more inference could be requested
@[simp]
def isIPLProof : {Γ : List PLLFormula} → {φ : PLLFormula} → (prf : LaxNDτ Γ φ) → Prop
  | _, _,  idenτ Γ Δ φ     => isIPLFormula φ -- only you could have a proof in IPL using lax formulae
  | _, _,  falsoElimτ _ prf  => isIPLProof prf
  | _, _,  impIntroτ prf => isIPLProof prf
  | _, _,  impElimτ prf1 prf2  => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  andIntroτ prf1 prf2 => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  andElim1τ prf => isIPLProof prf
  | _, _,  andElim2τ prf => isIPLProof prf
  | _, _,  orIntro1τ prf => isIPLProof prf
  | _, _,  orIntro2τ prf => isIPLProof prf
  | _, _,  orElimτ prf1 prf2 => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  laxIntroτ _  => false
  | _, _,  laxElimτ _ _ => false

def isIPLProof_robust {Γ : List PLLFormula} {φ : PLLFormula} (prf : LaxNDτ Γ φ) : Prop :=
  match prf with
  | idenτ Γ Δ φ => isIPLFormula φ
  | _ => false -- very incomplete and next fails
 -- | cast _ prf' => isIPLProof_robust prf'
  -- Other cases

-- @[simp]
theorem isIPLProof_cast {Γ₁ Γ₂ : List PLLFormula} {φ₁ φ₂ : PLLFormula}
  {prf₁ : LaxNDτ Γ₁ φ₁} {prf₂ : LaxNDτ Γ₂ φ₂}
  (h_ctx : Γ₁ = Γ₂) (h_form : φ₁ = φ₂) (h_cast : cast (by simp [h_ctx, h_form]) prf₁ = prf₂) :
  isIPLProof prf₁ = isIPLProof prf₂ := by
  subst h_ctx
  subst h_form
  subst h_cast
  rfl

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

theorem map_append_distrib {α β : Type} (f : α → β) (xs ys : List α) (z : α):
  List.map f (xs ++ z :: ys) = List.map f xs ++ f z :: List.map f ys := by
  simp [List.map_append]

section recursors

def erasePLLProof {Γ : List PLLFormula} {φ : PLLFormula} (h : LaxNDτ Γ φ) :
  LaxNDτ (List.map eraseSomehow Γ) (eraseSomehow φ) :=
  match h with
  | idenτ Γ Δ φ =>
    -- Handle identity rule: Γ ++ φ :: Δ ⊢ φ becomes erase(Γ) ++ erase(φ) :: erase(Δ) ⊢ erase(φ)
    let Γ' := List.map eraseSomehow Γ
    let Δ' := List.map eraseSomehow Δ
    let φ' := eraseSomehow φ
    -- how do we actually use definitions above to simplify statement of h1?
    have h1 : List.map eraseSomehow (Γ ++ φ :: Δ) = List.map eraseSomehow Γ ++ eraseSomehow φ :: List.map eraseSomehow Δ := by -- sorry -- make general lemma outside
      simp[List.map_append, List.map_cons]
    cast (congrArg (fun x => LaxNDτ x _) (Eq.symm h1))
        (idenτ (List.map eraseSomehow Γ) (List.map eraseSomehow Δ) (eraseSomehow φ))

  | @impIntroτ Γ Δ φ ψ prf =>
    -- Implication introduction: Γ ++ Δ ⊢ φ → ψ becomes erase(Γ) ++ erase(Δ) ⊢ erase(φ) → erase(ψ)
    let prf' := erasePLLProof prf
    have h1 : List.map eraseSomehow (Γ ++ φ :: Δ) = List.map eraseSomehow Γ ++ eraseSomehow φ :: List.map eraseSomehow Δ := by
      simp [List.map_append]
    let prf_fix := cast (congrArg (fun x => LaxNDτ x _) h1) prf'

    -- now need to fix up proof term to match expected return type; at least 2 more casts needed
    let ans := impIntroτ prf_fix
    have h2 : List.map eraseSomehow (Γ ++ Δ) =
      List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
      simp [List.map_append]
    let ans_ctx_fix := cast (congrArg (fun x => LaxNDτ x _) (Eq.symm h2)) ans
    -- not required -- have h_formula : eraseSomehow (φ.ifThen ψ) = (eraseSomehow φ).ifThen (eraseSomehow ψ) := by simp
    ans_ctx_fix

  | falsoElimτ φ prf =>
    -- False elimination: Γ ⊢ ⊥ → Γ ⊢ φ becomes erase(Γ) ⊢ ⊥ → erase(Γ) ⊢ erase(φ)
    falsoElimτ (eraseSomehow φ) (erasePLLProof prf)

  | impElimτ prf1 prf2 =>
    -- Implication elimination: Combine erased proofs
    impElimτ (erasePLLProof prf1) (erasePLLProof prf2)

  | andIntroτ prf1 prf2 =>
    -- Conjunction introduction: Combine erased proofs
    andIntroτ (erasePLLProof prf1) (erasePLLProof prf2)

  | andElim1τ prf =>
    -- Conjunction elimination (left)
    andElim1τ (erasePLLProof prf)

  | andElim2τ prf =>
    -- Conjunction elimination (right)
    andElim2τ (erasePLLProof prf)

  | orIntro1τ prf =>
    -- Disjunction introduction (left)
    orIntro1τ (erasePLLProof prf)

  | orIntro2τ prf =>
    -- Disjunction introduction (right)
    orIntro2τ (erasePLLProof prf)

  | @orElimτ Γ Δ φ ψ χ prf1 prf2 =>
    -- Disjunction elimination: Combine erased proofs
    let prf1' := erasePLLProof prf1
    let prf2' := erasePLLProof prf2
    have h1 : List.map eraseSomehow (Γ ++ φ :: Δ) =
      List.map eraseSomehow Γ ++ eraseSomehow φ ::List.map eraseSomehow Δ := by
      simp [eraseSomehow, List.map_append]
    let prf1_cxt_fix := cast (congrArg (fun x => LaxNDτ x _) h1) prf1'
    have h2 {Δ : List PLLFormula} : List.map eraseSomehow (Γ ++ Δ) =
      List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
      simp [List.map_append]
    let prf2_cxt_fix := cast (congrArg (fun x => LaxNDτ x _) h2) prf2'

    -- explicit arguments make no difference
    -- @orElimτ (List.map eraseSomehow Γ) (List.map eraseSomehow Δ) (eraseSomehow φ) (eraseSomehow ψ) (eraseSomehow χ)
    let ans := orElimτ prf1_cxt_fix prf2_cxt_fix
    let ans_cxt_fix := cast (congrArg (fun x => LaxNDτ x _) (Eq.symm h2)) ans
    ans_cxt_fix

  | @laxIntroτ Γ φ prf =>
    -- Lax introduction: Erase the inner somehow
    @erasePLLProof Γ φ prf

  | @laxElimτ Γ Δ φ ψ prf1 prf2 =>
  -- For laxElimτ, we need multiple casts
  let prf1' := erasePLLProof prf1
  let prf2' := erasePLLProof prf2

  -- First, handle the context equality
  have h_context1 : List.map eraseSomehow (Γ ++ Δ) = List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
    simp [List.map_append]

  -- Then, handle the formula equality for the first premise
  have h_formula1 : eraseSomehow (somehow φ) = eraseSomehow φ := by
    simp [eraseSomehow]
  let prf1_ctx_fix := cast (congrArg (fun x => LaxNDτ x _) h_context1) prf1'
  -- Cast the first premise to match the expected type
  let prf1_fix := cast (congrArg (fun x => LaxNDτ _ x) h_formula1) prf1_ctx_fix

  -- For prf2', we need to handle the context transformation
  -- The context in prf2' is (Γ ++ φ :: Δ), which needs to be transformed to
  -- (List.map eraseSomehow Γ ++ eraseSomehow φ :: List.map eraseSomehow Δ)
  have h_context2 : List.map eraseSomehow (Γ ++ φ :: Δ) =
                    List.map eraseSomehow Γ ++ eraseSomehow φ :: List.map eraseSomehow Δ := by
    simp [List.map_append]
  have h_formula2 : eraseSomehow (somehow ψ) = eraseSomehow ψ := by
    simp [eraseSomehow]

  -- Cast prf2' to fix its context
  let prf2_cxt_fix := cast (congrArg (fun x => LaxNDτ x _) h_context2) prf2'
  let prf2_fix := cast (congrArg (fun x => LaxNDτ _ x) h_formula2) prf2_cxt_fix

   -- Now we can use impInContext with the properly cast arguments
  let ans := impInContext prf1_fix prf2_fix -- notice no laxElimτ
  -- imvert h1_contezt and h_formula2 and put them together
  let ans_cxt_fix := cast (congrArg (fun x => LaxNDτ x _) (Eq.symm h_context1)) ans
  let ans_fix := cast (congrArg (fun x => LaxNDτ _ x) (Eq.symm h_formula2)) ans_cxt_fix

  ans_fix

end recursors

-- the construction below would show conservativity but for the issue with recursor 'LaxNDτ.rec'
/- def erasePLLProofFail {Γ : List PLLFormula} {φ : PLLFormula}
  (h : LaxNDτ Γ φ) :
  LaxNDτ (List.map eraseSomehow Γ) (eraseSomehow φ) := by
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

@[simp]
lemma isIPLerase (φ : PLLFormula) : isIPLFormula (eraseSomehow φ) := by
  induction φ
  all_goals simp [isIPLFormula]
  constructor; assumption; assumption
  constructor; assumption; assumption
  constructor; assumption; assumption
  assumption

-- variable (α β : Sort)
@[norm_cast] theorem eraseSomehow_context (Γ Δ : List PLLFormula) :
  List.map eraseSomehow (Γ ++ Δ) = List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
  simp [List.map_append]

@[norm_cast] theorem eraseSomehow_somehow (φ : PLLFormula) :
  eraseSomehow (somehow φ) = eraseSomehow φ := by
  simp [eraseSomehow]

theorem isIPLProof_cast_eq {Γ₁ Γ₂ : List PLLFormula} {φ₁ φ₂ : PLLFormula}
  {prf : LaxNDτ Γ₁ φ₁} (h : Γ₁ = Γ₂ ∧ φ₁ = φ₂) :
  isIPLProof (cast (by simp [h.1, h.2]) prf) = isIPLProof prf := by
  cases h
  subst h_left
  subst h_right
  simp

end Casting

-- this is the main theorem
theorem PLLconservative : {Γ : List PLLFormula} → {φ : PLLFormula} → (prf : LaxNDτ Γ φ) →
  isIPLProof (erasePLLProof prf) := by
  intros Γ φ prf; -- unfold isIPLProof
  -- let tmp := erasePLLProof prf -- no we have this already
  -- simp
  induction prf
  case idenτ Γ' Δ' φ' =>
    -- unfold isIPLProof
    simp [eraseSomehow, erasePLLProof, isIPLFormula, isIPLProof/- , cast_eq -/];
    have h : isIPLProof (idenτ (List.map eraseSomehow Γ') (List.map eraseSomehow Δ') (eraseSomehow φ')) := by
      simp
    norm_cast at h;
    have k {α β : Sort}{casting : α = β} :
      (idenτ (List.map eraseSomehow Γ') (List.map eraseSomehow Δ') (eraseSomehow φ')) =
      (cast casting (idenτ (List.map eraseSomehow Γ') (List.map eraseSomehow Δ') (eraseSomehow φ')))
    let tmp := isIPLProof_cast _ _ h
    -- apply isIPLProof_cast
  --  simp[h]
  --  simp only [cast_eq]
    sorry

  -- unfold isIPLFormula
  -- simp; unfold erasePLLProof; simp
  all_goals sorry

end Conservativity
