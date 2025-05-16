import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom

open PLLFormula

inductive LaxND : (List PLLFormula)→ PLLFormula → Prop -- Natural deduction for PLL
--  | atom : (Γ Δ : List PLLFormula) → (a : String) → LaxND (Γ ++ [prop a] ++ Δ) (prop a)
-- this first is not sufficiently general
  | iden : (Γ Δ : List PLLFormula) → (φ : PLLFormula) → LaxND (Γ ++ [φ] ++ Δ) φ
  | falsoElim : {Γ : List PLLFormula} → (φ : PLLFormula) → LaxND Γ falsePLL → LaxND Γ φ
  | impIntro : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxND (Γ ++ [φ] ++ Δ) ψ → LaxND (Γ ++ Δ) (ifThen φ ψ)
  | impElim  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (ifThen φ ψ) → LaxND Γ φ → LaxND Γ ψ
  | andIntro : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ φ → LaxND Γ ψ → LaxND Γ (and φ ψ)
  | andElim1 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (and φ ψ) → LaxND Γ φ
  | andElim2 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (and φ ψ) → LaxND Γ ψ
  | orIntro1 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ φ → LaxND Γ (or φ ψ)
  | orIntro2 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ ψ → LaxND Γ (or φ ψ)
  | orElim   : {Γ Δ : List PLLFormula} → {φ ψ χ : PLLFormula} →
      LaxND (Γ ++ [φ] ++ Δ) χ →
      LaxND (Γ ++ [ψ] ++ Δ) χ → LaxND (Γ ++ Δ) χ
  | laxIntro : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ φ → LaxND Γ (somehow φ)
  | laxElim : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxND (Γ ++ Δ) (somehow φ) → LaxND (Γ ++ [φ] ++ Δ) (somehow ψ) → LaxND (Γ ++ Δ) (somehow ψ)
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

lemma OMoops {Γ : List PLLFormula} {φ : PLLFormula} : (Γ ++ []) ⊢- ifThen (somehow (somehow φ)) (somehow φ) :=
  impIntro (
    laxElim
      (iden Γ [] (somehow (somehow φ)))
      (iden (Γ ++ [φ.somehow.somehow]) [] (somehow φ))
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
  | idenτ : (Γ Δ : List PLLFormula) → (φ : PLLFormula) → LaxNDτ (Γ ++ [φ] ++ Δ) φ
  | falsoElimτ  : {Γ : List PLLFormula} → (φ : PLLFormula) → LaxNDτ Γ falsePLL → LaxNDτ Γ φ
  | impIntroτ  : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDτ (Γ ++ [φ] ++ Δ) ψ → LaxNDτ (Γ ++ Δ) (ifThen φ ψ)
  | impElimτ   : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (ifThen φ ψ) → LaxNDτ Γ φ → LaxNDτ Γ ψ
  | andIntroτ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ ψ → LaxNDτ Γ (and φ ψ)
  | andElim1τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (and φ ψ) → LaxNDτ Γ φ
  | andElim2τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (and φ ψ) → LaxNDτ Γ ψ
  | orIntro1τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ (or φ ψ)
  | orIntro2τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ ψ → LaxNDτ Γ (or φ ψ)
  | orElimτ    : {Γ Δ : List PLLFormula} → {φ ψ χ : PLLFormula} →
      LaxNDτ (Γ ++ [φ] ++ Δ) χ →
      LaxNDτ (Γ ++ [ψ] ++ Δ) χ → LaxNDτ (Γ ++ Δ) χ
  | laxIntroτ  : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ (somehow φ)
  | laxElimτ  : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDτ (Γ ++ Δ) (somehow φ) → LaxNDτ (Γ ++ [φ] ++ Δ) (somehow ψ) → LaxNDτ (Γ ++ Δ) (somehow ψ)

open LaxNDτ

-- Define what it means for a PLL proof to be an IPL proof
-- more inference could be requested
def isIPLProof : (Γ : List PLLFormula) → (φ : PLLFormula) → LaxNDτ Γ φ → Prop
  | _, _,  idenτ Γ Δ φ     => isIPLFormula φ -- only you could have a proof in IPL using lax formulae
  | _, _,  falsoElimτ _ prf  => isIPLProof _ falsePLL prf
  | _, _,  @impIntroτ Γ Δ φ ψ prf => isIPLProof (Γ ++ [φ] ++ Δ) ψ prf
  | _, _,  @impElimτ Γ _ _ prf1 prf2  => isIPLProof Γ _ prf1 ∧ isIPLProof _ _ prf2
  | _, _,  @andIntroτ _ _ _ prf1 prf2 => isIPLProof _ _ prf1 ∧ isIPLProof _ _ prf2
  | _, _,  @andElim1τ _ _ _ prf     => isIPLProof _ _ prf
  | _, _,  andElim2τ prf => isIPLProof _ _ prf
  | _, _,  orIntro1τ prf => isIPLProof _ _ prf
  | _, _,  orIntro2τ prf => isIPLProof _ _ prf
  | _, _,  orElimτ prf1 prf2 => isIPLProof _ _ prf1 ∧ isIPLProof _ _ prf2
  | _, _,  laxIntroτ _  => false
  | _, _,  laxElimτ _ _ => false

end Conservativity
