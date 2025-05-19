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
      LaxND (Γ ++ [ψ] ++ Δ) χ → LaxND (Γ ++ Δ) χ
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
def isIPLProof : (Γ : List PLLFormula) → (φ : PLLFormula) → (prf : LaxNDτ Γ φ) → Prop
  | _, _,  idenτ Γ Δ φ     => isIPLFormula φ -- only you could have a proof in IPL using lax formulae
  | _, _,  falsoElimτ _ prf  => isIPLProof _ falsePLL prf
  | _, _,  @impIntroτ Γ Δ φ ψ prf => isIPLProof (Γ ++ φ :: Δ) ψ prf
  | _, _,  @impElimτ Γ _ _ prf1 prf2  => isIPLProof Γ _ prf1 ∧ isIPLProof _ _ prf2
  | _, _,  @andIntroτ _ _ _ prf1 prf2 => isIPLProof _ _ prf1 ∧ isIPLProof _ _ prf2
  | _, _,  @andElim1τ _ _ _ prf     => isIPLProof _ _ prf
  | _, _,  andElim2τ prf => isIPLProof _ _ prf
  | _, _,  orIntro1τ prf => isIPLProof _ _ prf
  | _, _,  orIntro2τ prf => isIPLProof _ _ prf
  | _, _,  orElimτ prf1 prf2 => isIPLProof _ _ prf1 ∧ isIPLProof _ _ prf2
  | _, _,  laxIntroτ _  => false
  | _, _,  laxElimτ _ _ => false

@[simp]
def eraseSomehow : PLLFormula → PLLFormula
  | PLLFormula.prop a => prop a
  | falsePLL    => falsePLL
  | ifThen φ ψ  => ifThen (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.and φ ψ     => and (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.or φ ψ      => or (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.somehow φ   => eraseSomehow φ

theorem map_append_distrib {α β : Type} (f : α → β) (xs ys : List α) (z : α):
  List.map f (xs ++ z :: ys) = List.map f xs ++ f z :: List.map f ys := by
  simp [List.map_append]

section recursors

def erasePLLProof {Γ : List PLLFormula} {φ : PLLFormula} (h : LaxNDτ Γ φ) :
  LaxNDτ (List.map eraseSomehow Γ) (eraseSomehow φ) :=
  match h with
  | idenτ G D f =>
    -- Handle identity rule: Γ ++ [φ] ++ Δ ⊢ φ becomes erase(Γ) ++ erase(φ) ++ erase(Δ) ⊢ erase(φ)
    let G' := List.map eraseSomehow G
    let D' := List.map eraseSomehow D
    let f' := eraseSomehow f
    have h1 : List.map eraseSomehow (G ++ f :: D) = G' ++ f' :: D' := by sorry
 /-      simp [List.map_append, List.map_cons]
  -/
    cast h1 (idenτ G' D' f')

  | impIntroτ prf =>
    -- Implication introduction: Γ ++ Δ ⊢ φ → ψ becomes erase(Γ) ++ erase(Δ) ⊢ erase(φ) → erase(ψ)
    let prf' := erasePLLProof prf
    have h1 {Δ : List PLLFormula} : List.map eraseSomehow (Γ ++ Δ) = List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
      simp [List.map_append]
    cast (congrArg (fun x => LaxNDτ x _) h1) (impIntroτ prf')

  | falsoElimτ φ prf =>
    -- False elimination: Γ ⊢ ⊥ → Γ ⊢ φ becomes erase(Γ) ⊢ erase(φ)
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

  | orElimτ prf1 prf2 =>
    -- Disjunction elimination: Combine erased proofs
    let prf1' := erasePLLProof prf1
    let prf2' := erasePLLProof prf2
    have h1 {Δ : List PLLFormula} : List.map eraseSomehow (Γ ++ Δ) = List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
      simp [List.map_append]
    cast (congrArg (fun x => LaxNDτ x _) h1) (orElimτ prf1' prf2')

  | laxIntroτ prf =>
    -- Lax introduction: Erase the inner somehow
    erasePLLProof prf

  | laxElimτ prf1 prf2 =>
    -- Lax elimination: Combine erased proofs
    let prf1' := erasePLLProof prf1
    let prf2' := erasePLLProof prf2
    have h1 : List.map eraseSomehow (Γ ++ Δ) = List.map eraseSomehow Γ ++ List.map eraseSomehow Δ := by
      simp [List.map_append]
    cast (congrArg (fun x => LaxNDτ x _) h1) (impInContext prf1' prf2')

end recursors

-- the construction below would show conservativity but for the issue with recursor 'LaxNDτ.rec'
def erasePLLProof {Γ : List PLLFormula} {φ : PLLFormula}
  (h : LaxNDτ Γ φ) :
  LaxNDτ (List.map eraseSomehow Γ) (eraseSomehow φ) := by
  induction h
  case idenτ G D f =>
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

theorem PLLconservative : (Γ : List PLLFormula) → (φ : PLLFormula) → (prf : LaxNDτ Γ φ) →
  isIPLProof (Γ.map eraseSomehow) (eraseSomehow φ) (erasePLLProof prf) := sorry

end Conservativity
