import LaxLogic.PLLFormula

open PLLFormula

@[match_pattern]
inductive PLLAxiom where
-- Axioms for the modal "somehow" operator
  | somehowR (M: PLLFormula)
  | somehowM (M: PLLFormula)
  | somehowS (M N: PLLFormula)
-- Axioms for propositional intuitionistic
  | impK (A B: PLLFormula)
  | impS (A B C: PLLFormula)
  | andElim1 (A B: PLLFormula)
  | andElim2 (A B: PLLFormula)
  | andIntro (A B: PLLFormula)
  | orIntro1 (A B: PLLFormula)
  | orIntro2 (A B: PLLFormula)
  | orElim (A B C: PLLFormula)
  | explosion (A: PLLFormula)
  deriving Inhabited, DecidableEq, BEq


inductive IntuitionisticAxiom where
-- Axioms for propositional intuitionistic
  | impK (A B: SomehowFree)
  | impS (A B C: SomehowFree)
  | andElim1 (A B: SomehowFree)
  | andElim2 (A B: SomehowFree)
  | andIntro (A B: SomehowFree)
  | orIntro1 (A B: SomehowFree)
  | orIntro2 (A B: SomehowFree)
  | orElim (A B C: SomehowFree)
  | explosion (A: SomehowFree)

def IntuitionisticAxiom.toPLLAxiom (iAx: IntuitionisticAxiom) : PLLAxiom :=
  match iAx with
  | impK A B => PLLAxiom.impK A.val B.val
  | impS A B C => PLLAxiom.impS A.val B.val C.val
  | andElim1 A B => PLLAxiom.andElim1 A.val B.val
  | andElim2 A B  => PLLAxiom.andElim2 A.val B.val
  | andIntro A B  => PLLAxiom.andIntro A.val B.val
  | orIntro1 A B  => PLLAxiom.orIntro1 A.val B.val
  | orIntro2 A B  => PLLAxiom.orIntro2 A.val B.val
  | orElim A B C  => PLLAxiom.orElim A.val B.val C.val
  | explosion A  => PLLAxiom.explosion A.val

namespace PLLAxiom

-- An PLLAxiom axiom is intuitionistic if it could arise from intuitionistic axiom being sent PLL Axioms.
def isIntuitionistPLLAxiom (ax: PLLAxiom) := ∃ (iAx: IntuitionisticAxiom), ax = iAx.toPLLAxiom

def IntuitionisticPLLAxiom := {ax: PLLAxiom | isIntuitionistPLLAxiom ax  }


-- Gets a list of the formulas used to generate an axiom
@[simp]
def formulas (ax: PLLAxiom) : List PLLFormula :=
  match ax with
  | somehowR M => [M]
  | somehowM M => [M]
  | somehowS M N => [M,N]
  | impK A B => [A,B]
  | impS A B C => [A,B,C]
  | andElim1 A B => [A,B]
  | andElim2 A B => [A,B]
  | andIntro A B => [A,B]
  | orIntro1 A B => [A,B]
  | orIntro2 A B => [A,B]
  | orElim A B C => [A,B,C]
  | explosion A => [A]



-- Gets the formula for the axiom

def get (ax: PLLAxiom): PLLFormula :=
  match ax with
    | somehowR M => ifThen M (somehow M)
    | somehowM M => ifThen (somehow (somehow M)) (somehow M)
    | somehowS M N => ifThen (and (somehow M) (somehow N)) (somehow (and M N))
-- standard axioms for propositional intuitionistic logic, source: https://homepage.mi-ras.ru/~sk/lehre/penn2017/lecture1.pdf
  -- 1. A ⊃ (B ⊃ A)
    | impK A B =>  ifThen A (ifThen B A)
  -- 2. (A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))
    | impS A B C => ifThen (ifThen A (ifThen B C)) (ifThen (ifThen A B) (ifThen A C))
  -- 3. (A ∧ B) ⊃ A
    | andElim1 A B => ifThen (and A B) A
  -- 4. (A ∧ B) ⊃ B
    | andElim2 A B => ifThen (and A B) B
  -- 5. A ⊃ (B ⊃ (A ∧ B))
    | andIntro A B => ifThen A (ifThen B (and A B))
  -- 6. A ⊃ (A ∨ B)
    | orIntro1 A B => ifThen A (or A B)
  -- 7. B ⊃ (A ∨ B)
    | orIntro2 A B => ifThen B (or A B)
  -- 8. (A ⊃ C) ⊃ ((B ⊃ C) ⊃ ((A ∨ B) ⊃ C))
    | orElim A B C=> ifThen (ifThen A C) (ifThen (ifThen B C) (ifThen (and A B) C))
  -- 9. ⊥ ⊃ A
    | explosion A => ifThen falsePLL A

-- This only used for printing proofs
def getName (ax: PLLAxiom) : String :=
match ax with
  | somehowR _  => "◯R"
  | somehowM _  => "◯M"
  | somehowS _ _  => "◯S"
  | impK _ _  => "⊃K"
  | impS _ _ _  => "⊃S"
  | andElim1 _ _  => "∧E₁"
  | andElim2 _ _  => "∧E₂"
  | andIntro _ _  => "∧I"
  | orIntro1 _ _  => "∨I₁"
  | orIntro2 _ _  => "∨I₂"
  | orElim _ _ _  => "∨E"
  | explosion _  => "ex falso"



-- THEOREMS  ---


@[simp] lemma or_dedup3 {p q r : Prop} :
    ((p ∨ q ∨ r) ∨ (p ∨ q) ∨ p ∨ r) ↔ (p ∨ q ∨ r) := by
  tauto

@[simp] lemma or_dedup2 {p q r : Prop} :
    ((p ∨ q) ∨ p ∨ r) ↔ (p ∨ q ∨ r) := by
  tauto

@[simp] lemma or_absorb_left  {p q : Prop} :  p ∨ (p ∨ q) ↔ p ∨ q := by
  tauto

@[simp] lemma or_absorb_right {p q : Prop} : (p ∨ q) ∨ p ↔ p ∨ q := by
  tauto

@[simp] lemma or_self  {p : Prop} : p ∨ p ↔ p := by
  tauto
@[simp] lemma or_comm   {p q : Prop}    : p ∨ q ↔ q ∨ p := by
  tauto
@[simp] lemma or_left_comm {p q r : Prop} : p ∨ q ∨ r ↔ q ∨ p ∨ r := by
  tauto
@[simp] lemma or_assoc  {p q r : Prop}    : (p ∨ q) ∨ r ↔ p ∨ q ∨ r := by
  tauto


lemma intu_ax_to_pll_ax_somehow_free  (iAx: IntuitionisticAxiom) : iAx.toPLLAxiom.get.isSomehowFree := by
  simp
  intro F subF G cn
  subst cn
  induction iAx with
   |impK A B =>
      simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
      have hA := A.prop
      have hB := B.prop
      simp_all [isSomehowFree]
      rcases subF with hGA | hGB
      all_goals (try have hA_contra := hA (G.somehow) hGA G)
      all_goals (try have hB_contra := hB (G.somehow) hGB G)
      all_goals (try contradiction )
   |impS A B C  =>
    simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
    have hA := A.prop
    have hB := B.prop
    have hC := C.prop
    simp_all [isSomehowFree]
    rcases subF with h |  h | h
    all_goals try have hA_contra := hA G.somehow h G
    all_goals try have hB_contra := hB G.somehow h G
    all_goals try have hC_contra := hC G.somehow h G
    all_goals try contradiction
   |andElim1 A B =>
     simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
     have hA := A.prop
     have hB := B.prop
     simp_all [isSomehowFree]
     rcases subF with h | h
     all_goals (try have hA_contra := hA (G.somehow) h G)
     all_goals (try have hB_contra := hB (G.somehow) h G)
     all_goals ( contradiction )
   |andElim2 A B =>
      simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
      have hA := A.prop
      have hB := B.prop
      simp_all [isSomehowFree]
      rcases subF with h | h
      all_goals (try have hA_contra := hA (G.somehow) h G)
      all_goals (try have hB_contra := hB (G.somehow) h G)
      all_goals ( contradiction )
   |andIntro A B  =>
      simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
      have hA := A.prop
      have hB := B.prop
      simp_all [isSomehowFree]
      rcases subF with h | h
      all_goals (try have hA_contra := hA (G.somehow) h G)
      all_goals (try have hB_contra := hB (G.somehow) h G)
      all_goals ( contradiction )
   |orIntro1 A B =>
      simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
      have hA := A.prop
      have hB := B.prop
      simp_all [isSomehowFree]
      rcases subF with h | h
      all_goals (try have hA_contra := hA (G.somehow) h G)
      all_goals (try have hB_contra := hB (G.somehow) h G)
      all_goals ( contradiction )
   |orIntro2 A B =>
      simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
      have hA := A.prop
      have hB := B.prop
      simp_all [isSomehowFree]
      rcases subF with h | h
      all_goals (try have hA_contra := hA (G.somehow) h G)
      all_goals (try have hB_contra := hB (G.somehow) h G)
      all_goals ( contradiction )
   |orElim A B C  =>
    simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
    have hA := A.prop
    have hB := B.prop
    have hC := C.prop
    simp_all [isSomehowFree]
    rcases subF with h |  h | h
    all_goals try have hA_contra := hA G.somehow h G
    all_goals try have hB_contra := hB G.somehow h G
    all_goals try have hC_contra := hC G.somehow h G
    all_goals try contradiction
   |explosion A  =>
      simp [IntuitionisticAxiom.toPLLAxiom, get, subformulasOf] at subF
      have hA := A.prop
      simp_all [isSomehowFree]
      have hA_contra := hA G.somehow subF  G
      contradiction


lemma intu_ax_somehow_free (iAx: IntuitionisticPLLAxiom) : iAx.val.get.isSomehowFree := by
  intro subF cn
  simp at cn
  obtain ⟨P, h ⟩ := cn
  obtain ⟨ax, isIntuAx⟩ := iAx
  simp [IntuitionisticPLLAxiom, isIntuitionistPLLAxiom] at isIntuAx
  obtain ⟨iAx, hIAx ⟩ := isIntuAx
  have h := intu_ax_to_pll_ax_somehow_free iAx
  subst hIAx
  obtain ⟨F, isSubF ⟩ := subF
  simp at isSubF
  subst h
  simp_all only [isSomehowFree, isSomehowFormula, not_exists, Subtype.forall]
  apply h
  · exact isSubF
  · rfl
