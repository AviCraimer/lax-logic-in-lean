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


namespace PLLAxiom

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
@[simp]
def get (ax: PLLAxiom): PLLFormula :=
  match ax with
    | somehowR M => ifThen M (somehow M)
    | somehowM M => ifThen (somehow (somehow M)) (somehow M)
    | somehowS M N => ifThen (and (somehow M) (somehow N)) (somehow (and M N))
-- stardard axioms for propostinal intuistionalist logic, source: https://homepage.mi-ras.ru/~sk/lehre/penn2017/lecture1.pdf
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
