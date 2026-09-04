import LaxLogic.PLLG4PInv

/-!
# Generalised identity for G4iLL′

`G4p` proves only atomic axioms (`init`), so the general identity
`A, Γ ⊢ A` is a theorem, not a rule.  Following Dyckhoff–Negri
(JSL 65(4), 2000, Lemma 3.2) we prove it together with a *telescoped
modus ponens*: for a list `As = [C₁, …, Cₖ]`,

  `MPT : G4p (As ++ [C₁ ⊃ (C₂ ⊃ … ⊃ (Cₖ ⊃ B))] ++ Γ) B`

by a single strong induction on total weight.  The telescope is forced
on us: decomposing `(C₁∧C₂) ⊃ R` with `impLAnd` produces the curried
`C₁ ⊃ (C₂ ⊃ R)` *and* leaves `C₁, C₂` in the context, so the plain
two-formula modus ponens statement is not closed under the `∧` case,
but the telescoped one is — with total weight decreasing by exactly the
`+2` that Dyckhoff's weight assigns to conjunction.  The `◯`-antecedent
case is where Iemhoff's `impLLaxLax` earns its keep: the boxed
hypothesis `◯C₁` serves as its *own* box.

Measure bookkeeping (`n` the outer bound):
* `Id A` at `weight A ≤ n` calls `Id` at strictly smaller weight and
  `MPT [C] D` at `weight C + weight D = weight A − 1 < n`;
* `MPT (C::Cs) B` at total `≤ n` calls `MPT` at strictly smaller total
  (every antecedent case shrinks) and `Id` at weight `< n` (the
  telescope tail weighs at least `weight B ≥ 1`);
* `MPT [] B` is `Id B` at the *same* `n` — so within each level we
  prove `Id` first and let `MPT` use it.
-/

open PLLFormula

namespace PLLND

namespace G4p

/-- Curried implication `C₁ ⊃ (C₂ ⊃ (… ⊃ B))` of a telescope of
antecedents.  `curryImp [] B = B`. -/
def curryImp (As : List PLLFormula) (B : PLLFormula) : PLLFormula :=
  As.foldr .ifThen B

@[simp] theorem curryImp_nil (B : PLLFormula) : curryImp [] B = B := rfl

@[simp] theorem curryImp_cons (C : PLLFormula) (As : List PLLFormula)
    (B : PLLFormula) : curryImp (C :: As) B = C.ifThen (curryImp As B) := rfl

/-- Total weight of a telescope. -/
def telWeight (As : List PLLFormula) (B : PLLFormula) : Nat :=
  (As.map PLLFormula.weight).sum + B.weight

@[simp] theorem telWeight_nil (B : PLLFormula) :
    telWeight [] B = B.weight := by simp [telWeight]

theorem telWeight_cons (C : PLLFormula) (As : List PLLFormula)
    (B : PLLFormula) :
    telWeight (C :: As) B = C.weight + telWeight As B := by
  simp [telWeight, Nat.add_assoc]

theorem telWeight_pos (As : List PLLFormula) (B : PLLFormula) :
    0 < telWeight As B :=
  Nat.lt_of_lt_of_le (weight_pos B) (Nat.le_add_left _ _)

/-- The joint induction: generalised identity and telescoped modus
ponens, bounded by total weight. -/
theorem identity_mpt : ∀ n : Nat,
    (∀ (A : PLLFormula) (Γ : List PLLFormula),
      A.weight ≤ n → G4p (A :: Γ) A) ∧
    (∀ (As : List PLLFormula) (B : PLLFormula) (Γ : List PLLFormula),
      telWeight As B ≤ n → G4p (As ++ curryImp As B :: Γ) B) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- Part 1: identity at level `n`, using `ih` only.
    have hId : ∀ (A : PLLFormula) (Γ : List PLLFormula),
        A.weight ≤ n → G4p (A :: Γ) A := by
      intro A Γ hw
      match A with
      | .prop a => exact .init (.head _)
      | .falsePLL => exact .botL (.head _)
      | .and A₁ A₂ =>
          simp only [PLLFormula.weight] at hw
          have h₁ : A₁.weight < n := by omega
          have h₂ : A₂.weight < n := by omega
          -- A₁∧A₂, Γ ⊢ A₁∧A₂ : decompose, then two identities
          refine .andL (Δ := Γ) (List.Perm.refl _) (.andR ?_ ?_)
          · exact (ih A₁.weight h₁).1 A₁ (A₂ :: Γ) (Nat.le_refl _)
          · exact ((ih A₂.weight h₂).1 A₂ (A₁ :: Γ)
              (Nat.le_refl _)).perm (List.Perm.swap _ _ _)
      | .or A₁ A₂ =>
          simp only [PLLFormula.weight] at hw
          have h₁ : A₁.weight < n := by omega
          have h₂ : A₂.weight < n := by omega
          refine .orL (Δ := Γ) (List.Perm.refl _) (.orR1 ?_) (.orR2 ?_)
          · exact (ih A₁.weight h₁).1 A₁ Γ (Nat.le_refl _)
          · exact (ih A₂.weight h₂).1 A₂ Γ (Nat.le_refl _)
      | .somehow A₁ =>
          simp only [PLLFormula.weight] at hw
          have h₁ : A₁.weight < n := by omega
          refine .laxL (Δ := Γ) (List.Perm.refl _) (.laxR ?_)
          exact (ih A₁.weight h₁).1 A₁ Γ (Nat.le_refl _)
      | .ifThen C D =>
          -- C⊃D, Γ ⊢ C⊃D : impR, then the singleton telescope
          simp only [PLLFormula.weight] at hw
          have hlt : telWeight [C] D < n := by
            simp only [telWeight_cons, telWeight_nil]; omega
          have h := (ih _ hlt).2 [C] D Γ (Nat.le_refl _)
          exact .impR (by simpa using h)
    refine ⟨hId, ?_⟩
    -- Part 2: telescoped modus ponens at level `n`, using `hId` and `ih`.
    intro As B Γ hw
    match As with
    | [] => simpa using hId B Γ (by simpa using hw)
    | C :: Cs =>
      -- context: C :: Cs ++ (C ⊃ R) :: Γ, where R := curryImp Cs B
      rw [telWeight_cons] at hw
      have htel : 0 < telWeight Cs B := telWeight_pos Cs B
      match C with
      | .prop a =>
          have hlt : telWeight Cs B < n := by
            have := weight_pos (prop a); omega
          -- expose `p ⊃ R`, consume it with `impLProp` (p is at hand)
          refine .impLProp (Δ := prop a :: (Cs ++ Γ))
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))
            (.head _) ?_
          -- premise: R :: prop a :: Cs ++ Γ ⊢ B, from MPT Cs B
          exact (((ih _ hlt).2 Cs B Γ (Nat.le_refl _)).weaken (prop a)).perm
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))
      | .falsePLL => exact .botL (.head _)
      | .and C₁ C₂ =>
          simp only [PLLFormula.weight] at hw
          have hlt : telWeight (C₁ :: C₂ :: Cs) B < n := by
            simp only [telWeight_cons]; omega
          -- step 1: impLAnd on the implication
          refine .impLAnd (Δ := C₁.and C₂ :: (Cs ++ Γ))
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _)) ?_
          -- step 2: andL on C₁∧C₂
          refine .andL
            (Δ := C₁.ifThen (C₂.ifThen (curryImp Cs B)) :: (Cs ++ Γ))
            (List.Perm.swap _ _ _) ?_
          -- premise: C₁ :: C₂ :: (C₁⊃(C₂⊃R)) :: Cs ++ Γ ⊢ B
          have m := (ih _ hlt).2 (C₁ :: C₂ :: Cs) B Γ (Nat.le_refl _)
          simp only [curryImp_cons, List.cons_append] at m
          exact m.perm ((List.perm_middle.cons _).cons _)
      | .or C₁ C₂ =>
          simp only [PLLFormula.weight] at hw
          have hlt₁ : telWeight (C₁ :: Cs) B < n := by
            rw [telWeight_cons]; have := weight_pos C₂; omega
          have hlt₂ : telWeight (C₂ :: Cs) B < n := by
            rw [telWeight_cons]; have := weight_pos C₁; omega
          -- step 1: impLOr on the implication
          refine .impLOr (Δ := C₁.or C₂ :: (Cs ++ Γ))
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _)) ?_
          -- step 2: orL on C₁∨C₂
          refine .orL
            (Δ := C₁.ifThen (curryImp Cs B) ::
                  C₂.ifThen (curryImp Cs B) :: (Cs ++ Γ))
            (((List.Perm.swap _ _ _).cons _).trans (List.Perm.swap _ _ _))
            ?_ ?_
          · -- branch C₁: MPT (C₁::Cs) B with junk C₂⊃R
            have m := (ih _ hlt₁).2 (C₁ :: Cs) B
              (C₂.ifThen (curryImp Cs B) :: Γ) (Nat.le_refl _)
            simp only [curryImp_cons, List.cons_append] at m
            exact m.perm
              ((List.perm_middle.trans (List.perm_middle.cons _)).cons _)
          · -- branch C₂: MPT (C₂::Cs) B with junk C₁⊃R
            have m := (ih _ hlt₂).2 (C₂ :: Cs) B
              (C₁.ifThen (curryImp Cs B) :: Γ) (Nat.le_refl _)
            simp only [curryImp_cons, List.cons_append] at m
            exact m.perm
              (((List.perm_middle.trans (List.perm_middle.cons _)).trans
                (List.Perm.swap _ _ _)).cons _)
      | .ifThen C₁ C₂ =>
          have hle : (C₁.ifThen C₂).weight ≤ n := by omega
          have hlt : telWeight Cs B < n := by
            have := weight_pos (C₁.ifThen C₂); omega
          -- impLImp on ((C₁⊃C₂)⊃R)
          refine .impLImp (Δ := C₁.ifThen C₂ :: (Cs ++ Γ))
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _)) ?_ ?_
          · -- premise 1: C₂⊃R :: (C₁⊃C₂) :: Cs ++ Γ ⊢ C₁⊃C₂ : identity
            exact (hId (C₁.ifThen C₂)
              (C₂.ifThen (curryImp Cs B) :: (Cs ++ Γ)) hle).perm
              (List.Perm.swap _ _ _)
          · -- premise 2: R :: (C₁⊃C₂) :: Cs ++ Γ ⊢ B, from MPT Cs B
            exact (((ih _ hlt).2 Cs B Γ (Nat.le_refl _)).weaken
              (C₁.ifThen C₂)).perm
              ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))
      | .somehow C₁ =>
          simp only [PLLFormula.weight] at hw
          have hle : C₁.weight ≤ n := by omega
          have hlt : telWeight Cs B < n := by omega
          -- impLLaxLax on ((◯C₁)⊃R); the context's ◯C₁ is its own box
          refine .impLLaxLax (Δ := Cs ++ Γ) (X := C₁)
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _)) ?_ ?_
          · -- premise 1: ◯C₁⊃R :: C₁ :: Cs ++ Γ ⊢ ◯C₁ :
            -- laxR, then identity slid past the kept implication
            exact .laxR ((hId C₁
              (C₁.somehow.ifThen (curryImp Cs B) :: (Cs ++ Γ)) hle).perm
              (List.Perm.swap _ _ _))
          · -- premise 2: R :: ◯C₁ :: Cs ++ Γ ⊢ B, from MPT Cs B
            exact (((ih _ hlt).2 Cs B Γ (Nat.le_refl _)).weaken
              C₁.somehow).perm
              ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))

/-- **Generalised identity**: `A, Γ ⊢ A` for every formula `A`. -/
theorem identity (A : PLLFormula) (Γ : List PLLFormula) : G4p (A :: Γ) A :=
  (identity_mpt A.weight).1 A Γ (Nat.le_refl _)

/-- Identity from membership. -/
theorem identity_mem {A : PLLFormula} {Γ : List PLLFormula} (h : A ∈ Γ) :
    G4p Γ A :=
  (identity A (Γ.erase A)).perm (List.perm_cons_erase h).symm

/-- **Modus ponens in the context**: `A, A ⊃ B, Γ ⊢ B`. -/
theorem mp (A B : PLLFormula) (Γ : List PLLFormula) :
    G4p (A :: A.ifThen B :: Γ) B := by
  simpa using (identity_mpt (telWeight [A] B)).2 [A] B Γ (Nat.le_refl _)

end G4p

end PLLND
