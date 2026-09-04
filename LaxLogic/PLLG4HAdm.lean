import LaxLogic.PLLG4HInv
import LaxLogic.PLLG4Adm

/-!
# The `G4c` rule API, generalised identity, telescoped MP

`G4c := ∃ n, G4h n` hides the height, so existence-level developments
(identity, `weak_Imp`, …) need the rules at the wrapper.  The **rule
lifters** below restate each `G4h` constructor for `G4c`, aligning the
heights of binary premises with `mono`.  With them, the identity/MP
development of `PLLG4Adm.lean` ports token-for-token except in the two
modal cases, which *shrink*: the box-keeping `laxL` needs no `Perm`
surgery at all, and in the `◯`-antecedent telescope case the identity
premise sits at the head of the full context, unswapped.

`identity_mem` and the two-hypothesis `mp` below are the corollaries the
cut and completeness proofs actually call.

The telescope machinery (`curryImp`, `telWeight`) is shared with the
original development (`G4.curryImp` etc.).
-/

open PLLFormula

namespace PLLND

namespace G4c

/-! ### Rule lifters -/

private theorem toSame {Γ₁ Γ₂ : List PLLFormula} {C₁ C₂ : PLLFormula}
    (d₁ : G4c Γ₁ C₁) (d₂ : G4c Γ₂ C₂) :
    ∃ n, G4h n Γ₁ C₁ ∧ G4h n Γ₂ C₂ := by
  obtain ⟨n₁, h₁⟩ := d₁
  obtain ⟨n₂, h₂⟩ := d₂
  exact ⟨max n₁ n₂, h₁.mono (Nat.le_max_left _ _),
    h₂.mono (Nat.le_max_right _ _)⟩

theorem init {Γ : List PLLFormula} {a : String}
    (h : prop a ∈ Γ) : G4c Γ (prop a) := ⟨0, .init h⟩

theorem botL {Γ : List PLLFormula} {C : PLLFormula}
    (h : falsePLL ∈ Γ) : G4c Γ C := ⟨0, .botL h⟩

theorem andR {Γ : List PLLFormula} {A B : PLLFormula}
    (d₁ : G4c Γ A) (d₂ : G4c Γ B) : G4c Γ (A.and B) := by
  obtain ⟨n, h₁, h₂⟩ := toSame d₁ d₂
  exact ⟨n + 1, .andR h₁ h₂⟩

theorem orR1 {Γ : List PLLFormula} {A B : PLLFormula}
    (d : G4c Γ A) : G4c Γ (A.or B) := by
  obtain ⟨n, h⟩ := d; exact ⟨n + 1, .orR1 h⟩

theorem orR2 {Γ : List PLLFormula} {A B : PLLFormula}
    (d : G4c Γ B) : G4c Γ (A.or B) := by
  obtain ⟨n, h⟩ := d; exact ⟨n + 1, .orR2 h⟩

theorem impR {Γ : List PLLFormula} {A B : PLLFormula}
    (d : G4c (A :: Γ) B) : G4c Γ (A.ifThen B) := by
  obtain ⟨n, h⟩ := d; exact ⟨n + 1, .impR h⟩

theorem laxR {Γ : List PLLFormula} {A : PLLFormula}
    (d : G4c Γ A) : G4c Γ A.somehow := by
  obtain ⟨n, h⟩ := d; exact ⟨n + 1, .laxR h⟩

theorem andL {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (h : Γ.Perm (A.and B :: Δ)) (d : G4c (A :: B :: Δ) C) : G4c Γ C := by
  obtain ⟨n, hd⟩ := d; exact ⟨n + 1, .andL h hd⟩

theorem orL {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (h : Γ.Perm (A.or B :: Δ)) (d₁ : G4c (A :: Δ) C) (d₂ : G4c (B :: Δ) C) :
    G4c Γ C := by
  obtain ⟨n, h₁, h₂⟩ := toSame d₁ d₂
  exact ⟨n + 1, .orL h h₁ h₂⟩

theorem laxL {Γ : List PLLFormula} {A B : PLLFormula}
    (h : A.somehow ∈ Γ) (d : G4c (A :: Γ) B.somehow) : G4c Γ B.somehow := by
  obtain ⟨n, hd⟩ := d; exact ⟨n + 1, .laxL h hd⟩

theorem impLProp {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
    (h : Γ.Perm ((prop a).ifThen B :: Δ)) (ha : prop a ∈ Δ)
    (d : G4c (B :: Δ) C) : G4c Γ C := by
  obtain ⟨n, hd⟩ := d; exact ⟨n + 1, .impLProp h ha hd⟩

theorem impLBot {Γ Δ : List PLLFormula} {B C : PLLFormula}
    (h : Γ.Perm (falsePLL.ifThen B :: Δ)) (d : G4c Δ C) : G4c Γ C := by
  obtain ⟨n, hd⟩ := d; exact ⟨n + 1, .impLBot h hd⟩

theorem impLAnd {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
    (h : Γ.Perm ((A.and B).ifThen D :: Δ))
    (d : G4c (A.ifThen (B.ifThen D) :: Δ) E) : G4c Γ E := by
  obtain ⟨n, hd⟩ := d; exact ⟨n + 1, .impLAnd h hd⟩

theorem impLOr {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
    (h : Γ.Perm ((A.or B).ifThen D :: Δ))
    (d : G4c (A.ifThen D :: B.ifThen D :: Δ) E) : G4c Γ E := by
  obtain ⟨n, hd⟩ := d; exact ⟨n + 1, .impLOr h hd⟩

theorem impLImp {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
    (h : Γ.Perm ((A.ifThen B).ifThen D :: Δ))
    (d₁ : G4c (B.ifThen D :: Δ) (A.ifThen B)) (d₂ : G4c (D :: Δ) E) :
    G4c Γ E := by
  obtain ⟨n, h₁, h₂⟩ := toSame d₁ d₂
  exact ⟨n + 1, .impLImp h h₁ h₂⟩

theorem impLLax {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (h : Γ.Perm (A.somehow.ifThen B :: Δ))
    (d₁ : G4c Γ A) (d₂ : G4c (B :: Δ) C) : G4c Γ C := by
  obtain ⟨n, h₁, h₂⟩ := toSame d₁ d₂
  exact ⟨n + 1, .impLLax h h₁ h₂⟩

theorem impLLaxLax {Γ Δ : List PLLFormula} {A B X C : PLLFormula}
    (h : Γ.Perm (A.somehow.ifThen B :: Δ)) (hX : X.somehow ∈ Δ)
    (d₁ : G4c (X :: Γ) A.somehow) (d₂ : G4c (B :: Δ) C) : G4c Γ C := by
  obtain ⟨n, h₁, h₂⟩ := toSame d₁ d₂
  exact ⟨n + 1, .impLLaxLax h hX h₁ h₂⟩

/-! ### Generalised identity and telescoped modus ponens -/

open G4 (curryImp telWeight telWeight_cons telWeight_nil telWeight_pos)

/-- The joint induction of `PLLG4Adm.identity_mpt`, at `G4c`. -/
theorem identity_mpt : ∀ n : Nat,
    (∀ (A : PLLFormula) (Γ : List PLLFormula),
      A.weight ≤ n → G4c (A :: Γ) A) ∧
    (∀ (As : List PLLFormula) (B : PLLFormula) (Γ : List PLLFormula),
      telWeight As B ≤ n → G4c (As ++ curryImp As B :: Γ) B) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hId : ∀ (A : PLLFormula) (Γ : List PLLFormula),
        A.weight ≤ n → G4c (A :: Γ) A := by
      intro A Γ hw
      match A with
      | .prop a => exact init (.head _)
      | .falsePLL => exact botL (.head _)
      | .and A₁ A₂ =>
          simp only [PLLFormula.weight] at hw
          have h₁ : A₁.weight < n := by omega
          have h₂ : A₂.weight < n := by omega
          refine andL (Δ := Γ) (List.Perm.refl _) (andR ?_ ?_)
          · exact (ih A₁.weight h₁).1 A₁ (A₂ :: Γ) (Nat.le_refl _)
          · exact ((ih A₂.weight h₂).1 A₂ (A₁ :: Γ)
              (Nat.le_refl _)).perm (List.Perm.swap _ _ _)
      | .or A₁ A₂ =>
          simp only [PLLFormula.weight] at hw
          have h₁ : A₁.weight < n := by omega
          have h₂ : A₂.weight < n := by omega
          refine orL (Δ := Γ) (List.Perm.refl _) (orR1 ?_) (orR2 ?_)
          · exact (ih A₁.weight h₁).1 A₁ Γ (Nat.le_refl _)
          · exact (ih A₂.weight h₂).1 A₂ Γ (Nat.le_refl _)
      | .somehow A₁ =>
          simp only [PLLFormula.weight] at hw
          have h₁ : A₁.weight < n := by omega
          -- the box is kept, so the identity premise is direct
          exact laxL (.head _) (laxR ((ih A₁.weight h₁).1 A₁ _ (Nat.le_refl _)))
      | .ifThen C D =>
          simp only [PLLFormula.weight] at hw
          have hlt : telWeight [C] D < n := by
            simp only [telWeight_cons, telWeight_nil]; omega
          have h := (ih _ hlt).2 [C] D Γ (Nat.le_refl _)
          exact impR (by simpa using h)
    refine ⟨hId, ?_⟩
    intro As B Γ hw
    match As with
    | [] => simpa using hId B Γ (by simpa using hw)
    | C :: Cs =>
      rw [telWeight_cons] at hw
      have htel : 0 < telWeight Cs B := telWeight_pos Cs B
      match C with
      | .prop a =>
          have hlt : telWeight Cs B < n := by
            have := weight_pos (prop a); omega
          refine impLProp (Δ := prop a :: (Cs ++ Γ))
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))
            (.head _) ?_
          exact (((ih _ hlt).2 Cs B Γ (Nat.le_refl _)).weaken (prop a)).perm
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))
      | .falsePLL => exact botL (.head _)
      | .and C₁ C₂ =>
          simp only [PLLFormula.weight] at hw
          have hlt : telWeight (C₁ :: C₂ :: Cs) B < n := by
            simp only [telWeight_cons]; omega
          refine impLAnd (Δ := C₁.and C₂ :: (Cs ++ Γ))
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _)) ?_
          refine andL
            (Δ := C₁.ifThen (C₂.ifThen (curryImp Cs B)) :: (Cs ++ Γ))
            (List.Perm.swap _ _ _) ?_
          have m := (ih _ hlt).2 (C₁ :: C₂ :: Cs) B Γ (Nat.le_refl _)
          simp only [G4.curryImp_cons, List.cons_append] at m
          exact m.perm ((List.perm_middle.cons _).cons _)
      | .or C₁ C₂ =>
          simp only [PLLFormula.weight] at hw
          have hlt₁ : telWeight (C₁ :: Cs) B < n := by
            rw [telWeight_cons]; have := weight_pos C₂; omega
          have hlt₂ : telWeight (C₂ :: Cs) B < n := by
            rw [telWeight_cons]; have := weight_pos C₁; omega
          refine impLOr (Δ := C₁.or C₂ :: (Cs ++ Γ))
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _)) ?_
          refine orL
            (Δ := C₁.ifThen (curryImp Cs B) ::
                  C₂.ifThen (curryImp Cs B) :: (Cs ++ Γ))
            (((List.Perm.swap _ _ _).cons _).trans (List.Perm.swap _ _ _))
            ?_ ?_
          · have m := (ih _ hlt₁).2 (C₁ :: Cs) B
              (C₂.ifThen (curryImp Cs B) :: Γ) (Nat.le_refl _)
            simp only [G4.curryImp_cons, List.cons_append] at m
            exact m.perm
              ((List.perm_middle.trans (List.perm_middle.cons _)).cons _)
          · have m := (ih _ hlt₂).2 (C₂ :: Cs) B
              (C₁.ifThen (curryImp Cs B) :: Γ) (Nat.le_refl _)
            simp only [G4.curryImp_cons, List.cons_append] at m
            exact m.perm
              (((List.perm_middle.trans (List.perm_middle.cons _)).trans
                (List.Perm.swap _ _ _)).cons _)
      | .ifThen C₁ C₂ =>
          have hle : (C₁.ifThen C₂).weight ≤ n := by omega
          have hlt : telWeight Cs B < n := by
            have := weight_pos (C₁.ifThen C₂); omega
          refine impLImp (Δ := C₁.ifThen C₂ :: (Cs ++ Γ))
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _)) ?_ ?_
          · exact (hId (C₁.ifThen C₂)
              (C₂.ifThen (curryImp Cs B) :: (Cs ++ Γ)) hle).perm
              (List.Perm.swap _ _ _)
          · exact (((ih _ hlt).2 Cs B Γ (Nat.le_refl _)).weaken
              (C₁.ifThen C₂)).perm
              ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))
      | .somehow C₁ =>
          simp only [PLLFormula.weight] at hw
          have hle : C₁.weight ≤ n := by omega
          have hlt : telWeight Cs B < n := by omega
          refine impLLaxLax (Δ := C₁.somehow :: (Cs ++ Γ)) (X := C₁)
            ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))
            (.head _) ?_ ?_
          · -- premise 1: C₁ heads the *full* context — identity, unswapped
            exact laxR (hId C₁ _ hle)
          · exact (((ih _ hlt).2 Cs B Γ (Nat.le_refl _)).weaken
              C₁.somehow).perm
              ((List.perm_middle.cons _).trans (List.Perm.swap _ _ _))

/-- **Generalised identity** at the final calculus. -/
theorem identity (A : PLLFormula) (Γ : List PLLFormula) : G4c (A :: Γ) A :=
  (identity_mpt A.weight).1 A Γ (Nat.le_refl _)

/-- Identity from membership. -/
theorem identity_mem {A : PLLFormula} {Γ : List PLLFormula} (h : A ∈ Γ) :
    G4c Γ A :=
  (identity A (Γ.erase A)).perm (perm_cons_erase h).symm

/-- **Modus ponens in the context**: `A, A ⊃ B, Γ ⊢ B`. -/
theorem mp (A B : PLLFormula) (Γ : List PLLFormula) :
    G4c (A :: A.ifThen B :: Γ) B := by
  simpa using (identity_mpt (telWeight [A] B)).2 [A] B Γ (Nat.le_refl _)

end G4c

end PLLND
