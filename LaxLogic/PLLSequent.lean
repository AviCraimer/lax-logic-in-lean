import LaxLogic.PLLConsequence

/-!
# A cut-free sequent calculus for PLL, and cut elimination (F&M Theorem 2.6)

`SCh n Γ C` is a G3-style single-succedent sequent calculus for PLL with an
explicit height index `n`: left rules keep their principal formula in the
context via a membership hypothesis, so weakening, contraction and exchange
are height-preserving admissible (`SCh.rename`), exactly as in the natural
deduction system of `PLLNDCore.lean`.  The two lax rules are Curry's

    Γ ⊢ A            Γ, A ⊢ ◯B
  ---------- ◯R    -------------- ◯L  (principal `◯A` kept in Γ)
   Γ ⊢ ◯A            Γ ⊢ ◯B

There is **no cut rule**; cut is *admissible* (`SC.cut`), proved by the
standard lexicographic induction on (cut formula, sum of heights) — heights
are what let a `Prop`-valued calculus carry that induction.  The one
reduction step beyond IPC is the `laxR`/`laxL` principal case, F&M Figure 2.

Corollaries (F&M Lemma 2.7): equivalence with natural deduction, the
disjunction property, and `◯`-reflection (`⊢ ◯M` implies `⊢ M`).
-/

open PLLFormula

namespace PLLND

/-- Height-indexed, cut-free sequent calculus for PLL. -/
inductive SCh : Nat → List PLLFormula → PLLFormula → Prop
  | init {n : Nat} {Γ : List PLLFormula} {a : String}
      (h : PLLFormula.prop a ∈ Γ) : SCh n Γ (.prop a)
  | botL {n : Nat} {Γ : List PLLFormula} {C : PLLFormula}
      (h : PLLFormula.falsePLL ∈ Γ) : SCh n Γ C
  | andR {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      SCh n Γ A → SCh n Γ B → SCh (n + 1) Γ (A.and B)
  | andL {n : Nat} {Γ : List PLLFormula} {A B C : PLLFormula}
      (h : A.and B ∈ Γ) : SCh n (A :: B :: Γ) C → SCh (n + 1) Γ C
  | orR1 {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      SCh n Γ A → SCh (n + 1) Γ (A.or B)
  | orR2 {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      SCh n Γ B → SCh (n + 1) Γ (A.or B)
  | orL {n : Nat} {Γ : List PLLFormula} {A B C : PLLFormula}
      (h : A.or B ∈ Γ) :
      SCh n (A :: Γ) C → SCh n (B :: Γ) C → SCh (n + 1) Γ C
  | impR {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      SCh n (A :: Γ) B → SCh (n + 1) Γ (A.ifThen B)
  | impL {n : Nat} {Γ : List PLLFormula} {A B C : PLLFormula}
      (h : A.ifThen B ∈ Γ) :
      SCh n Γ A → SCh n (B :: Γ) C → SCh (n + 1) Γ C
  | laxR {n : Nat} {Γ : List PLLFormula} {A : PLLFormula} :
      SCh n Γ A → SCh (n + 1) Γ (A.somehow)
  | laxL {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula}
      (h : A.somehow ∈ Γ) :
      SCh n (A :: Γ) (B.somehow) → SCh (n + 1) Γ (B.somehow)

/-- Cut-free derivability: some height works. -/
def SC (Γ : List PLLFormula) (C : PLLFormula) : Prop := ∃ n, SCh n Γ C

/-- Height weakening. -/
theorem SCh.mono : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    SCh n Γ C → ∀ {m : Nat}, n ≤ m → SCh m Γ C := by
  intro n Γ C d
  induction d with
  | init h => exact fun _ => .init h
  | botL h => exact fun _ => .botL h
  | andR _ _ ih₁ ih₂ =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .andR (ih₁ (by omega)) (ih₂ (by omega))
  | andL h _ ih =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .andL h (ih (by omega))
  | orR1 _ ih =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .orR1 (ih (by omega))
  | orR2 _ ih =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .orR2 (ih (by omega))
  | orL h _ _ ih₁ ih₂ =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .orL h (ih₁ (by omega)) (ih₂ (by omega))
  | impR _ ih =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .impR (ih (by omega))
  | impL h _ _ ih₁ ih₂ =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .impL h (ih₁ (by omega)) (ih₂ (by omega))
  | laxR _ ih =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .laxR (ih (by omega))
  | laxL h _ ih =>
      intro m hnm
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero _)
      | succ m' => exact .laxL h (ih (by omega))

/-- Height-preserving admissible weakening/contraction/exchange. -/
theorem SCh.rename : ∀ {n : Nat} {Γ Γ' : List PLLFormula} {C : PLLFormula},
    (∀ ψ ∈ Γ, ψ ∈ Γ') → SCh n Γ C → SCh n Γ' C := by
  intro n Γ Γ' C H d
  induction d generalizing Γ' with
  | init h => exact .init (H _ h)
  | botL h => exact .botL (H _ h)
  | andR _ _ ih₁ ih₂ => exact .andR (ih₁ H) (ih₂ H)
  | andL h _ ih =>
      refine .andL (H _ h) (ih ?_)
      intro ψ hψ
      simp only [List.mem_cons] at hψ
      rcases hψ with rfl | rfl | hψ
      · exact .head _
      · exact .tail _ (.head _)
      · exact .tail _ (.tail _ (H _ hψ))
  | orR1 _ ih => exact .orR1 (ih H)
  | orR2 _ ih => exact .orR2 (ih H)
  | orL h _ _ ih₁ ih₂ =>
      refine .orL (H _ h) (ih₁ ?_) (ih₂ ?_) <;>
        · intro ψ hψ
          simp only [List.mem_cons] at hψ
          rcases hψ with rfl | hψ
          · exact .head _
          · exact .tail _ (H _ hψ)
  | impR _ ih =>
      refine .impR (ih ?_)
      intro ψ hψ
      simp only [List.mem_cons] at hψ
      rcases hψ with rfl | hψ
      · exact .head _
      · exact .tail _ (H _ hψ)
  | impL h _ _ ih₁ ih₂ =>
      refine .impL (H _ h) (ih₁ H) (ih₂ ?_)
      intro ψ hψ
      simp only [List.mem_cons] at hψ
      rcases hψ with rfl | hψ
      · exact .head _
      · exact .tail _ (H _ hψ)
  | laxR _ ih => exact .laxR (ih H)
  | laxL h _ ih =>
      refine .laxL (H _ h) (ih ?_)
      intro ψ hψ
      simp only [List.mem_cons] at hψ
      rcases hψ with rfl | hψ
      · exact .head _
      · exact .tail _ (H _ hψ)

namespace SC

theorem rename {Γ Γ' : List PLLFormula} {C : PLLFormula}
    (H : ∀ ψ ∈ Γ, ψ ∈ Γ') : SC Γ C → SC Γ' C :=
  fun ⟨n, d⟩ => ⟨n, d.rename H⟩

/-! `SC`-level smart constructors (heights equalised by `mono`). -/

theorem init {Γ : List PLLFormula} {a : String} (h : PLLFormula.prop a ∈ Γ) :
    SC Γ (.prop a) := ⟨0, .init h⟩

theorem botL {Γ : List PLLFormula} {C : PLLFormula}
    (h : PLLFormula.falsePLL ∈ Γ) : SC Γ C := ⟨0, .botL h⟩

theorem andR {Γ : List PLLFormula} {A B : PLLFormula}
    (h₁ : SC Γ A) (h₂ : SC Γ B) : SC Γ (A.and B) :=
  have ⟨n, d₁⟩ := h₁; have ⟨m, d₂⟩ := h₂
  ⟨max n m + 1, .andR (d₁.mono (Nat.le_max_left ..)) (d₂.mono (Nat.le_max_right ..))⟩

theorem andL {Γ : List PLLFormula} {A B C : PLLFormula} (h : A.and B ∈ Γ)
    (h' : SC (A :: B :: Γ) C) : SC Γ C :=
  have ⟨n, d⟩ := h'; ⟨n + 1, .andL h d⟩

theorem orR1 {Γ : List PLLFormula} {A B : PLLFormula} (h : SC Γ A) :
    SC Γ (A.or B) :=
  have ⟨n, d⟩ := h; ⟨n + 1, .orR1 d⟩

theorem orR2 {Γ : List PLLFormula} {A B : PLLFormula} (h : SC Γ B) :
    SC Γ (A.or B) :=
  have ⟨n, d⟩ := h; ⟨n + 1, .orR2 d⟩

theorem orL {Γ : List PLLFormula} {A B C : PLLFormula} (h : A.or B ∈ Γ)
    (h₁ : SC (A :: Γ) C) (h₂ : SC (B :: Γ) C) : SC Γ C :=
  have ⟨n, d₁⟩ := h₁; have ⟨m, d₂⟩ := h₂
  ⟨max n m + 1, .orL h (d₁.mono (Nat.le_max_left ..)) (d₂.mono (Nat.le_max_right ..))⟩

theorem impR {Γ : List PLLFormula} {A B : PLLFormula}
    (h : SC (A :: Γ) B) : SC Γ (A.ifThen B) :=
  have ⟨n, d⟩ := h; ⟨n + 1, .impR d⟩

theorem impL {Γ : List PLLFormula} {A B C : PLLFormula} (h : A.ifThen B ∈ Γ)
    (h₁ : SC Γ A) (h₂ : SC (B :: Γ) C) : SC Γ C :=
  have ⟨n, d₁⟩ := h₁; have ⟨m, d₂⟩ := h₂
  ⟨max n m + 1, .impL h (d₁.mono (Nat.le_max_left ..)) (d₂.mono (Nat.le_max_right ..))⟩

theorem laxR {Γ : List PLLFormula} {A : PLLFormula} (h : SC Γ A) :
    SC Γ (A.somehow) :=
  have ⟨n, d⟩ := h; ⟨n + 1, .laxR d⟩

theorem laxL {Γ : List PLLFormula} {A B : PLLFormula} (h : A.somehow ∈ Γ)
    (h' : SC (A :: Γ) (B.somehow)) : SC Γ (B.somehow) :=
  have ⟨n, d⟩ := h'; ⟨n + 1, .laxL h d⟩

/-- General identity is admissible. -/
theorem iden : ∀ (φ : PLLFormula) {Γ : List PLLFormula}, φ ∈ Γ → SC Γ φ
  | .prop a, _, h => init h
  | .falsePLL, _, h => botL h
  | .and A B, _, h =>
      andL h (andR (iden A (.head _)) (iden B (.tail _ (.head _))))
  | .or A B, _, h =>
      orL h (orR1 (iden A (.head _))) (orR2 (iden B (.head _)))
  | .ifThen A B, _, h =>
      impR (impL (.tail _ h) (iden A (.head _)) (iden B (.head _)))
  | .somehow A, _, h =>
      laxL h (laxR (iden A (.head _)))

end SC

/-- **Cut admissibility** (F&M Theorem 2.6), with the context plumbing
generalised: from `Γ ⊢ A` and `Δ ⊢ C` where every hypothesis of `Δ` is
either the cut formula `A` or in `Γ`, conclude `Γ ⊢ C`.  Lexicographic
induction on (size of the cut formula, sum of the two heights); the
principal `laxR`/`laxL` case is the extra reduction of F&M Figure 2. -/
theorem cut_aux : ∀ (k : Nat), ∀ {A : PLLFormula}, sizeOf A ≤ k →
    ∀ (nm : Nat), ∀ {n m : Nat} {Γ Δ : List PLLFormula} {C : PLLFormula},
    n + m ≤ nm → SCh n Γ A → SCh m Δ C →
    (∀ ψ ∈ Δ, ψ = A ∨ ψ ∈ Γ) → SC Γ C := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro A hk nm
  induction nm using Nat.strong_induction_on with
  | _ nm ihnm =>
  intro n m Γ Δ C hnm d₁ d₂ HΔ
  -- cut with the same cut formula at a smaller height sum
  have cutS : ∀ {n' m' : Nat} {Γ' Δ' : List PLLFormula} {C' : PLLFormula},
      n' + m' < nm → SCh n' Γ' A → SCh m' Δ' C' →
      (∀ ψ ∈ Δ', ψ = A ∨ ψ ∈ Γ') → SC Γ' C' := by
    intro n' m' Γ' Δ' C' h d₁' d₂' H'
    exact ihnm _ h (le_refl _) d₁' d₂' H'
  -- cut with a strictly smaller cut formula (any heights)
  have cutF : ∀ {A' : PLLFormula}, sizeOf A' < sizeOf A →
      ∀ {Γ' Δ' : List PLLFormula} {C' : PLLFormula},
      SC Γ' A' → SC Δ' C' →
      (∀ ψ ∈ Δ', ψ = A' ∨ ψ ∈ Γ') → SC Γ' C' := by
    intro A' hA' Γ' Δ' C' h₁' h₂' H'
    obtain ⟨n', d₁'⟩ := h₁'
    obtain ⟨m', d₂'⟩ := h₂'
    exact ihk (sizeOf A') (by omega) (le_refl _) (n' + m') (le_refl _) d₁' d₂' H'
  -- commuting the cut over a last left rule of the left derivation:
  -- uniform in the right derivation, which stays whole.
  have leftCommute : ∀ {n' : Nat} {Γ' : List PLLFormula}, n' < n →
      SCh n' Γ' A → (∀ ψ ∈ Γ, ψ ∈ Γ') → SC Γ' C := by
    intro n' Γ' hlt d₁' HΓ
    refine cutS (by omega) d₁' d₂ ?_
    intro ψ hψ
    rcases HΔ _ hψ with h | h
    · exact .inl h
    · exact .inr (HΓ _ h)
  cases d₂ with
  | init h =>
      rcases HΔ _ h with rfl | hΓ
      · exact ⟨_, d₁⟩
      · exact SC.init hΓ
  | andR d₂₁ d₂₂ =>
      exact SC.andR (cutS (by omega) d₁ d₂₁ HΔ) (cutS (by omega) d₁ d₂₂ HΔ)
  | orR1 d₂' => exact SC.orR1 (cutS (by omega) d₁ d₂' HΔ)
  | orR2 d₂' => exact SC.orR2 (cutS (by omega) d₁ d₂' HΔ)
  | laxR d₂' => exact SC.laxR (cutS (by omega) d₁ d₂' HΔ)
  | impR d₂' =>
      refine SC.impR ?_
      refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂' ?_
      intro ψ hψ
      simp only [List.mem_cons] at hψ
      rcases hψ with rfl | hψ
      · exact .inr (.head _)
      · rcases HΔ _ hψ with h | h
        · exact .inl h
        · exact .inr (.tail _ h)
  | botL h =>
      rcases HΔ _ h with rfl | hΓ
      · -- the cut formula ⊥ is principal on the right: analyse `d₁`
        cases d₁ with
        | botL h' => exact SC.botL h'
        | andL h' d₁' =>
            exact SC.andL h' (leftCommute (by omega) d₁'
              (fun ψ h => .tail _ (.tail _ h)))
        | orL h' d₁₁ d₁₂ =>
            exact SC.orL h'
              (leftCommute (by omega) d₁₁ (fun ψ h => .tail _ h))
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
        | impL h' d₁₁ d₁₂ =>
            exact SC.impL h' ⟨_, d₁₁⟩
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
      · exact SC.botL hΓ
  | @andL m' _ X Y _ h d₂' =>
      rcases HΔ _ h with rfl | hΓ
      · -- principal: A = X ∧ Y
        -- cut A into the premise first (keeps X, Y in the context)
        have step : SC (X :: Y :: Γ) C := by
          refine cutS (by omega)
            (d₁.rename (fun ψ h => .tail _ (.tail _ h))) d₂' ?_
          intro ψ hψ
          simp only [List.mem_cons] at hψ
          rcases hψ with rfl | rfl | hψ
          · exact .inr (.head _)
          · exact .inr (.tail _ (.head _))
          · rcases HΔ _ hψ with h | h
            · exact .inl h
            · exact .inr (.tail _ (.tail _ h))
        cases d₁ with
        | botL h' => exact SC.botL h'
        | andR d₁₁ d₁₂ =>
            -- principal-principal: cut Y, then X
            have hY : SC (X :: Γ) C := by
              refine cutF (by simp only [and.sizeOf_spec, or.sizeOf_spec,
                ifThen.sizeOf_spec, somehow.sizeOf_spec]; omega)
                ⟨_, d₁₂.rename (fun ψ h => .tail _ h)⟩ step ?_
              intro ψ hψ
              simp only [List.mem_cons] at hψ
              rcases hψ with rfl | rfl | hψ
              · exact .inr (.head _)
              · exact .inl rfl
              · exact .inr (.tail _ hψ)
            refine cutF (by simp only [and.sizeOf_spec, or.sizeOf_spec,
                ifThen.sizeOf_spec, somehow.sizeOf_spec]; omega) ⟨_, d₁₁⟩ hY ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inl rfl
            · exact .inr hψ
        | andL h' d₁' =>
            exact SC.andL h' (leftCommute (by omega) d₁'
              (fun ψ h => .tail _ (.tail _ h)))
        | orL h' d₁₁ d₁₂ =>
            exact SC.orL h'
              (leftCommute (by omega) d₁₁ (fun ψ h => .tail _ h))
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
        | impL h' d₁₁ d₁₂ =>
            exact SC.impL h' ⟨_, d₁₁⟩
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
      · -- not principal
        refine SC.andL hΓ ?_
        refine cutS (by omega)
          (d₁.rename (fun ψ h => .tail _ (.tail _ h))) d₂' ?_
        intro ψ hψ
        simp only [List.mem_cons] at hψ
        rcases hψ with rfl | rfl | hψ
        · exact .inr (.head _)
        · exact .inr (.tail _ (.head _))
        · rcases HΔ _ hψ with h | h
          · exact .inl h
          · exact .inr (.tail _ (.tail _ h))
  | @orL m' _ X Y _ h d₂₁ d₂₂ =>
      rcases HΔ _ h with rfl | hΓ
      · -- principal: A = X ∨ Y
        have step₁ : SC (X :: Γ) C := by
          refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂₁ ?_
          intro ψ hψ
          simp only [List.mem_cons] at hψ
          rcases hψ with rfl | hψ
          · exact .inr (.head _)
          · rcases HΔ _ hψ with h | h
            · exact .inl h
            · exact .inr (.tail _ h)
        have step₂ : SC (Y :: Γ) C := by
          refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂₂ ?_
          intro ψ hψ
          simp only [List.mem_cons] at hψ
          rcases hψ with rfl | hψ
          · exact .inr (.head _)
          · rcases HΔ _ hψ with h | h
            · exact .inl h
            · exact .inr (.tail _ h)
        cases d₁ with
        | botL h' => exact SC.botL h'
        | orR1 d₁' =>
            refine cutF (by simp only [and.sizeOf_spec, or.sizeOf_spec,
                ifThen.sizeOf_spec, somehow.sizeOf_spec]; omega) ⟨_, d₁'⟩ step₁ ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inl rfl
            · exact .inr hψ
        | orR2 d₁' =>
            refine cutF (by simp only [and.sizeOf_spec, or.sizeOf_spec,
                ifThen.sizeOf_spec, somehow.sizeOf_spec]; omega) ⟨_, d₁'⟩ step₂ ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inl rfl
            · exact .inr hψ
        | andL h' d₁' =>
            exact SC.andL h' (leftCommute (by omega) d₁'
              (fun ψ h => .tail _ (.tail _ h)))
        | orL h' d₁₁ d₁₂ =>
            exact SC.orL h'
              (leftCommute (by omega) d₁₁ (fun ψ h => .tail _ h))
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
        | impL h' d₁₁ d₁₂ =>
            exact SC.impL h' ⟨_, d₁₁⟩
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
      · exact SC.orL hΓ
          (by
            refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂₁ ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inr (.head _)
            · rcases HΔ _ hψ with h | h
              · exact .inl h
              · exact .inr (.tail _ h))
          (by
            refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂₂ ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inr (.head _)
            · rcases HΔ _ hψ with h | h
              · exact .inl h
              · exact .inr (.tail _ h))
  | @impL m' _ X Y _ h d₂₁ d₂₂ =>
      rcases HΔ _ h with rfl | hΓ
      · -- principal: A = X ⊃ Y
        have argX : SC Γ X := cutS (by omega) d₁ d₂₁ HΔ
        have stepY : SC (Y :: Γ) C := by
          refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂₂ ?_
          intro ψ hψ
          simp only [List.mem_cons] at hψ
          rcases hψ with rfl | hψ
          · exact .inr (.head _)
          · rcases HΔ _ hψ with h | h
            · exact .inl h
            · exact .inr (.tail _ h)
        cases d₁ with
        | botL h' => exact SC.botL h'
        | impR d₁' =>
            -- principal-principal: cut X into the body, then cut Y
            have hY : SC Γ Y := by
              refine cutF (by simp only [and.sizeOf_spec, or.sizeOf_spec,
                ifThen.sizeOf_spec, somehow.sizeOf_spec]; omega) argX ⟨_, d₁'⟩ ?_
              intro ψ hψ
              simp only [List.mem_cons] at hψ
              rcases hψ with rfl | hψ
              · exact .inl rfl
              · exact .inr hψ
            refine cutF (by simp only [and.sizeOf_spec, or.sizeOf_spec,
                ifThen.sizeOf_spec, somehow.sizeOf_spec]; omega) hY stepY ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inl rfl
            · exact .inr hψ
        | andL h' d₁' =>
            exact SC.andL h' (leftCommute (by omega) d₁'
              (fun ψ h => .tail _ (.tail _ h)))
        | orL h' d₁₁ d₁₂ =>
            exact SC.orL h'
              (leftCommute (by omega) d₁₁ (fun ψ h => .tail _ h))
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
        | impL h' d₁₁ d₁₂ =>
            exact SC.impL h' ⟨_, d₁₁⟩
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
      · exact SC.impL hΓ (cutS (by omega) d₁ d₂₁ HΔ)
          (by
            refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂₂ ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inr (.head _)
            · rcases HΔ _ hψ with h | h
              · exact .inl h
              · exact .inr (.tail _ h))
  | @laxL m' _ X B h d₂' =>
      rcases HΔ _ h with rfl | hΓ
      · -- principal: A = ◯X — the F&M Figure 2 reduction
        have step : SC (X :: Γ) (B.somehow) := by
          refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂' ?_
          intro ψ hψ
          simp only [List.mem_cons] at hψ
          rcases hψ with rfl | hψ
          · exact .inr (.head _)
          · rcases HΔ _ hψ with h | h
            · exact .inl h
            · exact .inr (.tail _ h)
        cases d₁ with
        | botL h' => exact SC.botL h'
        | laxR d₁' =>
            refine cutF (by simp only [and.sizeOf_spec, or.sizeOf_spec,
                ifThen.sizeOf_spec, somehow.sizeOf_spec]; omega) ⟨_, d₁'⟩ step ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inl rfl
            · exact .inr hψ
        | andL h' d₁' =>
            exact SC.andL h' (leftCommute (by omega) d₁'
              (fun ψ h => .tail _ (.tail _ h)))
        | orL h' d₁₁ d₁₂ =>
            exact SC.orL h'
              (leftCommute (by omega) d₁₁ (fun ψ h => .tail _ h))
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
        | impL h' d₁₁ d₁₂ =>
            exact SC.impL h' ⟨_, d₁₁⟩
              (leftCommute (by omega) d₁₂ (fun ψ h => .tail _ h))
        | laxL h' d₁' =>
            exact SC.laxL h' (leftCommute (by omega) d₁'
              (fun ψ h => .tail _ h))
      · exact SC.laxL hΓ
          (by
            refine cutS (by omega) (d₁.rename (fun ψ h => .tail _ h)) d₂' ?_
            intro ψ hψ
            simp only [List.mem_cons] at hψ
            rcases hψ with rfl | hψ
            · exact .inr (.head _)
            · rcases HΔ _ hψ with h | h
              · exact .inl h
              · exact .inr (.tail _ h))

/-- **Cut is admissible** in the cut-free calculus (F&M Theorem 2.6). -/
theorem SC.cut {Γ : List PLLFormula} {A C : PLLFormula}
    (h₁ : SC Γ A) (h₂ : SC (A :: Γ) C) : SC Γ C := by
  obtain ⟨n, d₁⟩ := h₁
  obtain ⟨m, d₂⟩ := h₂
  refine cut_aux (sizeOf A) (le_refl _) (n + m) (le_refl _) d₁ d₂ ?_
  intro ψ hψ
  simp only [List.mem_cons] at hψ
  rcases hψ with rfl | hψ
  · exact .inl rfl
  · exact .inr hψ

/-! ### Equivalence with natural deduction (the Gentzen side of F&M Thm 2.3) -/

/-- Cut with a duplicated context. -/
def LaxND.cut1 {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (p : LaxND Γ φ) (q : LaxND (φ :: Γ) ψ) : LaxND Γ ψ :=
  (LaxND.cut p q).rename (by
    intro χ h
    simp only [List.mem_append] at h
    exact h.elim id id)

/-- Every cut-free sequent proof yields a natural deduction proof. -/
theorem SC_to_ND : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    SCh n Γ C → Nonempty (LaxND Γ C) := by
  intro n Γ C d
  induction d with
  | init h => exact ⟨.iden h⟩
  | botL h => exact ⟨.falsoElim _ (.iden h)⟩
  | andR _ _ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂
      exact ⟨.andIntro p₁ p₂⟩
  | @andL _ Γ' A B _ h _ ih =>
      obtain ⟨q⟩ := ih
      have pA : LaxND Γ' A := .andElim1 (.iden h)
      have pB : LaxND Γ' B := .andElim2 (.iden h)
      have qA : LaxND (B :: Γ') _ :=
        LaxND.cut1 (pA.rename (fun ψ h => .tail _ h)) q
      exact ⟨LaxND.cut1 pB qA⟩
  | orR1 _ ih => obtain ⟨p⟩ := ih; exact ⟨.orIntro1 p⟩
  | orR2 _ ih => obtain ⟨p⟩ := ih; exact ⟨.orIntro2 p⟩
  | orL h _ _ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂
      exact ⟨.orElim (.iden h) p₁ p₂⟩
  | impR _ ih => obtain ⟨p⟩ := ih; exact ⟨.impIntro p⟩
  | impL h _ _ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂
      exact ⟨LaxND.cut1 (.impElim (.iden h) p₁) p₂⟩
  | laxR _ ih => obtain ⟨p⟩ := ih; exact ⟨.laxIntro p⟩
  | laxL h _ ih =>
      obtain ⟨p⟩ := ih
      exact ⟨.laxElim (.iden h) p⟩

/-- Every natural deduction proof yields a cut-free sequent proof
(via admissibility of cut). -/
theorem ND_to_SC : ∀ {Γ : List PLLFormula} {C : PLLFormula},
    LaxND Γ C → SC Γ C := by
  intro Γ C p
  induction p with
  | iden h => exact SC.iden _ h
  | falsoElim φ _ ih => exact SC.cut ih (SC.botL (.head _))
  | impIntro _ ih => exact SC.impR ih
  | @impElim _ A B _ _ ih₁ ih₂ =>
      refine SC.cut ih₁ (SC.impL (.head _) ?_ (SC.iden _ (.head _)))
      exact ih₂.rename (fun ψ h => .tail _ h)
  | andIntro _ _ ih₁ ih₂ => exact SC.andR ih₁ ih₂
  | @andElim1 _ A B _ ih =>
      exact SC.cut ih (SC.andL (.head _) (SC.iden _ (.head _)))
  | @andElim2 _ A B _ ih =>
      exact SC.cut ih (SC.andL (.head _) (SC.iden _ (.tail _ (.head _))))
  | orIntro1 _ ih => exact SC.orR1 ih
  | orIntro2 _ ih => exact SC.orR2 ih
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      refine SC.cut ih₀ (SC.orL (.head _) ?_ ?_)
      · exact ih₁.rename (by
          intro ψ h
          simp only [List.mem_cons] at h ⊢
          exact h.imp id .inr)
      · exact ih₂.rename (by
          intro ψ h
          simp only [List.mem_cons] at h ⊢
          exact h.imp id .inr)
  | laxIntro _ ih => exact SC.laxR ih
  | laxElim _ _ ih₁ ih₂ =>
      refine SC.cut ih₁ (SC.laxL (.head _) ?_)
      exact ih₂.rename (by
        intro ψ h
        simp only [List.mem_cons] at h ⊢
        exact h.imp id .inr)

/-- **Cut elimination**, headline form (F&M Theorem 2.6): natural deduction
derivability coincides with cut-free sequent derivability. -/
theorem cutElimination {Γ : List PLLFormula} {C : PLLFormula} :
    Nonempty (LaxND Γ C) ↔ SC Γ C :=
  ⟨fun ⟨p⟩ => ND_to_SC p, fun ⟨_, d⟩ => SC_to_ND d⟩

/-! ### Consequences of cut elimination (F&M Lemma 2.7) -/

/-- **Disjunction property** (F&M Lemma 2.7(i)): a cut-free proof of
`⊢ A ∨ B` must end with a right disjunction rule. -/
theorem disjunction_property {A B : PLLFormula}
    (h : Nonempty (LaxND [] (A.or B))) :
    Nonempty (LaxND [] A) ∨ Nonempty (LaxND [] B) := by
  obtain ⟨n, d⟩ := cutElimination.mp h
  cases d with
  | botL h => exact absurd h (by simp)
  | andL h _ => exact absurd h (by simp)
  | orL h _ _ => exact absurd h (by simp)
  | impL h _ _ => exact absurd h (by simp)
  | orR1 d' => exact .inl (SC_to_ND d')
  | orR2 d' => exact .inr (SC_to_ND d')

/-- **`◯`-reflection** (F&M Lemma 2.7(ii)): `⊢ ◯M` implies `⊢ M` — the
inverse of necessitation, impossible in ordinary modal logics. -/
theorem somehow_reflection {A : PLLFormula}
    (h : Nonempty (LaxND [] (A.somehow))) : Nonempty (LaxND [] A) := by
  obtain ⟨n, d⟩ := cutElimination.mp h
  cases d with
  | botL h => exact absurd h (by simp)
  | andL h _ => exact absurd h (by simp)
  | orL h _ _ => exact absurd h (by simp)
  | impL h _ _ => exact absurd h (by simp)
  | laxL h _ => exact absurd h (by simp)
  | laxR d' => exact SC_to_ND d'

-- Cut elimination is choice-free: the lexicographic induction is plain
-- arithmetic on heights and `sizeOf`, and the ND↔SC round trip is
-- membership bookkeeping.
/-- info: 'PLLND.cutElimination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cutElimination

end PLLND
