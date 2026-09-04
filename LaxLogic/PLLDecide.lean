import LaxLogic.PLLG4
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Backward proof search for G4iLL: rule-instance enumeration

Chunk 3a of the decision procedure (F&M Theorem 2.8).  A sequent `(Γ, C)`
has a *finite* list of backward rule instances, `succs Γ C`: each instance
is the list of premise sequents of one way of applying one G4 rule with
conclusion `(Γ, C)`.  Left rules pick their principal formula `P ∈ Γ` and
use `Δ := Γ.erase P` as the side context — `G4`'s `Perm` hypothesis
(`List.perm_cons_erase`) absorbs the bookkeeping, and `G4.perm` transports
derivations between a rule's own side context and the canonical `erase`
representative.

* `succs_sound` : if some instance has all premises derivable, the
  conclusion is derivable — each instance really is a rule application.
* `succs_complete` (next chunk): every derivation ends with one of the
  enumerated instances, premises derivable.
* the Dershowitz–Manna decrease of `smeasure` along every instance, and
  the resulting `Decidable (G4 Γ C)` by well-founded recursion.
-/

open PLLFormula

namespace PLLND

/-- A sequent: context and goal. -/
abbrev Sequent : Type := List PLLFormula × PLLFormula

/-- The termination measure of a sequent: the multiset of Dyckhoff weights
of all formulas in it (context and goal).  A `List ℕ` coerced to
`Multiset ℕ`, so permutation facts transfer by `Multiset.coe_eq_coe`. -/
def smeasure (s : Sequent) : Multiset ℕ :=
  (s.2.weight :: s.1.map PLLFormula.weight : List ℕ)

/-- The backward rule instances contributed by principal formula `P` with
side context `Δ := Γ.erase P`.  Each element is the premise list of one
rule application. -/
def instsFor (Γ : List PLLFormula) (C : PLLFormula) (P : PLLFormula) :
    List (List Sequent) :=
  let Δ := Γ.erase P
  match P with
  | .and A B => [[(A :: B :: Δ, C)]]
  | .or A B => [[(A :: Δ, C), (B :: Δ, C)]]
  | .somehow A =>
      match C with
      | .somehow _ => [[(A :: Δ, C)]]
      | _ => []
  | .ifThen (.prop a) B => if prop a ∈ Δ then [[(B :: Δ, C)]] else []
  | .ifThen .falsePLL _ => [[(Δ, C)]]
  | .ifThen (.and A B) D => [[(A.ifThen (B.ifThen D) :: Δ, C)]]
  | .ifThen (.or A B) D => [[(A.ifThen D :: B.ifThen D :: Δ, C)]]
  | .ifThen (.ifThen A B) D => [[(B.ifThen D :: Δ, A.ifThen B), (D :: Δ, C)]]
  | .ifThen (.somehow A) B =>
      [(Δ, A), (B :: Δ, C)] ::
      Δ.filterMap fun Q =>
        match Q with
        | .somehow X => some [(X :: Δ.erase Q, A.somehow), (B :: Q :: Δ.erase Q, C)]
        | _ => none
  | _ => []

/-- Backward rule instances from the goal (leaves and right rules). -/
def rightInsts (Γ : List PLLFormula) : PLLFormula → List (List Sequent)
  | .prop a => if prop a ∈ Γ then [[]] else []
  | .falsePLL => []
  | .and A B => [[(Γ, A), (Γ, B)]]
  | .or A B => [[(Γ, A)], [(Γ, B)]]
  | .ifThen A B => [[(A :: Γ, B)]]
  | .somehow A => [[(Γ, A)]]

/-- All backward rule instances of the sequent `(Γ, C)`. -/
def succs (Γ : List PLLFormula) (C : PLLFormula) : List (List Sequent) :=
  (if falsePLL ∈ Γ then [[]] else []) ++ rightInsts Γ C
    ++ Γ.flatMap (instsFor Γ C)

namespace G4

/-- **Soundness of the enumeration**: every instance in `succs Γ C` with
all premises derivable yields `G4 Γ C`. -/
theorem succs_sound : ∀ {Γ : List PLLFormula} {C : PLLFormula}
    {inst : List Sequent}, inst ∈ succs Γ C →
    (∀ s ∈ inst, G4 s.1 s.2) → G4 Γ C := by
  intro Γ C inst hi hp
  simp only [succs, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · -- botL
    split at hi
    · exact .botL ‹_›
    · cases hi
  · -- right rules: split on the goal
    cases C with
    | prop a =>
        simp only [rightInsts] at hi
        split at hi
        · exact .init ‹_›
        · cases hi
    | falsePLL => cases hi
    | and A B =>
        cases hi with
        | head => exact .andR (hp _ (.head _)) (hp _ (.tail _ (.head _)))
        | tail _ h => cases h
    | or A B =>
        cases hi with
        | head => exact .orR1 (hp _ (.head _))
        | tail _ h =>
            cases h with
            | head => exact .orR2 (hp _ (.head _))
            | tail _ h => cases h
    | ifThen A B =>
        cases hi with
        | head => exact .impR (hp _ (.head _))
        | tail _ h => cases h
    | somehow A =>
        cases hi with
        | head => exact .laxR (hp _ (.head _))
        | tail _ h => cases h
  · -- left rules
    obtain ⟨P, hP, hi⟩ := List.mem_flatMap.mp hi
    have hperm := List.perm_cons_erase hP
    cases P with
    | prop a => cases hi
    | falsePLL => cases hi
    | and A B =>
        cases hi with
        | head => exact .andL hperm (hp _ (.head _))
        | tail _ h => cases h
    | or A B =>
        cases hi with
        | head => exact .orL hperm (hp _ (.head _)) (hp _ (.tail _ (.head _)))
        | tail _ h => cases h
    | somehow A =>
        cases C with
        | somehow B =>
            cases hi with
            | head => exact .laxL hperm (hp _ (.head _))
            | tail _ h => cases h
        | prop a => cases hi
        | falsePLL => cases hi
        | and _ _ => cases hi
        | or _ _ => cases hi
        | ifThen _ _ => cases hi
    | ifThen A' B =>
        cases A' with
        | prop a =>
            simp only [instsFor] at hi
            split at hi
            · cases hi with
              | head => exact .impLProp hperm ‹_› (hp _ (.head _))
              | tail _ h => cases h
            · cases hi
        | falsePLL =>
            cases hi with
            | head => exact .impLBot hperm (hp _ (.head _))
            | tail _ h => cases h
        | and A₁ A₂ =>
            cases hi with
            | head => exact .impLAnd hperm (hp _ (.head _))
            | tail _ h => cases h
        | or A₁ A₂ =>
            cases hi with
            | head => exact .impLOr hperm (hp _ (.head _))
            | tail _ h => cases h
        | ifThen A₁ A₂ =>
            cases hi with
            | head =>
                exact .impLImp hperm (hp _ (.head _)) (hp _ (.tail _ (.head _)))
            | tail _ h => cases h
        | somehow A₁ =>
            cases hi with
            | head =>
                exact .impLLax hperm (hp _ (.head _)) (hp _ (.tail _ (.head _)))
            | tail _ hi =>
                obtain ⟨Q, hQ, hf⟩ := List.mem_filterMap.mp hi
                cases Q with
                | somehow X =>
                    simp only [Option.some_inj] at hf; subst hf
                    exact .impLLaxLax
                      (hperm.trans ((List.perm_cons_erase hQ).cons _))
                      (hp _ (.head _)) (hp _ (.tail _ (.head _)))
                | prop _ => cases hf
                | falsePLL => cases hf
                | and _ _ => cases hf
                | or _ _ => cases hf
                | ifThen _ _ => cases hf

/-- Cancel the head of a `Perm` against the canonical `erase`
representative: a rule's own side context is a permutation of it. -/
private theorem perm_erase {Γ Δ : List PLLFormula} {P : PLLFormula}
    (h : Γ.Perm (P :: Δ)) : Δ.Perm (Γ.erase P) :=
  (h.symm.trans (List.perm_cons_erase (h.symm.subset (.head _)))).cons_inv

/-- **Completeness of the enumeration**: every derivation ends with one of
the instances in `succs Γ C`, all premises derivable.  Pure case analysis
on the last rule — no induction — with `G4.perm` mediating between the
rule's side context `Δ` and the canonical representative `Γ.erase P`. -/
theorem succs_complete : ∀ {Γ : List PLLFormula} {C : PLLFormula},
    G4 Γ C → ∃ inst ∈ succs Γ C, ∀ s ∈ inst, G4 s.1 s.2 := by
  intro Γ C d
  cases d with
  | init h =>
      exact ⟨[], by simp [succs, rightInsts, h], fun s hs => nomatch hs⟩
  | botL h =>
      exact ⟨[], by simp [succs, h], fun s hs => nomatch hs⟩
  | @andR _ A B d₁ d₂ =>
      refine ⟨[(Γ, A), (Γ, B)], by simp [succs, rightInsts], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₂
      · exact nomatch hs
  | @orR1 _ A B d₁ =>
      refine ⟨[(Γ, A)], by simp [succs, rightInsts], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁
      · exact nomatch hs
  | @orR2 _ A B d₂ =>
      refine ⟨[(Γ, B)], by simp [succs, rightInsts], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₂
      · exact nomatch hs
  | @impR _ A B d₁ =>
      refine ⟨[(A :: Γ, B)], by simp [succs, rightInsts], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁
      · exact nomatch hs
  | @laxR _ A d₁ =>
      refine ⟨[(Γ, A)], by simp [succs, rightInsts], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁
      · exact nomatch hs
  | @andL _ Δ A B _ h d₁ =>
      have hP : A.and B ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase (A.and B)) := perm_erase h
      refine ⟨[(A :: B :: Γ.erase (A.and B), C)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, .head _⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm ((he.cons B).cons A)
      · exact nomatch hs
  | @orL _ Δ A B _ h d₁ d₂ =>
      have hP : A.or B ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase (A.or B)) := perm_erase h
      refine ⟨[(A :: Γ.erase (A.or B), C), (B :: Γ.erase (A.or B), C)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, .head _⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm (he.cons A)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₂.perm (he.cons B)
      · exact nomatch hs
  | @laxL _ Δ A B h d₁ =>
      have hP : A.somehow ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase A.somehow) := perm_erase h
      refine ⟨[(A :: Γ.erase A.somehow, B.somehow)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, .head _⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm (he.cons A)
      · exact nomatch hs
  | @impLProp _ Δ a B _ h ha d₁ =>
      have hP : (prop a).ifThen B ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase ((prop a).ifThen B)) := perm_erase h
      refine ⟨[(B :: Γ.erase ((prop a).ifThen B), C)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, ?_⟩), ?_⟩
      · simp only [instsFor]
        rw [if_pos (he.subset ha)]
        exact .head _
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm (he.cons B)
      · exact nomatch hs
  | @impLBot _ Δ B _ h d₁ =>
      have hP : falsePLL.ifThen B ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase (falsePLL.ifThen B)) := perm_erase h
      refine ⟨[(Γ.erase (falsePLL.ifThen B), C)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, .head _⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm he
      · exact nomatch hs
  | @impLAnd _ Δ A B D _ h d₁ =>
      have hP : (A.and B).ifThen D ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase ((A.and B).ifThen D)) := perm_erase h
      refine ⟨[(A.ifThen (B.ifThen D) :: Γ.erase ((A.and B).ifThen D), C)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, .head _⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm (he.cons _)
      · exact nomatch hs
  | @impLOr _ Δ A B D _ h d₁ =>
      have hP : (A.or B).ifThen D ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase ((A.or B).ifThen D)) := perm_erase h
      refine ⟨[(A.ifThen D :: B.ifThen D :: Γ.erase ((A.or B).ifThen D), C)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, .head _⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm ((he.cons _).cons _)
      · exact nomatch hs
  | @impLImp _ Δ A B D _ h d₁ d₂ =>
      have hP : (A.ifThen B).ifThen D ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase ((A.ifThen B).ifThen D)) := perm_erase h
      refine ⟨[(B.ifThen D :: Γ.erase ((A.ifThen B).ifThen D), A.ifThen B),
               (D :: Γ.erase ((A.ifThen B).ifThen D), C)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, .head _⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm (he.cons _)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₂.perm (he.cons _)
      · exact nomatch hs
  | @impLLax _ Δ A B _ h d₁ d₂ =>
      have hP : A.somehow.ifThen B ∈ Γ := h.symm.subset (.head _)
      have he : Δ.Perm (Γ.erase (A.somehow.ifThen B)) := perm_erase h
      refine ⟨[(Γ.erase (A.somehow.ifThen B), A),
               (B :: Γ.erase (A.somehow.ifThen B), C)],
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP, .head _⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm he
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₂.perm (he.cons B)
      · exact nomatch hs
  | @impLLaxLax _ Δ A B X _ h d₁ d₂ =>
      have hP : A.somehow.ifThen B ∈ Γ := h.symm.subset (.head _)
      have h₁ : (X.somehow :: Δ).Perm (Γ.erase (A.somehow.ifThen B)) :=
        perm_erase h
      have hQ : X.somehow ∈ Γ.erase (A.somehow.ifThen B) := h₁.subset (.head _)
      have he : Δ.Perm ((Γ.erase (A.somehow.ifThen B)).erase X.somehow) :=
        (h₁.trans (List.perm_cons_erase hQ)).cons_inv
      refine ⟨_, List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hP,
        .tail _ (List.mem_filterMap.mpr ⟨X.somehow, hQ, rfl⟩)⟩), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₁.perm (he.cons X)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact d₂.perm ((he.cons X.somehow).cons B)
      · exact nomatch hs

/-! ### The measure decreases along every backward rule instance -/

/-- Package a Dershowitz–Manna witness from list-level data: the smaller
multiset is `Y ++ M` up to permutation, the larger `Z ++ M`, and every
element of `Y` is below some element of `Z`. -/
private theorem dm_of_perms {s t Y Z M : List ℕ}
    (hs : s.Perm (Y ++ M)) (ht : t.Perm (Z ++ M)) (hZ : Z ≠ [])
    (h : ∀ y ∈ Y, ∃ z ∈ Z, y < z) :
    Multiset.IsDershowitzMannaLT (↑s : Multiset ℕ) (↑t : Multiset ℕ) := by
  refine ⟨(M : Multiset ℕ), (Y : Multiset ℕ), (Z : Multiset ℕ), ?_, ?_, ?_, ?_⟩
  · simpa using hZ
  · rw [Multiset.coe_add]
    exact Multiset.coe_eq_coe.mpr (hs.trans List.perm_append_comm)
  · rw [Multiset.coe_add]
    exact Multiset.coe_eq_coe.mpr (ht.trans List.perm_append_comm)
  · simpa using h

private theorem perm_back1 {α : Type _} (a b : α) (l : List α) :
    (a :: b :: l).Perm (b :: a :: l) := List.Perm.swap b a l

private theorem perm_back2 {α : Type _} (a b c : α) (l : List α) :
    (a :: b :: c :: l).Perm (b :: c :: a :: l) :=
  (perm_back1 a b _).trans ((perm_back1 a c l).cons b)

/-- **Termination**: along every instance in `succs Γ C`, every premise is
strictly below the conclusion in the Dershowitz–Manna order on weight
multisets.  Case sweep matching `succs_sound`, each case exhibiting the
`X/Y/Z` decomposition; the only arithmetic is Dyckhoff's weight bookkeeping
(`weight_pos` + `omega`). -/
theorem succs_dec : ∀ {Γ : List PLLFormula} {C : PLLFormula}
    {inst : List Sequent} {s : Sequent}, inst ∈ succs Γ C → s ∈ inst →
    Multiset.IsDershowitzMannaLT (smeasure s) (smeasure (Γ, C)) := by
  intro Γ C inst s hi hs
  simp only [succs, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · -- botL: no premises
    split at hi
    · cases hi with
      | head => exact nomatch hs
      | tail _ h => cases h
    · cases hi
  · -- right rules
    cases C with
    | prop a =>
        simp only [rightInsts] at hi
        split at hi
        · cases hi with
          | head => exact nomatch hs
          | tail _ h => cases h
        · cases hi
    | falsePLL => cases hi
    | and A B =>
        cases hi with
        | head =>
            rcases List.mem_cons.mp hs with rfl | hs'
            · refine dm_of_perms (Y := [A.weight]) (Z := [(A.and B).weight])
                (M := Γ.map weight) (List.Perm.refl _) (List.Perm.refl _)
                (by simp) ?_
              intro y hy
              have hB := B.weight_pos
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              · exact nomatch hy
            rcases List.mem_cons.mp hs' with rfl | hs'
            · refine dm_of_perms (Y := [B.weight]) (Z := [(A.and B).weight])
                (M := Γ.map weight) (List.Perm.refl _) (List.Perm.refl _)
                (by simp) ?_
              intro y hy
              have hA := A.weight_pos
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              · exact nomatch hy
            · exact nomatch hs'
        | tail _ h => cases h
    | or A B =>
        cases hi with
        | head =>
            rcases List.mem_cons.mp hs with rfl | hs'
            · refine dm_of_perms (Y := [A.weight]) (Z := [(A.or B).weight])
                (M := Γ.map weight) (List.Perm.refl _) (List.Perm.refl _)
                (by simp) ?_
              intro y hy
              have hB := B.weight_pos
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              · exact nomatch hy
            · exact nomatch hs'
        | tail _ h =>
            cases h with
            | head =>
                rcases List.mem_cons.mp hs with rfl | hs'
                · refine dm_of_perms (Y := [B.weight]) (Z := [(A.or B).weight])
                    (M := Γ.map weight) (List.Perm.refl _) (List.Perm.refl _)
                    (by simp) ?_
                  intro y hy
                  have hA := A.weight_pos
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
                  · exact nomatch hy
                · exact nomatch hs'
            | tail _ h => cases h
    | ifThen A B =>
        cases hi with
        | head =>
            rcases List.mem_cons.mp hs with rfl | hs'
            · refine dm_of_perms (Y := [B.weight, A.weight])
                (Z := [(A.ifThen B).weight])
                (M := Γ.map weight) (List.Perm.refl _) (List.Perm.refl _)
                (by simp) ?_
              intro y hy
              have hA := A.weight_pos; have hB := B.weight_pos
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              · exact nomatch hy
            · exact nomatch hs'
        | tail _ h => cases h
    | somehow A =>
        cases hi with
        | head =>
            rcases List.mem_cons.mp hs with rfl | hs'
            · refine dm_of_perms (Y := [A.weight]) (Z := [A.somehow.weight])
                (M := Γ.map weight) (List.Perm.refl _) (List.Perm.refl _)
                (by simp) ?_
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              · exact nomatch hy
            · exact nomatch hs'
        | tail _ h => cases h
  · -- left rules
    obtain ⟨P, hP, hi⟩ := List.mem_flatMap.mp hi
    have hΓ : (Γ.map weight).Perm (P.weight :: (Γ.erase P).map weight) :=
      (List.perm_cons_erase hP).map _
    cases P with
    | prop a => cases hi
    | falsePLL => cases hi
    | and A B =>
        cases hi with
        | head =>
            rcases List.mem_cons.mp hs with rfl | hs'
            · refine dm_of_perms (Y := [A.weight, B.weight])
                (Z := [(A.and B).weight])
                (M := C.weight :: (Γ.erase (A.and B)).map weight)
                (perm_back2 _ _ _ _)
                ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
              intro y hy
              have hA := A.weight_pos; have hB := B.weight_pos
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              · exact nomatch hy
            · exact nomatch hs'
        | tail _ h => cases h
    | or A B =>
        cases hi with
        | head =>
            rcases List.mem_cons.mp hs with rfl | hs'
            · refine dm_of_perms (Y := [A.weight]) (Z := [(A.or B).weight])
                (M := C.weight :: (Γ.erase (A.or B)).map weight)
                (perm_back1 _ _ _)
                ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
              intro y hy
              have hB := B.weight_pos
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              · exact nomatch hy
            rcases List.mem_cons.mp hs' with rfl | hs'
            · refine dm_of_perms (Y := [B.weight]) (Z := [(A.or B).weight])
                (M := C.weight :: (Γ.erase (A.or B)).map weight)
                (perm_back1 _ _ _)
                ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
              intro y hy
              have hA := A.weight_pos
              rcases List.mem_cons.mp hy with rfl | hy
              · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
              · exact nomatch hy
            · exact nomatch hs'
        | tail _ h => cases h
    | somehow A =>
        cases C with
        | somehow B =>
            cases hi with
            | head =>
                rcases List.mem_cons.mp hs with rfl | hs'
                · refine dm_of_perms (Y := [A.weight])
                    (Z := [A.somehow.weight])
                    (M := B.somehow.weight ::
                      (Γ.erase A.somehow).map weight)
                    (perm_back1 _ _ _)
                    ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
                  intro y hy
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .head _, by simp only [PLLFormula.weight]; omega⟩
                  · exact nomatch hy
                · exact nomatch hs'
            | tail _ h => cases h
        | prop a => cases hi
        | falsePLL => cases hi
        | and _ _ => cases hi
        | or _ _ => cases hi
        | ifThen _ _ => cases hi
    | ifThen A' B =>
        cases A' with
        | prop a =>
            simp only [instsFor] at hi
            split at hi
            · cases hi with
              | head =>
                  rcases List.mem_cons.mp hs with rfl | hs'
                  · refine dm_of_perms (Y := [B.weight])
                      (Z := [((prop a).ifThen B).weight])
                      (M := C.weight ::
                        (Γ.erase ((prop a).ifThen B)).map weight)
                      (perm_back1 _ _ _)
                      ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
                    intro y hy
                    rcases List.mem_cons.mp hy with rfl | hy
                    · exact ⟨_, .head _,
                        by simp only [PLLFormula.weight]; omega⟩
                    · exact nomatch hy
                  · exact nomatch hs'
              | tail _ h => cases h
            · cases hi
        | falsePLL =>
            cases hi with
            | head =>
                rcases List.mem_cons.mp hs with rfl | hs'
                · refine dm_of_perms (Y := [])
                    (Z := [(falsePLL.ifThen B).weight])
                    (M := C.weight ::
                      (Γ.erase (falsePLL.ifThen B)).map weight)
                    (List.Perm.refl _)
                    ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp)
                    (by intro y hy; exact nomatch hy)
                · exact nomatch hs'
            | tail _ h => cases h
        | and A₁ A₂ =>
            cases hi with
            | head =>
                rcases List.mem_cons.mp hs with rfl | hs'
                · refine dm_of_perms
                    (Y := [(A₁.ifThen (A₂.ifThen B)).weight])
                    (Z := [((A₁.and A₂).ifThen B).weight])
                    (M := C.weight ::
                      (Γ.erase ((A₁.and A₂).ifThen B)).map weight)
                    (perm_back1 _ _ _)
                    ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
                  intro y hy
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .head _,
                      by simp only [PLLFormula.weight]; omega⟩
                  · exact nomatch hy
                · exact nomatch hs'
            | tail _ h => cases h
        | or A₁ A₂ =>
            cases hi with
            | head =>
                rcases List.mem_cons.mp hs with rfl | hs'
                · refine dm_of_perms
                    (Y := [(A₁.ifThen B).weight, (A₂.ifThen B).weight])
                    (Z := [((A₁.or A₂).ifThen B).weight])
                    (M := C.weight ::
                      (Γ.erase ((A₁.or A₂).ifThen B)).map weight)
                    (perm_back2 _ _ _ _)
                    ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
                  intro y hy
                  have h₁ := A₁.weight_pos; have h₂ := A₂.weight_pos
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .head _,
                      by simp only [PLLFormula.weight]; omega⟩
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .head _,
                      by simp only [PLLFormula.weight]; omega⟩
                  · exact nomatch hy
                · exact nomatch hs'
            | tail _ h => cases h
        | ifThen A₁ A₂ =>
            cases hi with
            | head =>
                rcases List.mem_cons.mp hs with rfl | hs'
                · -- first premise: goal changes to A₁ ⊃ A₂
                  refine dm_of_perms
                    (Y := [(A₁.ifThen A₂).weight, (A₂.ifThen B).weight])
                    (Z := [C.weight, ((A₁.ifThen A₂).ifThen B).weight])
                    (M := (Γ.erase ((A₁.ifThen A₂).ifThen B)).map weight)
                    (List.Perm.refl _) (hΓ.cons _) (by simp) ?_
                  intro y hy
                  have h₁ := A₁.weight_pos; have h₂ := A₂.weight_pos
                  have hB := B.weight_pos
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .tail _ (.head _),
                      by simp only [PLLFormula.weight]; omega⟩
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .tail _ (.head _),
                      by simp only [PLLFormula.weight]; omega⟩
                  · exact nomatch hy
                rcases List.mem_cons.mp hs' with rfl | hs'
                · refine dm_of_perms (Y := [B.weight])
                    (Z := [((A₁.ifThen A₂).ifThen B).weight])
                    (M := C.weight ::
                      (Γ.erase ((A₁.ifThen A₂).ifThen B)).map weight)
                    (perm_back1 _ _ _)
                    ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
                  intro y hy
                  have h₁ := A₁.weight_pos; have h₂ := A₂.weight_pos
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .head _,
                      by simp only [PLLFormula.weight]; omega⟩
                  · exact nomatch hy
                · exact nomatch hs'
            | tail _ h => cases h
        | somehow A₁ =>
            cases hi with
            | head =>
                rcases List.mem_cons.mp hs with rfl | hs'
                · -- first premise of R#→: goal changes to A₁, context shrinks
                  refine dm_of_perms (Y := [A₁.weight])
                    (Z := [C.weight, (A₁.somehow.ifThen B).weight])
                    (M := (Γ.erase (A₁.somehow.ifThen B)).map weight)
                    (List.Perm.refl _) (hΓ.cons _) (by simp) ?_
                  intro y hy
                  have hB := B.weight_pos
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .tail _ (.head _),
                      by simp only [PLLFormula.weight]; omega⟩
                  · exact nomatch hy
                rcases List.mem_cons.mp hs' with rfl | hs'
                · refine dm_of_perms (Y := [B.weight])
                    (Z := [(A₁.somehow.ifThen B).weight])
                    (M := C.weight ::
                      (Γ.erase (A₁.somehow.ifThen B)).map weight)
                    (perm_back1 _ _ _)
                    ((hΓ.cons _).trans (perm_back1 _ _ _)) (by simp) ?_
                  intro y hy
                  have h₁ := A₁.weight_pos
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact ⟨_, .head _,
                      by simp only [PLLFormula.weight]; omega⟩
                  · exact nomatch hy
                · exact nomatch hs'
            | tail _ hi =>
                -- L#→ instances from the filterMap over boxed context formulas
                obtain ⟨Q, hQ, hf⟩ := List.mem_filterMap.mp hi
                cases Q with
                | somehow X =>
                    simp only [Option.some_inj] at hf; subst hf
                    have hΔ : ((Γ.erase (A₁.somehow.ifThen B)).map weight).Perm
                        (X.somehow.weight ::
                          ((Γ.erase (A₁.somehow.ifThen B)).erase
                            X.somehow).map weight) :=
                      (List.perm_cons_erase hQ).map _
                    rcases List.mem_cons.mp hs with rfl | hs'
                    · refine dm_of_perms
                        (Y := [A₁.somehow.weight, X.weight])
                        (Z := [C.weight, (A₁.somehow.ifThen B).weight,
                               X.somehow.weight])
                        (M := ((Γ.erase (A₁.somehow.ifThen B)).erase
                          X.somehow).map weight)
                        (List.Perm.refl _)
                        ((hΓ.trans (hΔ.cons _)).cons _) (by simp) ?_
                      intro y hy
                      have hB := B.weight_pos
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact ⟨_, .tail _ (.head _),
                          by simp only [PLLFormula.weight]; omega⟩
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact ⟨_, .tail _ (.tail _ (.head _)),
                          by simp only [PLLFormula.weight]; omega⟩
                      · exact nomatch hy
                    rcases List.mem_cons.mp hs' with rfl | hs'
                    · refine dm_of_perms (Y := [B.weight])
                        (Z := [(A₁.somehow.ifThen B).weight])
                        (M := C.weight :: X.somehow.weight ::
                          ((Γ.erase (A₁.somehow.ifThen B)).erase
                            X.somehow).map weight)
                        (perm_back1 _ _ _)
                        (((hΓ.trans (hΔ.cons _)).cons _).trans
                          (perm_back1 _ _ _)) (by simp) ?_
                      intro y hy
                      have h₁ := A₁.weight_pos
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact ⟨_, .head _,
                          by simp only [PLLFormula.weight]; omega⟩
                      · exact nomatch hy
                    · exact nomatch hs'
                | prop _ => cases hf
                | falsePLL => cases hf
                | and _ _ => cases hf
                | or _ _ => cases hf
                | ifThen _ _ => cases hf

/-! ### The decision procedure -/

/-- Dependent bounded-∀ decidability: decide `∀ x ∈ l, p x` from
deciders available only for members. -/
private def decBAll {α : Type _} (p : α → Prop) :
    (l : List α) → (∀ x ∈ l, Decidable (p x)) → Decidable (∀ x ∈ l, p x)
  | [], _ => isTrue fun _ hx => nomatch hx
  | a :: l, h =>
      match h a (.head _), decBAll p l (fun x hx => h x (.tail _ hx)) with
      | isTrue ha, isTrue hl => isTrue (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hl x hx)
      | isFalse ha, _ => isFalse fun H => ha (H a (.head _))
      | _, isFalse hl => isFalse fun H => hl fun x hx => H x (.tail _ hx)

/-- Dependent bounded-∃ decidability. -/
private def decBEx {α : Type _} (p : α → Prop) :
    (l : List α) → (∀ x ∈ l, Decidable (p x)) → Decidable (∃ x ∈ l, p x)
  | [], _ => isFalse fun ⟨_, hx, _⟩ => nomatch hx
  | a :: l, h =>
      match h a (.head _), decBEx p l (fun x hx => h x (.tail _ hx)) with
      | isTrue ha, _ => isTrue ⟨a, .head _, ha⟩
      | isFalse _, isTrue hl =>
          isTrue (hl.imp fun _ ⟨hx, hp⟩ => ⟨.tail _ hx, hp⟩)
      | isFalse ha, isFalse hl => isFalse (by
          rintro ⟨x, hx, hp⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha hp
          · exact hl ⟨x, hx, hp⟩)

/-- **The decision procedure for G4iLL** (hence, once G3→G4 completeness
lands, for PLL derivability — F&M Theorem 2.8): well-founded recursion on
the Dershowitz–Manna measure, searching the finitely many backward rule
instances at each sequent. -/
def decideG4 : ∀ s : Sequent, Decidable (G4 s.1 s.2) :=
  WellFounded.fix (C := fun s => Decidable (G4 s.1 s.2))
    (InvImage.wf smeasure Multiset.wellFounded_isDershowitzMannaLT)
    fun s ih =>
      letI : Decidable (∃ inst ∈ succs s.1 s.2, ∀ p ∈ inst, G4 p.1 p.2) :=
        decBEx _ (succs s.1 s.2) fun inst hinst =>
          decBAll _ inst fun p hp => ih p (succs_dec hinst hp)
      decidable_of_iff _
        ⟨fun ⟨_, hi, hp⟩ => succs_sound hi hp, succs_complete⟩

instance instDecidableG4 (Γ : List PLLFormula) (C : PLLFormula) :
    Decidable (G4 Γ C) := decideG4 (Γ, C)

/-! ### Executable tests

`decide`-style kernel reduction is unavailable (`WellFounded.fix` does not
iota-reduce in the kernel), but the compiler runs the procedure fine; the
`#guard_msgs`/`#eval` pairs below are checked at build time. -/

-- ◯-unit `A ⊃ ◯A`
/-- info: true -/
#guard_msgs in
#eval decide (G4 [] ((prop "A").ifThen (prop "A").somehow))

-- ◯-multiplication `◯◯A ⊃ ◯A`
/-- info: true -/
#guard_msgs in
#eval decide (G4 [] ((prop "A").somehow.somehow.ifThen (prop "A").somehow))

-- ◯-reflection `◯A ⊃ A` is NOT a theorem of PLL
/-- info: false -/
#guard_msgs in
#eval decide (G4 [] ((prop "A").somehow.ifThen (prop "A")))

-- excluded middle fails (PLL is intuitionistic)
/-- info: false -/
#guard_msgs in
#eval decide (G4 [] ((prop "A").or ((prop "A").ifThen falsePLL)))

-- Howe's duplication sequent, this time found by the prover
/-- info: true -/
#guard_msgs in
#eval decide (G4 [((prop "B").ifThen ((prop "A").somehow.ifThen (prop "C"))).ifThen
    (prop "A").somehow, (prop "A").somehow.ifThen (prop "C"), (prop "B").somehow]
    (prop "C"))

-- ◯ does not commute with ∨ in general: `◯(A ∨ B) ⊃ (◯A ∨ ◯B)` fails
/-- info: false -/
#guard_msgs in
#eval decide (G4 [] (((prop "A").or (prop "B")).somehow.ifThen
    ((prop "A").somehow.or (prop "B").somehow)))

end G4

end PLLND
