import LaxLogic.PLLG4P

/-!
# G4iLL″, height-indexed: the final repaired calculus `G4h`/`G4c`

Design revisions 2–3 (`docs/g4p-ladder.md`): the box rules **keep
their box**, and `R◯→` **keeps its principal in the first premise**,
so no rule ever separates a hypothesis from material its premises may
still need —

    Γ, ◯χ, χ ⇒ ◯B                        Γ, ◯χ, ◯φ→ψ, χ ⇒ ◯φ    Γ, ◯χ, ψ ⇒ Δ
    -------------- laxL (= G3's L◯)      ------------------------------------ L◯→″
    Γ, ◯χ ⇒ ◯B                                    Γ, ◯χ, ◯φ→ψ ⇒ Δ

    Γ, ◯φ→ψ ⇒ φ    Γ, ψ ⇒ Δ
    ------------------------ R◯→″
    Γ, ◯φ→ψ ⇒ Δ

— and the judgment carries a **height index** (`G4h n Γ C`, premises at
`n`, conclusion at `n + 1`, exactly the `SCh` pattern of
`PLLSequent.lean`), so that the plumbing lemmas can be proven
*height-preserving* and the cut/contraction inductions can run on the
classical (formula weight, height) lexicographic measures.

Because the boxes are kept, `laxL` needs only a membership hypothesis
(as in `SCh`), and `L◯→″`'s first premise is simply `X :: Γ` — the
whole conclusion context, box and implication included, plus the
opening.  Revision 3 (2026-07-09) gives `R◯→″`'s first premise the
same discipline — the full conclusion context, exactly G3's `L⊃`
premise 1: contraction with a doubled `◯φ→ψ` fired by `R◯→` is
*semantically unfixable* from the consuming form's inverted premises (a
nucleus countermodel refutes the required inference), while the keeping
form hands the inner induction both copies.  The implication is still
*consumed* in every second premise: that is the Dyckhoff residue that
keeps the calculus G4-shaped.

This file: the calculus, height monotonicity, height-preserving
exchange and weakening, the working judgment `G4c := ∃ n, G4h n`, the
embedding `G4p ⊆ G4c` (hence `G4 ⊆ G4c` and the gap sequent), and
soundness `G4c → SC`.
-/

open PLLFormula

namespace PLLND

/-- **G4iLL″**, height-indexed.  Premises at `n`, conclusion at
`n + 1`; axioms at every height. -/
inductive G4h : Nat → List PLLFormula → PLLFormula → Prop
  | init {n : Nat} {Γ : List PLLFormula} {a : String}
      (h : prop a ∈ Γ) : G4h n Γ (prop a)
  | botL {n : Nat} {Γ : List PLLFormula} {C : PLLFormula}
      (h : falsePLL ∈ Γ) : G4h n Γ C
  | andR {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4h n Γ A → G4h n Γ B → G4h (n + 1) Γ (A.and B)
  | orR1 {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4h n Γ A → G4h (n + 1) Γ (A.or B)
  | orR2 {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4h n Γ B → G4h (n + 1) Γ (A.or B)
  | impR {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4h n (A :: Γ) B → G4h (n + 1) Γ (A.ifThen B)
  | laxR {n : Nat} {Γ : List PLLFormula} {A : PLLFormula} :
      G4h n Γ A → G4h (n + 1) Γ A.somehow
  | andL {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.and B :: Δ)) :
      G4h n (A :: B :: Δ) C → G4h (n + 1) Γ C
  | orL {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.or B :: Δ)) :
      G4h n (A :: Δ) C → G4h n (B :: Δ) C → G4h (n + 1) Γ C
  | laxL {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula}
      (h : A.somehow ∈ Γ) :
      G4h n (A :: Γ) B.somehow → G4h (n + 1) Γ B.somehow
  | impLProp {n : Nat} {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
      (h : Γ.Perm ((prop a).ifThen B :: Δ)) (ha : prop a ∈ Δ) :
      G4h n (B :: Δ) C → G4h (n + 1) Γ C
  | impLBot {n : Nat} {Γ Δ : List PLLFormula} {B C : PLLFormula}
      (h : Γ.Perm (falsePLL.ifThen B :: Δ)) :
      G4h n Δ C → G4h (n + 1) Γ C
  | impLAnd {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.and B).ifThen D :: Δ)) :
      G4h n (A.ifThen (B.ifThen D) :: Δ) E → G4h (n + 1) Γ E
  | impLOr {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.or B).ifThen D :: Δ)) :
      G4h n (A.ifThen D :: B.ifThen D :: Δ) E → G4h (n + 1) Γ E
  | impLImp {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
      G4h n (B.ifThen D :: Δ) (A.ifThen B) → G4h n (D :: Δ) E →
      G4h (n + 1) Γ E
  | impLLax {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) :
      G4h n Γ A → G4h n (B :: Δ) C → G4h (n + 1) Γ C
  | impLLaxLax {n : Nat} {Γ Δ : List PLLFormula} {A B X C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) (hX : X.somehow ∈ Δ) :
      G4h n (X :: Γ) A.somehow → G4h n (B :: Δ) C → G4h (n + 1) Γ C

/-- The working judgment: derivable at some height. -/
def G4c (Γ : List PLLFormula) (C : PLLFormula) : Prop := ∃ n, G4h n Γ C

namespace G4h

/-- Bumping the height by one. -/
theorem succ_mono : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    G4h n Γ C → G4h (n + 1) Γ C := by
  intro n Γ C d
  induction d with
  | init h => exact .init h
  | botL h => exact .botL h
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR ih
  | laxR _ ih => exact .laxR ih
  | andL h _ ih => exact .andL h ih
  | orL h _ _ ih₁ ih₂ => exact .orL h ih₁ ih₂
  | laxL h _ ih => exact .laxL h ih
  | impLProp h ha _ ih => exact .impLProp h ha ih
  | impLBot h _ ih => exact .impLBot h ih
  | impLAnd h _ ih => exact .impLAnd h ih
  | impLOr h _ ih => exact .impLOr h ih
  | impLImp h _ _ ih₁ ih₂ => exact .impLImp h ih₁ ih₂
  | impLLax h _ _ ih₁ ih₂ => exact .impLLax h ih₁ ih₂
  | impLLaxLax h hX _ _ ih₁ ih₂ => exact .impLLaxLax h hX ih₁ ih₂

/-- Height monotonicity. -/
theorem mono {n m : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (d : G4h n Γ C) (hnm : n ≤ m) : G4h m Γ C := by
  induction hnm with
  | refl => exact d
  | step _ ih => exact ih.succ_mono

/-- **Height-preserving exchange.** -/
theorem perm : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    G4h n Γ C → ∀ {Γ' : List PLLFormula}, Γ.Perm Γ' → G4h n Γ' C := by
  intro n Γ C d
  induction d with
  | init h => intro Γ' hp; exact .init (hp.subset h)
  | botL h => intro Γ' hp; exact .botL (hp.subset h)
  | andR _ _ ih₁ ih₂ => intro Γ' hp; exact .andR (ih₁ hp) (ih₂ hp)
  | orR1 _ ih => intro Γ' hp; exact .orR1 (ih hp)
  | orR2 _ ih => intro Γ' hp; exact .orR2 (ih hp)
  | impR _ ih => intro Γ' hp; exact .impR (ih (hp.cons _))
  | laxR _ ih => intro Γ' hp; exact .laxR (ih hp)
  | andL h d _ => intro Γ' hp; exact .andL (hp.symm.trans h) d
  | orL h d₁ d₂ _ _ => intro Γ' hp; exact .orL (hp.symm.trans h) d₁ d₂
  | laxL h _ ih =>
      intro Γ' hp
      exact .laxL (hp.subset h) (ih (hp.cons _))
  | impLProp h ha d _ => intro Γ' hp; exact .impLProp (hp.symm.trans h) ha d
  | impLBot h d _ => intro Γ' hp; exact .impLBot (hp.symm.trans h) d
  | impLAnd h d _ => intro Γ' hp; exact .impLAnd (hp.symm.trans h) d
  | impLOr h d _ => intro Γ' hp; exact .impLOr (hp.symm.trans h) d
  | impLImp h d₁ d₂ _ _ => intro Γ' hp; exact .impLImp (hp.symm.trans h) d₁ d₂
  | impLLax h _ d₂ ih₁ _ =>
      intro Γ' hp
      exact .impLLax (hp.symm.trans h) (ih₁ hp) d₂
  | impLLaxLax h hX _ d₂ ih₁ _ =>
      intro Γ' hp
      exact .impLLaxLax (hp.symm.trans h) hX (ih₁ (hp.cons _)) d₂

/-- **Height-preserving weakening.** -/
theorem weaken (ψ : PLLFormula) :
    ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    G4h n Γ C → G4h n (ψ :: Γ) C := by
  have rot : ∀ (x : PLLFormula) (l : List PLLFormula),
      (ψ :: x :: l).Perm (x :: ψ :: l) := fun x l => List.Perm.swap x ψ l
  intro n Γ C d
  induction d with
  | init h => exact .init (.tail _ h)
  | botL h => exact .botL (.tail _ h)
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR (ih.perm (rot _ _))
  | laxR _ ih => exact .laxR ih
  | @andL _ _ Δ A B _ h _ ih =>
      exact .andL ((h.cons ψ).trans (rot _ _))
        (ih.perm ((rot A (B :: Δ)).trans ((rot B Δ).cons A)))
  | @orL _ _ Δ A B _ h _ _ ih₁ ih₂ =>
      exact .orL ((h.cons ψ).trans (rot _ _))
        (ih₁.perm (rot A Δ)) (ih₂.perm (rot B Δ))
  | @laxL _ Γ' A _ h _ ih =>
      exact .laxL (.tail _ h) (ih.perm (rot A Γ'))
  | @impLProp _ _ Δ a B _ h ha _ ih =>
      exact .impLProp ((h.cons ψ).trans (rot _ _)) (.tail _ ha)
        (ih.perm (rot B Δ))
  | impLBot h _ ih =>
      exact .impLBot ((h.cons ψ).trans (rot _ _)) ih
  | @impLAnd _ _ Δ A B D _ h _ ih =>
      exact .impLAnd ((h.cons ψ).trans (rot _ _))
        (ih.perm (rot (A.ifThen (B.ifThen D)) Δ))
  | @impLOr _ _ Δ A B D _ h _ ih =>
      exact .impLOr ((h.cons ψ).trans (rot _ _))
        (ih.perm ((rot (A.ifThen D) _).trans ((rot (B.ifThen D) Δ).cons _)))
  | @impLImp _ _ Δ A B D _ h _ _ ih₁ ih₂ =>
      exact .impLImp ((h.cons ψ).trans (rot _ _))
        (ih₁.perm (rot (B.ifThen D) Δ)) (ih₂.perm (rot D Δ))
  | @impLLax _ _ Δ A B _ h _ _ ih₁ ih₂ =>
      exact .impLLax ((h.cons ψ).trans (rot _ _)) ih₁ (ih₂.perm (rot B Δ))
  | @impLLaxLax _ Γ' Δ A B X _ h hX _ _ ih₁ ih₂ =>
      exact .impLLaxLax ((h.cons ψ).trans (rot _ _)) (.tail _ hX)
        (ih₁.perm (rot X Γ')) (ih₂.perm (rot B Δ))

end G4h

namespace G4c

/-- Exchange at the working judgment. -/
theorem perm {Γ Γ' : List PLLFormula} {C : PLLFormula}
    (d : G4c Γ C) (hp : Γ.Perm Γ') : G4c Γ' C :=
  d.imp fun _ h => h.perm hp

/-- Weakening at the working judgment. -/
theorem weaken {Γ : List PLLFormula} {C : PLLFormula}
    (d : G4c Γ C) (ψ : PLLFormula) : G4c (ψ :: Γ) C :=
  d.imp fun _ h => h.weaken ψ

/-- Align two derivations at a common height. -/
private theorem toSame {Γ₁ Γ₂ : List PLLFormula} {C₁ C₂ : PLLFormula}
    (d₁ : G4c Γ₁ C₁) (d₂ : G4c Γ₂ C₂) :
    ∃ n, G4h n Γ₁ C₁ ∧ G4h n Γ₂ C₂ := by
  obtain ⟨n₁, h₁⟩ := d₁
  obtain ⟨n₂, h₂⟩ := d₂
  exact ⟨max n₁ n₂, h₁.mono (Nat.le_max_left _ _),
    h₂.mono (Nat.le_max_right _ _)⟩

/-- **`G4p` embeds in `G4c`** (hence so do `G4` and all its
derivations, via `G4p.ofG4`): the consuming box rules are simulated by
the keeping ones plus weakening. -/
theorem ofG4p : ∀ {Γ : List PLLFormula} {C : PLLFormula},
    G4p Γ C → G4c Γ C := by
  intro Γ C d
  induction d with
  | init h => exact ⟨0, .init h⟩
  | botL h => exact ⟨0, .botL h⟩
  | andR _ _ ih₁ ih₂ =>
      obtain ⟨n, h₁, h₂⟩ := toSame ih₁ ih₂
      exact ⟨n + 1, .andR h₁ h₂⟩
  | orR1 _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .orR1 h⟩
  | orR2 _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .orR2 h⟩
  | impR _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .impR h⟩
  | laxR _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .laxR h⟩
  | andL hp _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .andL hp h⟩
  | orL hp _ _ ih₁ ih₂ =>
      obtain ⟨n, h₁, h₂⟩ := toSame ih₁ ih₂
      exact ⟨n + 1, .orL hp h₁ h₂⟩
  | @laxL Γ₀ Δ A B hp _ ih =>
      -- old: premise over `A :: Δ`; new premise wants `A :: Γ₀`
      obtain ⟨n, h⟩ := (ih.weaken A.somehow).perm
        ((List.Perm.swap A A.somehow _).trans (hp.cons A).symm)
      exact ⟨n + 1, .laxL (hp.symm.subset (.head _)) h⟩
  | impLProp hp ha _ ih =>
      obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .impLProp hp ha h⟩
  | impLBot hp _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .impLBot hp h⟩
  | impLAnd hp _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .impLAnd hp h⟩
  | impLOr hp _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .impLOr hp h⟩
  | impLImp hp _ _ ih₁ ih₂ =>
      obtain ⟨n, h₁, h₂⟩ := toSame ih₁ ih₂
      exact ⟨n + 1, .impLImp hp h₁ h₂⟩
  | impLLax hp _ _ ih₁ ih₂ =>
      -- old premise 1 over `Δ`; the new one wants the full context
      obtain ⟨n, h₁, h₂⟩ := toSame ((ih₁.weaken _).perm hp.symm) ih₂
      exact ⟨n + 1, .impLLax hp h₁ h₂⟩
  | @impLLaxLax Γ₀ Δ A B X _ hp _ _ ih₁ ih₂ =>
      -- old premise 1 over `F :: X :: Δ`; new wants `X :: Γ₀ ~ X :: F :: ◯X :: Δ`
      have p₁ : G4c (X :: Γ₀) A.somehow :=
        (ih₁.weaken X.somehow).perm
          ((List.perm_middle (l₁ := [X.somehow, A.somehow.ifThen B])).trans
            (((List.Perm.swap _ _ _).cons _).trans (hp.cons X).symm))
      obtain ⟨n, h₁, h₂⟩ := toSame p₁ ih₂
      exact ⟨n + 1, .impLLaxLax hp (.head _) h₁ h₂⟩

/-- The gap sequent, now at the final calculus. -/
theorem gap_derivable :
    G4c [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa] (prop "r") :=
  ofG4p G4p.gap_derivable

private theorem sub_cons {Δ Γ : List PLLFormula}
    (hsub : ∀ ψ ∈ Δ, ψ ∈ Γ) (A : PLLFormula) :
    ∀ ψ ∈ A :: Δ, ψ ∈ A :: Γ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact .head _
  · exact .tail _ (hsub _ hψ)

/-- **Soundness of G4iLL″** into the cut-free G3 calculus `SC`.  The
box-keeping rules match `SC.laxL` exactly, so the modal cases are
*simpler* than for `G4`/`G4p`. -/
theorem toSC : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    G4h n Γ C → SC Γ C := by
  intro n Γ C d
  induction d with
  | init h => exact SC.init h
  | botL h => exact SC.botL h
  | andR _ _ ih₁ ih₂ => exact SC.andR ih₁ ih₂
  | orR1 _ ih => exact SC.orR1 ih
  | orR2 _ ih => exact SC.orR2 ih
  | impR _ ih => exact SC.impR ih
  | laxR _ ih => exact SC.laxR ih
  | @andL _ Γ' Δ' A B _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.andL (h.symm.subset (.head _))
        (ih.rename (sub_cons (sub_cons hΔ B) A))
  | @orL _ Γ' Δ' A B _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.orL (h.symm.subset (.head _))
        (ih₁.rename (sub_cons hΔ A)) (ih₂.rename (sub_cons hΔ B))
  | laxL h _ ih => exact SC.laxL h ih
  | @impLProp _ Γ' Δ' a B _ h ha _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.impL (h.symm.subset (.head _)) (SC.init (hΔ _ ha))
        (ih.rename (sub_cons hΔ B))
  | impLBot h _ ih =>
      exact ih.rename fun ψ hψ => h.symm.subset (.tail _ hψ)
  | @impLAnd _ Γ' Δ' A B D _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hmem := h.symm.subset (List.Mem.head _)
      have p : SC Γ' (A.ifThen (B.ifThen D)) := by
        refine SC.impR (SC.impR ?_)
        exact SC.impL (A := A.and B) (.tail _ (.tail _ hmem))
          (SC.andR (SC.iden _ (.tail _ (.head _))) (SC.iden _ (.head _)))
          (SC.iden _ (.head _))
      exact SC.cut p (ih.rename (sub_cons hΔ _))
  | @impLOr _ Γ' Δ' A B D _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hmem := h.symm.subset (List.Mem.head _)
      have p₁ : SC Γ' (A.ifThen D) :=
        SC.impR (SC.impL (A := A.or B) (.tail _ hmem)
          (SC.orR1 (SC.iden _ (.head _))) (SC.iden _ (.head _)))
      have p₂ : SC Γ' (B.ifThen D) :=
        SC.impR (SC.impL (A := A.or B) (.tail _ hmem)
          (SC.orR2 (SC.iden _ (.head _))) (SC.iden _ (.head _)))
      refine SC.cut p₁ (SC.cut (p₂.rename fun ψ hψ => .tail _ hψ)
        (ih.rename ?_))
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact .tail _ (.head _)
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact .head _
      · exact .tail _ (.tail _ (hΔ _ hψ))
  | @impLImp _ Γ' Δ' A B D _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hmem := h.symm.subset (List.Mem.head _)
      have hBD : SC Γ' (B.ifThen D) :=
        SC.impR (SC.impL (A := A.ifThen B) (.tail _ hmem)
          (SC.impR (SC.iden _ (.tail _ (.head _)))) (SC.iden _ (.head _)))
      have hAB : SC Γ' (A.ifThen B) := SC.cut hBD (ih₁.rename (sub_cons hΔ _))
      exact SC.impL hmem hAB (ih₂.rename (sub_cons hΔ D))
  | @impLLax _ Γ' Δ' A B _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.impL (h.symm.subset (.head _)) (SC.laxR ih₁)
        (ih₂.rename (sub_cons hΔ B))
  | @impLLaxLax _ Γ' Δ' A B X _ h hX _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hF : A.somehow.ifThen B ∈ Γ' := h.symm.subset (.head _)
      -- `◯A` by opening `◯X` — the premise is over the full context
      have hOA : SC Γ' A.somehow := SC.laxL (hΔ _ hX) ih₁
      exact SC.impL hF hOA (ih₂.rename (sub_cons hΔ B))

end G4c

end PLLND
