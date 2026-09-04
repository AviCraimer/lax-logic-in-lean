import LaxLogic.PLLG4HStr

/-!
# Contraction for G4iLL″: height-preserving atomic, then full — cut-free

Two results:

* `G4h.contract_atom` — contraction of an *atom*, height-preservingly:
  atoms are never the principal formula of a left rule (only `init`'s
  conclusion and `Lp→`'s side condition mention them), so both copies
  travel into every premise and the only content is permutation
  bookkeeping.  Consumed by the cut theorem's `init` case.
* `G4c.contract` — **full contraction, with no cut anywhere** (design
  revision 3, `docs/g4p-ladder.md`): outer induction on the weight of
  the contracted formula, inner structural induction on the
  derivation.  The classical Dyckhoff–Negri order — contraction before
  cut — is thereby restored for the lax calculus.
-/

open PLLFormula

namespace PLLND

namespace G4h

/-- Push a fresh head past two designated copies. -/
private theorem push2 {x q : PLLFormula} {Γ : List PLLFormula} :
    (x :: q :: q :: Γ).Perm (q :: q :: x :: Γ) :=
  (List.Perm.swap q x _).trans ((List.Perm.swap q x Γ).cons q)

/-- Push a block of new formulas past the two copies. -/
private theorem pushL (L : List PLLFormula) {q : PLLFormula}
    {Δ Γ₀ : List PLLFormula} (hΔ : Δ.Perm (q :: q :: Γ₀)) :
    (L ++ Δ).Perm (q :: q :: (L ++ Γ₀)) :=
  (hΔ.append_left L).trans (List.perm_middle.trans (List.perm_middle.cons q))

/-- Cross-split: a context that exposes both a principal `P` and the
two copies of `q` (with `P ≠ q`) admits a common remainder. -/
private theorem cross_split {P q : PLLFormula} {Γ' Δ Γ : List PLLFormula}
    (h : Γ'.Perm (P :: Δ)) (hp : Γ'.Perm (q :: q :: Γ)) (hne : P ≠ q) :
    ∃ Γ₀, Δ.Perm (q :: q :: Γ₀) ∧ Γ.Perm (P :: Γ₀) := by
  rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l₁, hΔ, hm⟩
  · exact absurd e hne
  rcases G4.perm_cons_cases hm with ⟨e, _⟩ | ⟨l₂, hΓ, hl₁⟩
  · exact absurd e.symm hne
  exact ⟨l₂, hΔ.trans (hl₁.cons q), hΓ⟩

/-- **Height-preserving contraction of an atom.** -/
theorem contract_atom {p : String} :
    ∀ {n : Nat} {Γ' : List PLLFormula} {E : PLLFormula}, G4h n Γ' E →
    ∀ {Γ : List PLLFormula}, Γ'.Perm (prop p :: prop p :: Γ) →
    G4h n (prop p :: Γ) E := by
  intro n Γ' E d
  induction d with
  | init h =>
      intro Γ hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · exact .init (by rw [e]; exact .head _)
      rcases List.mem_cons.mp h' with e | h''
      · exact .init (by rw [e]; exact .head _)
      · exact .init (.tail _ h'')
  | botL h =>
      intro Γ hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · cases e
      rcases List.mem_cons.mp h' with e | h''
      · cases e
      · exact .botL (.tail _ h'')
  | andR _ _ ih₁ ih₂ => intro Γ hp; exact .andR (ih₁ hp) (ih₂ hp)
  | orR1 _ ih => intro Γ hp; exact .orR1 (ih hp)
  | orR2 _ ih => intro Γ hp; exact .orR2 (ih hp)
  | laxR _ ih => intro Γ hp; exact .laxR (ih hp)
  | @impR _ _ A _ _ ih =>
      intro Γ hp
      exact .impR ((ih ((hp.cons A).trans push2)).perm (List.Perm.swap _ _ _))
  | @andL _ _ Δ A B _ h _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .andL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih (pushL [A, B] hΔ)).perm (List.perm_middle (l₁ := [A, B])).symm)
  | @orL _ _ Δ A B _ h _ _ ih₁ ih₂ =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .orL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih₁ (pushL [A] hΔ)).perm (List.perm_middle (l₁ := [A])).symm)
        ((ih₂ (pushL [B] hΔ)).perm (List.perm_middle (l₁ := [B])).symm)
  | @laxL _ _ A _ h _ ih =>
      intro Γ hp
      have h' : A.somehow ∈ prop p :: Γ := by
        rcases List.mem_cons.mp (hp.subset h) with e | h'
        · cases e
        rcases List.mem_cons.mp h' with e | h''
        · cases e
        · exact .tail _ h''
      exact .laxL h'
        ((ih ((hp.cons A).trans push2)).perm (List.Perm.swap _ _ _))
  | @impLProp _ _ Δ a B _ h ha _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      have ha' : prop a ∈ prop p :: Γ₀ := by
        rcases List.mem_cons.mp (hΔ.subset ha) with e | h'
        · rw [e]; exact .head _
        rcases List.mem_cons.mp h' with e | h''
        · rw [e]; exact .head _
        · exact .tail _ h''
      exact .impLProp ((hΓ.cons _).trans (List.Perm.swap _ _ _)) ha'
        ((ih (pushL [B] hΔ)).perm (List.perm_middle (l₁ := [B])).symm)
  | @impLBot _ _ Δ B _ h _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLBot ((hΓ.cons _).trans (List.Perm.swap _ _ _)) (ih hΔ)
  | @impLAnd _ _ Δ A B D _ h _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLAnd ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih (pushL [A.ifThen (B.ifThen D)] hΔ)).perm
          (List.perm_middle (l₁ := [A.ifThen (B.ifThen D)])).symm)
  | @impLOr _ _ Δ A B D _ h _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLOr ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih (pushL [A.ifThen D, B.ifThen D] hΔ)).perm
          (List.perm_middle (l₁ := [A.ifThen D, B.ifThen D])).symm)
  | @impLImp _ _ Δ A B D _ h _ _ ih₁ ih₂ =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLImp ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih₁ (pushL [B.ifThen D] hΔ)).perm
          (List.perm_middle (l₁ := [B.ifThen D])).symm)
        ((ih₂ (pushL [D] hΔ)).perm (List.perm_middle (l₁ := [D])).symm)
  | @impLLax _ _ Δ A B _ h _ _ ih₁ ih₂ =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLLax ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        (ih₁ hp)
        ((ih₂ (pushL [B] hΔ)).perm (List.perm_middle (l₁ := [B])).symm)
  | @impLLaxLax _ _ Δ A B X _ h hX _ _ ih₁ ih₂ =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      have hX' : X.somehow ∈ prop p :: Γ₀ := by
        rcases List.mem_cons.mp (hΔ.subset hX) with e | h'
        · cases e
        rcases List.mem_cons.mp h' with e | h''
        · cases e
        · exact .tail _ h''
      exact .impLLaxLax ((hΓ.cons _).trans (List.Perm.swap _ _ _)) hX'
        ((ih₁ ((hp.cons X).trans push2)).perm (List.Perm.swap _ _ _))
        ((ih₂ (pushL [B] hΔ)).perm (List.perm_middle (l₁ := [B])).symm)

end G4h

namespace G4c

/-!
### General contraction

Outer induction on the *weight* of the contracted formula, inner
structural induction on the derivation — **no cut anywhere**.  The
box-keeping rules (`laxL`, `L◯→″`) and the context-keeping `R◯→″`
(design revision 3) make every modal principal case close by the inner
induction plus strictly lighter contractions; the `L→→` principal case
is the Dyckhoff–Negri recipe (`impLImp_dup`, lighter contractions,
re-abstraction); the remaining principal cases are inversions of the
surviving copy followed by lighter contractions.
-/

private theorem push2 {x q : PLLFormula} {Γ : List PLLFormula} :
    (x :: q :: q :: Γ).Perm (q :: q :: x :: Γ) :=
  (List.Perm.swap q x _).trans ((List.Perm.swap q x Γ).cons q)

private theorem pushL (L : List PLLFormula) {q : PLLFormula}
    {Δ Γ₀ : List PLLFormula} (hΔ : Δ.Perm (q :: q :: Γ₀)) :
    (L ++ Δ).Perm (q :: q :: (L ++ Γ₀)) :=
  (hΔ.append_left L).trans (List.perm_middle.trans (List.perm_middle.cons q))

/-- Three-way split: the principal `P` is (an occurrence of) one of
the two designated copies of `q`, or lives beside them. -/
private theorem cross_split3 {P q : PLLFormula} {Γ' Δ Γ : List PLLFormula}
    (h : Γ'.Perm (P :: Δ)) (hp : Γ'.Perm (q :: q :: Γ)) :
    (P = q ∧ Δ.Perm (q :: Γ)) ∨
    ∃ Γ₀, Δ.Perm (q :: q :: Γ₀) ∧ Γ.Perm (P :: Γ₀) := by
  rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΔ⟩ | ⟨l₁, hΔ, hm⟩
  · exact .inl ⟨e, hΔ⟩
  rcases G4.perm_cons_cases hm with ⟨e, hl⟩ | ⟨l₂, hΓ, hl₁⟩
  · exact .inl ⟨e.symm, hΔ.trans (hl.symm.cons q)⟩
  · exact .inr ⟨l₂, hΔ.trans (hl₁.cons q), hΓ⟩

/-- Membership transport past the two copies. -/
private theorem mem_contract {ψ q : PLLFormula} {Γ' Γ : List PLLFormula}
    (hp : Γ'.Perm (q :: q :: Γ)) (h : ψ ∈ Γ') : ψ = q ∨ ψ ∈ Γ := by
  rcases List.mem_cons.mp (hp.subset h) with e | h'
  · exact .inl e
  rcases List.mem_cons.mp h' with e | h''
  · exact .inl e
  · exact .inr h''

/-- **Bounded contraction**: two copies of a formula of weight `≤ w`
collapse to one. -/
theorem contract_bounded : ∀ (w : Nat) {A : PLLFormula}, A.weight ≤ w →
    ∀ {n : Nat} {Γ' : List PLLFormula} {E : PLLFormula}, G4h n Γ' E →
    ∀ {Γ : List PLLFormula}, Γ'.Perm (A :: A :: Γ) → G4c (A :: Γ) E := by
  intro w
  induction w with
  | zero =>
      intro A hA
      exact absurd hA (by have := weight_pos A; omega)
  | succ w ihw =>
      intro A hA n Γ' E d
      induction d with
      | init h =>
          intro Γ hp
          rcases mem_contract hp h with e | h'
          · exact init (by rw [e]; exact .head _)
          · exact init (.tail _ h')
      | botL h =>
          intro Γ hp
          rcases mem_contract hp h with e | h'
          · exact botL (by rw [e]; exact .head _)
          · exact botL (.tail _ h')
      | andR _ _ ih₁ ih₂ => intro Γ hp; exact andR (ih₁ hp) (ih₂ hp)
      | orR1 _ ih => intro Γ hp; exact orR1 (ih hp)
      | orR2 _ ih => intro Γ hp; exact orR2 (ih hp)
      | laxR _ ih => intro Γ hp; exact laxR (ih hp)
      | @impR _ _ A₀ _ _ ih =>
          intro Γ hp
          exact impR ((ih ((hp.cons A₀).trans push2)).perm
            (List.Perm.swap _ _ _))
      | @laxL _ _ A₁ _ h _ ih =>
          -- fully parametric: the box is kept, both copies persist
          intro Γ hp
          have h' : A₁.somehow ∈ A :: Γ := by
            rcases mem_contract hp h with e | h'
            · rw [e]; exact .head _
            · exact .tail _ h'
          exact laxL h'
            ((ih ((hp.cons A₁).trans push2)).perm (List.Perm.swap _ _ _))
      | @andL _ _ Θ A₁ B₁ E₀ h d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · -- principal: invert the surviving copy, contract the pieces
            subst e
            simp only [PLLFormula.weight] at hA
            have hw₁ : A₁.weight ≤ w := by omega
            have hw₂ : B₁.weight ≤ w := by omega
            have hinv : G4h _ (A₁ :: B₁ :: A₁ :: B₁ :: Γ) E₀ :=
              d₁.inv (.and A₁ B₁) (((hΔ.cons B₁).cons A₁).trans
                (List.perm_middle (l₁ := [A₁, B₁])))
            have c₁ : G4c (A₁ :: B₁ :: B₁ :: Γ) E₀ :=
              ihw hw₁ hinv ((List.Perm.swap _ _ _).cons _)
            obtain ⟨n₁, c₁'⟩ := c₁
            have c₂ : G4c (B₁ :: A₁ :: Γ) E₀ := ihw hw₂ c₁' push2
            exact andL (List.Perm.refl _) (c₂.perm (List.Perm.swap _ _ _))
          · exact andL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih (pushL [A₁, B₁] hΔ)).perm
                (List.perm_middle (l₁ := [A₁, B₁])).symm)
      | @orL _ _ Θ A₁ B₁ E₀ h d₁ d₂ ih₁ ih₂ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            simp only [PLLFormula.weight] at hA
            have hw₁ : A₁.weight ≤ w := by omega
            have hw₂ : B₁.weight ≤ w := by omega
            have q₁ : G4h _ (A₁ :: A₁ :: Γ) E₀ :=
              d₁.inv (.or₁ A₁ B₁)
                ((hΔ.cons A₁).trans (List.Perm.swap _ _ _))
            have q₂ : G4h _ (B₁ :: B₁ :: Γ) E₀ :=
              d₂.inv (.or₂ A₁ B₁)
                ((hΔ.cons B₁).trans (List.Perm.swap _ _ _))
            exact orL (List.Perm.refl _)
              (ihw hw₁ q₁ (List.Perm.refl _))
              (ihw hw₂ q₂ (List.Perm.refl _))
          · exact orL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih₁ (pushL [A₁] hΔ)).perm
                (List.perm_middle (l₁ := [A₁])).symm)
              ((ih₂ (pushL [B₁] hΔ)).perm
                (List.perm_middle (l₁ := [B₁])).symm)
      | @impLProp _ _ Θ a B₁ E₀ h ha d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            simp only [PLLFormula.weight] at hA
            have hw : B₁.weight ≤ w := by omega
            have ha' : prop a ∈ Γ := by
              rcases List.mem_cons.mp (hΔ.subset ha) with e' | h''
              · cases e'
              · exact h''
            have q : G4h _ (B₁ :: B₁ :: Γ) E₀ :=
              d₁.inv (.impProp a B₁)
                ((hΔ.cons B₁).trans (List.Perm.swap _ _ _))
            exact impLProp (List.Perm.refl _) ha'
              (ihw hw q (List.Perm.refl _))
          · have ha' : prop a ∈ A :: Γ₀ := by
              rcases mem_contract hΔ ha with e | h''
              · rw [e]; exact .head _
              · exact .tail _ h''
            exact impLProp ((hΓ.cons _).trans (List.Perm.swap _ _ _)) ha'
              ((ih (pushL [B₁] hΔ)).perm
                (List.perm_middle (l₁ := [B₁])).symm)
      | @impLBot _ _ Θ B₁ _ h d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            exact ⟨_, (d₁.inv (.impBot B₁) hΔ).weaken _⟩
          · exact impLBot ((hΓ.cons _).trans (List.Perm.swap _ _ _)) (ih hΔ)
      | @impLAnd _ _ Θ A₁ B₁ D₁ E₀ h d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            simp only [PLLFormula.weight] at hA
            have hw : (A₁.ifThen (B₁.ifThen D₁)).weight ≤ w := by
              simp only [PLLFormula.weight]; omega
            have q : G4h _ (A₁.ifThen (B₁.ifThen D₁) ::
                A₁.ifThen (B₁.ifThen D₁) :: Γ) E₀ :=
              d₁.inv (.impAnd A₁ B₁ D₁)
                ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            exact impLAnd (List.Perm.refl _) (ihw hw q (List.Perm.refl _))
          · exact impLAnd ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih (pushL [A₁.ifThen (B₁.ifThen D₁)] hΔ)).perm
                (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)])).symm)
      | @impLOr _ _ Θ A₁ B₁ D₁ E₀ h d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            simp only [PLLFormula.weight] at hA
            have hw₁ : (A₁.ifThen D₁).weight ≤ w := by
              simp only [PLLFormula.weight]; omega
            have hw₂ : (B₁.ifThen D₁).weight ≤ w := by
              simp only [PLLFormula.weight]; omega
            have q : G4h _ (A₁.ifThen D₁ :: B₁.ifThen D₁ ::
                A₁.ifThen D₁ :: B₁.ifThen D₁ :: Γ) E₀ :=
              d₁.inv (.impOr A₁ B₁ D₁) (((hΔ.cons _).cons _).trans
                (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁])))
            have c₁ : G4c (A₁.ifThen D₁ :: B₁.ifThen D₁ ::
                B₁.ifThen D₁ :: Γ) E₀ :=
              ihw hw₁ q ((List.Perm.swap _ _ _).cons _)
            obtain ⟨n₁, c₁'⟩ := c₁
            have c₂ : G4c (B₁.ifThen D₁ :: A₁.ifThen D₁ :: Γ) E₀ :=
              ihw hw₂ c₁' push2
            exact impLOr (List.Perm.refl _)
              (c₂.perm (List.Perm.swap _ _ _))
          · exact impLOr ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih (pushL [A₁.ifThen D₁, B₁.ifThen D₁] hΔ)).perm
                (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁])).symm)
      | @impLImp _ _ Θ A₁ B₁ D₁ E₀ h d₁ d₂ ih₁ ih₂ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · -- principal: the Dyckhoff–Negri recipe — duplicate the
            -- spectator copy into premise 1, contract the strictly
            -- lighter pieces, re-abstract
            subst e
            simp only [PLLFormula.weight] at hA
            have hwA : A₁.weight ≤ w := by omega
            have hwK : (B₁.ifThen D₁).weight ≤ w := by
              simp only [PLLFormula.weight]; omega
            have hwD : D₁.weight ≤ w := by omega
            obtain ⟨n₀, r₀⟩ : G4c (A₁ :: B₁.ifThen D₁ :: B₁.ifThen D₁ ::
                B₁.ifThen D₁ :: Γ) (A₁.ifThen B₁) :=
              impLImp_dup d₁ ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            obtain ⟨n₁, r₁⟩ : G4c (B₁.ifThen D₁ :: A₁ ::
                B₁.ifThen D₁ :: Γ) (A₁.ifThen B₁) :=
              ihw hwK r₀ push2
            have r₂ : G4c (B₁.ifThen D₁ :: A₁ :: Γ) (A₁.ifThen B₁) :=
              ihw hwK r₁ ((List.Perm.swap _ _ _).cons _)
            obtain ⟨n₂, r₃⟩ := r₂.impR_inv
            have r₄ : G4c (A₁ :: B₁.ifThen D₁ :: Γ) B₁ :=
              ihw hwA r₃ ((List.Perm.swap _ _ _).cons _)
            have q₂ : G4h _ (D₁ :: D₁ :: Γ) E₀ :=
              d₂.inv (.impImp A₁ B₁ D₁)
                ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            exact impLImp (List.Perm.refl _) (impR r₄)
              (ihw hwD q₂ (List.Perm.refl _))
          · exact impLImp ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih₁ (pushL [B₁.ifThen D₁] hΔ)).perm
                (List.perm_middle (l₁ := [B₁.ifThen D₁])).symm)
              ((ih₂ (pushL [D₁] hΔ)).perm
                (List.perm_middle (l₁ := [D₁])).symm)
      | @impLLax _ _ Θ A₁ B₁ E₀ h d₁ d₂ ih₁ ih₂ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · -- principal: premise 1 keeps the context (revision 3), so
            -- the inner induction contracts it directly
            subst e
            simp only [PLLFormula.weight] at hA
            have hw : B₁.weight ≤ w := by omega
            have q₂ : G4h _ (B₁ :: B₁ :: Γ) E₀ :=
              d₂.inv (.impLax A₁ B₁)
                ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            exact impLLax (List.Perm.refl _) (ih₁ hp)
              (ihw hw q₂ (List.Perm.refl _))
          · exact impLLax ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              (ih₁ hp)
              ((ih₂ (pushL [B₁] hΔ)).perm
                (List.perm_middle (l₁ := [B₁])).symm)
      | @impLLaxLax _ _ Θ A₁ B₁ X E₀ h hX d₁ d₂ ih₁ ih₂ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · -- principal: the box premise carries the whole context —
            -- inner induction there; inversion + lighter contraction on
            -- the other premise
            subst e
            simp only [PLLFormula.weight] at hA
            have hw : B₁.weight ≤ w := by omega
            have hX' : X.somehow ∈ Γ := by
              rcases List.mem_cons.mp (hΔ.subset hX) with e' | h''
              · cases e'
              · exact h''
            have q₂ : G4h _ (B₁ :: B₁ :: Γ) E₀ :=
              d₂.inv (.impLax A₁ B₁)
                ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            exact impLLaxLax (List.Perm.refl _) hX'
              ((ih₁ ((hp.cons X).trans push2)).perm (List.Perm.swap _ _ _))
              (ihw hw q₂ (List.Perm.refl _))
          · have hX' : X.somehow ∈ A :: Γ₀ := by
              rcases mem_contract hΔ hX with e | h''
              · rw [e]; exact .head _
              · exact .tail _ h''
            exact impLLaxLax ((hΓ.cons _).trans (List.Perm.swap _ _ _)) hX'
              ((ih₁ ((hp.cons X).trans push2)).perm (List.Perm.swap _ _ _))
              ((ih₂ (pushL [B₁] hΔ)).perm
                (List.perm_middle (l₁ := [B₁])).symm)

/-- **Contraction is admissible in G4iLL″** — no cut anywhere in the
proof. -/
theorem contract {Γ' Γ : List PLLFormula} {A E : PLLFormula}
    (d : G4c Γ' E) (hp : Γ'.Perm (A :: A :: Γ)) : G4c (A :: Γ) E := by
  obtain ⟨n, hd⟩ := d
  exact contract_bounded A.weight (Nat.le_refl _) hd hp

/-- Contraction of the two front copies. -/
theorem contract_head {Γ : List PLLFormula} {A E : PLLFormula}
    (d : G4c (A :: A :: Γ) E) : G4c (A :: Γ) E :=
  contract d (List.Perm.refl _)

end G4c

end PLLND
