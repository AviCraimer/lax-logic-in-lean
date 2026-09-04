import LaxLogic.PLLG4P
import LaxLogic.PLLG4Inv

/-!
# Inversion lemmas for G4iLL′

Port of `PLLG4Inv.lean` to the repaired calculus `G4p`: the master
inversion `G4p.inv` (nine inversions from one traversal, driven by the
same decomposition relation `G4.Inv`), and `impR` inversion.  The only
novelty is bookkeeping: `impLLaxLax`'s first premise now carries the
kept implication, so an inverted occurrence inside the side context is
re-exposed past the two-element block `[implication, opened box]`
instead of past `[opened box]`.
-/

open PLLFormula

namespace PLLND

namespace G4p

/-- Weakening by a whole list. -/
theorem weakens (L : List PLLFormula) {Γ : List PLLFormula} {C : PLLFormula}
    (d : G4p Γ C) : G4p (L ++ Γ) C := by
  induction L with
  | nil => exact d
  | cons ψ L ih => exact ih.weaken ψ

open G4 (Inv perm_cons_cases perm_shuffle) in
/-- **Master inversion** for G4iLL′.  If `G4p Γ C` and `Γ` exposes a
principal `P` with `Inv P L`, then `G4p (L ++ Δ) C`. -/
theorem inv : ∀ {Γ : List PLLFormula} {C : PLLFormula}, G4p Γ C →
    ∀ {P : PLLFormula} {L Δ : List PLLFormula},
    Inv P L → Γ.Perm (P :: Δ) → G4p (L ++ Δ) C := by
  intro Γ C d
  induction d with
  | init h =>
      intro P L Δ hInv hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · subst e; cases hInv
      · exact .init (List.mem_append.mpr (.inr h'))
  | botL h =>
      intro P L Δ hInv hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · subst e; cases hInv
      · exact .botL (List.mem_append.mpr (.inr h'))
  | andR _ _ ih₁ ih₂ =>
      intro P L Δ hInv hp
      exact .andR (ih₁ hInv hp) (ih₂ hInv hp)
  | orR1 _ ih => intro P L Δ hInv hp; exact .orR1 (ih hInv hp)
  | orR2 _ ih => intro P L Δ hInv hp; exact .orR2 (ih hInv hp)
  | laxR _ ih => intro P L Δ hInv hp; exact .laxR (ih hInv hp)
  | @impR _ A₀ B₀ _ ih =>
      intro P L Δ hInv hp
      exact .impR ((ih hInv
        ((hp.cons A₀).trans (List.Perm.swap P A₀ Δ))).perm List.perm_middle)
  | @andL _ Θ A' B' _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact d₁.perm ((hΘΔ.cons B').cons A')
      · exact .andL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A', B']).trans List.perm_middle)).perm
            (perm_shuffle L [A', B'] l'))
  | @orL _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e
        cases hInv with
        | or₁ _ _ => exact d₁.perm (hΘΔ.cons A')
        | or₂ _ _ => exact d₂.perm (hΘΔ.cons B')
      · exact .orL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A']).trans List.perm_middle)).perm
            (perm_shuffle L [A'] l'))
          ((ih₂ hInv ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle L [B'] l'))
  | @laxL _ Θ A' _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
      · exact .laxL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A']).trans List.perm_middle)).perm
            (perm_shuffle L [A'] l'))
  | @impLProp _ Θ a' B' _ h ha d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e
        cases hInv with
        | impProp _ _ => exact d₁.perm (hΘΔ.cons B')
      · have ha' : prop a' ∈ L ++ l' := by
          rcases List.mem_cons.mp (hΘ.subset ha) with e | h'
          · subst e; cases hInv
          · exact List.mem_append.mpr (.inr h')
        exact .impLProp ((hΔ.append_left L).trans List.perm_middle) ha'
          ((ih₁ hInv ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle L [B'] l'))
  | @impLBot _ Θ B' _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact d₁.perm hΘΔ
      · exact .impLBot ((hΔ.append_left L).trans List.perm_middle)
          (ih₁ hInv hΘ)
  | @impLAnd _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact d₁.perm (hΘΔ.cons _)
      · exact .impLAnd ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A₁.ifThen (B₁.ifThen D₁)]).trans
            List.perm_middle)).perm
            (perm_shuffle L [A₁.ifThen (B₁.ifThen D₁)] l'))
  | @impLOr _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact d₁.perm ((hΘΔ.cons _).cons _)
      · exact .impLOr ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A₁.ifThen D₁, B₁.ifThen D₁]).trans
            List.perm_middle)).perm
            (perm_shuffle L [A₁.ifThen D₁, B₁.ifThen D₁] l'))
  | @impLImp _ Θ A₁ B₁ D₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact d₂.perm (hΘΔ.cons _)
      · exact .impLImp ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [B₁.ifThen D₁]).trans
            List.perm_middle)).perm (perm_shuffle L [B₁.ifThen D₁] l'))
          ((ih₂ hInv ((hΘ.append_left [D₁]).trans List.perm_middle)).perm
            (perm_shuffle L [D₁] l'))
  | @impLLax _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact d₂.perm (hΘΔ.cons _)
      · exact .impLLax ((hΔ.append_left L).trans List.perm_middle)
          (ih₁ hInv hΘ)
          ((ih₂ hInv ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle L [B₁] l'))
  | @impLLaxLax _ Θt A₁ B₁ X _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · -- the inverted formula is the rule's implication principal
        subst e; cases hInv
        exact d₂.perm (hΘΔ.cons _)
      · -- the inverted formula is inside `◯X :: Θt`
        rcases perm_cons_cases hΘ with ⟨e, _⟩ | ⟨l'', hΘt, hl'⟩
        · -- it cannot be the box: no `Inv` decomposes a `◯`-formula
          subst e; cases hInv
        · have hconc : (L ++ Δ).Perm
              (A₁.somehow.ifThen B₁ :: X.somehow :: (L ++ l'')) :=
            ((hΔ.trans (hl'.cons _)).append_left L).trans
              (List.perm_middle.trans (List.perm_middle.cons _))
          exact .impLLaxLax hconc
            ((ih₁ hInv
              ((hΘt.append_left [A₁.somehow.ifThen B₁, X]).trans
                List.perm_middle)).perm
              (perm_shuffle L [A₁.somehow.ifThen B₁, X] l''))
            ((ih₂ hInv ((hΘt.append_left [B₁, X.somehow]).trans
              List.perm_middle)).perm (perm_shuffle L [B₁, X.somehow] l''))

/-! ### Named corollaries -/

theorem andL_inv {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4p Γ C) (hp : Γ.Perm (A.and B :: Δ)) : G4p (A :: B :: Δ) C :=
  d.inv (.and A B) hp

theorem orL_inv₁ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4p Γ C) (hp : Γ.Perm (A.or B :: Δ)) : G4p (A :: Δ) C :=
  d.inv (.or₁ A B) hp

theorem orL_inv₂ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4p Γ C) (hp : Γ.Perm (A.or B :: Δ)) : G4p (B :: Δ) C :=
  d.inv (.or₂ A B) hp

theorem impLProp_inv {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
    (d : G4p Γ C) (hp : Γ.Perm ((prop a).ifThen B :: Δ)) : G4p (B :: Δ) C :=
  d.inv (.impProp a B) hp

theorem impLBot_inv {Γ Δ : List PLLFormula} {B C : PLLFormula}
    (d : G4p Γ C) (hp : Γ.Perm (falsePLL.ifThen B :: Δ)) : G4p Δ C :=
  d.inv (.impBot B) hp

theorem impLImp_inv₂ {Γ Δ : List PLLFormula} {A B D C : PLLFormula}
    (d : G4p Γ C) (hp : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
    G4p (D :: Δ) C :=
  d.inv (.impImp A B D) hp

theorem impLLax_inv₂ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4p Γ C) (hp : Γ.Perm (A.somehow.ifThen B :: Δ)) : G4p (B :: Δ) C :=
  d.inv (.impLax A B) hp

/-- **`impR` inversion** for G4iLL′. -/
theorem impR_inv : ∀ {Γ : List PLLFormula} {G : PLLFormula}, G4p Γ G →
    ∀ {A B : PLLFormula}, G = A.ifThen B → G4p (A :: Γ) B := by
  intro Γ G d
  induction d with
  | init h => intro A B e; cases e
  | botL h => intro A B e; exact .botL (.tail _ h)
  | andR _ _ _ _ => intro A B e; cases e
  | orR1 _ _ => intro A B e; cases e
  | orR2 _ _ => intro A B e; cases e
  | laxR _ _ => intro A B e; cases e
  | impR d₁ _ =>
      intro A B e
      cases e
      exact d₁
  | @andL _ Θ A' B' _ h d₁ ih₁ =>
      intro A B e
      exact .andL ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((ih₁ e).perm (List.perm_middle (l₁ := [A', B'])).symm)
  | @orL _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro A B e
      exact .orL ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((ih₁ e).perm (List.perm_middle (l₁ := [A'])).symm)
        ((ih₂ e).perm (List.perm_middle (l₁ := [B'])).symm)
  | laxL _ _ _ => intro A B e; cases e
  | @impLProp _ Θ a' B' _ h ha d₁ ih₁ =>
      intro A B e
      exact .impLProp ((h.cons A).trans (List.Perm.swap _ A Θ)) (.tail _ ha)
        ((ih₁ e).perm (List.perm_middle (l₁ := [B'])).symm)
  | @impLBot _ Θ B' _ h d₁ ih₁ =>
      intro A B e
      exact .impLBot ((h.cons A).trans (List.Perm.swap _ A Θ)) (ih₁ e)
  | @impLAnd _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro A B e
      exact .impLAnd ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((ih₁ e).perm (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)])).symm)
  | @impLOr _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro A B e
      exact .impLOr ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((ih₁ e).perm
          (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁])).symm)
  | @impLImp _ Θ A₁ B₁ D₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro A B e
      exact .impLImp ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((d₁.weaken A).perm (List.perm_middle (l₁ := [B₁.ifThen D₁])).symm)
        ((ih₂ e).perm (List.perm_middle (l₁ := [D₁])).symm)
  | @impLLax _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro A B e
      exact .impLLax ((h.cons A).trans (List.Perm.swap _ A Θ))
        (d₁.weaken A)
        ((ih₂ e).perm (List.perm_middle (l₁ := [B₁])).symm)
  | @impLLaxLax _ Θt A₁ B₁ X _ h d₁ d₂ ih₁ ih₂ =>
      intro A B e
      refine .impLLaxLax
        (?_ : (A :: _).Perm (A₁.somehow.ifThen B₁ :: X.somehow :: (A :: Θt)))
        ((d₁.weaken A).perm
          (List.perm_middle (l₁ := [A₁.somehow.ifThen B₁, X])).symm)
        ((ih₂ e).perm (List.perm_middle (l₁ := [B₁, X.somehow])).symm)
      exact (h.cons A).trans
        ((List.Perm.swap _ A _).trans ((List.Perm.swap _ A Θt).cons _))

end G4p

end PLLND
