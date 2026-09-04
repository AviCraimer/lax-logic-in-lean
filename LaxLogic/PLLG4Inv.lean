import LaxLogic.PLLG4

/-!
# Inversion lemmas for G4iLL

The goal-preserving inversions of Iemhoff's `G4`: for most left rules, if
the conclusion is derivable then so is (the relevant) premise.  These are
rule-local facts, true of `G4` independently of its incompleteness
(`PLLG4Gap.lean`); they support the decision procedure (`PLLDecide.lean`),
and the decomposition relation `Inv` they are parameterised by is reused
verbatim, height-preservingly, for the repaired calculus in
`PLLG4HInv.lean`.  (The equivalence `SC ↔ G4` these were once aimed at
does *not* hold — contraction is not admissible in `G4`; the equivalence
holds for the repaired `G4c`, `PLLG4HComp.lean`.)

All the goal-preserving inversions are instances of one master theorem
`G4.inv`, parameterised by an inductive relation `Inv P L` ("a context
occurrence of `P` may be replaced by the formulas `L`"):

  `G4 Γ C → Inv P L → Γ.Perm (P :: Δ) → G4 (L ++ Δ) C`

Nine inversions in one induction: `∧`-left, both `∨`-left components, and
the left-implication decompositions for antecedents `p`, `⊥`, `∧`, `∨`,
`⊃` (second premise), `◯` (second premise).  Note the atomic case needs
*no* side condition: `B` is simply stronger than `p ⊃ B`.  The `impR`
inversion (which changes the goal) is a separate theorem with the same
traversal.

**Deliberately absent**: `◯A → A` context strengthening (`Inv (◯A) [A]`).
It is semantically valid (`A ⊢ ◯A`), but *not* provable by this
structural induction: when the derivation ends in `impLLaxLax` using `◯A`
as its box, the strengthened context has lost the box and no rule fires.
This is the very obstruction the development turns on: the repair keeps
the box (revision 1), so the strengthening is never needed, and the
residual self-absorption it stood in for is proved outright over `G4c`
(`selfAbsorb`, `PLLG4HCut.lean`).

The traversal never mentions `List.erase`: the case split on "is the
rule's principal the formula being inverted, or a different one?" is the
erase-free `perm_cons_cases`, and contexts are re-associated with
`List.perm_middle` / `perm_shuffle`.  Everything stays in `Prop` — plain
structural induction on the derivation suffices for inversion.
-/

open PLLFormula

namespace PLLND

namespace G4

/-- Erase-free case split for two `Perm`-exposed heads: either they are
the same formula (and the tails match up), or there is a common remainder
`l'` against which each side exposes the other's head. -/
theorem perm_cons_cases {a b : PLLFormula} {l m : List PLLFormula}
    (h : (a :: l).Perm (b :: m)) :
    (a = b ∧ l.Perm m) ∨ ∃ l', l.Perm (b :: l') ∧ m.Perm (a :: l') := by
  by_cases hab : a = b
  · subst hab; exact .inl ⟨rfl, h.cons_inv⟩
  · have hb : b ∈ l := by
      rcases List.mem_cons.mp (h.symm.subset (.head _)) with e | hb
      · exact absurd e.symm hab
      · exact hb
    refine .inr ⟨l.erase b, perm_cons_erase hb, ?_⟩
    -- b :: m ~ a :: l ~ a :: b :: l.erase b ~ b :: a :: l.erase b
    exact ((h.symm.trans ((perm_cons_erase hb).cons a)).trans
      (List.Perm.swap b a _)).cons_inv

/-- `L ++ (S ++ X) ~ S ++ (L ++ X)`: move a block past another block. -/
theorem perm_shuffle (L S X : List PLLFormula) :
    (L ++ (S ++ X)).Perm (S ++ (L ++ X)) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_comm.append_right X

/-- Weakening by a whole list. -/
theorem weakens (L : List PLLFormula) {Γ : List PLLFormula} {C : PLLFormula}
    (d : G4 Γ C) : G4 (L ++ Γ) C := by
  induction L with
  | nil => exact d
  | cons ψ L ih => exact ih.weaken ψ

/-- The goal-preserving invertible left decompositions of G4iLL: `Inv P L`
says a context occurrence of `P` may be replaced by the formulas `L`
without losing derivability (`G4.inv`).  In each case `L` is (pointwise)
*stronger* than `P`, which is why no side conditions are needed. -/
inductive Inv : PLLFormula → List PLLFormula → Prop
  | and (A B : PLLFormula) : Inv (A.and B) [A, B]
  | or₁ (A B : PLLFormula) : Inv (A.or B) [A]
  | or₂ (A B : PLLFormula) : Inv (A.or B) [B]
  | impProp (a : String) (B : PLLFormula) : Inv ((prop a).ifThen B) [B]
  | impBot (B : PLLFormula) : Inv (falsePLL.ifThen B) []
  | impAnd (A B D : PLLFormula) :
      Inv ((A.and B).ifThen D) [A.ifThen (B.ifThen D)]
  | impOr (A B D : PLLFormula) :
      Inv ((A.or B).ifThen D) [A.ifThen D, B.ifThen D]
  | impImp (A B D : PLLFormula) : Inv ((A.ifThen B).ifThen D) [D]
  | impLax (A B : PLLFormula) : Inv (A.somehow.ifThen B) [B]

/-- **Master inversion.**  If `G4 Γ C` and `Γ` exposes a principal `P`
with `Inv P L`, then `G4 (L ++ Δ) C`.  Structural induction on the
derivation: when the derivation's own principal is a *different* formula,
the rule is peeled, all premises are inverted by the IH, and the rule is
re-applied; when it is the *same* formula, the corresponding premise is
(a permutation of) the answer. -/
theorem inv : ∀ {Γ : List PLLFormula} {C : PLLFormula}, G4 Γ C →
    ∀ {P : PLLFormula} {L Δ : List PLLFormula},
    Inv P L → Γ.Perm (P :: Δ) → G4 (L ++ Δ) C := by
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
            ((ih₁ hInv ((hΘt.append_left [X]).trans List.perm_middle)).perm
              (perm_shuffle L [X] l''))
            ((ih₂ hInv ((hΘt.append_left [B₁, X.somehow]).trans
              List.perm_middle)).perm (perm_shuffle L [B₁, X.somehow] l''))

/-! ### Named corollaries -/

theorem andL_inv {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4 Γ C) (hp : Γ.Perm (A.and B :: Δ)) : G4 (A :: B :: Δ) C :=
  d.inv (.and A B) hp

theorem orL_inv₁ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4 Γ C) (hp : Γ.Perm (A.or B :: Δ)) : G4 (A :: Δ) C :=
  d.inv (.or₁ A B) hp

theorem orL_inv₂ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4 Γ C) (hp : Γ.Perm (A.or B :: Δ)) : G4 (B :: Δ) C :=
  d.inv (.or₂ A B) hp

theorem impLProp_inv {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
    (d : G4 Γ C) (hp : Γ.Perm ((prop a).ifThen B :: Δ)) : G4 (B :: Δ) C :=
  d.inv (.impProp a B) hp

theorem impLBot_inv {Γ Δ : List PLLFormula} {B C : PLLFormula}
    (d : G4 Γ C) (hp : Γ.Perm (falsePLL.ifThen B :: Δ)) : G4 Δ C :=
  d.inv (.impBot B) hp

theorem impLImp_inv₂ {Γ Δ : List PLLFormula} {A B D C : PLLFormula}
    (d : G4 Γ C) (hp : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) : G4 (D :: Δ) C :=
  d.inv (.impImp A B D) hp

theorem impLLax_inv₂ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4 Γ C) (hp : Γ.Perm (A.somehow.ifThen B :: Δ)) : G4 (B :: Δ) C :=
  d.inv (.impLax A B) hp

/-- **`impR` inversion**: the right implication rule is invertible.
Separate from `G4.inv` because the goal changes; goal-changing premise
slots of traversed left rules are carried across by weakening. -/
theorem impR_inv : ∀ {Γ : List PLLFormula} {G : PLLFormula}, G4 Γ G →
    ∀ {A B : PLLFormula}, G = A.ifThen B → G4 (A :: Γ) B := by
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
        ((d₁.weaken A).perm (List.perm_middle (l₁ := [X])).symm)
        ((ih₂ e).perm (List.perm_middle (l₁ := [B₁, X.somehow])).symm)
      exact (h.cons A).trans
        ((List.Perm.swap _ A _).trans ((List.Perm.swap _ A Θt).cons _))

end G4

end PLLND
