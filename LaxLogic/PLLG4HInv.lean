import LaxLogic.PLLG4H
import LaxLogic.PLLG4Inv

/-!
# Height-preserving inversions for G4iLL″

The master inversion of `PLLG4Inv.lean`, restated for `G4h` **with the
height preserved**: if `G4h n Γ C` and `Γ` exposes a principal `P` with
`Inv P L`, then `G4h n (L ++ Δ) C`.  Height preservation is what the
cut and contraction measures will consume: inverting a side premise costs
nothing.  The two **right** inversions `impR_inv` and (in `PLLG4HCut.lean`)
`andR_inv` are what later let the main cut avoid a left-analysis in every
implication-shaped principal case.

Two bookkeeping notes against the `G4p` version:

* in the principal cases the answering premise lives one height below
  the derivation, so it is returned through `succ_mono`;
* the box-keeping modal rules make their traversal cases *shorter*:
  `laxL` needs only a membership transport (no `Perm` surgery), and
  `L◯→″`'s first premise carries the whole conclusion context, so the
  inverted occurrence is re-exposed by one `cons` instead of a
  two-element shuffle.
-/

open PLLFormula

namespace PLLND

namespace G4h

open G4 (Inv perm_cons_cases perm_shuffle) in
/-- **Master inversion, height-preserving.** -/
theorem inv : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    G4h n Γ C → ∀ {P : PLLFormula} {L Δ : List PLLFormula},
    Inv P L → Γ.Perm (P :: Δ) → G4h n (L ++ Δ) C := by
  intro n Γ C d
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
  | @impR _ _ A₀ B₀ _ ih =>
      intro P L Δ hInv hp
      exact .impR ((ih hInv
        ((hp.cons A₀).trans (List.Perm.swap P A₀ Δ))).perm List.perm_middle)
  | @andL _ _ Θ A' B' _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₁.perm ((hΘΔ.cons B').cons A')).succ_mono
      · exact .andL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A', B']).trans List.perm_middle)).perm
            (perm_shuffle L [A', B'] l'))
  | @orL _ _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e
        cases hInv with
        | or₁ _ _ => exact (d₁.perm (hΘΔ.cons A')).succ_mono
        | or₂ _ _ => exact (d₂.perm (hΘΔ.cons B')).succ_mono
      · exact .orL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A']).trans List.perm_middle)).perm
            (perm_shuffle L [A'] l'))
          ((ih₂ hInv ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle L [B'] l'))
  | @laxL _ Γ' A' _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      -- the box is kept: transport the membership, invert the premise
      have hA : A'.somehow ∈ L ++ Δ := by
        rcases List.mem_cons.mp (hp.subset h) with e | h'
        · subst e; cases hInv
        · exact List.mem_append.mpr (.inr h')
      exact .laxL hA
        ((ih₁ hInv ((hp.cons A').trans (List.Perm.swap P A' Δ))).perm
          List.perm_middle)
  | @impLProp _ _ Θ a' B' _ h ha d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e
        cases hInv with
        | impProp _ _ => exact (d₁.perm (hΘΔ.cons B')).succ_mono
      · have ha' : prop a' ∈ L ++ l' := by
          rcases List.mem_cons.mp (hΘ.subset ha) with e | h'
          · subst e; cases hInv
          · exact List.mem_append.mpr (.inr h')
        exact .impLProp ((hΔ.append_left L).trans List.perm_middle) ha'
          ((ih₁ hInv ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle L [B'] l'))
  | @impLBot _ _ Θ B' _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₁.perm hΘΔ).succ_mono
      · exact .impLBot ((hΔ.append_left L).trans List.perm_middle)
          (ih₁ hInv hΘ)
  | @impLAnd _ _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₁.perm (hΘΔ.cons _)).succ_mono
      · exact .impLAnd ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A₁.ifThen (B₁.ifThen D₁)]).trans
            List.perm_middle)).perm
            (perm_shuffle L [A₁.ifThen (B₁.ifThen D₁)] l'))
  | @impLOr _ _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₁.perm ((hΘΔ.cons _).cons _)).succ_mono
      · exact .impLOr ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A₁.ifThen D₁, B₁.ifThen D₁]).trans
            List.perm_middle)).perm
            (perm_shuffle L [A₁.ifThen D₁, B₁.ifThen D₁] l'))
  | @impLImp _ _ Θ A₁ B₁ D₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₂.perm (hΘΔ.cons _)).succ_mono
      · exact .impLImp ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [B₁.ifThen D₁]).trans
            List.perm_middle)).perm (perm_shuffle L [B₁.ifThen D₁] l'))
          ((ih₂ hInv ((hΘ.append_left [D₁]).trans List.perm_middle)).perm
            (perm_shuffle L [D₁] l'))
  | @impLLax _ _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₂.perm (hΘΔ.cons _)).succ_mono
      · exact .impLLax ((hΔ.append_left L).trans List.perm_middle)
          (ih₁ hInv hp)
          ((ih₂ hInv ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle L [B₁] l'))
  | @impLLaxLax _ Γ' Θ A₁ B₁ X _ h hX d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · -- the inverted formula is the rule's implication principal
        subst e; cases hInv
        exact (d₂.perm (hΘΔ.cons _)).succ_mono
      · -- the inverted formula sits in Θ; the box survives there
        have hX' : X.somehow ∈ L ++ l' := by
          rcases List.mem_cons.mp (hΘ.subset hX) with e | h'
          · subst e; cases hInv
          · exact List.mem_append.mpr (.inr h')
        exact .impLLaxLax ((hΔ.append_left L).trans List.perm_middle) hX'
          ((ih₁ hInv ((hp.cons X).trans (List.Perm.swap P X Δ))).perm
            List.perm_middle)
          ((ih₂ hInv ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle L [B₁] l'))

/-! ### Named height-preserving corollaries -/

theorem andL_inv {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4h n Γ C) (hp : Γ.Perm (A.and B :: Δ)) : G4h n (A :: B :: Δ) C :=
  d.inv (.and A B) hp

theorem orL_inv₁ {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4h n Γ C) (hp : Γ.Perm (A.or B :: Δ)) : G4h n (A :: Δ) C :=
  d.inv (.or₁ A B) hp

theorem orL_inv₂ {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4h n Γ C) (hp : Γ.Perm (A.or B :: Δ)) : G4h n (B :: Δ) C :=
  d.inv (.or₂ A B) hp

theorem impLProp_inv {n : Nat} {Γ Δ : List PLLFormula} {a : String}
    {B C : PLLFormula}
    (d : G4h n Γ C) (hp : Γ.Perm ((prop a).ifThen B :: Δ)) :
    G4h n (B :: Δ) C :=
  d.inv (.impProp a B) hp

theorem impLBot_inv {n : Nat} {Γ Δ : List PLLFormula} {B C : PLLFormula}
    (d : G4h n Γ C) (hp : Γ.Perm (falsePLL.ifThen B :: Δ)) : G4h n Δ C :=
  d.inv (.impBot B) hp

theorem impLImp_inv₂ {n : Nat} {Γ Δ : List PLLFormula} {A B D C : PLLFormula}
    (d : G4h n Γ C) (hp : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
    G4h n (D :: Δ) C :=
  d.inv (.impImp A B D) hp

theorem impLLax_inv₂ {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4h n Γ C) (hp : Γ.Perm (A.somehow.ifThen B :: Δ)) :
    G4h n (B :: Δ) C :=
  d.inv (.impLax A B) hp

/-- **`impR` inversion, height-preserving.** -/
theorem impR_inv : ∀ {n : Nat} {Γ : List PLLFormula} {G : PLLFormula},
    G4h n Γ G → ∀ {A B : PLLFormula}, G = A.ifThen B →
    G4h n (A :: Γ) B := by
  intro n Γ G d
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
      exact d₁.succ_mono
  | @andL _ _ Θ A' B' _ h d₁ ih₁ =>
      intro A B e
      exact .andL ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((ih₁ e).perm (List.perm_middle (l₁ := [A', B'])).symm)
  | @orL _ _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro A B e
      exact .orL ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((ih₁ e).perm (List.perm_middle (l₁ := [A'])).symm)
        ((ih₂ e).perm (List.perm_middle (l₁ := [B'])).symm)
  | laxL _ _ _ => intro A B e; cases e
  | @impLProp _ _ Θ a' B' _ h ha d₁ ih₁ =>
      intro A B e
      exact .impLProp ((h.cons A).trans (List.Perm.swap _ A Θ)) (.tail _ ha)
        ((ih₁ e).perm (List.perm_middle (l₁ := [B'])).symm)
  | @impLBot _ _ Θ B' _ h d₁ ih₁ =>
      intro A B e
      exact .impLBot ((h.cons A).trans (List.Perm.swap _ A Θ)) (ih₁ e)
  | @impLAnd _ _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro A B e
      exact .impLAnd ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((ih₁ e).perm
          (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)])).symm)
  | @impLOr _ _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro A B e
      exact .impLOr ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((ih₁ e).perm
          (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁])).symm)
  | @impLImp _ _ Θ A₁ B₁ D₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro A B e
      exact .impLImp ((h.cons A).trans (List.Perm.swap _ A Θ))
        ((d₁.weaken A).perm (List.perm_middle (l₁ := [B₁.ifThen D₁])).symm)
        ((ih₂ e).perm (List.perm_middle (l₁ := [D₁])).symm)
  | @impLLax _ _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro A B e
      exact .impLLax ((h.cons A).trans (List.Perm.swap _ A Θ))
        (d₁.weaken A)
        ((ih₂ e).perm (List.perm_middle (l₁ := [B₁])).symm)
  | @impLLaxLax _ Γ' Θ A₁ B₁ X _ h hX d₁ d₂ ih₁ ih₂ =>
      intro A B e
      exact .impLLaxLax ((h.cons A).trans (List.Perm.swap _ A Θ))
        (.tail _ hX)
        ((d₁.weaken A).perm (List.Perm.swap X A Γ'))
        ((ih₂ e).perm (List.perm_middle (l₁ := [B₁])).symm)

end G4h

namespace G4c

/-! ### The inversions at the working judgment -/

open G4 (Inv) in
theorem inv {Γ Δ : List PLLFormula} {C P : PLLFormula} {L : List PLLFormula}
    (d : G4c Γ C) (hInv : Inv P L) (hp : Γ.Perm (P :: Δ)) :
    G4c (L ++ Δ) C :=
  d.imp fun _ h => h.inv hInv hp

theorem impR_inv {Γ : List PLLFormula} {A B : PLLFormula}
    (d : G4c Γ (A.ifThen B)) : G4c (A :: Γ) B :=
  d.imp fun _ h => h.impR_inv rfl

theorem andL_inv {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4c Γ C) (hp : Γ.Perm (A.and B :: Δ)) : G4c (A :: B :: Δ) C :=
  d.inv (.and A B) hp

theorem orL_inv₁ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4c Γ C) (hp : Γ.Perm (A.or B :: Δ)) : G4c (A :: Δ) C :=
  d.inv (.or₁ A B) hp

theorem orL_inv₂ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4c Γ C) (hp : Γ.Perm (A.or B :: Δ)) : G4c (B :: Δ) C :=
  d.inv (.or₂ A B) hp

theorem impLProp_inv {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
    (d : G4c Γ C) (hp : Γ.Perm ((prop a).ifThen B :: Δ)) : G4c (B :: Δ) C :=
  d.inv (.impProp a B) hp

theorem impLBot_inv {Γ Δ : List PLLFormula} {B C : PLLFormula}
    (d : G4c Γ C) (hp : Γ.Perm (falsePLL.ifThen B :: Δ)) : G4c Δ C :=
  d.inv (.impBot B) hp

theorem impLImp_inv₂ {Γ Δ : List PLLFormula} {A B D C : PLLFormula}
    (d : G4c Γ C) (hp : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
    G4c (D :: Δ) C :=
  d.inv (.impImp A B D) hp

theorem impLLax_inv₂ {Γ Δ : List PLLFormula} {A B C : PLLFormula}
    (d : G4c Γ C) (hp : Γ.Perm (A.somehow.ifThen B :: Δ)) : G4c (B :: Δ) C :=
  d.inv (.impLax A B) hp

end G4c

end PLLND
