import LaxLogic.PLLG4PAdm

/-!
# G4iLL′: the weak implication rule, and `◯`-spines

The reusable engine of the contraction/cut ladder: **`weak_Imp`**, the
full Dyckhoff–Negri Lemma 4.1 extended to the lax modality —

    Γ ⇒ D        Γ, B ⇒ E
    -----------------------
        Γ, D→B ⇒ E

for **arbitrary** `D`, by structural induction on the first derivation
alone, the second inverted along the way.  Each way the first
derivation can *end* feeds exactly one left implication rule of the
calculus, which is the design rationale of the G4 rule set laid bare:

| first derivation ends | rebuild with |
|---|---|
| `init` (`D` an atom in `Γ`) | `Lp→` |
| `andR` | two nested IHs, then `L∧→` (Dyckhoff's currying) |
| `orRᵢ` | IH + weakening, then `L∨→` |
| `impR` | no IH: weaken its premise into `L→→`'s first premise |
| `laxR` | `R◯→` |
| `laxL` | `L◯→′` — the kept implication arrives by weakening |
| a left rule | invert the side premise, IH, re-apply |

The file also defines `◯`-**spines** (`Spine φ σ` iff `φ = ◯^k σ`) with
their `laxR`-lifts.  `weak_Imp`, `impLImp_dup` and the spines are the
end of the `G4p` line: the ladder proper (inversions, identity, these
three, then contraction, cut, completeness) is carried out over the
final `G4c` (**G4iLL″**) in the `PLLG4H*` files, where — thanks to the
two further retentions of revisions 2–3 — cut needs no standing
self-absorption lemma at all (`docs/g4p-ladder.md` records the design;
`docs/commentary.md` the synthesis).
-/

open PLLFormula

namespace PLLND

namespace G4p

/-- `Spine φ σ`: `φ = ◯^k σ` for some `k ≥ 0`. -/
inductive Spine : PLLFormula → PLLFormula → Prop
  | refl (φ : PLLFormula) : Spine φ φ
  | box {φ σ : PLLFormula} : Spine φ σ → Spine φ.somehow σ

/-- Climb a spine with `laxR`. -/
theorem Spine.lift {φ σ : PLLFormula} :
    Spine φ σ → ∀ {Γ : List PLLFormula}, G4p Γ σ → G4p Γ φ := by
  intro s
  induction s with
  | refl _ => exact fun d => d
  | box _ ih => exact fun d => .laxR (ih d)

/-- Descend one `◯` at the target's top. -/
theorem Spine.unbox {φ σ : PLLFormula} :
    Spine φ σ.somehow → Spine φ σ := by
  intro s
  generalize hσ : σ.somehow = τ at s
  induction s with
  | refl φ => exact hσ ▸ .box (.refl σ)
  | box s ih => exact .box (ih hσ)

/-- **Weak implication** (Dyckhoff–Negri Lemma 4.1, all antecedents,
lax rules included): from `Γ ⇒ D` and `Γ, B ⇒ E` conclude
`Γ, D→B ⇒ E`.  Induction on the first derivation only. -/
theorem weak_Imp : ∀ {Γ : List PLLFormula} {D : PLLFormula}, G4p Γ D →
    ∀ {B E : PLLFormula}, G4p (B :: Γ) E → G4p (D.ifThen B :: Γ) E := by
  intro Γ D d
  induction d with
  | init h =>
      -- D is an atom present in Γ: `Lp→`
      intro B E side
      exact .impLProp (List.Perm.refl _) h side
  | botL h =>
      intro B E _
      exact .botL (.tail _ h)
  | andR d₁ d₂ ih₁ ih₂ =>
      -- D = D₁∧D₂: curry through the two IHs, close with `L∧→`
      intro B E side
      exact .impLAnd (List.Perm.refl _) (ih₁ (ih₂ side))
  | orR1 d₁ ih =>
      -- D = D₁∨D₂ via the left disjunct: IH, weaken, `L∨→`
      intro B E side
      exact .impLOr (List.Perm.refl _)
        (((ih side).weaken _).perm (List.Perm.swap _ _ _))
  | orR2 d₂ ih =>
      intro B E side
      exact .impLOr (List.Perm.refl _) ((ih side).weaken _)
  | @impR _ D₁ D₂ d₁ _ =>
      -- D = D₁⊃D₂: its premise, weakened, is `L→→`'s first premise
      intro B E side
      exact .impLImp (List.Perm.refl _)
        (.impR ((d₁.weaken _).perm (List.Perm.swap _ _ _))) side
  | laxR d₁ _ =>
      -- D = ◯D₁: `R◯→`
      intro B E side
      exact .impLLax (List.Perm.refl _) d₁ side
  | @laxL _ Δ A _ h d₁ _ =>
      -- D = ◯D₁ via a box-opening: `L◯→′`, kept implication by weakening
      intro B E side
      exact .impLLaxLax (h.cons _) (d₁.weaken _) (side.perm (h.cons B))
  | @andL _ Θ A' B' _ h d₁ ih =>
      intro B E side
      have side' : G4p (B :: A' :: B' :: Θ) E :=
        (side.andL_inv ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A', B']))
      exact .andL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm (List.perm_middle (l₁ := [A', B'])).symm)
  | @orL _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro B E side
      have side₁ : G4p (B :: A' :: Θ) E :=
        (side.orL_inv₁ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A']))
      have side₂ : G4p (B :: B' :: Θ) E :=
        (side.orL_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B']))
      exact .orL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih₁ side₁).perm (List.perm_middle (l₁ := [A'])).symm)
        ((ih₂ side₂).perm (List.perm_middle (l₁ := [B'])).symm)
  | @impLProp _ Θ a B' _ h ha d₁ ih =>
      intro B E side
      have side' : G4p (B :: B' :: Θ) E :=
        (side.impLProp_inv ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B']))
      exact .impLProp ((h.cons _).trans (List.Perm.swap _ _ Θ)) (.tail _ ha)
        ((ih side').perm (List.perm_middle (l₁ := [B'])).symm)
  | @impLBot _ Θ B' _ h d₁ ih =>
      intro B E side
      have side' : G4p (B :: Θ) E :=
        side.impLBot_inv ((h.cons B).trans (List.Perm.swap _ B Θ))
      exact .impLBot ((h.cons _).trans (List.Perm.swap _ _ Θ)) (ih side')
  | @impLAnd _ Θ A₁ B₁ D₁ _ h d₁ ih =>
      intro B E side
      have side' : G4p (B :: A₁.ifThen (B₁.ifThen D₁) :: Θ) E :=
        (side.inv (.impAnd A₁ B₁ D₁)
          ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)]))
      exact .impLAnd ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm
          (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)])).symm)
  | @impLOr _ Θ A₁ B₁ D₁ _ h d₁ ih =>
      intro B E side
      have side' : G4p (B :: A₁.ifThen D₁ :: B₁.ifThen D₁ :: Θ) E :=
        (side.inv (.impOr A₁ B₁ D₁)
          ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁]))
      exact .impLOr ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm
          (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁])).symm)
  | @impLImp _ Θ A₁ B₁ D₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro B E side
      have side' : G4p (B :: D₁ :: Θ) E :=
        (side.impLImp_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [D₁]))
      exact .impLImp ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((d₁.weaken _).perm (List.perm_middle (l₁ := [B₁.ifThen D₁])).symm)
        ((ih₂ side').perm (List.perm_middle (l₁ := [D₁])).symm)
  | @impLLax _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro B E side
      have side' : G4p (B :: B₁ :: Θ) E :=
        (side.impLLax_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B₁]))
      exact .impLLax ((h.cons _).trans (List.Perm.swap _ _ Θ))
        (d₁.weaken _)
        ((ih₂ side').perm (List.perm_middle (l₁ := [B₁])).symm)
  | @impLLaxLax _ Θ A₁ B₁ X _ h d₁ d₂ ih₁ ih₂ =>
      intro B E side
      have side' : G4p (B :: B₁ :: X.somehow :: Θ) E :=
        (side.impLLax_inv₂ ((h.cons B).trans (List.Perm.swap _ B _))).perm
          (List.perm_middle (l₁ := [B₁]))
      refine .impLLaxLax
        ((h.cons _).trans (List.perm_middle
          (l₁ := [A₁.somehow.ifThen B₁, X.somehow])).symm)
        ((d₁.weaken _).perm (List.perm_middle
          (l₁ := [A₁.somehow.ifThen B₁, X])).symm)
        ((ih₂ side').perm (List.perm_middle (l₁ := [B₁, X.somehow])).symm)

/-- The `◯`-antecedent instance (Dyckhoff–Negri 4.1 as needed for the
lax rules). -/
theorem weak_ImpLax {Γ : List PLLFormula} {D B E : PLLFormula}
    (d : G4p Γ D.somehow) (side : G4p (B :: Γ) E) :
    G4p (D.somehow.ifThen B :: Γ) E :=
  weak_Imp d side

/-- **Duplication for `L→→`** (Dyckhoff–Negri Lemma 4.2, folded form):
a context occurrence of `(A→B)→D` may be replaced by
`A, B→D, B→D`.  Plain structural induction; in the principal case the
premise is `impR`-inverted and closed with `weak_Imp` — no measure. -/
theorem impLImp_dup : ∀ {Γ' : List PLLFormula} {E : PLLFormula},
    G4p Γ' E → ∀ {A B D : PLLFormula} {Γ : List PLLFormula},
    Γ'.Perm ((A.ifThen B).ifThen D :: Γ) →
    G4p (A :: B.ifThen D :: B.ifThen D :: Γ) E := by
  intro Γ' E d
  induction d with
  | init h =>
      intro A B D Γ hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · cases e
      · exact .init (.tail _ (.tail _ (.tail _ h')))
  | botL h =>
      intro A B D Γ hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · cases e
      · exact .botL (.tail _ (.tail _ (.tail _ h')))
  | andR _ _ ih₁ ih₂ =>
      intro A B D Γ hp
      exact .andR (ih₁ hp) (ih₂ hp)
  | orR1 _ ih => intro A B D Γ hp; exact .orR1 (ih hp)
  | orR2 _ ih => intro A B D Γ hp; exact .orR2 (ih hp)
  | laxR _ ih => intro A B D Γ hp; exact .laxR (ih hp)
  | @impR _ A₀ B₀ _ ih =>
      intro A B D Γ hp
      have h' := ih ((hp.cons A₀).trans (List.Perm.swap _ A₀ Γ))
      -- move A₀ back to the front past the three inserted formulas
      exact .impR (h'.perm
        (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
  | @andL _ Θ A' B' _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .andL
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A', B']).trans List.perm_middle)).perm
            ((G4.perm_shuffle [A, B.ifThen D, B.ifThen D] [A', B'] l')))
  | @orL _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .orL
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A']).trans List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D] [A'] l'))
          ((ih₂ ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D] [B'] l'))
  | @laxL _ Θ A' _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .laxL
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A']).trans List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D] [A'] l'))
  | @impLProp _ Θ a' B' _ h ha d₁ ih₁ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · have ha' : prop a' ∈ A :: B.ifThen D :: B.ifThen D :: l' := by
          rcases List.mem_cons.mp (hΘ.subset ha) with e | h'
          · cases e
          · exact .tail _ (.tail _ (.tail _ h'))
        exact .impLProp
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D]))) ha'
          ((ih₁ ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D] [B'] l'))
  | @impLBot _ Θ B' _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .impLBot
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          (ih₁ hΘ)
  | @impLAnd _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .impLAnd
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A₁.ifThen (B₁.ifThen D₁)]).trans
            List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D]
              [A₁.ifThen (B₁.ifThen D₁)] l'))
  | @impLOr _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .impLOr
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A₁.ifThen D₁, B₁.ifThen D₁]).trans
            List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D]
              [A₁.ifThen D₁, B₁.ifThen D₁] l'))
  | @impLImp _ Θ A₁ B₁ D₁ E₀ h d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · -- the duplicated formula is principal: impR-invert premise 1,
        -- then close with weak_Imp on the antecedent B₁
        cases e
        have p₁' : G4p (A₁ :: B₁.ifThen D₁ :: Θ) B₁ := d₁.impR_inv rfl
        have side : G4p (D₁ :: A₁ :: B₁.ifThen D₁ :: Θ) E₀ :=
          (d₂.weakens (L := [A₁, B₁.ifThen D₁])).perm
            (List.perm_middle (l₁ := [A₁, B₁.ifThen D₁]))
        have h' : G4p (B₁.ifThen D₁ :: A₁ :: B₁.ifThen D₁ :: Θ) E₀ :=
          weak_Imp p₁' side
        exact h'.perm ((List.Perm.swap _ _ _).trans
          (((hΘΓ.cons _).cons _).cons _))
      · exact .impLImp
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [B₁.ifThen D₁]).trans
            List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D] [B₁.ifThen D₁] l'))
          ((ih₂ ((hΘ.append_left [D₁]).trans List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D] [D₁] l'))
  | @impLLax _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .impLLax
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          (ih₁ hΘ)
          ((ih₂ ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (G4.perm_shuffle [A, B.ifThen D, B.ifThen D] [B₁] l'))
  | @impLLaxLax _ Θt A₁ B₁ X _ h d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · rcases G4.perm_cons_cases hΘ with ⟨e, _⟩ | ⟨l'', hΘt, hl'⟩
        · cases e
        · have hconc :
              (A :: B.ifThen D :: B.ifThen D :: Γ).Perm
                (A₁.somehow.ifThen B₁ :: X.somehow ::
                  (A :: B.ifThen D :: B.ifThen D :: l'')) :=
            ((hΓ.trans (hl'.cons _)).append_left
              [A, B.ifThen D, B.ifThen D]).trans
              ((List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])).trans
                ((List.perm_middle
                  (l₁ := [A, B.ifThen D, B.ifThen D])).cons _))
          exact .impLLaxLax hconc
            ((ih₁ ((hΘt.append_left [A₁.somehow.ifThen B₁, X]).trans
              List.perm_middle)).perm
              (G4.perm_shuffle [A, B.ifThen D, B.ifThen D]
                [A₁.somehow.ifThen B₁, X] l''))
            ((ih₂ ((hΘt.append_left [B₁, X.somehow]).trans
              List.perm_middle)).perm
              (G4.perm_shuffle [A, B.ifThen D, B.ifThen D]
                [B₁, X.somehow] l''))

end G4p

end PLLND
