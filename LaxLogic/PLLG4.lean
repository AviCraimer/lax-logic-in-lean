import LaxLogic.PLLSequent

/-!
# G4iLL: Iemhoff's terminating sequent calculus for PLL — the faithful transcription

Towards F&M Theorem 2.8 (decidability).  The calculus `G4` below is
Iemhoff's **G4iLL** — Dyckhoff's contraction-free G4ip for intuitionistic
propositional logic extended with four lax rules — transcribed verbatim,
from

* R. Iemhoff, *Proof Theory for Lax Logic*, in: Dick de Jongh on
  Intuitionistic and Provability Logics, Outstanding Contributions to
  Logic, Springer 2024 (arXiv:2209.08976);
* R. Dyckhoff, *Contraction-free sequent calculi for intuitionistic
  logic*, JSL 57(3), 1992.

As in G4ip, the left implication rule is split by the shape of the
antecedent of the implication; the two rules for `◯A ⊃ B` are Iemhoff's
`R#→` (`impLLax`) and `L#→` (`impLLaxLax`).  The latter keeps `◯X` in the
context — Iemhoff's device for Howe's duplication (Howe, MSCS 11(4),
2001, conjectured that no contraction-free calculus for lax logic
exists).

**But this calculus is incomplete for PLL** — that is the discovery of
`PLLG4Gap.lean`, which is downstream of this file.  `L◯→` keeps the box
but *consumes the implication*, and the sequent
`◯((◯p→r)→◯p), ◯p→r ⇒ r` needs the implication `◯p→r` twice, on the two
sides of a box-opening, so it is G3iLL-derivable and G4iLL-underivable
(both kernel-checked); contraction is not admissible here.  Howe's
conjecture is *not* refuted by G4iLL.  See `PLLG4Gap.lean` for the
separation, `PLLG4Tower.lean` for Howe's own sequent, and
`docs/commentary.md` / `docs/g4ill-gap-review.md` for the full account.
The complete repair is `G4h`/`G4c` (**G4iLL″**) in `PLLG4H.lean` and its
successors.  This file remains as the faithful base for the decider
(`PLLDecide.lean`) and the gap proof.

Every premise is smaller than its conclusion in the Dershowitz–Manna
multiset extension of `PLLFormula.weight` (Dyckhoff's weight with
`weight (◯A) = weight A + 1`), so naive backward proof search terminates;
that measure drives the prover, not the inductive definition itself.

## Design notes (slime discipline)

Contexts are **shared lists** (additive rules).  A left rule locates its
principal formula through a `List.Perm` *hypothesis* `h : Γ.Perm (P :: Δ)`
rather than by pattern in the conclusion index: conclusion contexts stay
plain variables, so there is no `++`, no `List.erase`, and no multiset
quotient anywhere near an index — `cases`/`induction` never fight the
unifier.  This buys three things at once:

* **exchange is one line per case** (`G4.perm`): compose the rule's `Perm`
  hypothesis with the ambient permutation, premises untouched;
* the Dershowitz–Manna measure is a multiset invariant of the context, so
  the `Perm` hypothesis preserves it on the nose for the prover;
* the prover instantiates `h` by `List.perm_cons_erase` when it picks a
  principal formula — `erase` appears in *proof terms* only, never in
  types being matched.

This file: the weight, the calculus, structural admissibility
(`perm`, `weaken`), and **soundness** into the cut-free G3 calculus
`SCh`/`SC` of `PLLSequent.lean` (which has admissible cut, `SC.cut`).
The converse — completeness `SC Γ C → G4 Γ C`, the claimed
Dyckhoff/Iemhoff equivalence — is exactly what fails (`PLLG4Gap.lean`);
completeness holds only for the repaired `G4c` (`PLLG4HComp.lean`).
-/

open PLLFormula

namespace PLLFormula

/-- Dyckhoff's weight, extended to `◯` à la Iemhoff: like `sizeOf`, except
that a conjunction weighs `2` more than its parts, which is what makes the
`impLAnd` premise strictly smaller.  Drives the termination of G4 proof
search under the Dershowitz–Manna multiset order. -/
def weight : PLLFormula → Nat
  | prop _ => 1
  | falsePLL => 1
  | and A B => A.weight + B.weight + 2
  | or A B => A.weight + B.weight + 1
  | ifThen A B => A.weight + B.weight + 1
  | somehow A => A.weight + 1

theorem weight_pos : ∀ φ : PLLFormula, 0 < φ.weight
  | prop _ => Nat.one_pos
  | falsePLL => Nat.one_pos
  | and _ _ => Nat.succ_pos _
  | or _ _ => Nat.succ_pos _
  | ifThen _ _ => Nat.succ_pos _
  | somehow _ => Nat.succ_pos _

end PLLFormula

namespace PLLND

/-- **G4iLL** (Iemhoff): contraction-free, terminating sequent calculus for
PLL.  Single succedent, shared-context (additive) rules.  Every left rule
*consumes* its principal formula, located by a `List.Perm` hypothesis
`Γ.Perm (P :: Δ)` — see the design notes in the module docstring. -/
inductive G4 : List PLLFormula → PLLFormula → Prop
  | init {Γ : List PLLFormula} {a : String}
      (h : prop a ∈ Γ) : G4 Γ (prop a)
  | botL {Γ : List PLLFormula} {C : PLLFormula}
      (h : falsePLL ∈ Γ) : G4 Γ C
  -- right rules, exactly as in G3
  | andR {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 Γ A → G4 Γ B → G4 Γ (A.and B)
  | orR1 {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 Γ A → G4 Γ (A.or B)
  | orR2 {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 Γ B → G4 Γ (A.or B)
  | impR {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 (A :: Γ) B → G4 Γ (A.ifThen B)
  | laxR {Γ : List PLLFormula} {A : PLLFormula} :
      G4 Γ A → G4 Γ A.somehow
  -- left rules for ∧, ∨, ◯
  | andL {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.and B :: Δ)) :
      G4 (A :: B :: Δ) C → G4 Γ C
  | orL {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.or B :: Δ)) :
      G4 (A :: Δ) C → G4 (B :: Δ) C → G4 Γ C
  | laxL {Γ Δ : List PLLFormula} {A B : PLLFormula}
      (h : Γ.Perm (A.somehow :: Δ)) :
      G4 (A :: Δ) B.somehow → G4 Γ B.somehow
  -- left implication, split by the antecedent of the implication
  | impLProp {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
      (h : Γ.Perm ((prop a).ifThen B :: Δ)) (ha : prop a ∈ Δ) :
      G4 (B :: Δ) C → G4 Γ C
  | impLBot {Γ Δ : List PLLFormula} {B C : PLLFormula}
      (h : Γ.Perm (falsePLL.ifThen B :: Δ)) :
      G4 Δ C → G4 Γ C
  | impLAnd {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.and B).ifThen D :: Δ)) :
      G4 (A.ifThen (B.ifThen D) :: Δ) E → G4 Γ E
  | impLOr {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.or B).ifThen D :: Δ)) :
      G4 (A.ifThen D :: B.ifThen D :: Δ) E → G4 Γ E
  | impLImp {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
      G4 (B.ifThen D :: Δ) (A.ifThen B) → G4 (D :: Δ) E → G4 Γ E
  -- Iemhoff's two rules for a ◯-antecedent implication
  | impLLax {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) :
      G4 Δ A → G4 (B :: Δ) C → G4 Γ C
  | impLLaxLax {Γ Δ : List PLLFormula} {A B X C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: X.somehow :: Δ)) :
      G4 (X :: Δ) A.somehow → G4 (B :: X.somehow :: Δ) C → G4 Γ C

/-- A member permutes to the head: `l ~ a :: l.erase a`.  This is
`List.perm_cons_erase` restated for `PLLFormula` lists with a plain
structural induction, because Mathlib's proof of the general lemma
depends on `Classical.choice` and would taint the whole
`G4 → G4c → decidability` audit chain. -/
theorem perm_cons_erase {a : PLLFormula} {l : List PLLFormula} (h : a ∈ l) :
    l.Perm (a :: l.erase a) := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    by_cases hba : b = a
    · subst hba
      rw [List.erase_cons_head]
    · rw [List.erase_cons_tail (by simpa using hba)]
      rcases List.mem_cons.mp h with e | h'
      · exact absurd e.symm hba
      · exact ((ih h').cons b).trans (.swap a b _)

namespace G4

/-! ### Structural admissibility -/

/-- **Exchange**: the payoff of the `Perm`-hypothesis design — every left
case just composes permutations; premises are untouched. -/
theorem perm : ∀ {Γ : List PLLFormula} {C : PLLFormula}, G4 Γ C →
    ∀ {Γ' : List PLLFormula}, Γ.Perm Γ' → G4 Γ' C := by
  intro Γ C d
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
  | laxL h d _ => intro Γ' hp; exact .laxL (hp.symm.trans h) d
  | impLProp h ha d _ => intro Γ' hp; exact .impLProp (hp.symm.trans h) ha d
  | impLBot h d _ => intro Γ' hp; exact .impLBot (hp.symm.trans h) d
  | impLAnd h d _ => intro Γ' hp; exact .impLAnd (hp.symm.trans h) d
  | impLOr h d _ => intro Γ' hp; exact .impLOr (hp.symm.trans h) d
  | impLImp h d₁ d₂ _ _ => intro Γ' hp; exact .impLImp (hp.symm.trans h) d₁ d₂
  | impLLax h d₁ d₂ _ _ => intro Γ' hp; exact .impLLax (hp.symm.trans h) d₁ d₂
  | impLLaxLax h d₁ d₂ _ _ =>
      intro Γ' hp; exact .impLLaxLax (hp.symm.trans h) d₁ d₂

/-- **Weakening** by one formula (at the head; anywhere follows with
`perm`).  The premises' contexts absorb `ψ` one position deeper via the
induction hypothesis and a transposition. -/
theorem weaken (ψ : PLLFormula) : ∀ {Γ : List PLLFormula} {C : PLLFormula},
    G4 Γ C → G4 (ψ :: Γ) C := by
  -- `ψ :: x :: l ~ x :: ψ :: l`, the only permutation shape needed below
  have rot : ∀ (x : PLLFormula) (l : List PLLFormula),
      (ψ :: x :: l).Perm (x :: ψ :: l) := fun x l => List.Perm.swap x ψ l
  intro Γ C d
  induction d with
  | init h => exact .init (.tail _ h)
  | botL h => exact .botL (.tail _ h)
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR (ih.perm (rot _ _))
  | laxR _ ih => exact .laxR ih
  | @andL _ Δ A B _ h _ ih =>
      exact .andL ((h.cons ψ).trans (rot _ _))
        (ih.perm ((rot A (B :: Δ)).trans ((rot B Δ).cons A)))
  | @orL _ Δ A B _ h _ _ ih₁ ih₂ =>
      exact .orL ((h.cons ψ).trans (rot _ _))
        (ih₁.perm (rot A Δ)) (ih₂.perm (rot B Δ))
  | @laxL _ Δ A _ h _ ih =>
      exact .laxL ((h.cons ψ).trans (rot _ _)) (ih.perm (rot A Δ))
  | @impLProp _ Δ a B _ h ha _ ih =>
      exact .impLProp ((h.cons ψ).trans (rot _ _)) (.tail _ ha)
        (ih.perm (rot B Δ))
  | impLBot h _ ih =>
      exact .impLBot ((h.cons ψ).trans (rot _ _)) ih
  | @impLAnd _ Δ A B D _ h _ ih =>
      exact .impLAnd ((h.cons ψ).trans (rot _ _))
        (ih.perm (rot (A.ifThen (B.ifThen D)) Δ))
  | @impLOr _ Δ A B D _ h _ ih =>
      exact .impLOr ((h.cons ψ).trans (rot _ _))
        (ih.perm ((rot (A.ifThen D) _).trans ((rot (B.ifThen D) Δ).cons _)))
  | @impLImp _ Δ A B D _ h _ _ ih₁ ih₂ =>
      exact .impLImp ((h.cons ψ).trans (rot _ _))
        (ih₁.perm (rot (B.ifThen D) Δ)) (ih₂.perm (rot D Δ))
  | @impLLax _ Δ A B _ h _ _ ih₁ ih₂ =>
      exact .impLLax ((h.cons ψ).trans (rot _ _)) ih₁ (ih₂.perm (rot B Δ))
  | @impLLaxLax _ Δ A B X _ h _ _ ih₁ ih₂ =>
      exact .impLLaxLax
        ((h.cons ψ).trans ((rot _ _).trans ((rot X.somehow Δ).cons _)))
        (ih₁.perm (rot X Δ))
        (ih₂.perm ((rot B _).trans ((rot X.somehow Δ).cons B)))

/-! ### Soundness into the cut-free G3 calculus -/

/-- Extend a context inclusion under one more hypothesis. -/
private theorem sub_cons {Δ Γ : List PLLFormula}
    (hsub : ∀ ψ ∈ Δ, ψ ∈ Γ) (A : PLLFormula) :
    ∀ ψ ∈ A :: Δ, ψ ∈ A :: Γ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact .head _
  · exact .tail _ (hsub _ hψ)

/-- **Soundness of G4iLL** into the cut-free G3 calculus: every G4 rule is
admissible in `SC`.  The only rules needing `SC.cut` are `impLAnd`,
`impLOr` (cutting the decomposed implications) and `impLImp` (cutting
`A ⊃ B`, obtained from the first premise and the derivable `B ⊃ D`). -/
theorem toSC : ∀ {Γ : List PLLFormula} {C : PLLFormula}, G4 Γ C → SC Γ C := by
  intro Γ C d
  induction d with
  | init h => exact SC.init h
  | botL h => exact SC.botL h
  | andR _ _ ih₁ ih₂ => exact SC.andR ih₁ ih₂
  | orR1 _ ih => exact SC.orR1 ih
  | orR2 _ ih => exact SC.orR2 ih
  | impR _ ih => exact SC.impR ih
  | laxR _ ih => exact SC.laxR ih
  | @andL Γ' Δ' A B _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.andL (h.symm.subset (.head _))
        (ih.rename (sub_cons (sub_cons hΔ B) A))
  | @orL Γ' Δ' A B _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.orL (h.symm.subset (.head _))
        (ih₁.rename (sub_cons hΔ A)) (ih₂.rename (sub_cons hΔ B))
  | @laxL Γ' Δ' A _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.laxL (h.symm.subset (.head _)) (ih.rename (sub_cons hΔ A))
  | @impLProp Γ' Δ' a B _ h ha _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.impL (h.symm.subset (.head _)) (SC.init (hΔ _ ha))
        (ih.rename (sub_cons hΔ B))
  | impLBot h _ ih =>
      exact ih.rename fun ψ hψ => h.symm.subset (.tail _ hψ)
  | @impLAnd Γ' Δ' A B D _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hmem := h.symm.subset (List.Mem.head _)
      -- the decomposed implication `A ⊃ (B ⊃ D)` is derivable, then cut
      have p : SC Γ' (A.ifThen (B.ifThen D)) := by
        refine SC.impR (SC.impR ?_)
        exact SC.impL (A := A.and B) (.tail _ (.tail _ hmem))
          (SC.andR (SC.iden _ (.tail _ (.head _))) (SC.iden _ (.head _)))
          (SC.iden _ (.head _))
      exact SC.cut p (ih.rename (sub_cons hΔ _))
  | @impLOr Γ' Δ' A B D _ h _ ih =>
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
      -- (A⊃D) :: (B⊃D) :: Δ  ⊆  (B⊃D) :: (A⊃D) :: Γ, crossing the order
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact .tail _ (.head _)
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact .head _
      · exact .tail _ (.tail _ (hΔ _ hψ))
  | @impLImp Γ' Δ' A B D _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hmem := h.symm.subset (List.Mem.head _)
      -- `B ⊃ D` is derivable outright …
      have hBD : SC Γ' (B.ifThen D) :=
        SC.impR (SC.impL (A := A.ifThen B) (.tail _ hmem)
          (SC.impR (SC.iden _ (.tail _ (.head _)))) (SC.iden _ (.head _)))
      -- … so the first premise cuts to `A ⊃ B` …
      have hAB : SC Γ' (A.ifThen B) := SC.cut hBD (ih₁.rename (sub_cons hΔ _))
      -- … and `impL` on the principal formula finishes
      exact SC.impL hmem hAB (ih₂.rename (sub_cons hΔ D))
  | @impLLax Γ' Δ' A B _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.impL (h.symm.subset (.head _)) (SC.laxR (ih₁.rename hΔ))
        (ih₂.rename (sub_cons hΔ B))
  | @impLLaxLax Γ' Δ' A B X _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ (.tail _ hψ))
      have hX : X.somehow ∈ Γ' := h.symm.subset (.tail _ (.head _))
      -- `◯A` follows from `◯X` by `laxL` on the first premise
      have hOA : SC Γ' A.somehow := SC.laxL hX (ih₁.rename (sub_cons hΔ X))
      refine SC.impL (h.symm.subset (.head _)) hOA (ih₂.rename ?_)
      refine sub_cons (fun ψ hψ => ?_) B
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hX
      · exact hΔ _ hψ

end G4

/-! ### Smoke tests -/

example : G4 [] ((prop "A").ifThen (prop "A").somehow) :=
  .impR (.laxR (.init (.head _)))

example : G4 [] ((prop "A").somehow.somehow.ifThen (prop "A").somehow) :=
  .impR (.laxL (List.Perm.refl _) (.laxL (List.Perm.refl _)
    (.laxR (.init (.head _)))))

/-- A duplication sequent `(B ⊃ (◯A ⊃ C)) ⊃ ◯A, ◯A ⊃ C, ◯B ⊢ C` that G4iLL
*does* derive, `impLLaxLax` re-using the boxed context formula in each
premise.  **NB this is not Howe's sequent** (MSCS 2001, §5): Howe's major
premise is bracketed `B ⊃ ((◯A ⊃ C) ⊃ ◯A)`, not `(B ⊃ (◯A ⊃ C)) ⊃ ◯A`,
and with that bracketing the sequent is G4iLL-*underivable*
(`PLLG4Tower.lean`, `howeCtx`).  This mis-bracketed derivable variant was
the original source of the belief that G4iLL absorbs Howe's example; the
belief is false — see `PLLG4Gap.lean`. -/
example :
    G4 [((prop "B").ifThen ((prop "A").somehow.ifThen (prop "C"))).ifThen
          (prop "A").somehow,
        (prop "A").somehow.ifThen (prop "C"),
        (prop "B").somehow] (prop "C") := by
  refine .impLImp (List.Perm.refl _) ?_ ?_
  · -- first premise: ◯A⊃C ⊃ ◯A, ◯A⊃C, ◯B ⊢ B ⊃ (◯A ⊃ C)
    refine .impR (.impR ?_)
    -- ◯A, B, (◯A⊃C)⊃◯A, ◯A⊃C, ◯B ⊢ C : `impLLaxLax`, box := the ◯A on the left
    refine .impLLaxLax
      (Δ := [prop "B",
             ((prop "A").somehow.ifThen (prop "C")).ifThen (prop "A").somehow,
             (prop "B").somehow])
      (X := prop "A")
      (by decide) (.laxR (.init (.head _))) (.init (.head _))
  · -- second premise: ◯A, ◯A⊃C, ◯B ⊢ C : `impLLaxLax` again, same box
    exact .impLLaxLax (Δ := [(prop "B").somehow]) (X := prop "A")
      (List.Perm.swap _ _ _) (.laxR (.init (.head _))) (.init (.head _))

end PLLND
