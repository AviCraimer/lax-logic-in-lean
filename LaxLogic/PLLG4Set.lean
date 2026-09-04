import LaxLogic.PLLG4HComp
import LaxLogic.PLLFinsetKit

/-!
# Termination B: the cumulative set-context calculus `G4s`

`G4iLL″` over `Finset` contexts, **fully cumulative**: every rule
retains its principal and inserts its pieces; nothing is ever erased.
Cumulativity is what the admissibility theorems bought: keeping more
is weakening-sound, and the consuming shapes are recovered on the list
side by inversion + contraction — so `G4s` proves exactly the `G4c`
sequents (`G4c.iff_set`), while on the set side backward search only
ever *grows* contexts inside the finite space of `PLLG4Space.lean`.

The `impLBot` rule is deliberately absent: cumulatively its premise
would equal its conclusion; the list rule's content is absorbed by
`weaken_subset` in the embedding.

The equivalence is engineered for reuse: `G4h.toSetFin` is a direct
height-preserving induction (all transports are `weaken_subset`), and
`G4sh.toSC_of_toFin` maps the cumulative rules onto `SC`'s keeping
rules — the shapes match almost verbatim, the three Dyckhoff rules
going through the same `SC.cut` constructions as `G4c.toSC` — after
which `completeness` closes the loop.

**Axiom hygiene.**  The clean chain is phrased through the choice-free
`toFin` of `PLLFinsetKit.lean`: `G4h.toSetFin`, `G4sh.toSC_of_toFin`
(which generalises over any list enumerating the finset — no
`Finset.toList`, hence no `Classical.choice`), `G4c.iff_setFin`, and
the height-bounded decider `G4sh.dec` all audit
`[propext, Quot.sound]`.  The legacy `toFinset`/`toList`-phrased forms
(`G4h.toSet`, `G4sh.toSC`, `G4c.iff_set`) are derived from them as
one-line wrappers; their *statements* mention `List.toFinset` resp.
`Finset.toList`, whose current Mathlib bodies embed choice, so those
three — and only those three — still audit
`[propext, Classical.choice, Quot.sound]`, irreparably by proof
changes alone.

The decider `G4sh.dec` (`Decidable (G4sh n Γ C)`) works by structural
recursion on the height through the two inversion lemmas
`g4sh_zero_iff`/`g4sh_succ_iff`: at each height the applicable rules
range over the finite context, so decidability is a finite Boolean
combination of memberships and recursive calls.  It is what lets the
minimal-height `Nat.find` induction of `PLLG4Dec.lean` run without
`Classical.propDecidable`.
-/

open PLLFormula

namespace PLLND

/-- **G4iLL″ on set contexts, fully cumulative**, height-indexed. -/
inductive G4sh : Nat → Finset PLLFormula → PLLFormula → Prop
  | init {n : Nat} {Γ : Finset PLLFormula} {a : String}
      (h : prop a ∈ Γ) : G4sh n Γ (prop a)
  | botL {n : Nat} {Γ : Finset PLLFormula} {C : PLLFormula}
      (h : falsePLL ∈ Γ) : G4sh n Γ C
  | andR {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula} :
      G4sh n Γ A → G4sh n Γ B → G4sh (n + 1) Γ (A.and B)
  | orR1 {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula} :
      G4sh n Γ A → G4sh (n + 1) Γ (A.or B)
  | orR2 {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula} :
      G4sh n Γ B → G4sh (n + 1) Γ (A.or B)
  | impR {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula} :
      G4sh n (insert A Γ) B → G4sh (n + 1) Γ (A.ifThen B)
  | laxR {n : Nat} {Γ : Finset PLLFormula} {A : PLLFormula} :
      G4sh n Γ A → G4sh (n + 1) Γ A.somehow
  | laxL {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula}
      (h : A.somehow ∈ Γ) :
      G4sh n (insert A Γ) B.somehow → G4sh (n + 1) Γ B.somehow
  | andL {n : Nat} {Γ : Finset PLLFormula} {A B C : PLLFormula}
      (h : A.and B ∈ Γ) :
      G4sh n (insert A (insert B Γ)) C → G4sh (n + 1) Γ C
  | orL {n : Nat} {Γ : Finset PLLFormula} {A B C : PLLFormula}
      (h : A.or B ∈ Γ) :
      G4sh n (insert A Γ) C → G4sh n (insert B Γ) C → G4sh (n + 1) Γ C
  | impLProp {n : Nat} {Γ : Finset PLLFormula} {a : String} {B C : PLLFormula}
      (h : (prop a).ifThen B ∈ Γ) (ha : prop a ∈ Γ) :
      G4sh n (insert B Γ) C → G4sh (n + 1) Γ C
  | impLAnd {n : Nat} {Γ : Finset PLLFormula} {A B D C : PLLFormula}
      (h : (A.and B).ifThen D ∈ Γ) :
      G4sh n (insert (A.ifThen (B.ifThen D)) Γ) C → G4sh (n + 1) Γ C
  | impLOr {n : Nat} {Γ : Finset PLLFormula} {A B D C : PLLFormula}
      (h : (A.or B).ifThen D ∈ Γ) :
      G4sh n (insert (A.ifThen D) (insert (B.ifThen D) Γ)) C →
      G4sh (n + 1) Γ C
  | impLImp {n : Nat} {Γ : Finset PLLFormula} {A B D C : PLLFormula}
      (h : (A.ifThen B).ifThen D ∈ Γ) :
      G4sh n (insert (B.ifThen D) Γ) (A.ifThen B) →
      G4sh n (insert D Γ) C → G4sh (n + 1) Γ C
  | impLLax {n : Nat} {Γ : Finset PLLFormula} {A B C : PLLFormula}
      (h : A.somehow.ifThen B ∈ Γ) :
      G4sh n Γ A → G4sh n (insert B Γ) C → G4sh (n + 1) Γ C
  | impLLaxLax {n : Nat} {Γ : Finset PLLFormula} {A B X C : PLLFormula}
      (h : A.somehow.ifThen B ∈ Γ) (hX : X.somehow ∈ Γ) :
      G4sh n (insert X Γ) A.somehow → G4sh n (insert B Γ) C →
      G4sh (n + 1) Γ C

/-- Set-context derivability at some height. -/
def G4s (Γ : Finset PLLFormula) (C : PLLFormula) : Prop := ∃ n, G4sh n Γ C

namespace G4sh

theorem succ_mono : ∀ {n : Nat} {Γ : Finset PLLFormula} {C : PLLFormula},
    G4sh n Γ C → G4sh (n + 1) Γ C := by
  intro n Γ C d
  induction d with
  | init h => exact .init h
  | botL h => exact .botL h
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR ih
  | laxR _ ih => exact .laxR ih
  | laxL h _ ih => exact .laxL h ih
  | andL h _ ih => exact .andL h ih
  | orL h _ _ ih₁ ih₂ => exact .orL h ih₁ ih₂
  | impLProp h ha _ ih => exact .impLProp h ha ih
  | impLAnd h _ ih => exact .impLAnd h ih
  | impLOr h _ ih => exact .impLOr h ih
  | impLImp h _ _ ih₁ ih₂ => exact .impLImp h ih₁ ih₂
  | impLLax h _ _ ih₁ ih₂ => exact .impLLax h ih₁ ih₂
  | impLLaxLax h hX _ _ ih₁ ih₂ => exact .impLLaxLax h hX ih₁ ih₂

theorem mono {n m : Nat} {Γ : Finset PLLFormula} {C : PLLFormula}
    (d : G4sh n Γ C) (hnm : n ≤ m) : G4sh m Γ C := by
  induction hnm with
  | refl => exact d
  | step _ ih => exact ih.succ_mono

/-- **Context monotonicity** — the one structural lemma the set world
needs (exchange is definitional, weakening and contraction are
absorbed by `⊆` and `insert`). Height-preserving. -/
theorem weaken_subset : ∀ {n : Nat} {Γ : Finset PLLFormula} {C : PLLFormula},
    G4sh n Γ C → ∀ {Γ' : Finset PLLFormula}, Γ ⊆ Γ' → G4sh n Γ' C := by
  intro n Γ C d
  induction d with
  | init h => intro Γ' hs; exact .init (hs h)
  | botL h => intro Γ' hs; exact .botL (hs h)
  | andR _ _ ih₁ ih₂ => intro Γ' hs; exact .andR (ih₁ hs) (ih₂ hs)
  | orR1 _ ih => intro Γ' hs; exact .orR1 (ih hs)
  | orR2 _ ih => intro Γ' hs; exact .orR2 (ih hs)
  | impR _ ih =>
      intro Γ' hs
      exact .impR (ih (insertSubsetInsert _ hs))
  | laxR _ ih => intro Γ' hs; exact .laxR (ih hs)
  | laxL h _ ih =>
      intro Γ' hs
      exact .laxL (hs h) (ih (insertSubsetInsert _ hs))
  | andL h _ ih =>
      intro Γ' hs
      exact .andL (hs h)
        (ih (insertSubsetInsert _ (insertSubsetInsert _ hs)))
  | orL h _ _ ih₁ ih₂ =>
      intro Γ' hs
      exact .orL (hs h) (ih₁ (insertSubsetInsert _ hs))
        (ih₂ (insertSubsetInsert _ hs))
  | impLProp h ha _ ih =>
      intro Γ' hs
      exact .impLProp (hs h) (hs ha) (ih (insertSubsetInsert _ hs))
  | impLAnd h _ ih =>
      intro Γ' hs
      exact .impLAnd (hs h) (ih (insertSubsetInsert _ hs))
  | impLOr h _ ih =>
      intro Γ' hs
      exact .impLOr (hs h)
        (ih (insertSubsetInsert _ (insertSubsetInsert _ hs)))
  | impLImp h _ _ ih₁ ih₂ =>
      intro Γ' hs
      exact .impLImp (hs h) (ih₁ (insertSubsetInsert _ hs))
        (ih₂ (insertSubsetInsert _ hs))
  | impLLax h _ _ ih₁ ih₂ =>
      intro Γ' hs
      exact .impLLax (hs h) (ih₁ hs) (ih₂ (insertSubsetInsert _ hs))
  | impLLaxLax h hX _ _ ih₁ ih₂ =>
      intro Γ' hs
      exact .impLLaxLax (hs h) (hs hX)
        (ih₁ (insertSubsetInsert _ hs))
        (ih₂ (insertSubsetInsert _ hs))

end G4sh

theorem perm_toFin {Γ Δ : List PLLFormula} (h : Γ.Perm Δ) :
    toFin Γ = toFin Δ :=
  subAntisymm
    (fun x hx => mem_toFin.mpr (h.mem_iff.mp (mem_toFin.mp hx)))
    (fun x hx => mem_toFin.mpr (h.mem_iff.mpr (mem_toFin.mp hx)))

/-- **The list calculus embeds height-preservingly** (choice-free
`toFin` form): every transport is `weaken_subset`. -/
theorem G4h.toSetFin : ∀ {n : Nat} {Γ : List PLLFormula} {E : PLLFormula},
    G4h n Γ E → G4sh n (toFin Γ) E := by
  intro n Γ E d
  induction d with
  | init h => exact .init (mem_toFin.mpr h)
  | botL h => exact .botL (mem_toFin.mpr h)
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | laxR _ ih => exact .laxR ih
  | impR _ ih =>
      rw [toFin_cons] at ih
      exact .impR ih
  | @laxL _ _ A _ h _ ih =>
      rw [toFin_cons] at ih
      exact .laxL (mem_toFin.mpr h) ih
  | @andL _ Γ₀ Δ A B _ h _ ih =>
      have hΓ : toFin Γ₀ = insert (A.and B) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      rw [toFin_cons, toFin_cons] at ih
      refine .andL (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih.weaken_subset ?_)
      exact insertSubsetInsert _ (insertSubsetInsert _
        (by rw [hΓ]; exact Finset.subset_insert _ _))
  | @orL _ Γ₀ Δ A B _ h _ _ ih₁ ih₂ =>
      have hΓ : toFin Γ₀ = insert (A.or B) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      rw [toFin_cons] at ih₁ ih₂
      refine .orL (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih₁.weaken_subset ?_) (ih₂.weaken_subset ?_)
      · exact insertSubsetInsert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)
      · exact insertSubsetInsert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)
  | @impLProp _ Γ₀ Δ a B _ h ha _ ih =>
      have hΓ : toFin Γ₀ = insert ((prop a).ifThen B) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      rw [toFin_cons] at ih
      refine .impLProp (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (by rw [hΓ]
            exact Finset.mem_insert_of_mem (mem_toFin.mpr ha))
        (ih.weaken_subset (insertSubsetInsert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
  | @impLBot _ Γ₀ Δ B _ h _ ih =>
      have hΓ : toFin Γ₀ = insert (falsePLL.ifThen B) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      exact (ih.weaken_subset
        (by rw [hΓ]; exact Finset.subset_insert _ _)).succ_mono
  | @impLAnd _ Γ₀ Δ A B D _ h _ ih =>
      have hΓ : toFin Γ₀ = insert ((A.and B).ifThen D) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      rw [toFin_cons] at ih
      refine .impLAnd (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih.weaken_subset (insertSubsetInsert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
  | @impLOr _ Γ₀ Δ A B D _ h _ ih =>
      have hΓ : toFin Γ₀ = insert ((A.or B).ifThen D) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      rw [toFin_cons, toFin_cons] at ih
      refine .impLOr (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih.weaken_subset (insertSubsetInsert _
          (insertSubsetInsert _
            (by rw [hΓ]; exact Finset.subset_insert _ _))))
  | @impLImp _ Γ₀ Δ A B D _ h _ _ ih₁ ih₂ =>
      have hΓ : toFin Γ₀ = insert ((A.ifThen B).ifThen D) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      rw [toFin_cons] at ih₁ ih₂
      refine .impLImp (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih₁.weaken_subset (insertSubsetInsert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
        (ih₂.weaken_subset (insertSubsetInsert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
  | @impLLax _ Γ₀ Δ A B _ h _ _ ih₁ ih₂ =>
      have hΓ : toFin Γ₀ = insert (A.somehow.ifThen B) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      rw [toFin_cons] at ih₂
      refine .impLLax (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        ih₁
        (ih₂.weaken_subset (insertSubsetInsert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
  | @impLLaxLax _ Γ₀ Δ A B X _ h hX _ _ ih₁ ih₂ =>
      have hΓ : toFin Γ₀ = insert (A.somehow.ifThen B) (toFin Δ) := by
        rw [perm_toFin h, toFin_cons]
      rw [toFin_cons] at ih₁ ih₂
      refine .impLLaxLax (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (by rw [hΓ]
            exact Finset.mem_insert_of_mem (mem_toFin.mpr hX))
        ih₁
        (ih₂.weaken_subset (insertSubsetInsert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))

/-- Legacy `toFinset` form, derived.  Its statement mentions
`List.toFinset`, whose Mathlib body embeds `Classical.choice`, so this
wrapper is choice-tainted by its statement alone; the clean chain uses
`G4h.toSetFin`. -/
theorem G4h.toSet {n : Nat} {Γ : List PLLFormula} {E : PLLFormula}
    (d : G4h n Γ E) : G4sh n Γ.toFinset E := by
  rw [← toFin_eq_toFinset]
  exact d.toSetFin

namespace G4sh

/-- **The cumulative calculus maps onto `SC`**, generalised over any
list enumerating the set-context (choice-free: no `Finset.toList`).
The keeping rules match the cumulative shapes; the three Dyckhoff
rules go through the same `SC.cut` constructions as `G4c.toSC`. -/
theorem toSC_of_toFin : ∀ {n : Nat} {Γs : Finset PLLFormula}
    {E : PLLFormula}, G4sh n Γs E →
    ∀ {Γ : List PLLFormula}, toFin Γ = Γs → SC Γ E := by
  intro n Γs E d
  induction d with
  | init h =>
      intro Γ hΓ; subst hΓ
      exact SC.init (mem_toFin.mp h)
  | botL h =>
      intro Γ hΓ; subst hΓ
      exact SC.botL (mem_toFin.mp h)
  | andR _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      exact SC.andR (ih₁ rfl) (ih₂ rfl)
  | orR1 _ ih =>
      intro Γ hΓ; subst hΓ
      exact SC.orR1 (ih rfl)
  | orR2 _ ih =>
      intro Γ hΓ; subst hΓ
      exact SC.orR2 (ih rfl)
  | laxR _ ih =>
      intro Γ hΓ; subst hΓ
      exact SC.laxR (ih rfl)
  | @impR _ _ A B _ ih =>
      intro Γ hΓ; subst hΓ
      exact SC.impR (ih (Γ := A :: Γ) (by rw [toFin_cons]))
  | @laxL _ _ A B h _ ih =>
      intro Γ hΓ; subst hΓ
      exact SC.laxL (mem_toFin.mp h) (ih (Γ := A :: Γ) (by rw [toFin_cons]))
  | @andL _ _ A B _ h _ ih =>
      intro Γ hΓ; subst hΓ
      exact SC.andL (mem_toFin.mp h)
        (ih (Γ := A :: B :: Γ) (by rw [toFin_cons, toFin_cons]))
  | @orL _ _ A B _ h _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      exact SC.orL (mem_toFin.mp h)
        (ih₁ (Γ := A :: Γ) (by rw [toFin_cons]))
        (ih₂ (Γ := B :: Γ) (by rw [toFin_cons]))
  | @impLProp _ _ a B _ h ha _ ih =>
      intro Γ hΓ; subst hΓ
      exact SC.impL (mem_toFin.mp h)
        (SC.init (mem_toFin.mp ha))
        (ih (Γ := B :: Γ) (by rw [toFin_cons]))
  | @impLAnd _ _ A B D _ h _ ih =>
      intro Γ hΓ; subst hΓ
      have hmem : (A.and B).ifThen D ∈ Γ := mem_toFin.mp h
      have p : SC Γ (A.ifThen (B.ifThen D)) := by
        refine SC.impR (SC.impR ?_)
        exact SC.impL (A := A.and B) (.tail _ (.tail _ hmem))
          (SC.andR (SC.iden _ (.tail _ (.head _))) (SC.iden _ (.head _)))
          (SC.iden _ (.head _))
      exact SC.cut p
        (ih (Γ := A.ifThen (B.ifThen D) :: Γ) (by rw [toFin_cons]))
  | @impLOr _ _ A B D _ h _ ih =>
      intro Γ hΓ; subst hΓ
      have hmem : (A.or B).ifThen D ∈ Γ := mem_toFin.mp h
      have p₁ : SC Γ (A.ifThen D) :=
        SC.impR (SC.impL (A := A.or B) (.tail _ hmem)
          (SC.orR1 (SC.iden _ (.head _))) (SC.iden _ (.head _)))
      have p₂ : SC Γ (B.ifThen D) :=
        SC.impR (SC.impL (A := A.or B) (.tail _ hmem)
          (SC.orR2 (SC.iden _ (.head _))) (SC.iden _ (.head _)))
      refine SC.cut p₁ (SC.cut (p₂.rename fun ψ hψ => .tail _ hψ)
        ((ih (Γ := A.ifThen D :: B.ifThen D :: Γ)
          (by rw [toFin_cons, toFin_cons])).rename ?_))
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | h'
      · exact .tail _ (.head _)
      rcases List.mem_cons.mp h' with rfl | h''
      · exact .head _
      · exact .tail _ (.tail _ h'')
  | @impLImp _ _ A B D _ h _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      have hmem : (A.ifThen B).ifThen D ∈ Γ := mem_toFin.mp h
      have hBD : SC Γ (B.ifThen D) :=
        SC.impR (SC.impL (A := A.ifThen B) (.tail _ hmem)
          (SC.impR (SC.iden _ (.tail _ (.head _)))) (SC.iden _ (.head _)))
      have hAB : SC Γ (A.ifThen B) :=
        SC.cut hBD (ih₁ (Γ := B.ifThen D :: Γ) (by rw [toFin_cons]))
      exact SC.impL hmem hAB (ih₂ (Γ := D :: Γ) (by rw [toFin_cons]))
  | @impLLax _ _ A B _ h _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      exact SC.impL (mem_toFin.mp h) (SC.laxR (ih₁ rfl))
        (ih₂ (Γ := B :: Γ) (by rw [toFin_cons]))
  | @impLLaxLax _ _ A B X _ h hX _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      exact SC.impL (mem_toFin.mp h)
        (SC.laxL (mem_toFin.mp hX) (ih₁ (Γ := X :: Γ) (by rw [toFin_cons])))
        (ih₂ (Γ := B :: Γ) (by rw [toFin_cons]))

/-- Legacy `Finset.toList` form, derived.  Statement-tainted
(`Finset.toList` picks its representative by `Classical.choice`); the
clean chain uses `toSC_of_toFin`. -/
theorem toSC {n : Nat} {Γs : Finset PLLFormula} {E : PLLFormula}
    (d : G4sh n Γs E) : SC Γs.toList E :=
  d.toSC_of_toFin (toFin_toList Γs)

end G4sh

/-- **The set calculus proves exactly the `G4c` sequents** — choice-free
`toFin` form. -/
theorem G4c.iff_setFin {Γ : List PLLFormula} {E : PLLFormula} :
    G4c Γ E ↔ G4s (toFin Γ) E := by
  constructor
  · rintro ⟨n, d⟩
    exact ⟨n, d.toSetFin⟩
  · rintro ⟨n, d⟩
    exact G4c.completeness (d.toSC_of_toFin rfl)

/-- Legacy `toFinset` form, derived.  Statement-tainted through
`List.toFinset`; the clean chain uses `G4c.iff_setFin`. -/
theorem G4c.iff_set {Γ : List PLLFormula} {E : PLLFormula} :
    G4c Γ E ↔ G4s Γ.toFinset E := by
  rw [← toFin_eq_toFinset]
  exact G4c.iff_setFin

/-! ## The height-bounded decider

`G4sh (n+1) Γ C` holds iff one of the finitely many rules applies with
premises at height `n`; `G4sh 0 Γ C` iff an axiom applies.  Both
right-hand sides are decidable (memberships, Boolean combinations, and
bounded quantifiers over the finite context), so `Decidable (G4sh n Γ C)`
follows by structural recursion on `n`. -/

/-- The axioms: `init` (conclusion an atom of the context) — `botL` is
handled separately. -/
def isInit (Γ : Finset PLLFormula) : PLLFormula → Prop
  | .prop a => prop a ∈ Γ
  | _ => False

/-- The `laxL` premise at a candidate principal `F`: `F = ◯x` and the
opened premise holds. -/
def laxLPrem (P : Finset PLLFormula → PLLFormula → Prop)
    (Γ : Finset PLLFormula) (A : PLLFormula) : PLLFormula → Prop
  | .somehow x => P (insert x Γ) (somehow A)
  | _ => False

/-- The `impLLaxLax` premises at a candidate witness `F`: `F = ◯x` and
both premises hold (`A`, `B` from the principal `◯A → B`). -/
def impLaxPrem (P : Finset PLLFormula → PLLFormula → Prop)
    (Γ : Finset PLLFormula) (A B C : PLLFormula) : PLLFormula → Prop
  | .somehow x => P (insert x Γ) A.somehow ∧ P (insert B Γ) C
  | _ => False

/-- One right rule applies to `C`, premises drawn from `P`. -/
def rightStep (P : Finset PLLFormula → PLLFormula → Prop)
    (Γ : Finset PLLFormula) : PLLFormula → Prop
  | .prop _ => False
  | .falsePLL => False
  | .and A B => P Γ A ∧ P Γ B
  | .or A B => P Γ A ∨ P Γ B
  | .ifThen A B => P (insert A Γ) B
  | .somehow A => P Γ A ∨ ∃ F ∈ Γ, laxLPrem P Γ A F

/-- One left rule applies at principal `F`, premises drawn from `P`. -/
def leftStep (P : Finset PLLFormula → PLLFormula → Prop)
    (Γ : Finset PLLFormula) (C : PLLFormula) : PLLFormula → Prop
  | .and A B => P (insert A (insert B Γ)) C
  | .or A B => P (insert A Γ) C ∧ P (insert B Γ) C
  | .ifThen (.prop a) B => prop a ∈ Γ ∧ P (insert B Γ) C
  | .ifThen (.and A B) D => P (insert (A.ifThen (B.ifThen D)) Γ) C
  | .ifThen (.or A B) D =>
      P (insert (A.ifThen D) (insert (B.ifThen D) Γ)) C
  | .ifThen (.ifThen A B) D =>
      P (insert (B.ifThen D) Γ) (A.ifThen B) ∧ P (insert D Γ) C
  | .ifThen (.somehow A) B =>
      (P Γ A ∧ P (insert B Γ) C) ∨ ∃ F ∈ Γ, impLaxPrem P Γ A B C F
  | _ => False

/-- **Inversion at height 0**: only the axioms apply. -/
theorem g4sh_zero_iff (Γ : Finset PLLFormula) (C : PLLFormula) :
    G4sh 0 Γ C ↔ falsePLL ∈ Γ ∨ isInit Γ C := by
  constructor
  · intro d
    cases d with
    | init h => exact .inr h
    | botL h => exact .inl h
  · rintro (h | h)
    · exact .botL h
    · cases C with
      | prop a => exact .init h
      | falsePLL => exact h.elim
      | and _ _ => exact h.elim
      | or _ _ => exact h.elim
      | ifThen _ _ => exact h.elim
      | somehow _ => exact h.elim

/-- **Inversion at successor height**: an axiom, a right rule with
premises one lower, or a left rule at some context formula. -/
theorem g4sh_succ_iff (n : Nat) (Γ : Finset PLLFormula) (C : PLLFormula) :
    G4sh (n + 1) Γ C ↔
      falsePLL ∈ Γ ∨ isInit Γ C ∨ rightStep (G4sh n) Γ C ∨
        ∃ F ∈ Γ, leftStep (G4sh n) Γ C F := by
  constructor
  · intro d
    cases d with
    | init h => exact .inr (.inl h)
    | botL h => exact .inl h
    | andR d₁ d₂ => exact .inr (.inr (.inl ⟨d₁, d₂⟩))
    | orR1 d => exact .inr (.inr (.inl (.inl d)))
    | orR2 d => exact .inr (.inr (.inl (.inr d)))
    | impR d => exact .inr (.inr (.inl d))
    | laxR d => exact .inr (.inr (.inl (.inl d)))
    | @laxL _ _ A B h d =>
        exact .inr (.inr (.inl (.inr ⟨A.somehow, h, d⟩)))
    | @andL _ _ A B _ h d => exact .inr (.inr (.inr ⟨A.and B, h, d⟩))
    | @orL _ _ A B _ h d₁ d₂ =>
        exact .inr (.inr (.inr ⟨A.or B, h, d₁, d₂⟩))
    | @impLProp _ _ a B _ h ha d =>
        exact .inr (.inr (.inr ⟨(prop a).ifThen B, h, ha, d⟩))
    | @impLAnd _ _ A B D _ h d =>
        exact .inr (.inr (.inr ⟨(A.and B).ifThen D, h, d⟩))
    | @impLOr _ _ A B D _ h d =>
        exact .inr (.inr (.inr ⟨(A.or B).ifThen D, h, d⟩))
    | @impLImp _ _ A B D _ h d₁ d₂ =>
        exact .inr (.inr (.inr ⟨(A.ifThen B).ifThen D, h, d₁, d₂⟩))
    | @impLLax _ _ A B _ h d₁ d₂ =>
        exact .inr (.inr (.inr ⟨A.somehow.ifThen B, h, .inl ⟨d₁, d₂⟩⟩))
    | @impLLaxLax _ _ A B X _ h hX d₁ d₂ =>
        exact .inr (.inr (.inr
          ⟨A.somehow.ifThen B, h, .inr ⟨X.somehow, hX, d₁, d₂⟩⟩))
  · rintro (h | h | hright | ⟨F, hF, hleft⟩)
    · exact .botL h
    · cases C with
      | prop a => exact .init h
      | falsePLL => exact h.elim
      | and _ _ => exact h.elim
      | or _ _ => exact h.elim
      | ifThen _ _ => exact h.elim
      | somehow _ => exact h.elim
    · cases C with
      | prop a => exact hright.elim
      | falsePLL => exact hright.elim
      | and A B => exact .andR hright.1 hright.2
      | or A B =>
          rcases hright with d | d
          · exact .orR1 d
          · exact .orR2 d
      | ifThen A B => exact .impR hright
      | somehow A =>
          rcases hright with d | ⟨F, hF, hw⟩
          · exact .laxR d
          · cases F with
            | somehow x => exact .laxL hF hw
            | prop _ => exact hw.elim
            | falsePLL => exact hw.elim
            | and _ _ => exact hw.elim
            | or _ _ => exact hw.elim
            | ifThen _ _ => exact hw.elim
    · cases F with
      | prop _ => exact hleft.elim
      | falsePLL => exact hleft.elim
      | somehow _ => exact hleft.elim
      | and A B => exact .andL hF hleft
      | or A B => exact .orL hF hleft.1 hleft.2
      | ifThen A' B =>
          cases A' with
          | prop a => exact .impLProp hF hleft.1 hleft.2
          | falsePLL => exact hleft.elim
          | and A₁ B₁ => exact .impLAnd hF hleft
          | or A₁ B₁ => exact .impLOr hF hleft
          | ifThen A₁ B₁ => exact .impLImp hF hleft.1 hleft.2
          | somehow A₁ =>
              rcases hleft with ⟨d₁, d₂⟩ | ⟨X, hX, hw⟩
              · exact .impLLax hF d₁ d₂
              · cases X with
                | somehow x => exact .impLLaxLax hF hX hw.1 hw.2
                | prop _ => exact hw.elim
                | falsePLL => exact hw.elim
                | and _ _ => exact hw.elim
                | or _ _ => exact hw.elim
                | ifThen _ _ => exact hw.elim

instance isInit.dec (Γ : Finset PLLFormula) :
    ∀ C, Decidable (isInit Γ C)
  | .prop a => inferInstanceAs (Decidable (prop a ∈ Γ))
  | .falsePLL => inferInstanceAs (Decidable False)
  | .and _ _ => inferInstanceAs (Decidable False)
  | .or _ _ => inferInstanceAs (Decidable False)
  | .ifThen _ _ => inferInstanceAs (Decidable False)
  | .somehow _ => inferInstanceAs (Decidable False)

def laxLPrem.dec (P : Finset PLLFormula → PLLFormula → Prop)
    (hP : ∀ Γ C, Decidable (P Γ C)) (Γ : Finset PLLFormula)
    (A : PLLFormula) : ∀ F, Decidable (laxLPrem P Γ A F)
  | .somehow _ => hP _ _
  | .prop _ => inferInstanceAs (Decidable False)
  | .falsePLL => inferInstanceAs (Decidable False)
  | .and _ _ => inferInstanceAs (Decidable False)
  | .or _ _ => inferInstanceAs (Decidable False)
  | .ifThen _ _ => inferInstanceAs (Decidable False)

def impLaxPrem.dec (P : Finset PLLFormula → PLLFormula → Prop)
    (hP : ∀ Γ C, Decidable (P Γ C)) (Γ : Finset PLLFormula)
    (A B C : PLLFormula) : ∀ F, Decidable (impLaxPrem P Γ A B C F)
  | .somehow _ => letI := hP; inferInstanceAs (Decidable (_ ∧ _))
  | .prop _ => inferInstanceAs (Decidable False)
  | .falsePLL => inferInstanceAs (Decidable False)
  | .and _ _ => inferInstanceAs (Decidable False)
  | .or _ _ => inferInstanceAs (Decidable False)
  | .ifThen _ _ => inferInstanceAs (Decidable False)

def rightStep.dec (P : Finset PLLFormula → PLLFormula → Prop)
    (hP : ∀ Γ C, Decidable (P Γ C)) (Γ : Finset PLLFormula) :
    ∀ C, Decidable (rightStep P Γ C)
  | .prop _ => inferInstanceAs (Decidable False)
  | .falsePLL => inferInstanceAs (Decidable False)
  | .and _ _ => letI := hP; inferInstanceAs (Decidable (_ ∧ _))
  | .or _ _ => letI := hP; inferInstanceAs (Decidable (_ ∨ _))
  | .ifThen _ _ => hP _ _
  | .somehow A =>
      letI := hP
      letI : ∀ F, Decidable (laxLPrem P Γ A F) := laxLPrem.dec P hP Γ A
      inferInstanceAs (Decidable (_ ∨ ∃ F ∈ Γ, laxLPrem P Γ A F))

def leftStep.dec (P : Finset PLLFormula → PLLFormula → Prop)
    (hP : ∀ Γ C, Decidable (P Γ C)) (Γ : Finset PLLFormula)
    (C : PLLFormula) : ∀ F, Decidable (leftStep P Γ C F)
  | .prop _ => inferInstanceAs (Decidable False)
  | .falsePLL => inferInstanceAs (Decidable False)
  | .somehow _ => inferInstanceAs (Decidable False)
  | .and _ _ => hP _ _
  | .or _ _ => letI := hP; inferInstanceAs (Decidable (_ ∧ _))
  | .ifThen (.prop _) _ => letI := hP; inferInstanceAs (Decidable (_ ∧ _))
  | .ifThen .falsePLL _ => inferInstanceAs (Decidable False)
  | .ifThen (.and _ _) _ => hP _ _
  | .ifThen (.or _ _) _ => hP _ _
  | .ifThen (.ifThen _ _) _ => letI := hP; inferInstanceAs (Decidable (_ ∧ _))
  | .ifThen (.somehow A) B =>
      letI := hP
      letI : ∀ F, Decidable (impLaxPrem P Γ A B C F) :=
        impLaxPrem.dec P hP Γ A B C
      inferInstanceAs (Decidable (_ ∨ ∃ F ∈ Γ, impLaxPrem P Γ A B C F))

/-- **The height-bounded decider**: `G4sh n Γ C` is decidable, by
structural recursion on the height through the inversion lemmas. -/
def G4sh.dec : ∀ (n : Nat) (Γ : Finset PLLFormula) (C : PLLFormula),
    Decidable (G4sh n Γ C)
  | 0, Γ, C => decidable_of_iff _ (g4sh_zero_iff Γ C).symm
  | n + 1, Γ, C =>
      have hP : ∀ Γ' C', Decidable (G4sh n Γ' C') := G4sh.dec n
      letI : Decidable (rightStep (G4sh n) Γ C) := rightStep.dec _ hP Γ C
      letI : ∀ F, Decidable (leftStep (G4sh n) Γ C F) :=
        leftStep.dec _ hP Γ C
      decidable_of_iff _ (g4sh_succ_iff n Γ C).symm

instance (n : Nat) (Γ : Finset PLLFormula) (C : PLLFormula) :
    Decidable (G4sh n Γ C) := G4sh.dec n Γ C

/-- info: 'PLLND.G4sh.dec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms G4sh.dec

/-- info: 'PLLND.G4c.iff_setFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms G4c.iff_setFin

/--
info: 'PLLND.G4c.iff_set' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G4c.iff_set

end PLLND
