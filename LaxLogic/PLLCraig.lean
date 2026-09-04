import LaxLogic.PLLG4Space

/-!
# Craig interpolation for PLL (Maehara's method)

**Craig interpolation** for propositional lax logic, proved by Maehara's
method over the cut-free complete sequent calculus `SCh`/`SC` of
`PLLSequent.lean`.  Since the repo proves `SC` equivalent to natural
deduction (`cutElimination`, F&M Theorem 2.6) and hence to the Hilbert
system and the term calculus, interpolation for `SC`-derivability *is*
Craig interpolation for PLL.

Given a derivation of `Γ ⊢ C` and a splitting of the context into two
parts `Γ₁; Γ₂`, Maehara's induction produces an **interpolant** `I`:

  * `Γ₁ ⊢ I` and `I, Γ₂ ⊢ C`, and
  * every atom of `I` occurs both in `Γ₁` and in `Γ₂, C`.

Because the left rules of `SCh` are membership-style (the principal
formula stays in the context), the working notion of splitting is a
membership assignment `∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂` (`SCh.maehara`); the
packaged statements (`SC.maehara'`, `craig_interpolation'`,
`craig_implication'`, and their Mathlib-phrased unprimed wrappers)
specialise it to permutation/append splittings.

The interpolant construction is the textbook one on the intuitionistic
fragment — interpolants combine by `∧`/`∨`/`⊃` according to the side
carrying the principal formula, with the split *swapped* for the minor
premise of `⊃L` when the principal implication sits in `Γ₁`.  The two
lax rules add exactly one twist:

  * `◯R` and `◯L`-with-principal-in-`Γ₂` pass the premise interpolant
    through unchanged;
  * `◯L` with principal `◯A ∈ Γ₁` **boxes** the premise interpolant,
    `I ↦ ◯I`.  Boxing is forced: to derive `Γ₁ ⊢ I` one would have to
    open `◯A ∈ Γ₁` with `◯L`, and `◯L` fires only at a `◯`-shaped
    succedent.  `◯I` restores the discipline on both sides — `Γ₁ ⊢ ◯I`
    opens `◯A` under the now-boxed goal, and `◯I, Γ₂ ⊢ ◯B` opens `◯I`
    under the `◯`-shaped end-formula `◯B`.

This mirrors the `□`-case of Maehara interpolation for constructive
modal calculi; the single-succedent lax `◯` needs no bookkeeping
beyond it.

**Axiom hygiene** (scrubbed 2026-07-18).  The whole chain is built on
the choice-free `finUnion` of `PLLFinsetKit.lean` and membership-form
lemmas, so `SCh.maehara` and the primed statements audit
`[propext, Quot.sound]` — no choice.  The unprimed forms restate them
through Mathlib's `∪`/`∩`, whose definitions embed `Classical.choice`,
so those *statements* audit `clean` however proved (the ‡ pattern of
the ledger); each is a two-line wrapper around its primed twin.
-/

open PLLFormula

namespace PLLND

/-! ### Atoms of a context -/

/-- The atoms occurring in a list of formulas (built on the choice-free
`finUnion`). -/
def atomsList : List PLLFormula → Finset String
  | [] => ∅
  | φ :: Γ => finUnion φ.atoms (atomsList Γ)

@[simp] theorem atomsList_nil : atomsList [] = ∅ := rfl

/-- Membership form — the working lemma of the choice-free chain. -/
@[simp] theorem mem_atomsList_cons {x : String} {φ : PLLFormula}
    {Γ : List PLLFormula} :
    x ∈ atomsList (φ :: Γ) ↔ x ∈ φ.atoms ∨ x ∈ atomsList Γ := mem_finUnion

/-- Equational form (statement mentions Mathlib `∪`; kept for reuse, not
`simp` — the clean chain uses `mem_atomsList_cons`). -/
theorem atomsList_cons {φ : PLLFormula} {Γ : List PLLFormula} :
    atomsList (φ :: Γ) = φ.atoms ∪ atomsList Γ :=
  subAntisymm
    (fun _ hx => Finset.mem_union.mpr (mem_finUnion.mp hx))
    (fun _ hx => mem_finUnion.mpr (Finset.mem_union.mp hx))

/-! ### Subset toolbox (choice-free) -/

private theorem sub_trans {s t u : Finset String}
    (h₁ : s ⊆ t) (h₂ : t ⊆ u) : s ⊆ u :=
  fun _ hx => h₂ (h₁ hx)

private theorem sub_finUnion_left {s t : Finset String} : s ⊆ finUnion s t :=
  fun _ hx => mem_finUnion.mpr (Or.inl hx)

private theorem sub_finUnion_right {s t : Finset String} : t ⊆ finUnion s t :=
  fun _ hx => mem_finUnion.mpr (Or.inr hx)

private theorem finUnion_sub {s t v : Finset String}
    (h₁ : s ⊆ v) (h₂ : t ⊆ v) : finUnion s t ⊆ v :=
  fun _ hx => (mem_finUnion.mp hx).elim (fun h => h₁ h) (fun h => h₂ h)

/-- Monotonicity of `⊆ finUnion _ _` in the right component. -/
private theorem sub_union_right_mono {s t u v : Finset String}
    (h : s ⊆ finUnion t u) (huv : u ⊆ v) : s ⊆ finUnion t v :=
  fun _ hx => mem_finUnion.mpr ((mem_finUnion.mp (h hx)).imp id (fun hh => huv hh))

/-- Monotonicity of `⊆ finUnion _ _` in the left component. -/
private theorem sub_union_left_mono {s t t' u : Finset String}
    (h : s ⊆ finUnion t u) (htt' : t ⊆ t') : s ⊆ finUnion t' u :=
  fun _ hx => mem_finUnion.mpr ((mem_finUnion.mp (h hx)).imp (fun hh => htt' hh) id)

/-- Atoms of a member are atoms of the list. -/
theorem atoms_subset_atomsList {φ : PLLFormula} {Γ : List PLLFormula}
    (h : φ ∈ Γ) : φ.atoms ⊆ atomsList Γ := by
  induction Γ with
  | nil => cases h
  | cons ψ Γ ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact sub_finUnion_left
      · exact sub_trans (ih h) sub_finUnion_right

/-- Consing a formula whose atoms are already present adds no atoms. -/
theorem atomsList_cons_subset {X : PLLFormula} {Γ : List PLLFormula}
    (hX : X.atoms ⊆ atomsList Γ) : atomsList (X :: Γ) ⊆ atomsList Γ :=
  finUnion_sub hX (fun _ hx => hx)

/-! ### Atom bookkeeping: connective components, membership-form -/

private theorem atoms_and_left {A B : PLLFormula} :
    A.atoms ⊆ (A.and B).atoms :=
  fun _ hx => mem_atoms_and.mpr (Or.inl hx)

private theorem atoms_and_right {A B : PLLFormula} :
    B.atoms ⊆ (A.and B).atoms :=
  fun _ hx => mem_atoms_and.mpr (Or.inr hx)

private theorem atoms_or_left {A B : PLLFormula} :
    A.atoms ⊆ (A.or B).atoms :=
  fun _ hx => mem_atoms_or.mpr (Or.inl hx)

private theorem atoms_or_right {A B : PLLFormula} :
    B.atoms ⊆ (A.or B).atoms :=
  fun _ hx => mem_atoms_or.mpr (Or.inr hx)

private theorem atoms_imp_left {A B : PLLFormula} :
    A.atoms ⊆ (A.ifThen B).atoms :=
  fun _ hx => mem_atoms_ifThen.mpr (Or.inl hx)

private theorem atoms_imp_right {A B : PLLFormula} :
    B.atoms ⊆ (A.ifThen B).atoms :=
  fun _ hx => mem_atoms_ifThen.mpr (Or.inr hx)

private theorem atoms_lax {A : PLLFormula} :
    A.atoms ⊆ (A.somehow).atoms :=
  fun _ hx => hx

/-- Combine: `(A ∧ B).atoms ⊆ X` from both components. -/
private theorem atoms_and_sub {A B : PLLFormula} {X : Finset String}
    (hA : A.atoms ⊆ X) (hB : B.atoms ⊆ X) : (A.and B).atoms ⊆ X :=
  fun _ hx => (mem_atoms_and.mp hx).elim (fun h => hA h) (fun h => hB h)

private theorem atoms_or_sub {A B : PLLFormula} {X : Finset String}
    (hA : A.atoms ⊆ X) (hB : B.atoms ⊆ X) : (A.or B).atoms ⊆ X :=
  fun _ hx => (mem_atoms_or.mp hx).elim (fun h => hA h) (fun h => hB h)

private theorem atoms_imp_sub {A B : PLLFormula} {X : Finset String}
    (hA : A.atoms ⊆ X) (hB : B.atoms ⊆ X) : (A.ifThen B).atoms ⊆ X :=
  fun _ hx => (mem_atoms_ifThen.mp hx).elim (fun h => hA h) (fun h => hB h)

private theorem atoms_falsePLL_sub {X : Finset String} :
    (PLLFormula.falsePLL).atoms ⊆ X :=
  fun x hx => absurd hx (Finset.notMem_empty x)

private theorem atoms_truePLL_sub {X : Finset String} : truePLL.atoms ⊆ X :=
  fun x hx => (mem_atoms_ifThen.mp hx).elim
    (fun h => absurd h (Finset.notMem_empty x))
    (fun h => absurd h (Finset.notMem_empty x))

/-! ### Splitting combinators

A *split* of `Γ` assigns each hypothesis to `Γ₁` or to `Γ₂`.  The three
combinators below are the only ways splits evolve during the induction:
a freshly introduced hypothesis joins the side of its principal
formula, and (for the minor premise of `⊃L` on the `Γ₁` side) the two
sides swap roles. -/

private theorem split_cons_left {φ : PLLFormula} {Γ Γ₁ Γ₂ : List PLLFormula}
    (H : ∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂) :
    ∀ ψ ∈ φ :: Γ, ψ ∈ φ :: Γ₁ ∨ ψ ∈ Γ₂ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact Or.inl (.head _)
  · rcases H _ hψ with h | h
    · exact Or.inl (.tail _ h)
    · exact Or.inr h

private theorem split_cons_right {φ : PLLFormula} {Γ Γ₁ Γ₂ : List PLLFormula}
    (H : ∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂) :
    ∀ ψ ∈ φ :: Γ, ψ ∈ Γ₁ ∨ ψ ∈ φ :: Γ₂ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact Or.inr (.head _)
  · rcases H _ hψ with h | h
    · exact Or.inl h
    · exact Or.inr (.tail _ h)

private theorem split_swap {Γ Γ₁ Γ₂ : List PLLFormula}
    (H : ∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂) :
    ∀ ψ ∈ Γ, ψ ∈ Γ₂ ∨ ψ ∈ Γ₁ :=
  fun ψ hψ => (H ψ hψ).symm

/-- `⊤` (definitionally `⊥ ⊃ ⊥`) is derivable in any context. -/
theorem SC.trueR {Γ : List PLLFormula} : SC Γ truePLL :=
  SC.impR (SC.botL (.head _))

/-! ### Maehara's lemma -/

/-- **Maehara's lemma** for the cut-free calculus, membership-split form:
from a derivation of `Γ ⊢ C` and an assignment of each hypothesis of `Γ`
to `Γ₁` or to `Γ₂`, an interpolant `I` with `Γ₁ ⊢ I`, `I, Γ₂ ⊢ C`, and
`I`'s atoms contained both in `Γ₁`'s and in `Γ₂, C`'s.

Interpolant construction, by the last rule and the side of its
principal formula (`Γ₁`-side / `Γ₂`-side):

| rule       | `Γ₁`-side              | `Γ₂`-side       |
|------------|------------------------|-----------------|
| `init`     | the atom itself        | `⊤`             |
| `botL`     | `⊥`                    | `⊤`             |
| `andR`     | `I₁ ∧ I₂`              | (same — right rule) |
| `andL`     | pass through           | pass through    |
| `orR1/2`   | pass through           | (right rule)    |
| `orL`      | `I₁ ∨ I₂`              | `I₁ ∧ I₂`       |
| `impR`     | pass through           | (right rule)    |
| `impL`     | `I₁ ⊃ I₂` (split swapped for the minor premise) | `I₁ ∧ I₂` |
| `laxR`     | pass through           | (right rule)    |
| `laxL`     | **`◯I`**               | pass through    |
-/
theorem SCh.maehara : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    SCh n Γ C → ∀ Γ₁ Γ₂ : List PLLFormula,
    (∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂) →
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∧ I.atoms ⊆ finUnion (atomsList Γ₂) C.atoms := by
  intro n Γ C d
  induction d with
  | @init n Γ a h =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · exact ⟨.prop a, SC.init h₁, SC.init (.head _),
          atoms_subset_atomsList h₁, sub_finUnion_right⟩
      · exact ⟨truePLL, SC.trueR, SC.init (.tail _ h₂),
          atoms_truePLL_sub, atoms_truePLL_sub⟩
  | @botL n Γ C h =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · exact ⟨.falsePLL, SC.botL h₁, SC.botL (.head _),
          atoms_falsePLL_sub, atoms_falsePLL_sub⟩
      · exact ⟨truePLL, SC.trueR, SC.botL (.tail _ h₂),
          atoms_truePLL_sub, atoms_truePLL_sub⟩
  | @andR n Γ A B dA dB ihA ihB =>
      intro Γ₁ Γ₂ H
      obtain ⟨I₁, s₁, t₁, a₁, b₁⟩ := ihA Γ₁ Γ₂ H
      obtain ⟨I₂, s₂, t₂, a₂, b₂⟩ := ihB Γ₁ Γ₂ H
      refine ⟨I₁.and I₂, SC.andR s₁ s₂, ?_, ?_, ?_⟩
      · refine SC.andL (.head _) (SC.andR ?_ ?_)
        · exact t₁.rename (by
            intro ψ hψ
            rcases List.mem_cons.mp hψ with rfl | h
            · exact .head _
            · exact .tail _ (.tail _ (.tail _ h)))
        · exact t₂.rename (by
            intro ψ hψ
            rcases List.mem_cons.mp hψ with rfl | h
            · exact .tail _ (.head _)
            · exact .tail _ (.tail _ (.tail _ h)))
      · exact atoms_and_sub a₁ a₂
      · exact atoms_and_sub
          (sub_union_right_mono b₁ atoms_and_left)
          (sub_union_right_mono b₂ atoms_and_right)
  | @andL n Γ A B C h d ih =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · -- principal `A ∧ B` assigned to `Γ₁`: pass through
        obtain ⟨I, s, t, a₁, a₂⟩ :=
          ih (A :: B :: Γ₁) Γ₂ (split_cons_left (split_cons_left H))
        have hA : A.atoms ⊆ atomsList Γ₁ :=
          sub_trans atoms_and_left (atoms_subset_atomsList h₁)
        have hB : B.atoms ⊆ atomsList Γ₁ :=
          sub_trans atoms_and_right (atoms_subset_atomsList h₁)
        have habs : atomsList (A :: B :: Γ₁) ⊆ atomsList Γ₁ := by
          intro x hx
          rcases mem_atomsList_cons.mp hx with h' | h'
          · exact hA h'
          · rcases mem_atomsList_cons.mp h' with h'' | h''
            · exact hB h''
            · exact h''
        exact ⟨I, SC.andL h₁ s, t, sub_trans a₁ habs, a₂⟩
      · -- principal `A ∧ B` assigned to `Γ₂`: pass through
        obtain ⟨I, s, t, a₁, a₂⟩ :=
          ih Γ₁ (A :: B :: Γ₂) (split_cons_right (split_cons_right H))
        have hA : A.atoms ⊆ atomsList Γ₂ :=
          sub_trans atoms_and_left (atoms_subset_atomsList h₂)
        have hB : B.atoms ⊆ atomsList Γ₂ :=
          sub_trans atoms_and_right (atoms_subset_atomsList h₂)
        have habs : atomsList (A :: B :: Γ₂) ⊆ atomsList Γ₂ := by
          intro x hx
          rcases mem_atomsList_cons.mp hx with h' | h'
          · exact hA h'
          · rcases mem_atomsList_cons.mp h' with h'' | h''
            · exact hB h''
            · exact h''
        refine ⟨I, s, ?_, a₁, sub_union_left_mono a₂ habs⟩
        refine SC.andL (.tail _ h₂) ?_
        exact t.rename (by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | h
          · exact .tail _ (.tail _ (.head _))
          · rcases List.mem_cons.mp h with rfl | h
            · exact .head _
            · rcases List.mem_cons.mp h with rfl | h
              · exact .tail _ (.head _)
              · exact .tail _ (.tail _ (.tail _ h)))
  | @orR1 n Γ A B d ih =>
      intro Γ₁ Γ₂ H
      obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ Γ₂ H
      exact ⟨I, s, SC.orR1 t, a₁, sub_union_right_mono a₂ atoms_or_left⟩
  | @orR2 n Γ A B d ih =>
      intro Γ₁ Γ₂ H
      obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ Γ₂ H
      exact ⟨I, s, SC.orR2 t, a₁, sub_union_right_mono a₂ atoms_or_right⟩
  | @orL n Γ A B C h d₁ d₂ ih₁ ih₂ =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · -- principal `A ∨ B` in `Γ₁`: interpolants combine with `∨`
        obtain ⟨I₁, s₁, t₁, a₁, b₁⟩ := ih₁ (A :: Γ₁) Γ₂ (split_cons_left H)
        obtain ⟨I₂, s₂, t₂, a₂, b₂⟩ := ih₂ (B :: Γ₁) Γ₂ (split_cons_left H)
        have hA : A.atoms ⊆ atomsList Γ₁ :=
          sub_trans atoms_or_left (atoms_subset_atomsList h₁)
        have hB : B.atoms ⊆ atomsList Γ₁ :=
          sub_trans atoms_or_right (atoms_subset_atomsList h₁)
        refine ⟨I₁.or I₂, SC.orL h₁ (SC.orR1 s₁) (SC.orR2 s₂), ?_, ?_, ?_⟩
        · refine SC.orL (.head _) ?_ ?_
          · exact t₁.rename (by
              intro ψ hψ
              rcases List.mem_cons.mp hψ with rfl | h
              · exact .head _
              · exact .tail _ (.tail _ h))
          · exact t₂.rename (by
              intro ψ hψ
              rcases List.mem_cons.mp hψ with rfl | h
              · exact .head _
              · exact .tail _ (.tail _ h))
        · exact atoms_or_sub
            (sub_trans a₁ (atomsList_cons_subset hA))
            (sub_trans a₂ (atomsList_cons_subset hB))
        · exact atoms_or_sub b₁ b₂
      · -- principal `A ∨ B` in `Γ₂`: interpolants combine with `∧`
        obtain ⟨I₁, s₁, t₁, a₁, b₁⟩ := ih₁ Γ₁ (A :: Γ₂) (split_cons_right H)
        obtain ⟨I₂, s₂, t₂, a₂, b₂⟩ := ih₂ Γ₁ (B :: Γ₂) (split_cons_right H)
        have hA : A.atoms ⊆ atomsList Γ₂ :=
          sub_trans atoms_or_left (atoms_subset_atomsList h₂)
        have hB : B.atoms ⊆ atomsList Γ₂ :=
          sub_trans atoms_or_right (atoms_subset_atomsList h₂)
        refine ⟨I₁.and I₂, SC.andR s₁ s₂, ?_, ?_, ?_⟩
        · refine SC.orL (.tail _ h₂) ?_ ?_
          · refine SC.andL (.tail _ (.head _)) ?_
            exact t₁.rename (by
              intro ψ hψ
              rcases List.mem_cons.mp hψ with rfl | h
              · exact .head _
              · rcases List.mem_cons.mp h with rfl | h
                · exact .tail _ (.tail _ (.head _))
                · exact .tail _ (.tail _ (.tail _ (.tail _ h))))
          · refine SC.andL (.tail _ (.head _)) ?_
            exact t₂.rename (by
              intro ψ hψ
              rcases List.mem_cons.mp hψ with rfl | h
              · exact .tail _ (.head _)
              · rcases List.mem_cons.mp h with rfl | h
                · exact .tail _ (.tail _ (.head _))
                · exact .tail _ (.tail _ (.tail _ (.tail _ h))))
        · exact atoms_and_sub a₁ a₂
        · exact atoms_and_sub
            (sub_union_left_mono b₁ (atomsList_cons_subset hA))
            (sub_union_left_mono b₂ (atomsList_cons_subset hB))
  | @impR n Γ A B d ih =>
      intro Γ₁ Γ₂ H
      obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ (A :: Γ₂) (split_cons_right H)
      refine ⟨I, s, ?_, a₁, ?_⟩
      · refine SC.impR ?_
        exact t.rename (by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | h
          · exact .tail _ (.head _)
          · rcases List.mem_cons.mp h with rfl | h
            · exact .head _
            · exact .tail _ (.tail _ h))
      · -- the discharged hypothesis `A` migrates from context to succedent
        intro x hx
        rcases mem_finUnion.mp (a₂ hx) with h' | h'
        · rcases mem_atomsList_cons.mp h' with h'' | h''
          · exact mem_finUnion.mpr (Or.inr (mem_atoms_ifThen.mpr (Or.inl h'')))
          · exact mem_finUnion.mpr (Or.inl h'')
        · exact mem_finUnion.mpr (Or.inr (mem_atoms_ifThen.mpr (Or.inr h')))
  | @impL n Γ A B C h d₁ d₂ ih₁ ih₂ =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · -- principal `A ⊃ B` in `Γ₁`: `I₁ ⊃ I₂`, with the split *swapped*
        -- for the minor premise `Γ ⊢ A`
        obtain ⟨J, sJ, tJ, aJ, bJ⟩ := ih₁ Γ₂ Γ₁ (split_swap H)
        obtain ⟨K, sK, tK, aK, bK⟩ := ih₂ (B :: Γ₁) Γ₂ (split_cons_left H)
        have hA : A.atoms ⊆ atomsList Γ₁ :=
          sub_trans atoms_imp_left (atoms_subset_atomsList h₁)
        have hB : B.atoms ⊆ atomsList Γ₁ :=
          sub_trans atoms_imp_right (atoms_subset_atomsList h₁)
        refine ⟨J.ifThen K, ?_, ?_, ?_, ?_⟩
        · refine SC.impR (SC.impL (.tail _ h₁) tJ ?_)
          exact sK.rename (by
            intro ψ hψ
            rcases List.mem_cons.mp hψ with rfl | h
            · exact .head _
            · exact .tail _ (.tail _ h))
        · refine SC.impL (.head _) ?_ ?_
          · exact sJ.rename (fun ψ hψ => .tail _ hψ)
          · exact tK.rename (by
              intro ψ hψ
              rcases List.mem_cons.mp hψ with rfl | h
              · exact .head _
              · exact .tail _ (.tail _ h))
        · exact atoms_imp_sub
            (sub_trans bJ (finUnion_sub (fun _ hx => hx) hA))
            (sub_trans aK (atomsList_cons_subset hB))
        · exact atoms_imp_sub (sub_trans aJ sub_finUnion_left) bK
      · -- principal `A ⊃ B` in `Γ₂`: interpolants combine with `∧`
        obtain ⟨I₁, s₁, t₁, a₁, b₁⟩ := ih₁ Γ₁ Γ₂ H
        obtain ⟨I₂, s₂, t₂, a₂, b₂⟩ := ih₂ Γ₁ (B :: Γ₂) (split_cons_right H)
        have hA : A.atoms ⊆ atomsList Γ₂ :=
          sub_trans atoms_imp_left (atoms_subset_atomsList h₂)
        have hB : B.atoms ⊆ atomsList Γ₂ :=
          sub_trans atoms_imp_right (atoms_subset_atomsList h₂)
        refine ⟨I₁.and I₂, SC.andR s₁ s₂, ?_, ?_, ?_⟩
        · refine SC.andL (.head _) ?_
          refine SC.impL (.tail _ (.tail _ (.tail _ h₂))) ?_ ?_
          · exact t₁.rename (by
              intro ψ hψ
              rcases List.mem_cons.mp hψ with rfl | h
              · exact .head _
              · exact .tail _ (.tail _ (.tail _ h)))
          · exact t₂.rename (by
              intro ψ hψ
              rcases List.mem_cons.mp hψ with rfl | h
              · exact .tail _ (.tail _ (.head _))
              · rcases List.mem_cons.mp h with rfl | h
                · exact .head _
                · exact .tail _ (.tail _ (.tail _ (.tail _ h))))
        · exact atoms_and_sub a₁ a₂
        · exact atoms_and_sub
            (sub_trans
              (sub_trans b₁ (finUnion_sub (fun _ hx => hx) hA))
              sub_finUnion_left)
            (sub_union_left_mono b₂ (atomsList_cons_subset hB))
  | @laxR n Γ A d ih =>
      intro Γ₁ Γ₂ H
      obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ Γ₂ H
      exact ⟨I, s, SC.laxR t, a₁, sub_union_right_mono a₂ atoms_lax⟩
  | @laxL n Γ A B h d ih =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · -- principal `◯A` in `Γ₁`: **box** the premise interpolant.
        -- A bare pass-through fails: `Γ₁ ⊢ I` would need `◯L` on
        -- `◯A ∈ Γ₁`, which fires only at a `◯`-shaped succedent.
        obtain ⟨I, s, t, a₁, a₂⟩ := ih (A :: Γ₁) Γ₂ (split_cons_left H)
        have hA : A.atoms ⊆ atomsList Γ₁ :=
          sub_trans atoms_lax (atoms_subset_atomsList h₁)
        refine ⟨I.somehow, SC.laxL h₁ (SC.laxR s), ?_, ?_, ?_⟩
        · refine SC.laxL (.head _) ?_
          exact t.rename (by
            intro ψ hψ
            rcases List.mem_cons.mp hψ with rfl | h
            · exact .head _
            · exact .tail _ (.tail _ h))
        · exact sub_trans a₁ (atomsList_cons_subset hA)
        · exact a₂
      · -- principal `◯A` in `Γ₂`: pass through
        obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ (A :: Γ₂) (split_cons_right H)
        have hA : A.atoms ⊆ atomsList Γ₂ :=
          sub_trans atoms_lax (atoms_subset_atomsList h₂)
        refine ⟨I, s, ?_, a₁, sub_union_left_mono a₂ (atomsList_cons_subset hA)⟩
        refine SC.laxL (.tail _ h₂) ?_
        exact t.rename (by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | h
          · exact .tail _ (.head _)
          · rcases List.mem_cons.mp h with rfl | h
            · exact .head _
            · exact .tail _ (.tail _ h))

/-! ### Packaged statements — choice-free (primed) forms -/

/-- **Maehara interpolation** for `SC`, choice-free form: every
permutation-splitting of the context of a derivable sequent has an
interpolant over the shared atoms, the sharing stated as two subset
facts through the choice-free `finUnion`. -/
theorem SC.maehara' {Γ : List PLLFormula} {C : PLLFormula} :
    SC Γ C → ∀ Γ₁ Γ₂ : List PLLFormula, Γ.Perm (Γ₁ ++ Γ₂) →
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∧ I.atoms ⊆ finUnion (atomsList Γ₂) C.atoms := by
  rintro ⟨n, d⟩ Γ₁ Γ₂ hp
  exact d.maehara Γ₁ Γ₂ (fun ψ hψ => List.mem_append.mp (hp.subset hψ))

/-- **Craig interpolation for PLL**, sequent form, choice-free: if
`Γ₁ ++ Γ₂ ⊢ C` is derivable then some interpolant `I` has `Γ₁ ⊢ I`,
`I, Γ₂ ⊢ C`, and atoms in `Γ₁`'s and in `Γ₂, C`'s. -/
theorem craig_interpolation' {Γ₁ Γ₂ : List PLLFormula} {C : PLLFormula}
    (h : SC (Γ₁ ++ Γ₂) C) :
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∧ I.atoms ⊆ finUnion (atomsList Γ₂) C.atoms :=
  h.maehara' Γ₁ Γ₂ (List.Perm.refl _)

/-- **Craig interpolation for PLL**, implication form, choice-free: if
`⊢ A ⊃ B` then there is an interpolant `I` over the common atoms of `A`
and `B` with `⊢ A ⊃ I` and `⊢ I ⊃ B`. -/
theorem craig_implication' {A B : PLLFormula} (h : SC [] (A.ifThen B)) :
    ∃ I : PLLFormula,
      SC [] (A.ifThen I) ∧ SC [] (I.ifThen B) ∧
      I.atoms ⊆ A.atoms ∧ I.atoms ⊆ B.atoms := by
  have h' : SC [A] (A.ifThen B) := h.rename (by intro ψ hψ; cases hψ)
  have hAB : SC [A] B :=
    SC.cut h' (SC.impL (.head _)
      (SC.iden A (.tail _ (.head _))) (SC.iden B (.head _)))
  obtain ⟨I, s, t, a₁, a₂⟩ := hAB.maehara' [A] [] (List.Perm.refl _)
  refine ⟨I, SC.impR s, SC.impR t, ?_, ?_⟩
  · exact fun x hx => (mem_finUnion.mp (a₁ hx)).elim id
      (fun h'' => absurd h'' (Finset.notMem_empty x))
  · exact fun x hx => (mem_finUnion.mp (a₂ hx)).elim
      (fun h'' => absurd h'' (Finset.notMem_empty x)) id

/-! ### Packaged statements — Mathlib `∪`/`∩` (unprimed) wrappers

The statements below mention `Finset.union`/`Finset.inter`, whose Mathlib
definitions embed `Classical.choice`; they therefore audit `clean`
*by statement vocabulary alone* (the ‡ pattern of the ledger), and each
is a two-line consequence of its choice-free primed twin above. -/

/-- **Maehara interpolation** for `SC`: every permutation-splitting of the
context of a derivable sequent has an interpolant over the shared atoms. -/
theorem SC.maehara {Γ : List PLLFormula} {C : PLLFormula} :
    SC Γ C → ∀ Γ₁ Γ₂ : List PLLFormula, Γ.Perm (Γ₁ ++ Γ₂) →
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∩ (atomsList Γ₂ ∪ C.atoms) := by
  intro h Γ₁ Γ₂ hp
  obtain ⟨I, s, t, a₁, a₂⟩ := h.maehara' Γ₁ Γ₂ hp
  exact ⟨I, s, t, Finset.subset_inter a₁
    (fun x hx => Finset.mem_union.mpr (mem_finUnion.mp (a₂ hx)))⟩

/-- **Craig interpolation for PLL**, sequent form: if `Γ₁ ++ Γ₂ ⊢ C` is
derivable then some interpolant `I` has `Γ₁ ⊢ I`, `I, Γ₂ ⊢ C`, and atoms
occurring both in `Γ₁` and in `Γ₂, C`. -/
theorem craig_interpolation {Γ₁ Γ₂ : List PLLFormula} {C : PLLFormula}
    (h : SC (Γ₁ ++ Γ₂) C) :
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∩ (atomsList Γ₂ ∪ C.atoms) :=
  h.maehara Γ₁ Γ₂ (List.Perm.refl _)

/-- **Craig interpolation for PLL**, implication form: if `⊢ A ⊃ B` then
there is an interpolant `I` over the common atoms of `A` and `B` with
`⊢ A ⊃ I` and `⊢ I ⊃ B`. -/
theorem craig_implication {A B : PLLFormula} (h : SC [] (A.ifThen B)) :
    ∃ I : PLLFormula,
      SC [] (A.ifThen I) ∧ SC [] (I.ifThen B) ∧
      I.atoms ⊆ A.atoms ∩ B.atoms := by
  obtain ⟨I, s, t, a₁, a₂⟩ := craig_implication' h
  exact ⟨I, s, t, Finset.subset_inter a₁ a₂⟩

/-! ### Axiom audit — the primed chain is choice-free; the unprimed
wrappers are `clean` by statement vocabulary alone (‡) -/

/-- info: 'PLLND.SCh.maehara' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SCh.maehara

/-- info: 'PLLND.SC.maehara'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SC.maehara'

/-- info: 'PLLND.craig_interpolation'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms craig_interpolation'

/-- info: 'PLLND.craig_implication'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms craig_implication'

/--
info: 'PLLND.SC.maehara' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SC.maehara

/--
info: 'PLLND.craig_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms craig_interpolation

/--
info: 'PLLND.craig_implication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms craig_implication

end PLLND
