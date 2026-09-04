import wip.rnClassify
import LaxLogic.PLLFiniteModel

/-!
# The substituted odd-rung chain has NO non-trivial upper bound

The question: is there a formula `φ` with

* (A) `Deriv [rnSub (2*k+1)] φ` for every `k`, and
* (B) `¬ Deriv [] φ`?

Answer: **no** — for `φ` of any shape whatever (one variable or not,
`◯`-free or not).  Two ingredients:

1. `rank_bound` — in a FINITE constraint model every world forces some
   substituted odd rung.  The bound is `rnSub (2*(2*n)+1)` where `n`
   bounds the size of the world's `Rᵢ`-up-set: a world whose strict
   up-set is already covered by `rnSub (2*K+1)` either forces
   `rnSub (2*K+3)` or (failing that, VACUOUSLY at the world's own
   cluster) forces `rnSub (2*K+4) = rnSub (2*K+3) ⊃ rnSub (2*K+1)`,
   hence in both cases `rnSub (2*K+5)`.  No `◯`-reasoning at all is
   used: the argument runs entirely in the `∨`/`⊃` recursion of the
   ladder, with `◯⊥` as an opaque `Rᵢ`-hereditary atom.

2. `finite_model_property` (already in `LaxLogic/PLLFiniteModel.lean`):
   `Nonempty (LaxND [] φ)` iff `φ` is forced at every world of every
   finite constraint model.

So (A) makes `φ` valid on every finite model, and the FMP turns that
into `Deriv [] φ` — (B) fails.  `chain_bound_is_theorem`.
-/

open PLLFormula
open scoped Classical

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 1. The rung rank of a world in a finite model -/

section Rank

variable (C : ConstraintModel)

/-- The `Rᵢ`-up-set of `w`, as a `Finset` of a finite model. -/
noncomputable def upF [Fintype C.W] (w : C.W) : Finset C.W :=
  Finset.univ.filter (fun v => C.Ri w v)

variable {C}

theorem mem_upF [Fintype C.W] {w v : C.W} : v ∈ upF C w ↔ C.Ri w v := by
  simp [upF]

theorem self_mem_upF [Fintype C.W] (w : C.W) : w ∈ upF C w :=
  mem_upF.mpr (C.refl_i w)

theorem upF_subset [Fintype C.W] {w v : C.W} (h : C.Ri w v) :
    upF C v ⊆ upF C w := fun _ hu => mem_upF.mpr (C.trans_i h (mem_upF.mp hu))

/-- **The rank bound.**  If the `Rᵢ`-up-set of `w` has at most `n`
elements then `w` forces the `2*(2*n)+1`-st substituted rung. -/
theorem rank_bound [Fintype C.W] :
    ∀ (n : Nat) (w : C.W), (upF C w).card ≤ n →
      C.force w (rnSub (2 * (2 * n) + 1)) := by
  intro n
  induction n with
  | zero =>
      intro w hw
      have hpos : 0 < (upF C w).card :=
        Finset.card_pos.mpr ⟨w, self_mem_upF w⟩
      omega
  | succ n ih =>
      intro w hw
      -- `K = 2*n`: every STRICTLY higher world forces `rnSub (2*K+1)`.
      have hstrict : ∀ v : C.W, upF C v ⊂ upF C w →
          C.force v (rnSub (2 * (2 * n) + 1)) := by
        intro v hlt
        have hcard : (upF C v).card < (upF C w).card := Finset.card_lt_card hlt
        exact ih v (by omega)
      have hidx : 2 * (2 * (n + 1)) + 1 = 2 * (2 * n + 1) + 3 := by omega
      rw [hidx, rnSub_odd_eq (2 * n + 1)]
      by_cases hc : C.force w (rnSub (2 * (2 * n + 1) + 1))
      · exact Or.inl hc
      · refine Or.inr ?_
        rw [rnSub_even_eq (2 * n + 1)]
        intro v hv hA
        -- `v` above `w` forcing `rnSub (2*K+3)`: either strictly higher
        -- (use the IH) or in `w`'s own cluster (contradicts `hc`).
        by_cases hlt : upF C v ⊂ upF C w
        · have hb : 2 * (2 * n + 1) - 1 = 2 * (2 * n) + 1 := by omega
          rw [hb]
          exact hstrict v hlt
        · exfalso
          have hsub : upF C v ⊆ upF C w := upF_subset hv
          have heq : upF C v = upF C w :=
            Finset.Subset.antisymm hsub
              (by
                by_contra hns
                exact hlt ⟨hsub, fun h => hns h⟩)
          have hwv : C.Ri v w := by
            have : w ∈ upF C v := by rw [heq]; exact self_mem_upF w
            exact mem_upF.mp this
          exact hc (C.force_hered hwv hA)

end Rank

/-- **Every world of a finite constraint model forces some substituted
odd rung.**  (The rung index is bounded by the size of the model.) -/
theorem exists_rung_of_finite (C : ConstraintModel) (hfin : Finite C.W)
    (w : C.W) : ∃ k, C.force w (rnSub (2 * k + 1)) := by
  haveI := hfin
  haveI : Fintype C.W := Fintype.ofFinite C.W
  exact ⟨2 * Fintype.card C.W, rank_bound _ w (Finset.card_le_univ _)⟩

/-! ## 2. The verdict -/

/-- **No non-trivial upper bound**: any `φ` entailed by every
substituted odd rung is a PLL theorem.  Hence there is NO `φ` with
(A) `∀ k, Deriv [rnSub (2*k+1)] φ` and (B) `¬ Deriv [] φ` — with or
without the variable `p`, with or without `◯`. -/
theorem chain_bound_is_theorem {φ : PLLFormula}
    (hA : ∀ k, Deriv [rnSub (2 * k + 1)] φ) : Deriv [] φ := by
  refine finite_model_property.mpr ?_
  intro C hfin w
  obtain ⟨k, hk⟩ := exists_rung_of_finite C hfin w
  obtain ⟨d⟩ := hA k
  refine soundness d C w ?_
  intro ψ hψ
  have he : ψ = rnSub (2 * k + 1) := by simpa using hψ
  subst he
  exact hk

/-- Contrapositive, in the exact shape of the question. -/
theorem no_witness (φ : PLLFormula) :
    ¬ ((∀ k, Deriv [rnSub (2 * k + 1)] φ) ∧ ¬ Deriv [] φ) := by
  rintro ⟨hA, hB⟩
  exact hB (chain_bound_is_theorem hA)

/-! ## 3. Where a candidate must die: the even-rung split

`(A)` is equivalent to "every EVEN rung entails `φ`", because the odd
rungs are the partial joins of the even ones. -/

theorem odd_split (a : Nat) (φ : PLLFormula) :
    Deriv [rnSub (2 * a + 3)] φ ↔
      (Deriv [rnSub (2 * a + 1)] φ ∧ Deriv [rnSub (2 * a + 2)] φ) := by
  rw [rnSub_odd_eq a]
  constructor
  · intro h
    exact ⟨Deriv.cutHead (Deriv.orIntro1 (Deriv.iden (by simp))) h,
           Deriv.cutHead (Deriv.orIntro2 (Deriv.iden (by simp))) h⟩
  · rintro ⟨h1, h2⟩
    exact Deriv.orElim (Deriv.iden (by simp)) h1.toHead h2.toHead

/-! ## 4. The `∀`-side of the UI attack collapses too

`chainF k = ◯(rnSub (2*k+1))` sits ABOVE the `k`-th odd rung, so a
bound of the c-chain is a bound of the rung chain — and the schema
`no_pre_interp_schema` of `wip/uiObstruct.lean` therefore has
contradictory hypotheses. -/

/-- Any `φ` above the whole c-chain is a theorem. -/
theorem c_chain_bound_is_theorem {φ : PLLFormula}
    (hc : ∀ k, Deriv [chainF k] φ) : Deriv [] φ :=
  chain_bound_is_theorem fun k =>
    Deriv.cutHead (dSomehowIntro (Deriv.iden (.head _))) (hc k)

/-- `⊤ = ⊥ ⊃ ⊥` is variable-free and above everything. -/
theorem top_atomFree : atomFree (PLLFormula.falsePLL.ifThen .falsePLL) = true := rfl

/-- **The `∀`-side obstruction schema is VACUOUS**: its two hypotheses
cannot both hold.  (`hU` at `χ = ⊤` demands `⊬ φ`, while `hc` forces
`⊢ φ`.) -/
theorem pre_interp_schema_vacuous {φ : PLLFormula}
    (hc : ∀ k, Deriv [chainF k] φ)
    (hU : ∀ χ, atomFree χ = true → (∀ k, Deriv [chainF k] χ) →
      ¬ Deriv [χ] φ) : False := by
  have hthm : Deriv [] φ := c_chain_bound_is_theorem hc
  refine hU (PLLFormula.falsePLL.ifThen .falsePLL) top_atomFree
    (fun _ => Deriv.impIntro (Deriv.iden (.head _))) ?_
  exact hthm.rename (by simp)

/-! ## Axiom hygiene — sorry-free (the FMP itself is transitively clean) -/

/-- info: 'PLLND.RNEmbed.rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_bound

/-- info: 'PLLND.RNEmbed.chain_bound_is_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_bound_is_theorem

/-- info: 'PLLND.RNEmbed.no_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_witness

/-- info: 'PLLND.RNEmbed.odd_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms odd_split

/-- info: 'PLLND.RNEmbed.c_chain_bound_is_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c_chain_bound_is_theorem

/-- info: 'PLLND.RNEmbed.pre_interp_schema_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre_interp_schema_vacuous

/-! ## 5. Corroboration: the rank bound, computed

The five-world truncation of the lift (ladder worlds `0..4`, fallible
top `5`, `Rₘ` sending only world `0` to the top) — every world forces
some odd rung, with rank exactly the world index, as `rank_bound`
predicts. -/

/-- The 5-rung truncation of `ladder.cm`, as a `FinCM`. -/
def ladderFin : FinCM :=
  ⟨6,
   -- Rᵢ: `w` sees every `v` with `v + 2 ≤ w`, and everything sees the top `5`
   [(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),
    (0,5),(1,5),(2,5),(3,5),(4,5)],
   -- Rₘ: only world 0 escapes to the fallible top
   [(0,5)],
   [5], []⟩

/-- Rank = world index: world `w` forces `rnSub (2w+1)` and no earlier
odd rung.  (Kernel-checked.) -/
example : (List.range 5).all (fun w =>
      FinCM.forceB ladderFin w (rnSub (2 * w + 1)) &&
      (decide (w = 0) || !FinCM.forceB ladderFin w (rnSub (2 * (w - 1) + 1))))
    = true := by decide

end RNEmbed
end PLLND
