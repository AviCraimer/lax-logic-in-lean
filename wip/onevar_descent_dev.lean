import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4HCut
import LaxLogic.PLLG4HComp
import LaxLogic.PLLG4Dec

/-!
# Development: the one-variable budget DESCENT — reduced state

Target (syntactic; `descent_forcing` in wip/onevar.lean follows by
soundness):  past the threshold, with all atoms in {p},

    G4c [itpA p S fuel (b+1) Γ C] (itpA p S fuel b Γ C)

STRUCTURE OF THE REDUCTION (all compiled, holes marked):

* ∃-side descent `[itpE (b+1)] ⊢ itpE b` — FREE, it is `itp_budget_mono.1`.
* itpA base case (`itpA 0 = ⊥`) — closed.
* itpA successor — reduced to the library combinator `itpAfull_map`, whose
  two obligations are exactly the two open pieces:
    (H1) `hoth`  — member-wise map of the non-truncation disjuncts,
         the ~mechanical mirror of `itp_budget_mono`'s clause walk
         (threshold bookkeeping needed at the jump clauses; the same-Γ
         jumps need the seen-set-refined threshold as in absorb_base).
    (H2) `itpE_stab` — the DISTILLED CORE: the ∃-ascent at threshold
         (∃-side stabilisation), which feeds the ◯-goal truncation
         disjunct through `itpAfull_map`'s guard obligation `htr`.
         Note `itp_budget_mono.1` gives the reverse direction free, so
         H2 states an EQUIVALENCE `itpE b ≡ itpE (b+1)` past threshold.

The deep-probe experiment (wip/slick_probe.lean) tests H2 computationally
past the threshold on the climbing configuration X9.
-/

open PLLFormula
namespace PLLND
namespace OnevarDev

/-- Jump goals (copied from wip/absorb_base.lean:37, not imported to keep
the wip olean chain out of this file's dependencies). -/
def jGoals (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

/-- **(H2) The distilled core — ∃-side stabilisation at threshold.**
The library gives `[itpE (b+1)] ⊢ itpE b` unconditionally
(`itp_budget_mono.1`); this is the converse past the threshold.
The pair convention: input budget `b` with `threshold ≤ b + 1`, so it can
be instantiated at the (b-1, b) pair from a `threshold ≤ b` hypothesis.

STRUCTURE (one-step unfolding of the (b+1)-conjunct table): the budget
appears only in the gated conjuncts, whose guards sit in NEGATIVE position.
Conjunct-wise, H2 at (Γ, b) needs
  * H2 at (Γ, b-1)           — same-context budget regress (!),
  * the itpA-DESCENT at (Γ, b-1)  — mutual with `itpA_descent`,
  * H2 at (D::Γ, b) for D ∈ S \ Γ — defect drops, threshold renews (safe).
The same-context regress is the genuine combinatorial content: each step
consumes one gated clause instance, and the number of distinct gated
clauses at a fixed Γ is bounded by `(jGoals S).card` — the seen-set
refinement of wip/absorb_base's cascade.  The one-variable hypothesis must
enter HERE: the gated conjuncts' values must collapse (◯◯ ≡ ◯ on the
closed fragment) before the J+2 slack per defect level is exhausted.
The deep probe (wip/slick_probe.lean) tests exactly this on X9: whether
the itpE/itpA equivalence classes freeze by the threshold b = 16. -/
theorem itpE_stab (p : String) (S : Finset PLLFormula)
    (fuel b : Nat) (Γ : List PLLFormula)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jGoals S).card + 2) ≤ b + 1)
    (hSv : ∀ F ∈ S, F.atoms ⊆ {p})
    (hΓv : ∀ F ∈ Γ, F.atoms ⊆ {p}) :
    G4c [itpE p S fuel b Γ] (itpE p S fuel (b + 1) Γ) := by
  sorry

/-- **The one-variable budget descent**, reduced to (H1) + (H2). -/
theorem itpA_descent (p : String) (S : Finset PLLFormula) : ∀ (fuel : Nat)
    (b : Nat) (Γ : List PLLFormula) (C : PLLFormula),
    1 ≤ defect S Γ →
    defect S Γ * ((jGoals S).card + 2) ≤ b →
    (∀ F ∈ S, F.atoms ⊆ {p}) → (∀ F ∈ Γ, F.atoms ⊆ {p}) → C.atoms ⊆ {p} →
    G4c [itpA p S fuel (b + 1) Γ C] (itpA p S fuel b Γ C) := by
  intro fuel
  induction fuel with
  | zero =>
      intro b Γ C _ _ _ _ _
      simp only [itpA]
      exact G4c.botL (.head _)                       -- itpA 0 = ⊥, both budgets
  | succ fuel ih =>
      intro b Γ C hd1 hroom hSv hΓv hCv
      rw [itpA_succ, itpA_succ]
      -- the threshold forces b ≥ 2 (defect ≥ 1, slack ≥ 2)
      have hb2 : 2 ≤ b := by
        have h2 : 1 * 2 ≤ defect S Γ * ((jGoals S).card + 2) :=
          Nat.mul_le_mul hd1 (by omega)
        omega
      -- (H2 feed) the ◯-goal truncation guard: high side b+1 = b₁'+1 forces
      -- b₁' = b; the low side takes b₂' = b-1; the guard obligation is the
      -- ∃-ascent [itpE (b-1)] ⊢ itpE b, i.e. itpE_stab at the (b-1, b) pair.
      have htr : ∀ b₁', b + 1 = b₁' + 1 → ∃ b₂', b = b₂' + 1 ∧
          G4c [itpE p S fuel b₂' Γ] (itpE p S fuel b₁' Γ) := by
        intro b₁' hb₁
        have hb : b₁' = b := by omega
        rw [hb]
        refine ⟨b - 1, by omega, ?_⟩
        have h := itpE_stab p S fuel (b - 1) Γ hd1 (by omega) hSv hΓv
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ b)] at h
      -- (H1) the mechanical bulk: each ordinary disjunct of the (b+1)-table
      -- maps into the b-table.  Mirrors itp_budget_mono's clause walk with
      -- `ih` at the recursive positions; the jump clauses additionally need
      -- the threshold rethreaded (same-Γ jumps: seen-set refinement TBD).
      have hoth : ∀ φ ∈ itpAoth p S fuel (b + 1) Γ C,
          ∃ ψ ∈ itpAoth p S fuel b Γ C, G4c [φ] ψ := by
        sorry
      exact itpAfull_map hoth htr

end OnevarDev
end PLLND
