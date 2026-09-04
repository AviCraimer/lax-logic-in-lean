import Mathlib

/-!
# The idealised believer: introspection and closure under consequence

Reading `◯M` as "M is believed", a believer is a nucleus `j`.  This file records
the two idealisations the belief reading builds in — following Hintikka's stance
that epistemic and doxastic modalities describe an *ideal*, logically competent
agent, not a real one (J. Hintikka, *Knowledge and Belief: An Introduction to the
Logic of the Two Notions*, Cornell Univ. Press, 1962).

Only the meet-semilattice-with-top structure of the belief operator is used — no
Heyting implication — so both facts hold for any nucleus on `[SemilatticeInf]
[OrderTop]`.

## The self-aware believer — full introspection

    ◯◯M ⊣⊢ ◯M          (`belief_introspection`; `◯M ⊢ ◯◯M` is the unit)

Believing-that-you-believe coincides with believing: the believer has perfect
access to its own belief state.  (Object-logic counterparts in the codebase:
`somehowR`/unit and `somehowM`/multiplication in `PLLTheorems.lean`, `joinTm`
in `PLLConstraints.lean`.)

## The consequence-closed believer — logical omniscience

    Γ ⊢ M   ⟹   ◯Γ ⊢ ◯M          (`belief_consequence`; `◯Γ` pointwise)

This is exactly Hintikka's *logical omniscience* (SEP, *Epistemic Logic*: "an
agent knows all logical consequences of what it knows").  A nucleus preserves
finite meets, so `⋀◯Γ = ◯(⋀Γ)` (`nucleus_listInf`), and monotonicity carries
`⋀Γ ≤ M` to `◯(⋀Γ) ≤ ◯M`.  The empty-context case is *necessitation*
`⊢M ⟹ ⊢◯M` (`belief_necessitation`): the believer believes every theorem.
Here `Γ ⊢ M` is read algebraically as `⋀Γ ≤ M`; via PLL's mechanised
soundness/completeness this is PLL-provability.
-/

namespace BeliefLax

variable {H : Type*} [SemilatticeInf H] [OrderTop H] (j : Nucleus H)

omit [OrderTop H] in
/-- **Full introspection** (the self-aware believer): `◯◯M ⊣⊢ ◯M`.  The `⊢`
direction is multiplication `j (j m) ≤ j m`; the `⊣` direction is the unit
`j m ≤ j (j m)`. -/
theorem belief_introspection (m : H) : j (j m) = j m := j.idempotent m

/-- `◯` preserves the meet of a list pointwise: `⋀ ◯Γ = ◯(⋀ Γ)`. -/
theorem nucleus_listInf (Γ : List H) :
    (Γ.map (j ·)).foldr (· ⊓ ·) ⊤ = j (Γ.foldr (· ⊓ ·) ⊤) := by
  induction Γ with
  | nil => simp only [List.map_nil, List.foldr_nil]; exact (le_antisymm le_top j.le_apply).symm
  | cons a t ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih, ← j.map_inf]

/-- **Closure under logical consequence** (Hintikka's logical omniscience): if
`Γ ⊢ M` then `◯Γ ⊢ ◯M`, with `◯Γ` the pointwise `{◯A : A ∈ Γ}` and `Γ ⊢ M`
read as `⋀Γ ≤ M`. -/
theorem belief_consequence (Γ : List H) (m : H)
    (h : Γ.foldr (· ⊓ ·) ⊤ ≤ m) : (Γ.map (j ·)).foldr (· ⊓ ·) ⊤ ≤ j m := by
  rw [nucleus_listInf j]
  exact j.monotone h

/-- **Necessitation** (empty context): if `⊢M` (i.e. `⊤ ≤ M`) then `⊢◯M`. -/
theorem belief_necessitation (m : H) (h : (⊤ : H) ≤ m) : (⊤ : H) ≤ j m :=
  calc (⊤ : H) = j ⊤ := (le_antisymm le_top j.le_apply).symm
    _ ≤ j m := j.monotone h

end BeliefLax

#print axioms BeliefLax.belief_introspection
#print axioms BeliefLax.nucleus_listInf
#print axioms BeliefLax.belief_consequence
#print axioms BeliefLax.belief_necessitation
