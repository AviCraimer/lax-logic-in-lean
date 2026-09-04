import LaxLogic.BeliefCollapse

/-!
# `N(B) ≅ B`: nuclei on a Boolean algebra are an order isomorphism with `B`

This mechanises the sharp form of the "classical belief is degenerate" result
(handover §2A / §3b-1, cf. `wip/belief_boolean_collapse.lean`). Reading `◯M`
as "M is believed", a believer is a **nucleus** `j` on the algebra of
propositions: an inflationary, idempotent, meet-preserving map. This is
`Mathlib`'s `Nucleus`.

The Boolean collapse (`nucleus_eq_sup_bot`) shows every nucleus `j` on a
Boolean algebra `B` is the closed nucleus at `a = j ⊥`, i.e. `j x = x ⊔ j ⊥`.
This file upgrades that to the sharp statement: the map `j ↦ j ⊥` is not just
injective-and-surjective but an **order isomorphism**

    N(B) ≃o B

between the (pointwise-ordered) poset of nuclei on `B` and `B` itself. So on a
Boolean algebra the entire lattice of possible "dogmatic believers" is just a
relabelling of `B`: nuclei carry no more structure than the algebra of
propositions they act on. (Contrast the constructive case, where `N(H)` is
generally a much richer frame than `H` — this is exactly the sense in which
classical belief is degenerate and constructive belief is evidential.)
-/

namespace BeliefLax

variable {B : Type*} [BooleanAlgebra B]

-- `closedNucleus`, `closedNucleus_apply` and the collapse `nucleus_eq_sup_bot`
-- are provided by `BeliefCollapse` (the shared base module).

/-- The underlying bijection `Nucleus B ≃ B` of `j ↦ j ⊥`, with inverse
`a ↦ closedNucleus a`. Built first, as its own `Equiv`, so that its
(non-trivial) `left_inv`/`right_inv` proofs are fully elaborated against
concrete types before we assemble the `OrderIso` around it. -/
def nucleusEquivBot : Nucleus B ≃ B where
  toFun j := j ⊥
  invFun a := closedNucleus a
  left_inv j := by
    apply Nucleus.ext
    intro x
    exact (nucleus_eq_sup_bot j x).symm
  right_inv a := by simp [closedNucleus_apply]

@[simp] lemma nucleusEquivBot_apply (j : Nucleus B) : nucleusEquivBot j = j ⊥ := rfl

@[simp] lemma nucleusEquivBot_symm_apply (a : B) :
    (nucleusEquivBot (B := B)).symm a = closedNucleus a := rfl

/-- **`N(B) ≅ B`.** On a Boolean algebra `B`, the map `j ↦ j ⊥` is an order
isomorphism from the poset of nuclei on `B` (ordered pointwise) to `B`.
Its inverse sends `a : B` to the closed nucleus `closedNucleus a`. -/
def nucleusOrderIsoBot : Nucleus B ≃o B where
  toEquiv := nucleusEquivBot
  map_rel_iff' := by
    intro j k
    constructor
    · intro h x
      calc j x = x ⊔ j ⊥ := nucleus_eq_sup_bot j x
        _ ≤ x ⊔ k ⊥ := sup_le_sup_left h x
        _ = k x := (nucleus_eq_sup_bot k x).symm
    · intro h
      exact h ⊥

@[simp] lemma nucleusOrderIsoBot_apply (j : Nucleus B) :
    nucleusOrderIsoBot j = j ⊥ := rfl

@[simp] lemma nucleusOrderIsoBot_symm_apply (a : B) :
    (nucleusOrderIsoBot (B := B)).symm a = closedNucleus a := rfl

end BeliefLax

#print axioms BeliefLax.closedNucleus
#print axioms BeliefLax.closedNucleus_apply
#print axioms BeliefLax.nucleus_eq_sup_bot
#print axioms BeliefLax.nucleusEquivBot
#print axioms BeliefLax.nucleusEquivBot_apply
#print axioms BeliefLax.nucleusEquivBot_symm_apply
#print axioms BeliefLax.nucleusOrderIsoBot
#print axioms BeliefLax.nucleusOrderIsoBot_apply
#print axioms BeliefLax.nucleusOrderIsoBot_symm_apply
