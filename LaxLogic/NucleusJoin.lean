import Mathlib

/-!
# The join of two commuting nuclei is their composite

Two nuclei `j`, `k` on a meet-semilattice — read doxastically as two belief
operators `◯₁`, `◯₂` (`Mathlib`'s `Nucleus`, as in `BeliefCollapse`) — have a
least upper bound in the lattice of nuclei whenever it exists: the **join**
`◯₁ ⊔ ◯₂`, the *pooled* belief. The join is not computed pointwise (the
pointwise supremum fails idempotence) and in general is a transfinite closure
of the alternating tower `jkjk…`. This file records the classical fact that
**when the two commute the join terminates in one step**: if `j ∘ k = k ∘ j`
then the composite `k ∘ j` is already a nucleus and is the join.

* `compNucleus` — the composite of two commuting nuclei, as a nucleus;
* `isLUB_comp_of_comm` — it is the least upper bound of the two (over any
  meet-semilattice; no completeness assumed);
* `sup_eq_comp_of_comm` / `sup_apply_of_comm` — hence on a complete lattice
  `j ⊔ k = k ∘ j`, pointwise `(j ⊔ k) x = k (j x)`.

Doxastic reading: two believers need not share their beliefs (`j ≠ k`);
their consensus is the meet `j ⊓ k` (believe `x` iff both do, computed
pointwise) and their pooled belief is the join; commutation
`◯₁◯₂ ≡ ◯₂◯₁` — mutual transparency about what each believes the other
believes — is exactly the condition that makes pooling a finite two-step
operation.

We also record the boundary in the other direction (`eq_of_transparent_comm`):
if the two are *mutually transparent* (`◯₁◯₂M ⊃ ◯₂M` and `◯₂◯₁M ⊃ ◯₁M`) **and**
commute, then they coincide as operators.
-/

namespace BeliefLax

section SemilatticeInf
variable {X : Type*} [SemilatticeInf X]

/-- The composite `k ∘ j` of two nuclei is a nucleus **when they commute**. -/
def compNucleus (j k : Nucleus X) (h : ∀ x, j (k x) = k (j x)) : Nucleus X where
  toFun x := k (j x)
  map_inf' x y := by rw [j.map_inf, k.map_inf]
  le_apply' x := le_trans j.le_apply k.le_apply
  idempotent' x := by
    have e : k (j (k (j x))) = k (j x) := by
      rw [h (j x), j.idempotent, k.idempotent]
    exact e.le

@[simp] lemma compNucleus_apply (j k : Nucleus X) (h : ∀ x, j (k x) = k (j x))
    (x : X) : compNucleus j k h x = k (j x) := rfl

/-- **Commuting nuclei: the join is the composite.** For nuclei `j`, `k` with
`j ∘ k = k ∘ j`, the composite `k ∘ j` is the least upper bound of `j` and `k`
in the lattice of nuclei — so their join terminates in one step. -/
theorem isLUB_comp_of_comm (j k : Nucleus X) (h : ∀ x, j (k x) = k (j x)) :
    IsLUB {j, k} (compNucleus j k h) := by
  have hjc : j ≤ compNucleus j k h := fun x => k.le_apply
  have hkc : k ≤ compNucleus j k h := fun x => OrderHomClass.mono k j.le_apply
  constructor
  · intro n hn
    rcases Set.mem_insert_iff.mp hn with h1 | h1
    · rw [h1]; exact hjc
    · rw [Set.mem_singleton_iff.mp h1]; exact hkc
  · intro m hm
    have hj : j ≤ m := mem_upperBounds.mp hm j (by simp)
    have hk : k ≤ m := mem_upperBounds.mp hm k (by simp)
    intro x
    calc k (j x) ≤ m (j x) := hk (j x)
      _ ≤ m (m x) := OrderHomClass.mono m (hj x)
      _ = m x := m.idempotent x

/-- **Mutual transparency plus commutation forces identity.** If each believer
sees through the other's beliefs — `j (k x) ≤ k x` and `k (j x) ≤ j x` — and
the two commute, then `j = k`. (The transparency inequalities are the
nontrivial halves; the reverse inequalities are inflationarity.) -/
theorem eq_of_transparent_comm (j k : Nucleus X)
    (hjk : ∀ x, j (k x) ≤ k x) (hkj : ∀ x, k (j x) ≤ j x)
    (hc : ∀ x, j (k x) = k (j x)) : j = k := by
  ext x
  have e1 : j (k x) = k x := le_antisymm (hjk x) j.le_apply
  have e2 : k (j x) = j x := le_antisymm (hkj x) k.le_apply
  have hkj' : k x = j x := by rw [← e1, hc x, e2]
  exact hkj'.symm

end SemilatticeInf

section CompleteLattice
variable {X : Type*} [CompleteLattice X]

/-- The lattice join of two commuting nuclei is their composite. -/
theorem sup_eq_comp_of_comm (j k : Nucleus X) (h : ∀ x, j (k x) = k (j x)) :
    j ⊔ k = compNucleus j k h :=
  isLUB_pair.unique (isLUB_comp_of_comm j k h)

/-- The join of two commuting nuclei, pointwise: `(j ⊔ k) x = k (j x)`. -/
theorem sup_apply_of_comm (j k : Nucleus X) (h : ∀ x, j (k x) = k (j x)) (x : X) :
    (j ⊔ k) x = k (j x) := by rw [sup_eq_comp_of_comm j k h, compNucleus_apply]

end CompleteLattice

/-! ### Axiom audit — measured and pinned on creation (2026-07-20) -/

/-- info: 'BeliefLax.compNucleus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compNucleus

/--
info: 'BeliefLax.isLUB_comp_of_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isLUB_comp_of_comm

/--
info: 'BeliefLax.eq_of_transparent_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eq_of_transparent_comm

/--
info: 'BeliefLax.sup_eq_comp_of_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sup_eq_comp_of_comm

end BeliefLax
