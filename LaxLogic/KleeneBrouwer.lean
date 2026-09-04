import Mathlib.Data.List.Basic

/-!
# The Kleene–Brouwer(–Kolmogorov) order is constructively well-founded

For a tree `T` of finite sequences over an alphabet with a relation
`lt`, the KB relation puts proper extensions *before* their prefixes
and otherwise compares by an `lt`-smaller letter at a common split.
Classically: if `T` has no infinite branch and `lt` is well-founded,
then `KB` is well-founded — proved by extracting an infinite branch
from an infinite `KB`-descent, a choice/limit argument.

**Constructively** the theorem splits in two, and the split is the
whole story:

* With the tree's well-foundedness *stated inductively* — every node
  accessible for the child relation, i.e. `Acc`, the bar-induction
  structure built into the hypothesis — the theorem has a completely
  elementary proof: a child-accessibility induction with a nested
  letter-accessibility induction, given below.  No choice, no bar
  induction, no fan theorem; also no linearity, no transitivity and no
  decidability of `lt` (so well-founded *preorder* alphabets — the
  Kolmogorov refinement — are covered by taking strict parts), and
  `KB` is taken in the generous any-common-split form, which contains
  the usual first-difference form, so well-foundedness transfers.

* From the *negative* formulation ("no infinite branch") the theorem
  is not provable in bare constructive logic: converting
  no-infinite-path well-foundedness into inductive well-foundedness is
  precisely (decidable) bar induction.  The extra principle lives
  entirely in that conversion, not in KB itself.

The axiom audit at the bottom certifies the first point mechanically:
the proofs use **no axioms at all** — not even `propext`.
-/

namespace KleeneBrouwer

variable {α : Type*} (lt : α → α → Prop) (T : List α → Prop)

/-- `v` branches `lt`-left of `u`: at some common position the letters
compare by `lt`.  (Any common split — no first-difference or linearity
assumptions.) -/
def DevLeft (v u : List α) : Prop :=
  ∃ (w : List α) (a b : α) (v' u' : List α),
    v = w ++ a :: v' ∧ u = w ++ b :: u' ∧ lt a b

/-- The Kleene–Brouwer relation on `T`: proper extensions first,
otherwise an `lt`-smaller letter at a common split. -/
def KB (s t : List α) : Prop :=
  T s ∧ T t ∧ ((t <+: s ∧ s ≠ t) ∨ DevLeft lt s t)

/-- One-step tree extension within `T`: `s` is a child of `t`. -/
def Child (s t : List α) : Prop :=
  T s ∧ ∃ a, s = t ++ [a]

/-! Two core list facts, re-proved by hand: the library versions carry
`propext` through their `simp`-based proofs, and this file certifies
axiom-freeness. -/

private theorem append_nil' : ∀ (l : List α), l ++ [] = l
  | [] => rfl
  | a :: l => congrArg (a :: ·) (append_nil' l)

private theorem append_assoc' : ∀ (l₁ l₂ l₃ : List α),
    (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃)
  | [], _, _ => rfl
  | a :: l₁, l₂, l₃ => congrArg (a :: ·) (append_assoc' l₁ l₂ l₃)

/-- The one list fact the proof needs, constructively: a split of
`u ++ [x]` as `w ++ b :: d` is either exactly at the end or strictly
inside `u`. -/
theorem cons_split {x b : α} : ∀ (w u : List α) {d : List α},
    u ++ [x] = w ++ b :: d →
    (w = u ∧ b = x ∧ d = []) ∨ ∃ u₃, u = w ++ b :: u₃ ∧ d = u₃ ++ [x] := by
  intro w
  induction w with
  | nil =>
      intro u d h
      cases u with
      | nil =>
          injection h with h1 h2
          exact .inl ⟨rfl, h1.symm, h2.symm⟩
      | cons e u₀ =>
          injection h with h1 h2
          subst h1
          exact .inr ⟨u₀, rfl, h2.symm⟩
  | cons f w₀ ih =>
      intro u d h
      cases u with
      | nil =>
          injection h with h1 h2
          cases w₀ with
          | nil => exact nomatch h2
          | cons _ _ => exact nomatch h2
      | cons e u₀ =>
          injection h with h1 h2
          subst h1
          rcases ih u₀ h2 with ⟨rfl, rfl, rfl⟩ | ⟨u₃, hu, hd⟩
          · exact .inl ⟨rfl, rfl, rfl⟩
          · exact .inr ⟨u₃, by rw [hu]; rfl, hd⟩

/-- **Main lemma.**  If the node `u` is accessible for the child
relation and everything branching `lt`-left of `u` is already
`KB`-accessible, then every `T`-extension of `u` (including `u`
itself) is `KB`-accessible.

Induction structure: outer, accessibility of `u` in the tree; inner,
accessibility in `lt` of the first letter `a` below `u` — the subtree
over `u ++ [a]` is handled by the outer hypothesis once its
left-deviants are split into those deviating inside `u` (given) and
those deviating at position `|u|` with an `lt`-smaller letter (inner
hypothesis). -/
theorem acc_kb_of_acc_child
    (hlt : WellFounded lt)
    (hpc : ∀ ⦃s t : List α⦄, T s → t <+: s → T t) :
    ∀ u : List α, Acc (Child T) u → T u →
    (∀ v, T v → DevLeft lt v u → Acc (KB lt T) v) →
    ∀ t, T t → u <+: t → Acc (KB lt T) t := by
  intro u haccu
  induction haccu with
  | intro u _ ihu =>
    intro hTu HL
    -- the subtree over each child `u ++ [a]`, by `lt`-accessibility of `a`
    have inner : ∀ a : α, Acc lt a → T (u ++ [a]) →
        ∀ t, T t → (u ++ [a]) <+: t → Acc (KB lt T) t := by
      intro a hacca
      induction hacca with
      | intro a _ iha =>
        intro hTa
        refine ihu (u ++ [a]) ⟨hTa, a, rfl⟩ hTa ?_
        -- classify the left-deviants of `u ++ [a]`
        rintro v hTv ⟨w, c, b, v', u₂, hveq, hueq, hcb⟩
        rcases cons_split w u hueq with ⟨rfl, rfl, rfl⟩ | ⟨u₃, hu, -⟩
        · -- deviation at position `|u|`: letter `c` with `lt c a`
          subst hveq
          exact iha c hcb (hpc hTv ⟨v', by rw [append_assoc']; rfl⟩)
            _ hTv ⟨v', by rw [append_assoc']; rfl⟩
        · -- deviation strictly inside `u`: covered by `HL`
          exact HL v hTv ⟨w, c, b, v', u₃, hveq, hu, hcb⟩
    -- now every `T`-extension of `u`
    intro t hTt hut
    obtain ⟨r, rfl⟩ := hut
    cases r with
    | nil =>
        rw [append_nil'] at hTt ⊢
        refine Acc.intro _ fun v hv => ?_
        obtain ⟨hTv, -, hcase⟩ := hv
        rcases hcase with ⟨⟨r', rfl⟩, hne⟩ | hdev
        · cases r' with
          | nil => exact absurd (append_nil' u) hne
          | cons c rest =>
              exact inner c (hlt.apply c)
                (hpc hTv ⟨rest, by rw [append_assoc']; rfl⟩)
                (u ++ c :: rest) hTv ⟨rest, by rw [append_assoc']; rfl⟩
        · exact HL v hTv hdev
    | cons c rest =>
        exact inner c (hlt.apply c)
          (hpc hTt ⟨rest, by rw [append_assoc']; rfl⟩)
          (u ++ c :: rest) hTt ⟨rest, by rw [append_assoc']; rfl⟩

/-- **The Kleene–Brouwer order on an inductively well-founded tree over
a well-founded alphabet is well-founded** — constructively. -/
theorem wellFounded_kb
    (hlt : WellFounded lt)
    (hpc : ∀ ⦃s t : List α⦄, T s → t <+: s → T t)
    (hacc : ∀ l, T l → Acc (Child T) l) :
    WellFounded (KB lt T) := by
  refine ⟨fun t => Acc.intro t fun v hv => ?_⟩
  have hTv : T v := hv.1
  have hnil : T [] := hpc hTv ⟨v, rfl⟩
  refine acc_kb_of_acc_child lt T hlt hpc [] (hacc [] hnil) hnil ?_
    v hTv ⟨v, rfl⟩
  rintro v' - ⟨w, a, b, v'', u', -, hueq, -⟩
  cases w with
  | nil => exact nomatch hueq
  | cons _ _ => exact nomatch hueq

/-- Packaged form: from well-foundedness of the child relation. -/
theorem wellFounded_kb'
    (hlt : WellFounded lt)
    (hpc : ∀ ⦃s t : List α⦄, T s → t <+: s → T t)
    (hacc : WellFounded (Child T)) :
    WellFounded (KB lt T) :=
  wellFounded_kb lt T hlt hpc fun l _ => hacc.apply l

/-! The audit: fully constructive — no `Classical.choice`, no
`propext`, no `Quot.sound`. -/

/-- info: 'KleeneBrouwer.wellFounded_kb' does not depend on any axioms -/
#guard_msgs in
#print axioms wellFounded_kb

end KleeneBrouwer
