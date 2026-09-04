import LaxLogic.PLLFormula

/-!
# A choice-free `Finset` toolkit

Mathlib's `Finset` layer is only partially constructive: the *type* and
the `insert`/`filter`/`card`/`⊆` layer are choice-free, but `List.toFinset`,
`Finset.union`, `Finset.image`, `Finset.product`, `Finset.powerset`,
`Finset.sdiff`, `Finset.toList` and `Finset.decidableEq` all carry
`Classical.choice` in their bodies (through `Multiset.dedup`'s
permutation-invariance lemma, or — for `toList` — `Quotient.out`
outright).  Any definition built on them, and any *statement* mentioning
them, audits `[propext, Classical.choice, Quot.sound]` however it is
proved.

This file rebuilds exactly the operations the decidability-and-
completeness chain needs, choice-free:

* `toFin` — `List α → Finset α` by a local deduplicator (`nubb`);
* `finDecEq` — decidable equality of finsets via double inclusion;
* `finUnion`, `finImage`, `finPairMap`, `finPow`, `finSdiff` — the set
  algebra, lifted from list operations by `Quotient.liftOn` with
  *extensionality* as the permutation-invariance proof (this is where
  Mathlib's versions lean on the tainted `Perm.dedup`);
* `exists_rep` — the `Prop`-level representative: every finset *has* a
  duplicate-free list enumerating it (`Quot.ind`, no choice — only the
  *canonical* choice of such a list would need `Classical.choice`);
* choice-free re-proofs of the few `insert`/`⊆` lemmas whose Mathlib
  proofs are tainted (`insert_subset`, `insert_subset_insert`,
  `singleton_subset_iff`, `coe_insert`).

Everything here audits `[propext, Quot.sound]` or less — see the guards
at the foot.  The bridge lemmas to Mathlib's own operations
(`toFin_eq_toFinset`) are collected at the very end and are the only
tainted statements in the file.
-/

namespace PLLND

variable {α β γ : Type _}

/-! ## `toFin`: lists to finsets, choice-free -/

/-- Deduplicate a list (keeping the last occurrence of each element).
`List.dedup` itself is clean, but its membership lemma `List.mem_dedup`
is not; a local deduplicator with local lemmas keeps the audit exact. -/
def nubb [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => let r := nubb l; if a ∈ r then r else a :: r

theorem mem_nubb [DecidableEq α] {l : List α} {a : α} :
    a ∈ nubb l ↔ a ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons b l ih =>
      show a ∈ (if b ∈ nubb l then nubb l else b :: nubb l) ↔ _
      by_cases hb : b ∈ nubb l
      · rw [if_pos hb, ih, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h)
          · exact ih.mp hb
          · exact h
      · rw [if_neg hb, List.mem_cons, List.mem_cons, ih]

theorem nodup_nubb [DecidableEq α] (l : List α) : (nubb l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons b l ih =>
      show (if b ∈ nubb l then nubb l else b :: nubb l).Nodup
      split
      · exact ih
      · exact List.nodup_cons.mpr ⟨by assumption, ih⟩

theorem length_nubb_le [DecidableEq α] (l : List α) :
    (nubb l).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons b l ih =>
      show (if b ∈ nubb l then nubb l else b :: nubb l).length ≤ l.length + 1
      split
      · exact Nat.le_succ_of_le ih
      · exact Nat.succ_le_succ ih

/-- A finset from a list, with a choice-free body. -/
def toFin [DecidableEq α] (l : List α) : Finset α :=
  ⟨(nubb l : Multiset α), Multiset.coe_nodup.mpr (nodup_nubb l)⟩

@[simp] theorem mem_toFin [DecidableEq α] {l : List α} {a : α} :
    a ∈ toFin l ↔ a ∈ l := by
  rw [toFin, Finset.mem_mk, Multiset.mem_coe, mem_nubb]

theorem card_toFin_le [DecidableEq α] (l : List α) :
    (toFin l).card ≤ l.length := by
  rw [toFin, Finset.card_mk, Multiset.coe_card]
  exact length_nubb_le l

/-! ## Extensionality helpers, choice-free -/

theorem subAntisymm {s t : Finset α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  Finset.ext fun a => ⟨fun ha => h₁ ha, fun ha => h₂ ha⟩

/-- Decidable equality of finsets via double inclusion (Mathlib's
`Finset.decidableEq` runs through the tainted `List.decidablePerm`).
Deliberately *not* an instance: supply with `letI` where needed. -/
def finDecEq [DecidableEq α] : DecidableEq (Finset α) := fun s t =>
  decidable_of_iff (s ⊆ t ∧ t ⊆ s)
    ⟨fun ⟨h₁, h₂⟩ => subAntisymm h₁ h₂, fun h => h ▸ ⟨subset_rfl, subset_rfl⟩⟩

theorem toFin_cons [DecidableEq α] (a : α) (l : List α) :
    toFin (a :: l) = insert a (toFin l) :=
  subAntisymm
    (fun x hx => by
      rcases List.mem_cons.mp (mem_toFin.mp hx) with rfl | h
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (mem_toFin.mpr h))
    (fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | h
      · exact mem_toFin.mpr (List.mem_cons_self ..)
      · exact mem_toFin.mpr (List.mem_cons_of_mem _ (mem_toFin.mp h)))

/-- **The `Prop`-level representative**: every finset is enumerated by a
duplicate-free list.  `Quot.ind` supplies the existential with no choice;
only a *canonical* such list (`Finset.toList`) would need
`Classical.choice`. -/
theorem exists_rep (s : Finset α) :
    ∃ l : List α, l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ s := by
  rcases s with ⟨m, hm⟩
  induction m using Quotient.inductionOn with
  | h l =>
      exact ⟨l, Multiset.coe_nodup.mp hm,
        fun x => (Finset.mem_mk.trans Multiset.mem_coe).symm⟩

/-- The multiset-level representative: every finset's underlying
multiset is the coercion of some list. -/
theorem exists_rep_val (s : Finset α) :
    ∃ l : List α, (↑l : Multiset α) = s.val := by
  rcases s with ⟨m, hm⟩
  induction m using Quotient.inductionOn with
  | h l => exact ⟨l, rfl⟩

/-! ## The set algebra, lifted with extensional invariance -/

private theorem toFin_perm [DecidableEq α] {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : toFin l₁ = toFin l₂ :=
  subAntisymm
    (fun a ha => mem_toFin.mpr (h.mem_iff.mp (mem_toFin.mp ha)))
    (fun a ha => mem_toFin.mpr (h.mem_iff.mpr (mem_toFin.mp ha)))

/-- Union, choice-free (Mathlib's `∪` is tainted through
`Multiset.ndunion`'s embedded proofs). -/
def finUnion [DecidableEq α] (s t : Finset α) : Finset α :=
  Quotient.liftOn₂ s.val t.val (fun l₁ l₂ => toFin (l₁ ++ l₂))
    (fun _ _ _ _ p₁ p₂ =>
      subAntisymm
        (fun a ha => by
          rw [mem_toFin, List.mem_append] at ha ⊢
          exact ha.imp p₁.mem_iff.mp p₂.mem_iff.mp)
        (fun a ha => by
          rw [mem_toFin, List.mem_append] at ha ⊢
          exact ha.imp p₁.mem_iff.mpr p₂.mem_iff.mpr))

@[simp] theorem mem_finUnion [DecidableEq α] {s t : Finset α} {a : α} :
    a ∈ finUnion s t ↔ a ∈ s ∨ a ∈ t := by
  rcases s with ⟨ms, hs⟩
  rcases t with ⟨mt, ht⟩
  induction ms using Quotient.inductionOn with
  | h ls =>
  induction mt using Quotient.inductionOn with
  | h lt =>
      show a ∈ toFin (ls ++ lt) ↔ a ∈ ls ∨ a ∈ lt
      rw [mem_toFin, List.mem_append]

/-- Image, choice-free. -/
def finImage [DecidableEq β] (f : α → β) (s : Finset α) : Finset β :=
  Quotient.liftOn s.val (fun l => toFin (l.map f))
    (fun _ _ p =>
      subAntisymm
        (fun b hb => by
          rw [mem_toFin, List.mem_map] at hb ⊢
          exact hb.imp fun _ ⟨ha, hfa⟩ => ⟨p.mem_iff.mp ha, hfa⟩)
        (fun b hb => by
          rw [mem_toFin, List.mem_map] at hb ⊢
          exact hb.imp fun _ ⟨ha, hfa⟩ => ⟨p.mem_iff.mpr ha, hfa⟩))

@[simp] theorem mem_finImage [DecidableEq β] {f : α → β} {s : Finset α} {b : β} :
    b ∈ finImage f s ↔ ∃ a ∈ s, f a = b := by
  rcases s with ⟨ms, hs⟩
  induction ms using Quotient.inductionOn with
  | h ls =>
      show b ∈ toFin (ls.map f) ↔ ∃ a ∈ ls, f a = b
      rw [mem_toFin, List.mem_map]

/-- Binary image over a pair of finsets (`(a, b) ↦ f a b` for `a ∈ s`,
`b ∈ t`) — subsumes `Finset.product` composed with `Finset.image`,
both tainted in Mathlib. -/
def finPairMap [DecidableEq γ] (f : α → β → γ) (s : Finset α)
    (t : Finset β) : Finset γ :=
  Quotient.liftOn₂ s.val t.val
    (fun l₁ l₂ => toFin (l₁.flatMap fun a => l₂.map (f a)))
    (fun _ _ _ _ p₁ p₂ =>
      subAntisymm
        (fun c hc => by
          rw [mem_toFin, List.mem_flatMap] at hc ⊢
          obtain ⟨a, ha, hc⟩ := hc
          rw [List.mem_map] at hc
          obtain ⟨b, hb, hfb⟩ := hc
          exact ⟨a, p₁.mem_iff.mp ha,
            List.mem_map.mpr ⟨b, p₂.mem_iff.mp hb, hfb⟩⟩)
        (fun c hc => by
          rw [mem_toFin, List.mem_flatMap] at hc ⊢
          obtain ⟨a, ha, hc⟩ := hc
          rw [List.mem_map] at hc
          obtain ⟨b, hb, hfb⟩ := hc
          exact ⟨a, p₁.mem_iff.mpr ha,
            List.mem_map.mpr ⟨b, p₂.mem_iff.mpr hb, hfb⟩⟩))

@[simp] theorem mem_finPairMap [DecidableEq γ] {f : α → β → γ} {s : Finset α}
    {t : Finset β} {c : γ} :
    c ∈ finPairMap f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a b = c := by
  rcases s with ⟨ms, hs⟩
  rcases t with ⟨mt, ht⟩
  induction ms using Quotient.inductionOn with
  | h ls =>
  induction mt using Quotient.inductionOn with
  | h lt =>
      show c ∈ toFin (ls.flatMap fun a => lt.map (f a)) ↔
        ∃ a ∈ ls, ∃ b ∈ lt, f a b = c
      rw [mem_toFin, List.mem_flatMap]
      constructor
      · rintro ⟨a, ha, hc⟩
        rw [List.mem_map] at hc
        exact ⟨a, ha, hc⟩
      · rintro ⟨a, ha, hc⟩
        exact ⟨a, ha, List.mem_map.mpr hc⟩

private theorem sum_map_const_le {l : List α} {f : α → Nat} {n : Nat}
    (h : ∀ a ∈ l, f a ≤ n) : (l.map f).sum ≤ l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul, Nat.add_comm (l.length * n) n]
      exact Nat.add_le_add (h a (List.mem_cons_self ..))
        (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem card_finPairMap_le [DecidableEq γ] (f : α → β → γ) (s : Finset α)
    (t : Finset β) : (finPairMap f s t).card ≤ s.card * t.card := by
  rcases s with ⟨ms, hs⟩
  rcases t with ⟨mt, ht⟩
  induction ms using Quotient.inductionOn with
  | h ls =>
  induction mt using Quotient.inductionOn with
  | h lt =>
      refine Nat.le_trans
        (card_toFin_le (ls.flatMap fun a => lt.map (f a))) ?_
      show (ls.flatMap fun a => lt.map (f a)).length ≤
        ls.length * lt.length
      rw [List.length_flatMap]
      exact sum_map_const_le fun a _ => Nat.le_of_eq (by rw [List.length_map])

/-- Powerset, choice-free, via `List.sublists`. -/
def finPow [DecidableEq α] (s : Finset α) : Finset (Finset α) :=
  letI : DecidableEq (Finset α) := finDecEq
  Quotient.liftOn s.val (fun l => toFin (l.sublists.map toFin))
    (fun l₁ l₂ p =>
      subAntisymm
        (fun T hT' => by
          rw [mem_toFin, List.mem_map] at hT' ⊢
          obtain ⟨u, hu, hTu⟩ := hT'
          rw [List.mem_sublists] at hu
          have hTsub : ∀ a, a ∈ T → a ∈ l₂ := fun a ha => by
            rw [← hTu] at ha
            exact p.mem_iff.mp (hu.subset (mem_toFin.mp ha))
          refine ⟨l₂.filter (fun x => decide (x ∈ T)), ?_, ?_⟩
          · rw [List.mem_sublists]
            exact List.filter_sublist
          · refine subAntisymm (fun a ha => ?_) (fun a ha => ?_)
            · rw [mem_toFin, List.mem_filter, decide_eq_true_eq] at ha
              exact ha.2
            · rw [mem_toFin, List.mem_filter, decide_eq_true_eq]
              exact ⟨hTsub a ha, ha⟩)
        (fun T hT' => by
          rw [mem_toFin, List.mem_map] at hT' ⊢
          obtain ⟨u, hu, hTu⟩ := hT'
          rw [List.mem_sublists] at hu
          have hTsub : ∀ a, a ∈ T → a ∈ l₁ := fun a ha => by
            rw [← hTu] at ha
            exact p.mem_iff.mpr (hu.subset (mem_toFin.mp ha))
          refine ⟨l₁.filter (fun x => decide (x ∈ T)), ?_, ?_⟩
          · rw [List.mem_sublists]
            exact List.filter_sublist
          · refine subAntisymm (fun a ha => ?_) (fun a ha => ?_)
            · rw [mem_toFin, List.mem_filter, decide_eq_true_eq] at ha
              exact ha.2
            · rw [mem_toFin, List.mem_filter, decide_eq_true_eq]
              exact ⟨hTsub a ha, ha⟩))

@[simp] theorem mem_finPow [DecidableEq α] {s T : Finset α} :
    T ∈ finPow s ↔ T ⊆ s := by
  letI : DecidableEq (Finset α) := finDecEq
  rcases s with ⟨ms, hs⟩
  induction ms using Quotient.inductionOn with
  | h ls =>
      show T ∈ toFin (ls.sublists.map toFin) ↔
        T ⊆ (⟨⟦ls⟧, hs⟩ : Finset α)
      rw [mem_toFin, List.mem_map]
      constructor
      · rintro ⟨u, hu, rfl⟩ a ha
        rw [List.mem_sublists] at hu
        show a ∈ ls
        exact hu.subset (mem_toFin.mp ha)
      · intro hsub
        refine ⟨ls.filter (fun x => decide (x ∈ T)), ?_, ?_⟩
        · rw [List.mem_sublists]
          exact List.filter_sublist
        · refine subAntisymm (fun a ha => ?_) (fun a ha => ?_)
          · rw [mem_toFin, List.mem_filter, decide_eq_true_eq] at ha
            exact ha.2
          · rw [mem_toFin, List.mem_filter, decide_eq_true_eq]
            refine ⟨?_, ha⟩
            show a ∈ ls
            exact hsub ha

theorem card_finPow_le [DecidableEq α] (s : Finset α) :
    (finPow s).card ≤ 2 ^ s.card := by
  letI : DecidableEq (Finset α) := finDecEq
  rcases s with ⟨ms, hs⟩
  induction ms using Quotient.inductionOn with
  | h ls =>
      refine Nat.le_trans (card_toFin_le (ls.sublists.map toFin)) ?_
      show (ls.sublists.map toFin).length ≤ 2 ^ ls.length
      rw [List.length_map, List.length_sublists]

/-- Difference as a filter (Mathlib's `\` is tainted through
`Multiset.sub`'s embedded proofs). -/
def finSdiff (s t : Finset α) [DecidableEq α] : Finset α :=
  letI : DecidableEq (Finset α) := finDecEq
  s.filter (fun x => x ∉ t)

@[simp] theorem mem_finSdiff [DecidableEq α] {s t : Finset α} {a : α} :
    a ∈ finSdiff s t ↔ a ∈ s ∧ a ∉ t := by
  rw [finSdiff, Finset.mem_filter]

theorem finSdiff_empty [DecidableEq α] (s : Finset α) :
    finSdiff s ∅ = s :=
  subAntisymm (fun a ha => (mem_finSdiff.mp ha).1)
    (fun a ha => mem_finSdiff.mpr ⟨ha, Finset.notMem_empty a⟩)

/-- The visited-set step strictly shrinks the unvisited part of the
space: the choice-free replacement for `card_erase_lt_of_mem` over `\`. -/
theorem card_finSdiff_insert_lt [DecidableEq α] {E V : Finset α} {S : α}
    (hE : S ∈ E) (hV : S ∉ V) :
    (finSdiff E (insert S V)).card < (finSdiff E V).card := by
  have hsub : finSdiff E (insert S V) ⊆ finSdiff E V := fun a ha => by
    obtain ⟨haE, haV⟩ := mem_finSdiff.mp ha
    exact mem_finSdiff.mpr
      ⟨haE, fun hmem => haV (Finset.mem_insert_of_mem hmem)⟩
  have hS : S ∈ finSdiff E V := mem_finSdiff.mpr ⟨hE, hV⟩
  have hS' : S ∉ finSdiff E (insert S V) :=
    fun hmem => (mem_finSdiff.mp hmem).2 (Finset.mem_insert_self ..)
  exact Finset.card_lt_card ⟨hsub, fun h => hS' (h hS)⟩

/-! ## Choice-free re-proofs of tainted Mathlib `insert`/`⊆` lemmas -/

theorem insertSubset [DecidableEq α] {a : α} {s t : Finset α} (ha : a ∈ t) (h : s ⊆ t) :
    insert a s ⊆ t := fun x hx => by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ha
  · exact h hx

theorem insertSubsetInsert [DecidableEq α] (a : α) {s t : Finset α} (h : s ⊆ t) :
    insert a s ⊆ insert a t := fun x hx => by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert_self ..
  · exact Finset.mem_insert_of_mem (h hx)

theorem singletonSubset {a : α} {s : Finset α} (h : a ∈ s) :
    ({a} : Finset α) ⊆ s := fun x hx => by
  rw [Finset.mem_singleton] at hx
  exact hx ▸ h

/-- `Finset.coe_insert`, re-proved choice-free. -/
theorem coeInsert [DecidableEq α] (a : α) (s : Finset α) :
    (↑(insert a s) : Set α) = insert a ↑s :=
  Set.ext fun x => by
    rw [Finset.mem_coe, Finset.mem_insert, Set.mem_insert_iff,
      Finset.mem_coe]

/-! ## Bridges to Mathlib's tainted operations

These are *deliberately* the only tainted statements in this file: they
let the legacy `toFinset`-phrased results be derived from the clean
chain.  Anything that must audit choice-free must not mention them. -/

theorem toFin_eq_toFinset [DecidableEq α] (l : List α) :
    toFin l = l.toFinset :=
  subAntisymm
    (fun a ha => List.mem_toFinset.mpr (mem_toFin.mp ha))
    (fun a ha => mem_toFin.mpr (List.mem_toFinset.mp ha))

theorem toFin_toList [DecidableEq α] (s : Finset α) :
    toFin s.toList = s :=
  subAntisymm
    (fun a ha => Finset.mem_toList.mp (mem_toFin.mp ha))
    (fun a ha => mem_toFin.mpr (Finset.mem_toList.mpr ha))

theorem finSdiff_eq_sdiff [DecidableEq α] (s t : Finset α) :
    finSdiff s t = s \ t :=
  subAntisymm
    (fun a ha => Finset.mem_sdiff.mpr (mem_finSdiff.mp ha))
    (fun a ha => mem_finSdiff.mpr (Finset.mem_sdiff.mp ha))

/-- info: 'PLLND.toFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms toFin

/-- info: 'PLLND.finDecEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finDecEq

/-- info: 'PLLND.exists_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_rep

/-- info: 'PLLND.finUnion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finUnion

/-- info: 'PLLND.mem_finPow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_finPow

/--
info: 'PLLND.card_finSdiff_insert_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms card_finSdiff_insert_lt

end PLLND
