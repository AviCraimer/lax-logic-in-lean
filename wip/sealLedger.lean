import absorb_base

/-!
# The ledger cannot cross a `◯`-seal: the entry/seal dilemma, machine-checked

ROUND 3 of the assault on `cascade_low_pos_box` (`wip/absorb_base.lean`, the
tower's one `sorry`).  The round's brief was:

> Extend `cascade_main`'s pigeonhole over jump goals through the `◯`-clauses,
> so that every budget-consuming recursive call is financed by the ledger.

This file records what that route runs into, as theorems rather than as prose.
Two things are established.

**§3 — the MEASURE is not the obstruction.**  With the goal-size measure
`gsize` and the lex triple `(c, defect S Γ, gsize g)`, two of the three
surviving sealed sites of `cascade_main` strictly decrease it:

* the **goal-γ disjunct** (`absorb_base` :2748) descends from goal `◯D` to
  goal `D` at the *same* budget and the *same* context — third component
  strictly down;
* the **clause-γ-head component** (:3261) descends from budget `c'+1` to `c'`
  — first component strictly down.

The **truncation disjunct** (:3513) does not move any component: it restarts
at the same budget, context, goal *and* fuel (`fh = F+1`, `fuel = fl+1`).  So
a `(budget, defect, goal-size)`-lex induction would discharge two of the three
sites outright — the measure question, open since July, is settled here.

**§4 — the LEDGER is the obstruction, and no ledger works.**  What blocks the
route is not termination but *financing*, and the failure is at the seam
between the holdout and `cascade_main`, in both directions at once:

* `cascade_main` must be **entered** from the holdout's own room
  `defect S Γ · (|jumpGoals S| + 2) ≤ c` — that is all the holdout has;
* at the clause-γ-head seal `cascade_main` must **hand the holdout back** its
  room one budget lower, at `c - 1`.

`no_ledger_survives_gamma_seal` shows these two demands are contradictory for
**every** ledger predicate and **every** room predicate whatsoever, given only
that the room is *budget-sensitive somewhere* — i.e. that there is one
instance at which it holds at `c+1` and fails at `c`.  The proof is two
applications and no arithmetic: the hypotheses compose to derive the room at
`c` from the room at `c+1`.  §5 exhibits the required budget-sensitive
instance inside the re-parameterised kernel's own band: a piece-closed,
`◯`-involving, covered space with `defect = 1`.

And a budget-*insensitive* room is not an escape: a room that never
distinguishes `c` from `c+1` is equivalent to a `c`-free side condition, and
the `c`-free form of the kernel is already refuted
(`ReparamRefute.not_reparamKernelRoomFree`).

**§6 diagnoses the existing design exactly.**  The two ledgers actually in the
file sit on opposite horns:

* `cascade_main`'s unshifted ledger satisfies both seal demands (`ledger0_seal1`,
  `ledger0_seal2`, proved in general) and **fails** the entry demand
  (`ledger0_entry_fails`) — which is why `cascade_main` is entered from
  `kcap_room`'s full allotment at the top and never from the holdout;
* `cascade_main_bf`'s shifted ledger satisfies the entry demand
  (`ledgerS_entry`, proved in general) and **fails** both seal demands
  (`ledgerS_seal1_fails`, `ledgerS_seal2_fails`) — which costs it nothing,
  because over a box-free space every sealed site is dead code.

So the shift is exactly what the box-free tier can afford and the `◯`-band
cannot, and no constant in between exists: `shift_dilemma` bounds the shift
below by `|jumpGoals S| + 1` and above by `0` at one and the same instance.

**What this leaves.**  The route is not "grind the three sites"; it is to take
the clause-γ-head component *out of the pair descent altogether*, so that no
recursive call reads the room one budget down.  `wip/boxSndTight.lean`'s
`boxSnd_tight` is the existing sorry-free evidence that this is the right
shape: it reaches the boxed goal clause `◯(E@c ⇢ A@(c+1))` at an
**arbitrary** target budget `c` from a matched-budget source, i.e. the boxed
goal position is budget-free.  Generalising it from atomic `prop q` bodies to
arbitrary goal bodies is the next round's target.
-/

open PLLFormula

namespace PLLND
namespace SealLedger

/-! ## 1.  The room, and the ledgers actually in `wip/absorb_base.lean` -/

/-- The holdout's room hypothesis, verbatim from `cascade_low_pos_box`
(`wip/absorb_base.lean`:2374). -/
def Room (S : Finset PLLFormula) (Γ : List PLLFormula) (c : Nat) : Prop :=
  defect S Γ * ((jumpGoals S).card + 2) ≤ c

/-- `cascade_main`'s A-half ledger, verbatim (`wip/absorb_base.lean`:2446). -/
def Ledger0 (S : Finset PLLFormula) (Γ : List PLLFormula)
    (seen : Finset PLLFormula) (c : Nat) : Prop :=
  (jumpGoals S \ seen).card + 1 + defect S Γ * ((jumpGoals S).card + 2) ≤ c

/-- `cascade_main_bf`'s A-half ledger, verbatim (`wip/absorb_base.lean`:938):
the same ledger shifted by one full defect level. -/
def LedgerS (S : Finset PLLFormula) (Γ : List PLLFormula)
    (seen : Finset PLLFormula) (c : Nat) : Prop :=
  (jumpGoals S \ seen).card + 1 + defect S Γ * ((jumpGoals S).card + 2)
    ≤ c + ((jumpGoals S).card + 2)

/-- The ledger family with an arbitrary constant shift. -/
def LedgerX (shift : Nat) (S : Finset PLLFormula) (Γ : List PLLFormula)
    (seen : Finset PLLFormula) (c : Nat) : Prop :=
  (jumpGoals S \ seen).card + 1 + defect S Γ * ((jumpGoals S).card + 2)
    ≤ c + shift

/-! ## 2.  The three surviving sealed sites of `cascade_main`, transcribed

Each is stated with the room `cascade_main` actually supplies at that site
(`hroomW : defect · (J+2) ≤ c' + 1` at the goal-γ and truncation sites,
`hroomW0 : defect · (J+2) ≤ c'` at the clause-γ-head site), and with the
fuels the traversal actually passes.  These are the three `cascade_low` calls
at `wip/absorb_base.lean`:2764, :3291 and :3516. -/

/-- **Sealed site 1 — the goal-γ disjunct** (`absorb_base`:2748).  Goal `◯D`
descends to goal `D`; budget, context and head fuel are those of the caller
(`fh = F`, one below the traversal's current fuel level). -/
def Seal1 (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
    D ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl →
    Room S Γ (c' + 1) →
    G4c Δ (itpE p S fl (c' + 2) Γ) →
    G4c Δ (itpA p S F (c' + 2) Γ D) →
    G4c Δ (itpA p S fl (c' + 1) Γ D)

/-- **Sealed site 2 — the clause-γ-head component** (`absorb_base`:3261).  The
γ-clause `◯A₁ ⊃ B ∈ Γ` puts its boxed first component one budget down: the
target budget is `c'`, the source budget `c' + 1`. -/
def Seal2 (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (A₁ : PLLFormula),
    A₁.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl →
    Room S Γ c' →
    G4c Δ (itpE p S fl (c' + 1) Γ) →
    G4c Δ (itpA p S F (c' + 1) Γ A₁.somehow) →
    G4c Δ (itpA p S fl c' Γ A₁.somehow)

/-- **Sealed site 3 — the truncation disjunct** (`absorb_base`:3513).  The
whole head is rebuilt from the truncation disjunct and the descent restarts at
the caller's own fuel level (`fh = F + 1`, `fuel = fl + 1`): budget, context,
goal and fuel all unchanged. -/
def Seal3 (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (g : PLLFormula),
    g ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl →
    Room S Γ (c' + 1) →
    G4c Δ (itpE p S (fl + 1) (c' + 2) Γ) →
    G4c Δ (itpA p S (F + 1) (c' + 2) Γ g) →
    G4c Δ (itpA p S (fl + 1) (c' + 1) Γ g)

/-! ## 3.  The measure: `(budget, defect, goal size)` lex

Sites 1 and 2 strictly decrease it; site 3 does not move it at all. -/

/-- Structural size of a goal formula. -/
def gsize : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and A B => gsize A + gsize B + 1
  | .or A B => gsize A + gsize B + 1
  | .ifThen A B => gsize A + gsize B + 1
  | .somehow A => gsize A + 1

/-- The lex order on `(budget, defect, goal size)`. -/
def lexLt (x y : Nat × Nat × Nat) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧
    (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2)))

theorem lexLt_irrefl (x : Nat × Nat × Nat) : ¬ lexLt x x := by
  intro h
  simp only [lexLt] at h
  rcases h with h | ⟨-, h | ⟨-, h⟩⟩ <;> omega

/-- **Site 1 strictly decreases the measure**: same budget, same context,
goal `◯D` replaced by `D`. -/
theorem seal1_lexLt (S : Finset PLLFormula) (Γ : List PLLFormula)
    (c : Nat) (D : PLLFormula) :
    lexLt (c, defect S Γ, gsize D) (c, defect S Γ, gsize D.somehow) := by
  refine Or.inr ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
  simp only [gsize]
  omega

/-- **Site 2 strictly decreases the measure**: the budget drops by one, so the
goal may be replaced by anything at all. -/
theorem seal2_lexLt (S : Finset PLLFormula) (Γ Γ' : List PLLFormula)
    (c : Nat) (g h : PLLFormula) :
    lexLt (c, defect S Γ', gsize h) (c + 1, defect S Γ, gsize g) :=
  Or.inl (Nat.lt_succ_self c)

/-- **Site 3 does not move the measure**: budget, context and goal are the
caller's own.  This is the one sealed site a `(budget, defect, goal-size)`-lex
induction cannot discharge. -/
theorem seal3_not_lexLt (S : Finset PLLFormula) (Γ : List PLLFormula)
    (c : Nat) (g : PLLFormula) :
    ¬ lexLt (c, defect S Γ, gsize g) (c, defect S Γ, gsize g) :=
  lexLt_irrefl _

/-! ## 4.  The entry/seal dilemma — no ledger, of any shape, can do both

The holdout hands `cascade_main` nothing but its own room, so any ledger must
be *derivable* from the room at the entry budget (`entry`).  The clause-γ-head
seal hands the holdout back its own room one budget lower, so any ledger must
*imply* the room at `c` from itself at `c + 1` (`seal`).  Composed, those two
turn the room at `c + 1` into the room at `c`. -/

/-- **THE OBSTRUCTION.**  For any room predicate and any ledger predicate
whatsoever: if the room is budget-sensitive at even one instance — it holds at
`c + 1` and fails at `c` — then the entry demand and the clause-γ-head seal
demand cannot both be met.

No arithmetic and no assumption on the shape of either predicate: the two
demands compose to lift the room across a budget drop, which is exactly what
a budget hypothesis must not do. -/
theorem no_ledger_survives_gamma_seal
    {Room' : Finset PLLFormula → List PLLFormula → Nat → Prop}
    {L : Finset PLLFormula → List PLLFormula → Finset PLLFormula → Nat → Prop}
    {S : Finset PLLFormula} {Γ : List PLLFormula} {g : PLLFormula} {c : Nat}
    (hhi : Room' S Γ (c + 1)) (hlo : ¬ Room' S Γ c)
    (hentry : ∀ S' Γ' g' c', Room' S' Γ' c' → L S' Γ' {g'} c')
    (hseal : ∀ S' Γ' seen' c', L S' Γ' seen' (c' + 1) → Room' S' Γ' c') :
    False :=
  hlo (hseal S Γ {g} c (hentry S Γ g (c + 1) hhi))

/-! ## 5.  A budget-sensitive instance inside the kernel's own band

`Sγ` is piece-closed for all four closure hypotheses of the re-parameterised
`cascade_low_pos_box`, `◯`-involving, and covers `Γγ`; `defect Sγ Γγ = 1`, so
`hd1` holds, and `|jumpGoals Sγ| = 2`, so the room is `4 ≤ c` — which holds at
`4` and fails at `3`.  Everything the kernel asks of an instance is met. -/

/-- The minimal `◯`-band space: one γ-clause and its whole subformula set. -/
def Sγ : Finset PLLFormula :=
  {((prop "a").somehow).ifThen (prop "b"), (prop "a").somehow,
   prop "a", prop "b"}

/-- The context: everything but the γ-clause's consequent, so the clause is
live and the defect is `1`. -/
def Γγ : List PLLFormula :=
  [((prop "a").somehow).ifThen (prop "b"), (prop "a").somehow, prop "a"]

theorem sγ_and : ∀ {A B : PLLFormula}, A.and B ∈ Sγ → A ∈ Sγ ∧ B ∈ Sγ := by
  intro A B h
  simp only [Sγ, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h <;> cases h

theorem sγ_or : ∀ {A B : PLLFormula}, A.or B ∈ Sγ → A ∈ Sγ ∧ B ∈ Sγ := by
  intro A B h
  simp only [Sγ, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h <;> cases h

theorem sγ_imp : ∀ {A B : PLLFormula}, A.ifThen B ∈ Sγ → A ∈ Sγ ∧ B ∈ Sγ := by
  intro A B h
  simp only [Sγ, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h <;> cases h <;> refine ⟨?_, ?_⟩ <;> simp [Sγ]

theorem sγ_some : ∀ {A : PLLFormula}, A.somehow ∈ Sγ → A ∈ Sγ := by
  intro A h
  simp only [Sγ, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h <;> cases h <;> simp [Sγ]

theorem sγ_cover : ∀ X ∈ Γγ, X ∈ Sγ := by decide +kernel

theorem sγ_defect : defect Sγ Γγ = 1 := by decide +kernel

theorem sγ_jump : (jumpGoals Sγ).card = 2 := by decide +kernel

/-- The single missing space formula is a legitimate goal, and it is not a
jump goal — the worst case for the entry demand. -/
theorem sγ_goal : (prop "b") ∈ Sγ := by decide +kernel

theorem sγ_jump_sdiff_goal :
    (jumpGoals Sγ \ {prop "b"}).card = 2 := by decide +kernel

/-- The room at `Sγ, Γγ` is `4 ≤ c`. -/
theorem sγ_room_iff (c : Nat) : Room Sγ Γγ c ↔ 4 ≤ c := by
  simp only [Room, sγ_defect, sγ_jump]

/-- **The room is budget-sensitive at `Sγ`.** -/
theorem sγ_room_hi : Room Sγ Γγ 4 := (sγ_room_iff 4).mpr (Nat.le_refl _)

theorem sγ_room_lo : ¬ Room Sγ Γγ 3 := by
  rw [sγ_room_iff]
  omega

/-- **The dilemma, instantiated.**  No ledger predicate can serve both the
entry from the holdout's room and the clause-γ-head seal back into it. -/
theorem no_ledger
    (L : Finset PLLFormula → List PLLFormula → Finset PLLFormula → Nat → Prop)
    (hentry : ∀ S Γ g c, Room S Γ c → L S Γ {g} c)
    (hseal : ∀ S Γ seen c, L S Γ seen (c + 1) → Room S Γ c) :
    False :=
  no_ledger_survives_gamma_seal (g := prop "b") sγ_room_hi sγ_room_lo
    hentry hseal

/-! ## 6.  The two ledgers of `wip/absorb_base.lean` sit on opposite horns -/

/-- `cascade_main`'s unshifted ledger meets the **goal-γ** seal demand, in
general. -/
theorem ledger0_seal1 (S : Finset PLLFormula) (Γ : List PLLFormula)
    (seen : Finset PLLFormula) (c : Nat) (h : Ledger0 S Γ seen c) :
    Room S Γ c := by
  simp only [Ledger0] at h
  simp only [Room]
  omega

/-- `cascade_main`'s unshifted ledger meets the **clause-γ-head** seal demand,
in general — this is `hroomW0` (`wip/absorb_base.lean`:2498). -/
theorem ledger0_seal2 (S : Finset PLLFormula) (Γ : List PLLFormula)
    (seen : Finset PLLFormula) (c : Nat) (h : Ledger0 S Γ seen (c + 1)) :
    Room S Γ c := by
  simp only [Ledger0] at h
  simp only [Room]
  omega

/-- …and **fails the entry demand**: at `Sγ` the holdout's room holds at `c = 4`
with `defect = 1`, and the unshifted ledger at `seen = {g}` does not follow.
This is why `cascade_main` is entered from `kcap_room`'s full allotment and
never from the holdout. -/
theorem ledger0_entry_fails :
    ¬ (∀ S Γ g c, 1 ≤ defect S Γ → Room S Γ c → Ledger0 S Γ {g} c) := by
  intro h
  have := h Sγ Γγ (prop "b") 4 (by rw [sγ_defect]) sγ_room_hi
  simp only [Ledger0, sγ_defect, sγ_jump, sγ_jump_sdiff_goal] at this
  omega

/-- `cascade_main_bf`'s shifted ledger meets the **entry** demand, in general:
the shift is exactly one full defect level, which is what a fresh chain
allotment costs. -/
theorem ledgerS_entry (S : Finset PLLFormula) (Γ : List PLLFormula)
    (g : PLLFormula) (c : Nat) (h : Room S Γ c) : LedgerS S Γ {g} c := by
  have hcard : (jumpGoals S \ {g}).card ≤ (jumpGoals S).card :=
    Finset.card_le_card (Finset.sdiff_subset)
  simp only [Room] at h
  simp only [LedgerS]
  omega

/-- …and **fails the goal-γ seal demand**: at `Sγ` with every jump goal seen,
the shifted ledger holds at `c = 3` where the room does not. -/
theorem ledgerS_seal1_fails :
    ¬ (∀ S Γ seen c, LedgerS S Γ seen c → Room S Γ c) := by
  intro h
  refine sγ_room_lo (h Sγ Γγ (jumpGoals Sγ) 3 ?_)
  simp only [LedgerS, sγ_defect, sγ_jump, Finset.sdiff_self]
  decide

/-- …and **fails the clause-γ-head seal demand** as well. -/
theorem ledgerS_seal2_fails :
    ¬ (∀ S Γ seen c, LedgerS S Γ seen (c + 1) → Room S Γ c) := by
  intro h
  refine sγ_room_lo (h Sγ Γγ (jumpGoals Sγ) 3 ?_)
  simp only [LedgerS, sγ_defect, sγ_jump, Finset.sdiff_self]
  decide

/-! ## 7.  No constant shift exists

The shift is bounded below by `|jumpGoals S| + 1` (entry) and above by `0`
(clause-γ-head seal) at one and the same instance. -/

/-- The entry demand forces the shift to at least `|jumpGoals Sγ| + 1 = 3`. -/
theorem shift_lower (shift : Nat)
    (hentry : ∀ S Γ g c, 1 ≤ defect S Γ → Room S Γ c → LedgerX shift S Γ {g} c) :
    3 ≤ shift := by
  have := hentry Sγ Γγ (prop "b") 4 (by rw [sγ_defect]) sγ_room_hi
  simp only [LedgerX, sγ_defect, sγ_jump, sγ_jump_sdiff_goal] at this
  omega

/-- The clause-γ-head seal demand forces the shift to be `0`. -/
theorem shift_upper (shift : Nat)
    (hseal : ∀ S Γ seen c, LedgerX shift S Γ seen (c + 1) → Room S Γ c) :
    shift = 0 := by
  by_contra hne
  refine sγ_room_lo (hseal Sγ Γγ (jumpGoals Sγ) 3 ?_)
  simp only [LedgerX, sγ_defect, sγ_jump, Finset.sdiff_self]
  simp only [Finset.card_empty]
  omega

/-- **No constant shift works.**  The shifted-ledger family — the only family
the box-free tier and the `◯`-band tier have in common — is empty of solutions
to the two demands. -/
theorem shift_dilemma (shift : Nat)
    (hentry : ∀ S Γ g c, 1 ≤ defect S Γ → Room S Γ c → LedgerX shift S Γ {g} c)
    (hseal : ∀ S Γ seen c, LedgerX shift S Γ seen (c + 1) → Room S Γ c) :
    False := by
  have h1 := shift_lower shift hentry
  have h2 := shift_upper shift hseal
  omega

end SealLedger
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.SealLedger.no_ledger_survives_gamma_seal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.SealLedger.no_ledger_survives_gamma_seal

/-- info: 'PLLND.SealLedger.no_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SealLedger.no_ledger

/-- info: 'PLLND.SealLedger.shift_dilemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SealLedger.shift_dilemma

/-- info: 'PLLND.SealLedger.seal1_lexLt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SealLedger.seal1_lexLt

/-- info: 'PLLND.SealLedger.seal3_not_lexLt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SealLedger.seal3_not_lexLt

/--
info: 'PLLND.SealLedger.ledger0_entry_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.SealLedger.ledger0_entry_fails

/--
info: 'PLLND.SealLedger.ledgerS_seal1_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.SealLedger.ledgerS_seal1_fails
