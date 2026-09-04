import round4Comp

/-!
# ROUND 5 — the γ-γ core: the `◯`-goal descent's own γ-row is the irreducible
# residue, and no budget-sensitive hypothesis can finance it

The round's brief was to prove `cascade_boxgoal_pos` (`wip/absorb_base.lean`,
the development's one `sorry`) as a direct-form clone of `cascade_main`'s
A-half.  The brief also carried a HARD CONSTRAINT: if the build ever needs a
seal-style demand — handing a target disjunct back one budget lower — STOP,
because `SealLedger.no_ledger_survives_gamma_seal` machine-refutes that route.

That demand arises, and this file records exactly where and why, as theorems
where the content is formal and as pinned arithmetic where it is bookkeeping.

## Where the demand arises — the γ-γ core

Unfold `cascade_boxgoal_pos`'s source `A@(fs, b+1)(Γ, ◯D)` one level.  Its
γ-row for a live clause `◯A₁ ⊃ B₀ ∈ Γ` contains the disjunct

    ( ◯( E@(b)(Γ) ⊃ A@(b)(Γ, ◯A₁) ) ) ∧ A@(b+1)(B₀::Γ, ◯D)

and every disjunct of the target `A@(ft, b)(Γ, ◯D)` that can absorb it pairs
the grown second component with a first component at budget `b - 1`:

    ( ◯( E@(b-1)(Γ) ⊃ A@(b-1)(Γ, ◯A₁) ) ) ∧ A@(b)(B₀::Γ, ◯D).

Producing that first component from the held one is the `◯`-goal descent
`b → b-1` at the SAME context — an instance of `cascade_boxgoal_pos` itself,
one budget down.  This is self-similar: the `◯`-goal table's own γ-rows are
the recursion, and each step drops the budget by one.

## Why no side condition survives the recursion

`cascade_boxgoal_pos`'s only budget hypothesis is the room
`defect S Γ · (|jumpGoals S| + 2) ≤ b`.  The recursion needs it at `b - 1`.
`room_not_descending` (below) refutes the transport at an instance meeting
every hypothesis of the statement (`Sγ`, `defect = 1`, `◯a ∈ Sγ`), and
`no_self_financed_crossing` generalises it: NO side-condition family that

* the three call sites can supply from the room (`hsupply`),
* survives the γ-γ budget drop (`hcross`), and
* still does the room's job (`hneed`)

exists at all.  This sharpens PROGRESS §59: round 3 refuted ledgers threaded
through `cascade_main`'s seals; this refutes every financing of the round-4
architecture's OWN self-recursion.  Consequently a proof of
`cascade_boxgoal_pos` must do one of

1. close the γ-γ core with NO budget-sensitive hypothesis on the recursion
   path — i.e. prove the room-free `◯`-goal descent (`Round4.BoxDesc`) there
   (the atomic-body proof `Round4Free.boxDesc_atom_all` is exactly this:
   `itpA_atom_forces` produces the inner value outright, no recursion); or
2. not recurse at the γ-row at all — a forcing-style direct production of the
   boxed first component.

## What IS financed — the entry band

The round's positive finding: the same-context CPS entries the other rows
need (`LedgerS`-entered descents at jump goals, the `cascade_main_bf`
machinery) are affordable from the bare room down to exactly TWO budget
levels below it, and not below that (`ledgerS_entry_two_below`,
`ledgerS_entry_dies_at_sγ`).  So the jump rows (the case PROGRESS §60(d)
flagged as the hard one) are NOT the obstruction: the γ-γ core is.

## Probe record (`wip/round5probe.lean`, `wip/round5probe2.lean`)

Round 4's screens never reached the statement's own regime (every screened
budget sat below the room).  The round-5 probes put the floor and the two
corner configurations on the record — the room floor `b = defect·(J+2)` at
fuels deep enough for nested γ-γ unfoldings, and the fresh-`⊃`-antecedent
body over a context missing the antecedent (where the guard-ascent step is
room-priced).  Every cell PROVED, including the γ-head crossing rows with no
room in the sequent at all — machine evidence that alternative 1 (the
room-free form) is the true target.
-/

open PLLFormula

namespace PLLND
namespace Round5

open PLLND.SealLedger

/-- **The room does not descend.**  `cascade_boxgoal_pos`'s room hypothesis at
`b` does not yield it at `b - 1`, at an instance satisfying every hypothesis
of the statement (`Sγ` is piece-closed, `◯a ∈ Sγ`, `Γγ ⊆ Sγ`,
`defect Sγ Γγ = 1`).  So the γ-γ self-recursion cannot be financed by the
statement's own hypotheses. -/
theorem room_not_descending :
    ¬ (∀ S Γ c, Room S Γ (c + 1) → Room S Γ c) := by
  intro h
  exact sγ_room_lo (h Sγ Γγ 3 sγ_room_hi)

/-- **No side-condition family finances the γ-γ core.**  If `Φ` is supplied by
the room at the call sites, survives the γ-γ budget drop, and still implies
the room (does the room's job at the recursive occurrence), then `Φ` cannot
exist: the three demands compose to transport the room across a budget drop,
which `Sγ` refutes.  Compare `SealLedger.no_ledger_survives_gamma_seal`
(round 3): that killed ledgers threaded through `cascade_main`'s seals; this
kills every financing of the round-4 architecture's own self-recursion. -/
theorem no_self_financed_crossing
    {Φ : Finset PLLFormula → List PLLFormula → Nat → Prop}
    (hsupply : ∀ S Γ c, 1 ≤ defect S Γ → Room S Γ c → Φ S Γ c)
    (hcross : ∀ S Γ c, Φ S Γ (c + 1) → Φ S Γ c)
    (hneed : ∀ S Γ c, Φ S Γ c → Room S Γ c) : False := by
  refine sγ_room_lo (hneed Sγ Γγ 3 (hcross Sγ Γγ 3 ?_))
  refine hsupply Sγ Γγ 4 ?_ sγ_room_hi
  rw [sγ_defect]

/-- **The entry band is two deep.**  The shifted ledger's entry demand at a
jump goal is met from the bare room down to two budget levels below it: the
`cascade_main_bf` machinery can be ENTERED at `c` from the room at `c + 2`.
This is what finances the jump-row landings (the case PROGRESS §60(d) flagged)
one budget below the statement's own level — the jump rows are not the
obstruction. -/
theorem ledgerS_entry_two_below (S : Finset PLLFormula)
    (Γ : List PLLFormula) (x : PLLFormula) (hx : x ∈ jumpGoals S)
    (c : Nat) (h : Room S Γ (c + 2)) : LedgerS S Γ {x} c := by
  have hcard : (jumpGoals S \ {x}).card = (jumpGoals S).card - 1 := by
    rw [Finset.card_sdiff, Finset.singleton_inter_of_mem hx,
      Finset.card_singleton]
  have hpos : 1 ≤ (jumpGoals S).card :=
    Finset.card_pos.mpr ⟨x, hx⟩
  simp only [Room] at h
  simp only [LedgerS, hcard]
  omega

/-- …and it dies below that: at `Sγ` (room `4 ≤ c`, satisfied at `4`) the
entry at budget `1` — three below the room — fails even at a jump goal.  With
`ledgerS_entry_two_below` this pins the exact band: entries are financed at
`c ≥ room − 2` and not at `c = room − 3`. -/
theorem ledgerS_entry_dies_at_sγ :
    ¬ LedgerS Sγ Γγ {(prop "a").somehow} 1 := by
  intro h
  have hJ : (jumpGoals Sγ).card = 2 := sγ_jump
  have hd : defect Sγ Γγ = 1 := sγ_defect
  have hc : (jumpGoals Sγ \ {(prop "a").somehow}).card = 1 := by
    decide +kernel
  simp only [LedgerS, hJ, hd, hc] at h
  omega

/-- **Alternative 1 suffices, certified.**  The room-free `◯`-goal descent
(`Round4.BoxDesc`, the form every probe supports and the atomic case proves)
implies `cascade_boxgoal_pos`'s statement verbatim — the room and the defect
bound are discarded.  So the recommended round-6 target closes the
development's `sorry` the moment it lands. -/
theorem boxgoal_pos_of_boxDesc (p : String) (S : Finset PLLFormula)
    (h : Round4.BoxDesc p S)
    (fs ft b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula)
    (hgS : D.somehow ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hfs : fs ≤ ft) (hb : 1 ≤ b) (_hd1 : 1 ≤ defect S Γ)
    (_hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ b)
    (hamb : G4c Δ (itpE p S ft (b + 1) Γ))
    (hsrc : G4c Δ (itpA p S fs (b + 1) Γ D.somehow)) :
    G4c Δ (itpA p S ft b Γ D.somehow) :=
  h fs ft b Γ Δ D hgS hΓS hfs hb hamb hsrc

end Round5
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round5.room_not_descending' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round5.room_not_descending

/--
info: 'PLLND.Round5.no_self_financed_crossing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round5.no_self_financed_crossing

/--
info: 'PLLND.Round5.ledgerS_entry_two_below' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round5.ledgerS_entry_two_below

/--
info: 'PLLND.Round5.ledgerS_entry_dies_at_sγ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round5.ledgerS_entry_dies_at_sγ

/--
info: 'PLLND.Round5.boxgoal_pos_of_boxDesc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round5.boxgoal_pos_of_boxDesc
