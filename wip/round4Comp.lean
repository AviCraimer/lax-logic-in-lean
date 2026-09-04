import sealLedger

/-!
# ROUND 4, Task 0 — the POSITIVE twin of `no_ledger_survives_gamma_seal`

`wip/sealLedger.lean` proves that no ledger predicate can both be *entered*
from the holdout's room and *re-supply* that room one budget lower
(`no_ledger_survives_gamma_seal`).  That is a statement about a
**financing scheme**, and it rules out the round-3 route without touching a
single proof detail.

This file is the mirror image: the financing scheme that *does* close, written
as an abstract composition over the actual predicates, with every fuel and
budget annotated and nothing hidden.  It is checked BEFORE any of the three
sealed sites is attacked, exactly as PROGRESS §59's method note prescribes.

## The architecture

`cascade_low_pos_box` (the holdout) is consumed from exactly **three** places
in the whole development — the three `cascade_low` calls of `cascade_main`'s
A-half at `wip/absorb_base.lean`:2764, :3291 and :3516.  (`grep -n
"cascade_low "` finds no others; `cascade_low_pos_box` itself is `private` and
`cascade_low_pos` / `cascade_low` are consumed only there.)  So the holdout is
not a lemma the tower needs: it is a lemma **those three sites** need.  Kill
the three sites and the holdout is dead code — the `sorry` stops reaching the
crown whether or not it is ever proved.

All three sites sit at a `◯`-goal.  Precisely:

| site | file:line | goal of the obligation | ambient fuel | source fuel | target fuel | source budget | target budget |
|------|-----------|------------------------|--------------|-------------|-------------|---------------|---------------|
| 1 | :2764 | `D` (body of the enclosing `◯D`) | `fl` | `F` | `fl` | `c'+2` | `c'+1` |
| 2 | :3291 | `◯A₁`, `◯A₁ ∈ S` | `fl` | `F` | `fl` | `c'+1` | `c'` |
| 3 | :3516 | `◯D` (`g = ◯D`, the branch's own case split) | `fl+1` | `F+1` | `fl+1` | `c'+2` | `c'+1` |

with `F ≤ fl` at all three.  Sites 2 and 3 are `◯`-goal obligations outright.
Site 1 is *not* — its goal is the body `D` — but site 1 lives inside the
`| somehow D =>` arm of the A-half's goal-clause analysis, i.e. inside the
case `g = ◯D`, and that whole case is closed **before** the head is unfolded
by the same `◯`-goal descent applied to the caller's own head and ambient
(`boxDesc_kills_site1` below).  So site 1 is *eliminated*, not discharged.

That leaves one obligation:

    BoxDesc :  E@(ft, b+1)(Γ)  ⟶  A@(fs, b+1)(Γ, ◯D)  ⟶  A@(ft, b)(Γ, ◯D)
               (fs ≤ ft,  1 ≤ b,  ◯D ∈ S,  Γ ⊆ S)

— the holdout **restricted to `◯`-goals**, with `hroom`, `hd1` and every
ledger DELETED.  `BoxDesc` is legitimate to state room-free precisely because
`wip/seal2Free.lean`'s `gammaHead_budget_free` already proves its atomic
instance with the target budget universally quantified: the `◯`-goal position
consumes no budget, so there is nothing for a room to finance.

## What is checked here

`boxDesc_seal2`, `boxDesc_seal3` and `boxDesc_kills_site1` type-check the
composition against `wip/sealLedger.lean`'s verbatim transcriptions.  Two
book-keeping discrepancies between the transcriptions and the call sites are
recorded rather than papered over (§4).

## Status: the composition has been APPLIED

`wip/absorb_base.lean` was rewired to this architecture in the same session
(PROGRESS §60(e)).  `cascade_main`'s A-half now carries the
`by_cases hbox : ∃ D, g = D.somehow` split of §4; the goal-γ and truncation
sites are dead code (`exact absurd ⟨D, rfl⟩ hbox`); the clause-γ-head site is
a `cascade_boxgoal` call; and `cascade_low_pos_box`, `cascade_low_pos` and
`cascade_low` are deleted.  The file's single `sorry` is now
`cascade_boxgoal_pos`, which is `BoxDescR` plus the deleted holdout's own
`1 ≤ defect S Γ` — see `boxDescR_pos_of_holdout` in §8 for the certificate
that this is a weakening.  So the table of line numbers above refers to the
file *before* that rewiring; the sites no longer exist.

## What is NOT claimed

That `BoxDesc` is provable.  At an **atomic** body it is
`gammaHead_budget_free` up to fuel plumbing; at a general body it is the open
mathematical step PROGRESS §59's amendment identifies (the context-shrinking
value move of `boxGoal_remap`, licensed only by `itpA_atom_forces`).  This
file fixes the *target*; it does not reach it.
-/

open PLLFormula

namespace PLLND
namespace Round4

open PLLND.SealLedger

/-! ## 1. The one obligation -/

/-- **`BoxDesc` — the `◯`-goal direct descent.**  The holdout's conclusion at a
`◯`-shaped goal, with the room hypothesis, the defect bound and every ledger
removed.  The only budget hypothesis is `1 ≤ b`, which is not financing: at
`b = 0` the target table is literally `⊥` (goal clause and truncation are both
budget-gated), so `1 ≤ b` is a *well-formedness* side condition, not a room.

The only fuel hypothesis is `fs ≤ ft`, which the three sites supply verbatim
(`hF : F ≤ fl`), and which is likewise not financing: at `ft = 0` it forces
`fs = 0` and the source is `⊥`. -/
def BoxDesc (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fs ft b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
    D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → fs ≤ ft → 1 ≤ b →
    G4c Δ (itpE p S ft (b + 1) Γ) →
    G4c Δ (itpA p S fs (b + 1) Γ D.somehow) →
    G4c Δ (itpA p S ft b Γ D.somehow)

/-! ## 2. Site 2 — the clause-γ-head component (`absorb_base`:3291)

`Seal2`'s obligation is a `BoxDesc` instance at `fs := F`, `ft := fl`,
`b := c'`.  The room hypothesis it carries is consumed for one thing only:
`1 ≤ c'`, which the call site derives from `1 ≤ defect S Γ` (`absorb_base`
:3294–:3303, the `by omega` block).  Nothing else in `Room` is used. -/

/-- **`BoxDesc` discharges sealed site 2.**  The room is used only to produce
`1 ≤ c'`; delete `hd1` and even that use disappears. -/
theorem boxDesc_seal2 (p : String) (S : Finset PLLFormula)
    (h : BoxDesc p S) (hd1 : ∀ Γ : List PLLFormula, 1 ≤ defect S Γ) :
    Seal2 p S := by
  intro F fl c' Γ Δ A₁ hA₁S hΓS hF hroom _hamb' hsrc
  have hc : 1 ≤ c' := by
    have h2 : 1 * ((jumpGoals S).card + 2) ≤
        defect S Γ * ((jumpGoals S).card + 2) :=
      Nat.mul_le_mul_right _ (hd1 Γ)
    simp only [Room] at hroom
    omega
  obtain ⟨b, rfl⟩ : ∃ b, c' = b + 1 := ⟨c' - 1, by omega⟩
  exact h F fl (b + 1) Γ Δ A₁ hA₁S hΓS hF (by omega) _hamb' hsrc

/-- The same, with `1 ≤ c'` supplied directly — the form the call site is in
(`absorb_base`:3294 proves exactly this side condition before calling). -/
theorem boxDesc_seal2_of_pos (p : String) (S : Finset PLLFormula)
    (h : BoxDesc p S)
    (F fl c' : Nat) (Γ Δ : List PLLFormula) (A₁ : PLLFormula)
    (hA₁S : A₁.somehow ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S) (hF : F ≤ fl)
    (hc : 1 ≤ c')
    (hamb : G4c Δ (itpE p S fl (c' + 1) Γ))
    (hsrc : G4c Δ (itpA p S F (c' + 1) Γ A₁.somehow)) :
    G4c Δ (itpA p S fl c' Γ A₁.somehow) :=
  h F fl c' Γ Δ A₁ hA₁S hΓS hF hc hamb hsrc

/-! ## 3. Site 3 — the truncation disjunct (`absorb_base`:3516)

The transcription `Seal3` quantifies over an arbitrary goal `g ∈ S`; the site
itself is inside `cases g with | somehow D`, so only the `◯`-goal instance is
ever asked for.  At that instance it is a `BoxDesc` instance with
`fs := F+1`, `ft := fl+1`, `b := c'+1`, and the room is not used at all. -/

/-- **`BoxDesc` discharges sealed site 3** at the goal shape the site actually
reaches.  No room, no defect bound, no `1 ≤ c` side condition (the site's
budget is `c'+1`, positive by construction). -/
theorem boxDesc_seal3 (p : String) (S : Finset PLLFormula)
    (h : BoxDesc p S)
    (F fl c' : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula)
    (hgS : D.somehow ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S) (hF : F ≤ fl)
    (hamb : G4c Δ (itpE p S (fl + 1) (c' + 2) Γ))
    (hsrc : G4c Δ (itpA p S (F + 1) (c' + 2) Γ D.somehow)) :
    G4c Δ (itpA p S (fl + 1) (c' + 1) Γ D.somehow) :=
  h (F + 1) (fl + 1) (c' + 1) Γ Δ D hgS hΓS (Nat.succ_le_succ hF)
    (Nat.le_add_left 1 c') hamb hsrc

/-! ## 4. Site 1 — ELIMINATED, not discharged

`Seal1`'s goal is the *body* `D`, so it is not a `BoxDesc` instance and never
will be.  But site 1 is reached only from the `| somehow D =>` arm of the
A-half's goal-clause analysis, i.e. only when the caller's own goal is `◯D`.
The same `BoxDesc` applied to the caller's own head and ambient produces the
caller's target value outright, and the caller's own continuation `hcls`
consumes it.  So the arm containing site 1 is never entered.

This is the exact point where the round-3 dilemma is dodged: the composition
below uses `hcls` *once, at the caller's own budget*, and never hands anything
back to the holdout one budget lower — so `no_ledger_survives_gamma_seal`'s
`hseal` premise is simply never instantiated. -/

/-- **`BoxDesc` eliminates sealed site 1.**  In `cascade_main`'s A-half at
`fuel = fl+1`, `fh = F+1`, `c = c'+1`, `g = ◯D`, `g ∈ seen`: the target value
is produced directly and the continuation closes `R`.  No room, no ledger, no
seen-set arithmetic, and — the point — **no call at a lower budget**. -/
theorem boxDesc_kills_site1 (p : String) (S : Finset PLLFormula)
    (h : BoxDesc p S)
    (F fl c' : Nat) (Γ Δ : List PLLFormula) (D R : PLLFormula)
    (hgS : D.somehow ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S) (hF : F ≤ fl)
    (hcls : ∀ Δ', (∀ ψ ∈ Δ, ψ ∈ Δ') →
      G4c Δ' (itpA p S (fl + 1) (c' + 1) Γ D.somehow) → G4c Δ' R)
    (hamb : G4c Δ (itpE p S (fl + 1) (c' + 2) Γ))
    (hhead : G4c Δ (itpA p S (F + 1) (c' + 2) Γ D.somehow)) :
    G4c Δ R :=
  hcls Δ (fun _ hψ => hψ)
    (h (F + 1) (fl + 1) (c' + 1) Γ Δ D hgS hΓS (Nat.succ_le_succ hF)
      (Nat.le_add_left 1 c') hamb hhead)

/-! ## 5. The composition, in one statement

`BoxDesc` alone accounts for all three sealed sites: two as instances, one by
elimination.  Nothing else is required — in particular no room predicate is
transported across a budget drop, which is what
`no_ledger_survives_gamma_seal` forbids. -/

/-- **THE POSITIVE TWIN.**  One room-free `◯`-goal descent discharges sealed
sites 2 and 3 and eliminates sealed site 1.  Compare
`no_ledger_survives_gamma_seal`: the ledger route had to move a room
hypothesis from `c+1` to `c`; this route moves nothing — every use of
`BoxDesc` is at the caller's own budget, and the one budget drop
(`b+1 ⟶ b`) happens *inside* `BoxDesc`, where no hypothesis has to survive
it. -/
theorem boxDesc_discharges_the_seals (p : String) (S : Finset PLLFormula)
    (h : BoxDesc p S) :
    -- site 2, at the site's own side condition `1 ≤ c'`
    (∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (A₁ : PLLFormula),
      A₁.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl → 1 ≤ c' →
      G4c Δ (itpE p S fl (c' + 1) Γ) →
      G4c Δ (itpA p S F (c' + 1) Γ A₁.somehow) →
      G4c Δ (itpA p S fl c' Γ A₁.somehow)) ∧
    -- site 3, at the goal shape the site reaches
    (∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
      D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl →
      G4c Δ (itpE p S (fl + 1) (c' + 2) Γ) →
      G4c Δ (itpA p S (F + 1) (c' + 2) Γ D.somehow) →
      G4c Δ (itpA p S (fl + 1) (c' + 1) Γ D.somehow)) ∧
    -- site 1, eliminated at the caller
    (∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (D R : PLLFormula),
      D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl →
      (∀ Δ', (∀ ψ ∈ Δ, ψ ∈ Δ') →
        G4c Δ' (itpA p S (fl + 1) (c' + 1) Γ D.somehow) → G4c Δ' R) →
      G4c Δ (itpE p S (fl + 1) (c' + 2) Γ) →
      G4c Δ (itpA p S (F + 1) (c' + 2) Γ D.somehow) →
      G4c Δ R) :=
  ⟨fun F fl c' Γ Δ A₁ hA₁S hΓS hF hc hamb hsrc =>
     boxDesc_seal2_of_pos p S h F fl c' Γ Δ A₁ hA₁S hΓS hF hc hamb hsrc,
   fun F fl c' Γ Δ D hgS hΓS hF hamb hsrc =>
     boxDesc_seal3 p S h F fl c' Γ Δ D hgS hΓS hF hamb hsrc,
   fun F fl c' Γ Δ D R hgS hΓS hF hcls hamb hhead =>
     boxDesc_kills_site1 p S h F fl c' Γ Δ D R hgS hΓS hF hcls hamb hhead⟩

/-! ## 6. The two book-keeping discrepancies, recorded

**(i) `Seal2` as transcribed is missing `1 ≤ c'`.**  `cascade_low` takes
`hc : 1 ≤ c` as an explicit hypothesis and the call site at
`absorb_base`:3294 proves it (from `1 ≤ defect S Γ`, itself derived from
`B ∈ S ∖ Γ` at :3295).  `Seal2` carries only `Room S Γ c'`, which at
`defect S Γ = 0` is vacuous and does **not** give `1 ≤ c'`.  So `Seal2` as
literally written is stronger than the site's obligation, and at `c' = 0` it
is false for a trivial reason: the target `itpA p S fl 0 Γ ◯A₁` is `⊥`
(`FloorRefute.tgtz_bot` is the same phenomenon).  `boxDesc_seal2_of_pos` is
the site's actual obligation; `boxDesc_seal2` recovers the transcription
under the side condition the site has.

**(ii) `Seal3` as transcribed is more general than the site.**  It quantifies
over `g ∈ S`; the site (`absorb_base`:3508–:3516) is inside
`cases g with | somehow D`, so only `g = ◯D` is asked for.  `boxDesc_seal3`
proves the instance the site needs.

Neither discrepancy changes the round's conclusion, and both are in the safe
direction (the transcriptions ask for at least as much as the sites). -/

/-- Discrepancy (i), machine-checked: `Room S Γ 0` holds whenever the defect
is `0`, so `Seal2`'s hypotheses do **not** entail `1 ≤ c'`. -/
theorem seal2_room_gives_no_positivity :
    ∃ (S : Finset PLLFormula) (Γ : List PLLFormula), Room S Γ 0 :=
  ⟨∅, [], by simp [Room, defect]⟩

/-! ## 7. The round-3 dilemma, read forwards

`no_ledger_survives_gamma_seal` needs **both** demands:

* `hentry` — the ledger must follow from the holdout's room at the entry
  budget;
* `hseal`  — the ledger at `c + 1` must re-supply the room at `c`.

The round-4 architecture makes only the first.  Every occurrence of `BoxDesc`
in §5 is at the *caller's own* budget, and `BoxDesc`'s statement contains no
ledger, no room and no defect — so there is nothing for `hseal` to be
instantiated at.  The dilemma is not evaded by a cleverer ledger; the second
demand simply stops being made.

That matters because round 3 also proved which ledger is waiting on the other
side.  `LedgerS` — the shifted ledger the box-free spine `cascade_main_bf`
already runs on — **satisfies the entry demand in general**
(`SealLedger.ledgerS_entry`) and fails both seal demands
(`ledgerS_seal1_fails`, `ledgerS_seal2_fails`).  Those two failures were what
excluded it from the `◯`-band.  With the seals discharged by `BoxDesc` they
cost nothing, exactly as they already cost nothing over a box-free space. -/

/-- **The shifted ledger is entered from the holdout's room**, in general —
round 3's `ledgerS_entry`, re-exported here as the half of the dilemma the
round-4 architecture actually uses. -/
theorem shifted_ledger_is_entered (S : Finset PLLFormula) (Γ : List PLLFormula)
    (g : PLLFormula) (c : Nat) (h : Room S Γ c) : LedgerS S Γ {g} c :=
  ledgerS_entry S Γ g c h

/-! ## 8. The room-carrying fallback

`BoxDesc` is stated room-free because the atomic instance is
(`wip/round4Free.lean`'s `boxDesc_atom_all`, and `seal2Free`'s
`gammaHead_budget_free` before it).  Should the general body turn out to need
financing after all, the architecture does not have to change: all three sites
supply the room **at the target budget** —

* site 1 and site 3: `hroomW : defect · (J+2) ≤ c' + 1` with target budget
  `c' + 1`;
* site 2: `hroomW0 : defect · (J+2) ≤ c'` with target budget `c'`

— so `BoxDescR` below is available at every site with no change to
`cascade_main`, and the whole of §§2–5 goes through with `BoxDesc` replaced by
`BoxDescR`.  (Strictly more is available: `cascade_main`'s own ledger
`hroom` is in scope at all three sites, at `c' + 1` for sites 1 and 3 and at
`c' + 1` for site 2 as well.  The room at the target budget is the largest
*uniform* hypothesis, which is why it is the one recorded.) -/

/-- `BoxDesc` with the room at the target budget — the strongest hypothesis
all three sites supply uniformly. -/
def BoxDescR (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fs ft b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
    D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → fs ≤ ft → 1 ≤ b →
    Room S Γ b →
    G4c Δ (itpE p S ft (b + 1) Γ) →
    G4c Δ (itpA p S fs (b + 1) Γ D.somehow) →
    G4c Δ (itpA p S ft b Γ D.somehow)

theorem boxDescR_of_boxDesc (p : String) (S : Finset PLLFormula)
    (h : BoxDesc p S) : BoxDescR p S :=
  fun fs ft b Γ Δ D hD hΓ hf hb _ hamb hsrc => h fs ft b Γ Δ D hD hΓ hf hb hamb hsrc

/-! ### The replacement is a WEAKENING, certified

`wip/absorb_base.lean`'s round-4 `sorry` is `cascade_boxgoal_pos`, which is
`BoxDescR` plus the old holdout's own `1 ≤ defect S Γ`.  `Holdout` below is
`cascade_low_pos_box`'s statement transcribed verbatim, and
`boxDescR_pos_of_holdout` derives the new obligation from the old one — so
the round-4 rewiring assumes strictly less than the file assumed before it.
Nothing has been strengthened, and no new falsity can have been introduced. -/

/-- `cascade_low_pos_box`'s statement, transcribed verbatim
(`wip/absorb_base.lean`, the round-3 holdout). -/
def Holdout (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula),
    g ∈ S → (∀ X ∈ Γ, X ∈ S) → 1 ≤ c → 1 ≤ defect S Γ →
    defect S Γ * ((jumpGoals S).card + 2) ≤ c →
    G4c Δ (itpE p S fuel (c + 1) Γ) →
    G4c Δ (itpA p S fh (c + 1) Γ g) →
    fh ≤ fuel →
    G4c Δ (itpA p S fuel c Γ g)

/-- **The round-4 obligation follows from the round-3 holdout.**  It is that
holdout at a `◯`-goal, and nothing else — so replacing the one by the other in
`wip/absorb_base.lean` is a weakening, unconditionally. -/
theorem boxDescR_pos_of_holdout (p : String) (S : Finset PLLFormula)
    (h : Holdout p S)
    (fs ft b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula)
    (hgS : D.somehow ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hfs : fs ≤ ft) (hb : 1 ≤ b) (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ b)
    (hamb : G4c Δ (itpE p S ft (b + 1) Γ))
    (hsrc : G4c Δ (itpA p S fs (b + 1) Γ D.somehow)) :
    G4c Δ (itpA p S ft b Γ D.somehow) :=
  h fs Γ ft b D.somehow Δ hgS hΓS hb hd1 hroom hamb hsrc hfs

/-- **The composition survives the fallback.**  The room-carrying obligation
discharges sites 2 and 3 and eliminates site 1, with each site's own room
passed straight through — no ledger, and still no hypothesis transported
across a budget drop. -/
theorem boxDescR_discharges_the_seals (p : String) (S : Finset PLLFormula)
    (h : BoxDescR p S) :
    (∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (A₁ : PLLFormula),
      A₁.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl → 1 ≤ c' → Room S Γ c' →
      G4c Δ (itpE p S fl (c' + 1) Γ) →
      G4c Δ (itpA p S F (c' + 1) Γ A₁.somehow) →
      G4c Δ (itpA p S fl c' Γ A₁.somehow)) ∧
    (∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
      D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl → Room S Γ (c' + 1) →
      G4c Δ (itpE p S (fl + 1) (c' + 2) Γ) →
      G4c Δ (itpA p S (F + 1) (c' + 2) Γ D.somehow) →
      G4c Δ (itpA p S (fl + 1) (c' + 1) Γ D.somehow)) ∧
    (∀ (F fl c' : Nat) (Γ Δ : List PLLFormula) (D R : PLLFormula),
      D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl → Room S Γ (c' + 1) →
      (∀ Δ', (∀ ψ ∈ Δ, ψ ∈ Δ') →
        G4c Δ' (itpA p S (fl + 1) (c' + 1) Γ D.somehow) → G4c Δ' R) →
      G4c Δ (itpE p S (fl + 1) (c' + 2) Γ) →
      G4c Δ (itpA p S (F + 1) (c' + 2) Γ D.somehow) →
      G4c Δ R) :=
  ⟨fun F fl c' Γ Δ A₁ hA₁S hΓS hF hc hrm hamb hsrc =>
     h F fl c' Γ Δ A₁ hA₁S hΓS hF hc hrm hamb hsrc,
   fun F fl c' Γ Δ D hgS hΓS hF hrm hamb hsrc =>
     h (F + 1) (fl + 1) (c' + 1) Γ Δ D hgS hΓS (Nat.succ_le_succ hF)
       (Nat.le_add_left 1 c') hrm hamb hsrc,
   fun F fl c' Γ Δ D R hgS hΓS hF hrm hcls hamb hhead =>
     hcls Δ (fun _ hψ => hψ)
       (h (F + 1) (fl + 1) (c' + 1) Γ Δ D hgS hΓS (Nat.succ_le_succ hF)
         (Nat.le_add_left 1 c') hrm hamb hhead)⟩

end Round4
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round4.boxDesc_discharges_the_seals' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round4.boxDesc_discharges_the_seals

/-- info: 'PLLND.Round4.boxDesc_kills_site1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Round4.boxDesc_kills_site1

/--
info: 'PLLND.Round4.boxDescR_discharges_the_seals' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round4.boxDescR_discharges_the_seals

/-- info: 'PLLND.Round4.boxDescR_pos_of_holdout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Round4.boxDescR_pos_of_holdout

/-! **The composition is room-free.**  Pinned as a type check: `BoxDesc`'s
statement mentions no `defect`, no `jumpGoals`, no budget inequality beyond
`1 ≤ b`, and no ledger. -/

/--
info: PLLND.Round4.BoxDesc (p : String) (S : Finset PLLFormula) : Prop
-/
#guard_msgs in
#check PLLND.Round4.BoxDesc
