import round5core

/-!
# ROUND 6 — the E-half room constant TIGHTENS (`J+3 → J+2`), machine-checked;
# the truncation-tower's financing band, pinned at both ends

PROGRESS §61(f) named two residues gating the truncation-tower route to
`Round4.BoxDesc` at general bodies.  Residue (i) was the E-half room-constant
tightening: the one-step budget ascent

    Δ ⊢ E@(f, c)(Γ)  →  Δ ⊢ E@(f, c+1)(Γ)

is proved in `wip/absorb_base.lean` (`cascade_main`'s E-half) under the room

    (jumpGoals S).card + 3 + defect S Γ · ((jumpGoals S).card + 2) ≤ c

and §61(f)(i) claimed, hand-checked only, that the `+3` tightens to `+2`
because the internal entry demand (`hroomA`) has slack 1.  **This file
machine-checks the tightening**: `easc_tight` below is the E-half verbatim
with the constant `+2`, sorry-free.

## Why the statement is parametric in `EntryDesc`

The E-half's proof consumes the A-half (the CPS descent machinery) at exactly
one interface: the entry-shaped same-context descent at a singleton seen-set
(`hAd`/`hAg` in `cascade_main`).  `cascade_main` is `private` to
`wip/absorb_base.lean`, so the tightened E-half is stated with that interface
as the explicit hypothesis `EntryDesc` — which is precisely the instance
`cascade_main`'s own A-half provides (via `ihfA` at a singleton seen-set,
identity continuation), and precisely what any transplant into
`wip/absorb_base.lean` would have in scope.  Nothing else of the A-half is
used, and no room constant of the A-half changes.

## Where the slack is, exactly

The E-half at source budget `c''+1` needs, internally:

* `hroomA` (the entry demand): `(J∖{x}).card + 1 + defect·(J+2) ≤ c''` — from
  the `+3` room this had slack 1; from the `+2` room it closes EXACTLY
  (`(J∖{x}).card ≤ J`);
* `hEg` (the self-recursion at a defect-paying grown context): re-establishes
  the (tightened) room one defect level down — slack `J+2` per level, so the
  tightening costs nothing there;
* `hAg` (the entry demand at a grown context): same defect-level slack.

So `+2` is the exact constant: `tight_ascent_from_room` shows the tightened
demand at any defect-paying grown context follows from the BARE room
(`Room S Γ b`, the only budget hypothesis `cascade_boxgoal_pos` carries), and
`tight_exact_at_sγ` pins that with `+3` the same instance fails — the
tightening is load-bearing for the tower, not cosmetic.

## The tower's financing band (residue (iii), new this round)

The truncation-tower proof of the `◯`-goal descent maps each source row to a
target disjunct; its room-priced steps are the same-context CPS entries
(`LedgerS`-entries to the shifted spine) that the goal-size landings need.
Their budgets, relative to the statement's own `b`:

* goal-row landing (body `D`, generic): entry at `c = b` — financed by
  `SealLedger.ledgerS_entry` from the bare room, slack 1;
* landings whose body is a JUMP GOAL of the space (the γ-head bodies `A₁`):
  financed down to `c = b−2` (`tower_entry_depth1`, `tower_entry_depth2` =
  round 5's `ledgerS_entry_two_below`) and dead at `c = b−3` (round 5's
  `ledgerS_entry_dies_at_sγ`);
* landings at a GENERIC body (the goal-row of a nested tower level): financed
  down to `c = b−1` only — `depth1_entry_exact_at_s3` holds with zero slack
  and `no_depth2_entry_at_s3` pins the failure one level down, both at the
  nested-box witness `S3` (piece-closure of `◯◯(a⊃b) ⊃ c`), the smallest
  space whose γ-clause has a boxed body and hence sustains a second
  same-context γ-crossing whose inner goal-row body (`a⊃b`) is not a jump
  goal.

So the truncation-tower's γ-nest is financed for ONE same-context γ-crossing
in general, TWO when every landing body en route is a jump goal, and no
further.  `no_self_financed_nest` is the composition in general form, strictly
sharpening round 5's `no_self_financed_crossing`: even a side-condition family
whose per-level need is only the TWO-BELOW entry (`Room` at `c+2`, the weakest
demand any of the tower's spine entries makes) cannot survive three budget
crossings.  Round 5 refuted families that must re-supply the room at the same
level; this refutes families that need it only two levels up — the exact
demand profile of the truncation-tower design.
-/

open PLLFormula

namespace PLLND
namespace Round6

open PLLND.SealLedger

/-! ## 0. Cloned context helpers (private in `wip/absorb_base.lean`) -/

theorem weaken_sub {Γ Γ' : List PLLFormula} {C : PLLFormula}
    (h : ∀ ψ ∈ Γ, ψ ∈ Γ') (d : G4c Γ C) : G4c Γ' C := by
  rw [G4c.iff_set] at d ⊢
  refine d.weaken_subset ?_
  intro y hy
  rw [List.mem_toFinset] at hy ⊢
  exact h y hy

theorem consume₁ {Δ : List PLLFormula} {X Z : PLLFormula}
    (dX : G4c Δ X) (L : G4c [X] Z) : G4c Δ Z :=
  G4c.cut dX (weaken_sub (by
    intro ψ hψ
    rcases List.mem_singleton.mp hψ with rfl
    exact .head _) L)

theorem consume₂ {Δ : List PLLFormula} {X Y Z : PLLFormula}
    (dX : G4c Δ X) (dY : G4c Δ Y) (L : G4c [X, Y] Z) : G4c Δ Z :=
  G4c.cut dX (G4c.cut (dY.weaken X) (weaken_sub (by
    intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact .tail _ (.head _)
    · rcases List.mem_singleton.mp hψ with rfl
      exact .head _) L))

theorem fire {Δ : List PLLFormula} {X Y : PLLFormula}
    (dImp : G4c Δ (X.ifThen Y)) (dX : G4c Δ X) : G4c Δ Y :=
  consume₂ dX dImp (G4c.mp X Y [])

theorem projE {Δ l : List PLLFormula} {φ : PLLFormula}
    (dE : G4c Δ (andAll l)) (hmem : φ ∈ l) : G4c Δ φ :=
  G4c.cut dE (G4c.andAll_elim hmem (G4c.identity_mem (.head _)))

theorem box_fire {Δ : List PLLFormula} {X Y W : PLLFormula}
    (dBox : G4c Δ ((X.ifThen Y).somehow)) (dX : G4c Δ X)
    (k : G4c (Y :: Δ) W.somehow) : G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  have dY : G4c ((X.ifThen Y) :: (X.ifThen Y).somehow :: Δ) Y :=
    fire (G4c.identity_mem (.head _))
      (weaken_sub (fun ψ hψ => .tail _ (.tail _ hψ)) dX)
  refine G4c.cut dY (weaken_sub ?_ k)
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact .head _
  · exact .tail _ (.tail _ (.tail _ hψ))

theorem defect_lt_of_mem {S : Finset PLLFormula}
    {Γ Γ' : List PLLFormula} {x : PLLFormula}
    (hsub : Γ.toFinset ⊆ Γ'.toFinset) (hxS : x ∈ S) (hxΓ : x ∉ Γ)
    (hxΓ' : x ∈ Γ') : defect S Γ' < defect S Γ := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hy.1, fun h => hy.2 (hsub h)⟩
  · intro hsub2
    have h2 := hsub2 (Finset.mem_sdiff.mpr
      ⟨hxS, fun h => hxΓ (List.mem_toFinset.mp h)⟩)
    rw [Finset.mem_sdiff] at h2
    exact h2.2 (List.mem_toFinset.mpr hxΓ')

/-! ## 1. The A-half interface the E-half consumes -/

/-- **The entry-shaped same-context descent** — the only thing `cascade_main`'s
E-half uses its A-half for (`hAd`/`hAg`): the pair descent at a singleton
seen-set, identity continuation, entered at the unshifted ledger's own entry
demand.  `cascade_main`'s A-half provides exactly this instance (at every fuel);
the eventual transplant has it in scope as `ihfA`. -/
def EntryDesc (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (Γ : List PLLFormula) (f β : Nat) (h : PLLFormula) (Δ : List PLLFormula),
    h ∈ S → (∀ X ∈ Γ, X ∈ S) →
    (jumpGoals S \ {h}).card + 1 +
      defect S Γ * ((jumpGoals S).card + 2) ≤ β →
    G4c Δ (itpE p S f (β + 1) Γ) →
    G4c Δ (itpA p S f (β + 1) Γ h) →
    G4c Δ (itpA p S f β Γ h)

/-! ## 2. THE TIGHTENED E-HALF

`cascade_main`'s E-half (`wip/absorb_base.lean`:3405–3939) transcribed, with
the room constant `(jumpGoals S).card + 3` replaced by
`(jumpGoals S).card + 2` and the A-half calls routed through `EntryDesc`.
Every internal room obligation is re-closed by `omega` from the tightened
hypothesis; `hroomA` closes with zero slack, which is the sense in which `+2`
is exact. -/

set_option maxHeartbeats 2000000 in
theorem easc_tight (p : String) (S : Finset PLLFormula)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (hA : EntryDesc p S) :
    ∀ (fh : Nat) (Γ : List PLLFormula) (c : Nat) (Δ : List PLLFormula),
      (∀ X ∈ Γ, X ∈ S) →
      (jumpGoals S).card + 2 +
        defect S Γ * ((jumpGoals S).card + 2) ≤ c →
      G4c Δ (itpE p S fh c Γ) →
      G4c Δ (itpE p S fh (c + 1) Γ) := by
  intro fh
  induction fh with
  | zero =>
      intro Γ c Δ hΓS hroom hsrc
      simp only [itpE]
      exact G4c.truePLL_intro _
  | succ F ih =>
      intro Γ c Δ hΓS hroom hsrc
      obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
      rw [itpE_succ p S F (c'' + 2) Γ]
      refine G4c.andAll_intro ?_
      intro ψ hψ
      -- fuel-level source at any weaker budget
      have hsrcF : ∀ (b' : Nat), b' ≤ c'' + 1 → G4c Δ (itpE p S F b' Γ) :=
        fun b' hb' => consume₁ (consume₁ hsrc
          ((itp_fuel_mono p S F).1 _ Γ))
          ((itp_budget_mono_le p S hb' F).1 Γ)
      have hSor : ∀ {X : PLLFormula}, X ∈ Γ ∨ X ∈ S → X ∈ S :=
        fun h => h.elim (fun h' => hΓS _ h') id
      have hScons : ∀ {X : PLLFormula}, X ∈ S →
          ∀ F' ∈ X :: Γ, F' ∈ S := by
        intro X hX F' hF'
        rcases List.mem_cons.mp hF' with rfl | hF'
        · exact hX
        · exact hΓS _ hF'
      -- entry room for same-context A-descents: EXACT from the tightened room
      have hroomA : ∀ (x : PLLFormula), (jumpGoals S \ {x}).card + 1 +
          defect S Γ * ((jumpGoals S).card + 2) ≤ c'' := by
        intro x
        have hc := Finset.card_le_card
          (Finset.sdiff_subset (s := jumpGoals S) (t := {x}))
        omega
      -- one-step ascent at a defect-paying grown context
      have hEg : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
          (∀ X ∈ Γ', X ∈ S) →
          ∀ (Δ' : List PLLFormula), G4c Δ' (itpE p S F (c'' + 1) Γ') →
          G4c Δ' (itpE p S F (c'' + 2) Γ') := by
        intro Γ' hlt hΓS' Δ' hsrc'
        refine ih Γ' (c'' + 1) Δ' hΓS' ?_ hsrc'
        have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
            defect S Γ' * ((jumpGoals S).card + 2) +
            ((jumpGoals S).card + 2) := by ring
        have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
            defect S Γ * ((jumpGoals S).card + 2) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      -- entry-shaped same-context A-descent (the `EntryDesc` interface)
      have hAd : ∀ (β : Nat) (h : PLLFormula) (Δ' : List PLLFormula),
          h ∈ S →
          (jumpGoals S \ {h}).card + 1 +
            defect S Γ * ((jumpGoals S).card + 2) ≤ β →
          G4c Δ' (itpE p S F (β + 1) Γ) →
          G4c Δ' (itpA p S F (β + 1) Γ h) →
          G4c Δ' (itpA p S F β Γ h) :=
        fun β h Δ' hgS' hr hamb' hhead' =>
          hA Γ F β h Δ' hgS' hΓS hr hamb' hhead'
      -- entry-shaped A-descent at a defect-paying grown context
      have hAg : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
          ∀ (β : Nat) (h : PLLFormula) (Δ' : List PLLFormula),
          h ∈ S → (∀ X ∈ Γ', X ∈ S) → c'' ≤ β →
          G4c Δ' (itpE p S F (β + 1) Γ') →
          G4c Δ' (itpA p S F (β + 1) Γ' h) →
          G4c Δ' (itpA p S F β Γ' h) := by
        intro Γ' hlt β h Δ' hgS' hΓS' hβ hamb' hhead'
        refine hA Γ' F β h Δ' hgS' hΓS' ?_ hamb' hhead'
        have hc := Finset.card_le_card
          (Finset.sdiff_subset (s := jumpGoals S) (t := {h}))
        have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
            defect S Γ' * ((jumpGoals S).card + 2) +
            ((jumpGoals S).card + 2) := by ring
        have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
            defect S Γ * ((jumpGoals S).card + 2) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      simp only [itpEcls] at hψ
      rcases List.mem_append.mp hψ with hψ | hψ
      · rcases List.mem_append.mp hψ with hψ | hψ
        · -- the ⊥ clause
          split at hψ
          next hbot =>
            rcases List.mem_singleton.mp hψ with rfl
            refine projE (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_
            simp only [itpEcls]
            exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
              (Or.inl (by rw [if_pos hbot]; exact .head _))))
          next => cases hψ
        · -- the atom clauses
          obtain ⟨F', hF'Γ, heq⟩ := List.mem_filterMap.mp hψ
          cases F' with
          | prop q =>
              simp only at heq
              split at heq
              next => cases heq
              next hq =>
                injection heq with heq'
                subst heq'
                refine projE (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                  (Or.inr (List.mem_filterMap.mpr ⟨prop q, hF'Γ, ?_⟩))))
                simp only
                rw [if_neg hq]
          | falsePLL => cases heq
          | and _ _ => cases heq
          | or _ _ => cases heq
          | ifThen _ _ => cases heq
          | somehow _ => cases heq
      · -- the rule clauses
        obtain ⟨F', hF'Γ, hin⟩ := List.mem_flatMap.mp hψ
        cases F' with
        | prop _ => cases hin
        | falsePLL => cases hin
        | and A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                have hlt : defect S (A :: B :: Γ) < defect S Γ := by
                  by_cases hA' : A ∈ Γ
                  · have hB : B ∉ Γ := fun hB => h1 ⟨hA', hB⟩
                    exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                      (by intro y hy; simp only [List.toFinset_cons,
                        Finset.mem_insert]; exact Or.inr (Or.inr hy))
                      (h2.2.resolve_left hB) hB (.tail _ (.head _))
                  · exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                      (by intro y hy; simp only [List.toFinset_cons,
                        Finset.mem_insert]; exact Or.inr (Or.inr hy))
                      (h2.1.resolve_left hA') hA' (.head _)
                refine hEg _ hlt
                  (by
                    intro F' hF'
                    rcases List.mem_cons.mp hF' with rfl | hF'
                    · exact hSor h2.1
                    · exact hScons (hSor h2.2) _ hF') Δ (projE
                  (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inr
                  (List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩))
                simp only
                rw [if_neg h1, if_pos h2]
                exact .head _
              next => cases hin
        | or A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                have hA' : A ∉ Γ := fun h => h1 (Or.inl h)
                have hB : B ∉ Γ := fun h => h1 (Or.inr h)
                refine consume₁ (projE
                  (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                  (or_mono
                    (hEg _ (defect_cons_lt h2.1 hA') (hScons h2.1) _
                      (G4c.identity_mem (.head _)))
                    (hEg _ (defect_cons_lt h2.2 hB) (hScons h2.2) _
                      (G4c.identity_mem (.head _))))
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inr
                  (List.mem_flatMap.mpr ⟨A.or B, hF'Γ, ?_⟩))
                simp only
                rw [if_neg h1, if_pos h2]
                exact .head _
              next => cases hin
        | somehow χ =>
            simp only at hin
            split at hin
            next => cases hin
            next hg2 =>
              rcases List.mem_singleton.mp hin with rfl
              have hχΓ : χ ∉ Γ := fun h => hg2 (Or.inl h)
              have hχS : χ ∈ S := by
                by_contra h
                exact hg2 (Or.inr h)
              refine consume₁ (projE
                (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                (box_mono (hEg _ (defect_cons_lt hχS hχΓ) (hScons hχS) _
                  (G4c.identity_mem (.head _))))
              simp only [itpEcls]
              refine List.mem_append.mpr (Or.inr
                (List.mem_flatMap.mpr ⟨χ.somehow, hF'Γ, ?_⟩))
              simp only
              rw [if_neg hg2]
              exact .head _
        | ifThen A' B =>
            cases A' with
            | prop q =>
                simp only at hin
                split at hin
                next => cases hin
                next hBΓ =>
                  split at hin
                  next hBS =>
                    split at hin
                    next hq =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine hEg _ (defect_cons_lt hBS hBΓ) (hScons hBS) Δ
                        (projE
                        (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
                      simp only
                      rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                      exact .head _
                    next hq =>
                      split at hin
                      next => cases hin
                      next hqp =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine consume₁ (projE
                          (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                          (imp_mono (G4c.init (.head _))
                            (hEg _ (defect_cons_lt hBS hBΓ) (hScons hBS) _
                              (G4c.identity_mem (.head _))))
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                        exact .head _
                  next => cases hin
            | falsePLL => cases hin
            | and A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    refine hEg _ (defect_cons_lt h2 h1) (hScons h2) Δ (projE
                      (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                    simp only [itpEcls]
                    refine List.mem_append.mpr (Or.inr
                      (List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩))
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                  next => cases hin
            | or A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    have hlt : defect S (A₁.ifThen B :: B₁.ifThen B :: Γ) <
                        defect S Γ := by
                      by_cases hA' : A₁.ifThen B ∈ Γ
                      · have hBn : B₁.ifThen B ∉ Γ := fun hB => h1 ⟨hA', hB⟩
                        exact defect_lt_of_mem
                          (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                          (by intro y hy; simp only [List.toFinset_cons,
                            Finset.mem_insert]; exact Or.inr (Or.inr hy))
                          (h2.2.resolve_left hBn) hBn (.tail _ (.head _))
                      · exact defect_lt_of_mem
                          (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                          (by intro y hy; simp only [List.toFinset_cons,
                            Finset.mem_insert]; exact Or.inr (Or.inr hy))
                          (h2.1.resolve_left hA') hA' (.head _)
                    refine hEg _ hlt
                      (by
                        intro F' hF'
                        rcases List.mem_cons.mp hF' with rfl | hF'
                        · exact hSor h2.1
                        · exact hScons (hSor h2.2) _ hF') Δ (projE
                      (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                    simp only [itpEcls]
                    refine List.mem_append.mpr (Or.inr
                      (List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩))
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                  next => cases hin
            | ifThen A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next hDG =>
                  split at hin
                  next hDS =>
                    split at hin
                    next hBD =>
                      split at hin
                      next hABS =>
                        -- gated present piece: convert the antecedent
                        -- through the A-descent, fire, ascend
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4c.impR ?_
                        have hJs : G4c ((itpE p S F (c'' + 1) Γ).ifThen
                            (itpA p S F (c'' + 1) Γ (A₁.ifThen B₁)) :: Δ)
                            ((itpE p S F c'' Γ).ifThen
                              (itpA p S F c'' Γ (A₁.ifThen B₁))) := by
                          refine G4c.impR ?_
                          refine hAd c'' (A₁.ifThen B₁) _ (himp hABS).1
                            (hroomA _)
                            (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                              (hsrcF (c'' + 1) (Nat.le_refl _))) ?_
                          exact fire (G4c.identity_mem (.tail _ (.head _)))
                            (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                              (hsrcF (c'' + 1) (Nat.le_refl _)))
                        refine consume₁ (fire (projE
                          (l := itpEcls p S F (c'' + 1) Γ)
                          (hsrc.weaken _) ?_) hJs)
                          (hEg (B :: Γ) (defect_cons_lt hDS hDG)
                            (hScons hDS) _
                            (G4c.identity_mem (.head _)))
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr
                            ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                        simp only
                        rw [if_neg hDG, if_pos hDS, if_pos hBD, if_pos hABS]
                        exact .head _
                      next => cases hin
                    next hBD =>
                      split at hin
                      next hBDS =>
                        -- fresh piece: ascend the introduced guard,
                        -- fire, descend at the grown context
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4c.impR ?_
                        have hJs : G4c ((itpE p S F (c'' + 2)
                            (B₁.ifThen B :: Γ)).ifThen
                            (itpA p S F (c'' + 2) (B₁.ifThen B :: Γ)
                              (A₁.ifThen B₁)) :: Δ)
                            ((itpE p S F (c'' + 1)
                              (B₁.ifThen B :: Γ)).ifThen
                              (itpA p S F (c'' + 1) (B₁.ifThen B :: Γ)
                                (A₁.ifThen B₁))) := by
                          refine G4c.impR ?_
                          have hE2 : G4c (itpE p S F (c'' + 1)
                              (B₁.ifThen B :: Γ) ::
                              (itpE p S F (c'' + 2)
                                (B₁.ifThen B :: Γ)).ifThen
                              (itpA p S F (c'' + 2) (B₁.ifThen B :: Γ)
                                (A₁.ifThen B₁)) :: Δ)
                              (itpE p S F (c'' + 2)
                                (B₁.ifThen B :: Γ)) :=
                            hEg _ (defect_cons_lt hBDS hBD) (hScons hBDS) _
                              (G4c.identity_mem (.head _))
                          refine hAg _ (defect_cons_lt hBDS hBD)
                            (c'' + 1) (A₁.ifThen B₁) _
                            (himp (hΓS _ hF'Γ)).1 (hScons hBDS)
                            (Nat.le_succ _)
                            hE2 ?_
                          exact fire (G4c.identity_mem
                            (.tail _ (.head _))) hE2
                        refine consume₁ (fire (projE
                          (l := itpEcls p S F (c'' + 1) Γ)
                          (hsrc.weaken _) ?_) hJs)
                          (hEg (B :: Γ) (defect_cons_lt hDS hDG)
                            (hScons hDS) _
                            (G4c.identity_mem (.head _)))
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr
                            ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                        simp only
                        rw [if_neg hDG, if_pos hDS, if_neg hBD,
                          if_pos hBDS]
                        exact .head _
                      next => cases hin
                  next => cases hin
            | somehow A₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next hBG =>
                  split at hin
                  next hBS =>
                    rcases List.mem_append.mp hin with hin | hin
                    · split at hin
                      next hAS =>
                        rcases List.mem_cons.mp hin with rfl | hin'
                        · -- jump conjunct: descend the antecedent
                          refine G4c.impR ?_
                          have hAs : G4c (itpA p S F (c'' + 1) Γ A₁ :: Δ)
                              (itpA p S F c'' Γ A₁) :=
                            hAd c'' A₁ _ (hsome (himp hAS).1) (hroomA _)
                              ((hsrcF (c'' + 1) (Nat.le_refl _)).weaken _)
                              (G4c.identity_mem (.head _))
                          refine consume₁ (fire (projE
                            (l := itpEcls p S F (c'' + 1) Γ)
                            (hsrc.weaken _) ?_) hAs)
                            (hEg (B :: Γ) (defect_cons_lt hBS hBG)
                              (hScons hBS) _
                              (G4c.identity_mem (.head _)))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hBG, if_pos hBS, if_pos hAS]
                          exact List.mem_append.mpr (Or.inl (.head _))
                        · -- γ-head conjunct: cross, descend, re-cross
                          rcases List.mem_singleton.mp hin' with rfl
                          refine G4c.impR ?_
                          have hGs : G4c ((((itpE p S F (c'' + 1) Γ).ifThen
                              (itpA p S F (c'' + 1) Γ
                                A₁.somehow)).somehow) :: Δ)
                              (((itpE p S F c'' Γ).ifThen
                                (itpA p S F c'' Γ A₁.somehow)).somehow) := by
                            refine box_fire
                              (X := itpE p S F (c'' + 1) Γ)
                              (Y := itpA p S F (c'' + 1) Γ A₁.somehow)
                              (G4c.identity_mem (.head _))
                              ((hsrcF (c'' + 1) (Nat.le_refl _)).weaken _)
                              ?_
                            refine G4c.laxR (G4c.impR ?_)
                            refine hAd c'' A₁.somehow _ (himp hAS).1
                              (hroomA _)
                              (weaken_sub (fun ψ h =>
                                .tail _ (.tail _ (.tail _ h)))
                                (hsrcF (c'' + 1) (Nat.le_refl _)))
                              (G4c.identity_mem (.tail _ (.head _)))
                          refine consume₁ (fire (projE
                            (l := itpEcls p S F (c'' + 1) Γ)
                            (hsrc.weaken _) ?_) hGs)
                            (hEg (B :: Γ) (defect_cons_lt hBS hBG)
                              (hScons hBS) _
                              (G4c.identity_mem (.head _)))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hBG, if_pos hBS, if_pos hAS]
                          exact List.mem_append.mpr
                            (Or.inl (.tail _ (.head _)))
                      next => cases hin
                    · -- γ-context conjuncts (ungated)
                      obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                      cases X with
                      | somehow x =>
                          simp only at heq
                          split at heq
                          next => cases heq
                          next hg2 =>
                            injection heq with heq'
                            subst heq'
                            have hxΓ : x ∉ Γ := fun h => hg2 (Or.inl h)
                            have hxS : x ∈ S := by
                              by_contra h
                              exact hg2 (Or.inr h)
                            refine G4c.impR ?_
                            have hGs : G4c ((((itpE p S F (c'' + 2)
                                (x :: Γ)).ifThen
                                (itpA p S F (c'' + 2) (x :: Γ)
                                  A₁.somehow)).somehow) :: Δ)
                                (((itpE p S F (c'' + 1) (x :: Γ)).ifThen
                                  (itpA p S F (c'' + 1) (x :: Γ)
                                    A₁.somehow)).somehow) := by
                              refine G4c.cut
                                (A := (itpE p S F (c'' + 1)
                                  (x :: Γ)).somehow)
                                (projE (l := itpEcls p S F (c'' + 1) Γ)
                                  (hsrc.weaken _) ?_) ?_
                              · simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨x.somehow, hXΓ, ?_⟩))
                                simp only
                                rw [if_neg hg2]
                                exact .head _
                              · refine G4c.laxL (.head _) ?_
                                have hE2 : G4c (itpE p S F (c'' + 1)
                                    (x :: Γ) ::
                                    (itpE p S F (c'' + 1)
                                      (x :: Γ)).somehow ::
                                    (((itpE p S F (c'' + 2)
                                      (x :: Γ)).ifThen
                                      (itpA p S F (c'' + 2) (x :: Γ)
                                        A₁.somehow)).somehow) :: Δ)
                                    (itpE p S F (c'' + 2) (x :: Γ)) :=
                                  hEg _ (defect_cons_lt hxS hxΓ)
                                    (hScons hxS) _
                                    (G4c.identity_mem (.head _))
                                refine box_fire
                                  (X := itpE p S F (c'' + 2) (x :: Γ))
                                  (Y := itpA p S F (c'' + 2) (x :: Γ)
                                    A₁.somehow)
                                  (G4c.identity_mem
                                    (.tail _ (.tail _ (.head _))))
                                  hE2 ?_
                                refine G4c.laxR (G4c.impR ?_)
                                refine hAg (x :: Γ)
                                  (defect_cons_lt hxS hxΓ) (c'' + 1)
                                  A₁.somehow _ (himp (hΓS _ hF'Γ)).1
                                  (hScons hxS)
                                  (Nat.le_succ _) ?_
                                  (G4c.identity_mem (.tail _ (.head _)))
                                exact hEg _ (defect_cons_lt hxS hxΓ)
                                  (hScons hxS) _
                                  (G4c.identity_mem
                                    (.tail _ (.tail _ (.head _))))
                            refine consume₁ (fire (projE
                              (l := itpEcls p S F (c'' + 1) Γ)
                              (hsrc.weaken _) ?_) hGs)
                              (hEg (B :: Γ) (defect_cons_lt hBS hBG)
                                (hScons hBS) _
                                (G4c.identity_mem (.head _)))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                            simp only
                            rw [if_neg hBG, if_pos hBS]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_filterMap.mpr
                                ⟨x.somehow, hXΓ, ?_⟩))
                            simp only
                            rw [if_neg hg2]
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq
                  next => cases hin

/-! ## 3. The tightening is what the bare room can pay — and it is exact -/

/-- **The tightened ascent demand at a defect-paying grown context follows
from the BARE room** — `cascade_boxgoal_pos`'s only budget hypothesis.  This
is the fresh-antecedent guard ascent of PROGRESS §61(f)(i): with the `+3`
constant the same arithmetic is short by exactly 1. -/
theorem tight_ascent_from_room (S : Finset PLLFormula)
    {Γ Γ' : List PLLFormula} (hlt : defect S Γ' < defect S Γ)
    {b : Nat} (h : Room S Γ b) :
    (jumpGoals S).card + 2 +
      defect S Γ' * ((jumpGoals S).card + 2) ≤ b := by
  have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
      defect S Γ' * ((jumpGoals S).card + 2) +
      ((jumpGoals S).card + 2) := by ring
  have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
      defect S Γ * ((jumpGoals S).card + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [Room] at h
  omega

/-- **The `+3` constant is NOT payable from the bare room** at the round-3
witness: at `Sγ`'s room floor `b = 4` with the grown context saturated
(`defect 0`), the `+2` demand holds and the `+3` demand fails.  So the
tightening `easc_tight` establishes is load-bearing for any proof financed by
`cascade_boxgoal_pos`'s own room, not a cosmetic improvement. -/
theorem tight_exact_at_sγ :
    ((jumpGoals Sγ).card + 2 + 0 * ((jumpGoals Sγ).card + 2) ≤ 4) ∧
    ¬ ((jumpGoals Sγ).card + 3 + 0 * ((jumpGoals Sγ).card + 2) ≤ 4) := by
  rw [sγ_jump]
  omega

/-! ## 4. The tower's spine-entry band: depths 0, 1, 2 financed; depth 3 not

The truncation-tower maps the `◯`-goal source's rows to target disjuncts; the
goal-size landings enter the shifted CPS spine (`LedgerS`) at budgets `b`,
`b−1`, `b−2`, … — one budget per same-context γ-crossing.  The entries: -/

/-- Depth 0 (the goal-row landing, any body): entry at the statement's own
target budget, from the bare room — round 3's `ledgerS_entry`, re-exported at
the depth reading. -/
theorem tower_entry_depth0 (S : Finset PLLFormula) (Γ : List PLLFormula)
    (g : PLLFormula) (b : Nat) (h : Room S Γ b) : LedgerS S Γ {g} b :=
  ledgerS_entry S Γ g b h

/-- Depth 1 (the first γ-crossing's goal-size landing): entry one budget down,
from the bare room — the landing body is a γ-clause body, hence a jump goal of
the space. -/
theorem tower_entry_depth1 (S : Finset PLLFormula) (Γ : List PLLFormula)
    {x : PLLFormula} (hx : x ∈ jumpGoals S) (c : Nat)
    (h : Room S Γ (c + 1)) : LedgerS S Γ {x} c := by
  refine Round5.ledgerS_entry_two_below S Γ x hx c ?_
  simp only [Room] at h ⊢
  omega

/-- Depth 2 (the second γ-crossing's landing): entry two budgets down — round
5's `ledgerS_entry_two_below` verbatim, and the last financed depth. -/
theorem tower_entry_depth2 (S : Finset PLLFormula) (Γ : List PLLFormula)
    {x : PLLFormula} (hx : x ∈ jumpGoals S) (c : Nat)
    (h : Room S Γ (c + 2)) : LedgerS S Γ {x} c :=
  Round5.ledgerS_entry_two_below S Γ x hx c h

/-! ### The nested-box witness: a γ-clause with a BOXED body

A second same-context γ-crossing needs a γ-clause whose jump-goal body is
itself `◯`-shaped — then the goal-size landing at level 1 is again a
`◯`-goal and the tower recurses a second budget down.  `S3` is the smallest
such space: the piece-closure of `◯◯(a⊃b) ⊃ c`.  Its γ-clause
`◯(◯(a⊃b)) ⊃ c` has body `◯(a⊃b)`; the nested level's goal-row body `a⊃b`
is NOT a jump goal of `S3` (`jumpGoals S3 = {◯(a⊃b), ◯◯(a⊃b)}`), so its
landing gets no sdiff discount: the entry holds with zero slack at
`c = b − 1` and fails at `c = b − 2`. -/

/-- The nested-box space: pieces of `◯◯(a⊃b) ⊃ c`. -/
def S3 : Finset PLLFormula :=
  { ((prop "a").ifThen (prop "b")).somehow.somehow.ifThen (prop "c"),
    ((prop "a").ifThen (prop "b")).somehow.somehow,
    ((prop "a").ifThen (prop "b")).somehow,
    (prop "a").ifThen (prop "b"),
    prop "a", prop "b", prop "c" }

/-- Everything but the γ-consequent `c`: `defect = 1`, the γ-gate live. -/
def Γ3 : List PLLFormula :=
  [ ((prop "a").ifThen (prop "b")).somehow.somehow.ifThen (prop "c"),
    ((prop "a").ifThen (prop "b")).somehow.somehow,
    ((prop "a").ifThen (prop "b")).somehow,
    (prop "a").ifThen (prop "b"),
    prop "a", prop "b" ]

theorem s3_defect : defect S3 Γ3 = 1 := by decide +kernel

theorem s3_jump : (jumpGoals S3).card = 2 := by decide +kernel

theorem s3_cover : ∀ X ∈ Γ3, X ∈ S3 := by decide +kernel

/-- The γ-clause with the boxed body is present and live (consequent fresh):
the configuration that sustains a second same-context γ-crossing, whose inner
goal-row body is not a jump goal. -/
theorem s3_nested_gamma :
    ((prop "a").ifThen (prop "b")).somehow.somehow.ifThen (prop "c") ∈ Γ3 ∧
    (prop "c" : PLLFormula) ∉ Γ3 ∧
    ((prop "a").ifThen (prop "b")).somehow ∈ jumpGoals S3 ∧
    ((prop "a").ifThen (prop "b")) ∉ jumpGoals S3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem s3_room_iff (c : Nat) : Room S3 Γ3 c ↔ 4 ≤ c := by
  simp only [Room, s3_defect, s3_jump]

/-- The bare room at the floor: every hypothesis of `cascade_boxgoal_pos` is
satisfiable over `S3`/`Γ3` at `b = 4`. -/
theorem s3_room_hi : Room S3 Γ3 4 := (s3_room_iff 4).mpr (Nat.le_refl _)

/-- **The generic-body entry holds with ZERO slack one budget down**: at the
floor `b = 4`, the nested level's goal-row body `a⊃b` enters the spine at
`c = 3 = b − 1` — `7 ≤ 7`. -/
theorem depth1_entry_exact_at_s3 :
    LedgerS S3 Γ3 {(prop "a").ifThen (prop "b")} 3 := by
  have hc : (jumpGoals S3 \ {(prop "a").ifThen (prop "b")}).card = 2 := by
    decide +kernel
  simp only [LedgerS, hc, s3_defect, s3_jump]
  omega

/-- **…and FAILS one budget further down** (`c = 2 = b − 2` — `7 ≤ 6`).  This
is the truncation-tower's exact residue: the second same-context γ-crossing
over a boxed-body γ-clause carries a generic-body goal-row landing at
`c = b − 2`, and no entry finances it.  (For jump-goal bodies the band
reaches `b − 2` and dies at `b − 3`: round 5's `ledgerS_entry_dies_at_sγ`.) -/
theorem no_depth2_entry_at_s3 :
    ¬ LedgerS S3 Γ3 {(prop "a").ifThen (prop "b")} 2 := by
  intro h
  have hc : (jumpGoals S3 \ {(prop "a").ifThen (prop "b")}).card = 2 := by
    decide +kernel
  simp only [LedgerS, hc, s3_defect, s3_jump] at h
  omega

/-! ## 5. The composition, in general form -/

/-- **No side-condition family survives three γ-crossings, even at the
two-below demand.**  Round 5's `no_self_financed_crossing` refuted families
that must re-supply the room at their own level (`hneed : Φ c → Room c`);
the truncation-tower's spine entries demand only `Room (c+2)` (the two-below
entry).  This refutes even that: a family supplied by the bare room, surviving
the per-crossing budget drop, and paying the two-below entry at each level,
cannot exist — the third crossing at `Sγ`'s floor already contradicts
`sγ_room_lo`.  So the financed band of §4 is not an artefact of `LedgerS`:
no ledger family extends it by even one level. -/
theorem no_self_financed_nest
    {Φ : Finset PLLFormula → List PLLFormula → Nat → Prop}
    (hsupply : ∀ S Γ c, 1 ≤ defect S Γ → Room S Γ c → Φ S Γ c)
    (hcross : ∀ S Γ c, Φ S Γ (c + 1) → Φ S Γ c)
    (hneed : ∀ S Γ c, Φ S Γ c → Room S Γ (c + 2)) : False := by
  have h1 : Φ Sγ Γγ 4 := by
    refine hsupply Sγ Γγ 4 ?_ sγ_room_hi
    rw [sγ_defect]
  have h2 : Φ Sγ Γγ 1 :=
    hcross Sγ Γγ 1 (hcross Sγ Γγ 2 (hcross Sγ Γγ 3 h1))
  exact sγ_room_lo (hneed Sγ Γγ 1 h2)

end Round6
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round6.easc_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6.easc_tight

/--
info: 'PLLND.Round6.tight_ascent_from_room' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6.tight_ascent_from_room

/--
info: 'PLLND.Round6.tight_exact_at_sγ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6.tight_exact_at_sγ

/--
info: 'PLLND.Round6.tower_entry_depth1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6.tower_entry_depth1

/--
info: 'PLLND.Round6.depth1_entry_exact_at_s3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6.depth1_entry_exact_at_s3

/--
info: 'PLLND.Round6.no_depth2_entry_at_s3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6.no_depth2_entry_at_s3

/--
info: 'PLLND.Round6.no_self_financed_nest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6.no_self_financed_nest

/-! **The tightened statement, pinned as a type check**: the room constant is
`+ 2`, the only other hypotheses are the coverage invariant and the
`EntryDesc` interface. -/

/--
info: PLLND.Round6.easc_tight (p : String) (S : Finset PLLFormula)
  (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S) (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
  (hA : PLLND.Round6.EntryDesc p S) (fh : ℕ) (Γ : List PLLFormula) (c : ℕ) (Δ : List PLLFormula) :
  (∀ X ∈ Γ, X ∈ S) →
    (PLLND.jumpGoals S).card + 2 + PLLND.defect S Γ * ((PLLND.jumpGoals S).card + 2) ≤ c →
      PLLND.G4c Δ (PLLND.itpE p S fh c Γ) → PLLND.G4c Δ (PLLND.itpE p S fh (c + 1) Γ)
-/
#guard_msgs in
#check PLLND.Round6.easc_tight
