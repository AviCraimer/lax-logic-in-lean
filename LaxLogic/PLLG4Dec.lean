import LaxLogic.PLLG4Set
import LaxLogic.PLLG4Space

/-!
# Termination C: the decider — F&M Theorem 2.8

Backward proof search for the cumulative set calculus `G4s`: the
working context is carried as a **list** (computable iteration), the
loop-check keys sequents by the context's `toFin`, and a **fuel**
parameter makes the recursion structural.  The gate admits only
sequents inside the finite space of `PLLG4Space.lean`, so fuel
`|seqEnumF \ V| + 1` always suffices: every recursive call inserts the
current set-sequent into `V`, and gated sequents live in `seqEnumF`.

* `search_sound'` — success yields a `G4s` derivation (visited hits
  return `false`, so success never uses them).
* `search_complete'` — a *minimal-height* `G4sh` derivation searches
  successfully: strong induction on height, carrying the invariant
  that every visited sequent has minimal height strictly above the
  current subderivation, so a premise can never collide with the
  visited set.  The minimal height is `Nat.find` over height
  existence, **decided by the height-bounded decider `G4sh.dec`**
  (`PLLG4Set.lean`) — no `Classical.propDecidable`.

Chained through `G4c.iff_setFin` and `G4c.equiv_tm`:
`Decidable (G4c Γ C)` and **decidability of PLL provability**.

**Axiom audit (re-measured 2026-07-18, after the choice-scrub).**
`search`, `seqEnumF` and the whole decision chain are built on the
choice-free `Finset` toolkit (`PLLFinsetKit.lean`), the atoms/space
layer of `PLLG4Space.lean` is choice-free, and the minimal-height
induction runs on `G4sh.dec` — so

  `G4c_iff_search`, `decidableG4c`, `decidablePLL`
  all audit `[propext, Quot.sound]`.

The only residually choice-tainted results here are the legacy
`toFinset`-phrased wrappers `search_sound`, `search_complete` and
`height_bound` (and `seqEnum`/`seqEnum_card`), whose *statements*
mention `List.toFinset`/`Finset.powerset`/`Finset.product` — Mathlib
bodies that embed `Classical.choice` (`Multiset.dedup`'s
permutation-invariance lemma; `Multiset.toList` is choice outright).
`#print axioms` walks the bodies of statement constants, so those
statements cannot audit choice-free however they are proved; the clean
chain uses the primed forms.
-/

open PLLFormula

namespace PLLND

-- Within this file every `DecidableEq (Finset _)` resolves to the
-- choice-free `finDecEq`, so the statements below stay clean and all
-- occurrences agree definitionally.
attribute [local instance 2000] finDecEq

/-- The finite ambient space of set-sequents (legacy form; statement
constants `Finset.powerset`/`×ˢ` are choice-tainted in Mathlib).  The
clean chain uses `seqEnumF`. -/
def seqEnum (as : Finset String) (W : Nat) :
    Finset (Finset PLLFormula × PLLFormula) :=
  (enum as W).powerset ×ˢ enum as W

/-- The finite ambient space of set-sequents, choice-free. -/
def seqEnumF (as : Finset String) (W : Nat) :
    Finset (Finset PLLFormula × PLLFormula) :=
  finPairMap Prod.mk (finPow (enum as W)) (enum as W)

theorem mem_seqEnumF {as : Finset String} {W : Nat}
    {p : Finset PLLFormula × PLLFormula} :
    p ∈ seqEnumF as W ↔ p.1 ⊆ enum as W ∧ p.2 ∈ enum as W := by
  constructor
  · intro hp
    obtain ⟨a, ha, b, hb, hab⟩ := mem_finPairMap.mp hp
    cases hab
    exact ⟨mem_finPow.mp ha, hb⟩
  · intro ⟨h₁, h₂⟩
    exact mem_finPairMap.mpr ⟨p.1, mem_finPow.mpr h₁, p.2, h₂, rfl⟩

theorem seqEnumF_card_le (as : Finset String) (W : Nat) :
    (seqEnumF as W).card ≤ 2 ^ (enum as W).card * (enum as W).card := by
  exact Nat.le_trans (card_finPairMap_le _ _ _)
    (Nat.mul_le_mul_right _ (card_finPow_le _))

/-- The two spaces are extensionally equal (the proof mentions the
tainted Mathlib constants, so only the wrappers use it). -/
theorem seqEnumF_eq_seqEnum (as : Finset String) (W : Nat) :
    seqEnumF as W = seqEnum as W :=
  subAntisymm
    (fun p hp => by
      obtain ⟨h₁, h₂⟩ := mem_seqEnumF.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr h₁, h₂⟩)
    (fun p hp => by
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
      exact mem_seqEnumF.mpr ⟨Finset.mem_powerset.mp h₁, h₂⟩)

private theorem orl {a b : Bool} (h : a = true) : (a || b) = true := by
  simp [h]

private theorem orr {a b : Bool} (h : b = true) : (a || b) = true := by
  simp [h]

private theorem andI {a b : Bool} (h₁ : a = true) (h₂ : b = true) :
    (a && b) = true := by simp [h₁, h₂]

private theorem anyI {α : Type _} {l : List α} {p : α → Bool} {x : α}
    (hx : x ∈ l) (h : p x = true) : l.any p = true := by
  simp only [List.any_eq_true]
  exact ⟨x, hx, h⟩

/-- Backward proof search for `G4s`. -/
def search (W : Nat) (as : Finset String) :
    Nat → Finset (Finset PLLFormula × PLLFormula) →
    List PLLFormula → PLLFormula → Bool
  | 0, _, _, _ => false
  | fuel + 1, V, Γ, C =>
    if (∀ F ∈ Γ, InSpace W as F) ∧ InSpace W as C ∧ (toFin Γ, C) ∉ V then
      decide (falsePLL ∈ Γ)
      || (match C with
          | .prop a => decide (PLLFormula.prop a ∈ Γ)
          | .falsePLL => false
          | .and A B =>
              search W as fuel (insert (toFin Γ, C) V) Γ A
              && search W as fuel (insert (toFin Γ, C) V) Γ B
          | .or A B =>
              search W as fuel (insert (toFin Γ, C) V) Γ A
              || search W as fuel (insert (toFin Γ, C) V) Γ B
          | .ifThen A B =>
              search W as fuel (insert (toFin Γ, C) V) (A :: Γ) B
          | .somehow A =>
              search W as fuel (insert (toFin Γ, C) V) Γ A
              || Γ.any fun X => match X with
                  | .somehow x =>
                      search W as fuel (insert (toFin Γ, C) V) (x :: Γ) C
                  | _ => false)
      || Γ.any fun F => match F with
          | .and A B =>
              search W as fuel (insert (toFin Γ, C) V) (A :: B :: Γ) C
          | .or A B =>
              search W as fuel (insert (toFin Γ, C) V) (A :: Γ) C
              && search W as fuel (insert (toFin Γ, C) V) (B :: Γ) C
          | .ifThen (.prop a) B =>
              decide (PLLFormula.prop a ∈ Γ)
              && search W as fuel (insert (toFin Γ, C) V) (B :: Γ) C
          | .ifThen (.and A B) D =>
              search W as fuel (insert (toFin Γ, C) V)
                (A.ifThen (B.ifThen D) :: Γ) C
          | .ifThen (.or A B) D =>
              search W as fuel (insert (toFin Γ, C) V)
                (A.ifThen D :: B.ifThen D :: Γ) C
          | .ifThen (.ifThen A B) D =>
              search W as fuel (insert (toFin Γ, C) V)
                (B.ifThen D :: Γ) (A.ifThen B)
              && search W as fuel (insert (toFin Γ, C) V) (D :: Γ) C
          | .ifThen (.somehow A) B =>
              (search W as fuel (insert (toFin Γ, C) V) Γ A
                && search W as fuel (insert (toFin Γ, C) V) (B :: Γ) C)
              || Γ.any fun X => match X with
                  | .somehow x =>
                      search W as fuel (insert (toFin Γ, C) V)
                        (x :: Γ) A.somehow
                      && search W as fuel (insert (toFin Γ, C) V)
                        (B :: Γ) C
                  | _ => false
          | _ => false
    else false

/-- **Soundness of the search, with the height payload**: success at
fuel `n` yields a derivation of height at most `n` (choice-free `toFin`
form). -/
theorem search_sound' (W : Nat) (as : Finset String) :
    ∀ (fuel : Nat) (V : Finset (Finset PLLFormula × PLLFormula))
    (Γ : List PLLFormula) (C : PLLFormula),
    search W as fuel V Γ C = true → G4sh fuel (toFin Γ) C := by
  intro fuel
  induction fuel with
  | zero => intro V Γ C h; simp [search] at h
  | succ fuel ih =>
    intro V Γ C h
    simp only [search] at h
    split at h
    case isFalse => simp at h
    case isTrue hg =>
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    rcases h with (hbot | hC) | ⟨F, hFmem, hF⟩
    · exact .botL (mem_toFin.mpr hbot)
    · cases C with
      | prop a =>
          simp only [decide_eq_true_eq] at hC
          exact .init (mem_toFin.mpr hC)
      | falsePLL => simp at hC
      | and A B =>
          simp only [Bool.and_eq_true] at hC
          exact .andR (ih _ _ _ hC.1) (ih _ _ _ hC.2)
      | or A B =>
          simp only [Bool.or_eq_true] at hC
          rcases hC with hs | hs
          · exact .orR1 (ih _ _ _ hs)
          · exact .orR2 (ih _ _ _ hs)
      | ifThen A B =>
          have d := ih _ _ _ hC
          rw [toFin_cons] at d
          exact .impR d
      | somehow A =>
          simp only [Bool.or_eq_true, List.any_eq_true] at hC
          rcases hC with hs | ⟨X, hXmem, hX⟩
          · exact .laxR (ih _ _ _ hs)
          · cases X with
            | somehow x =>
                have d := ih _ _ _ hX
                rw [toFin_cons] at d
                exact .laxL (mem_toFin.mpr hXmem) d
            | prop a => simp at hX
            | falsePLL => simp at hX
            | and _ _ => simp at hX
            | or _ _ => simp at hX
            | ifThen _ _ => simp at hX
    · have hFΓ := mem_toFin.mpr hFmem
      cases F with
      | prop a => simp at hF
      | falsePLL => simp at hF
      | and A B =>
          have d := ih _ _ _ hF
          rw [toFin_cons, toFin_cons] at d
          exact .andL hFΓ d
      | or A B =>
          simp only [Bool.and_eq_true] at hF
          have h₁ := ih _ _ _ hF.1
          have h₂ := ih _ _ _ hF.2
          rw [toFin_cons] at h₁ h₂
          exact .orL hFΓ h₁ h₂
      | somehow A => simp at hF
      | ifThen A' B =>
          cases A' with
          | prop a =>
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hF
              have d := ih _ _ _ hF.2
              rw [toFin_cons] at d
              exact .impLProp hFΓ (mem_toFin.mpr hF.1) d
          | falsePLL => simp at hF
          | and A₁ B₁ =>
              have d := ih _ _ _ hF
              rw [toFin_cons] at d
              exact .impLAnd hFΓ d
          | or A₁ B₁ =>
              have d := ih _ _ _ hF
              rw [toFin_cons, toFin_cons] at d
              exact .impLOr hFΓ d
          | ifThen A₁ B₁ =>
              simp only [Bool.and_eq_true] at hF
              have h₁ := ih _ _ _ hF.1
              have h₂ := ih _ _ _ hF.2
              rw [toFin_cons] at h₁ h₂
              exact .impLImp hFΓ h₁ h₂
          | somehow A₁ =>
              simp only [Bool.or_eq_true, Bool.and_eq_true,
                List.any_eq_true] at hF
              rcases hF with ⟨hs₁, hs₂⟩ | ⟨X, hXmem, hX⟩
              · have h₁ := ih _ _ _ hs₁
                have h₂ := ih _ _ _ hs₂
                rw [toFin_cons] at h₂
                exact .impLLax hFΓ h₁ h₂
              · cases X with
                | somehow x =>
                    simp only [Bool.and_eq_true] at hX
                    have h₁ := ih _ _ _ hX.1
                    have h₂ := ih _ _ _ hX.2
                    rw [toFin_cons] at h₁ h₂
                    exact .impLLaxLax hFΓ (mem_toFin.mpr hXmem) h₁ h₂
                | prop a => simp at hX
                | falsePLL => simp at hX
                | and _ _ => simp at hX
                | or _ _ => simp at hX
                | ifThen _ _ => simp at hX

/-- Legacy `toFinset` form, derived; statement-tainted through
`List.toFinset`. -/
theorem search_sound (W : Nat) (as : Finset String) :
    ∀ (fuel : Nat) (V : Finset (Finset PLLFormula × PLLFormula))
    (Γ : List PLLFormula) (C : PLLFormula),
    search W as fuel V Γ C = true → G4sh fuel Γ.toFinset C := by
  intro fuel V Γ C h
  rw [← toFin_eq_toFinset]
  exact search_sound' W as fuel V Γ C h

/-- **Completeness of the search** for minimal-height derivations,
carrying the visited-set invariant (choice-free `toFin` form; all
`Nat.find`s below run on the height-bounded decider `G4sh.dec`). -/
theorem search_complete' (W : Nat) (as : Finset String) :
    ∀ (n : Nat) (Γ : List PLLFormula) (C : PLLFormula) (fuel : Nat)
    (V : Finset (Finset PLLFormula × PLLFormula)),
    G4sh n (toFin Γ) C →
    (∀ m, G4sh m (toFin Γ) C → n ≤ m) →
    (∀ F ∈ Γ, InSpace W as F) → InSpace W as C →
    (∀ T ∈ V, ∀ m, G4sh m T.1 T.2 → n < m) →
    (finSdiff (seqEnumF as W) V).card < fuel →
    search W as fuel V Γ C = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro Γ C fuel V d hmin hctx hgoal hV hfuel
  cases fuel with
  | zero => exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel =>
  have hSmem : (toFin Γ, C) ∈ seqEnumF as W :=
    mem_seqEnumF.mpr
      ⟨fun F hF => InSpace.mem_enum W (hctx F (mem_toFin.mp hF)),
       InSpace.mem_enum W hgoal⟩
  have hnotV : (toFin Γ, C) ∉ V := fun hin => by
    have := hV _ hin n d
    omega
  have hfuel' :
      (finSdiff (seqEnumF as W) (insert (toFin Γ, C) V)).card < fuel := by
    have := card_finSdiff_insert_lt hSmem hnotV
    omega
  have mkInv : ∀ {pm : Nat}, pm < n →
      ∀ T ∈ insert (toFin Γ, C) V, ∀ m, G4sh m T.1 T.2 → pm < m := by
    intro pm hpm T hT m dm
    rcases Finset.mem_insert.mp hT with heq | hT'
    · subst heq
      exact lt_of_lt_of_le hpm (hmin m dm)
    · exact lt_trans hpm (hV T hT' m dm)
  simp only [search]
  rw [if_pos ⟨hctx, hgoal, hnotV⟩]
  cases d with
  | init h =>
      refine orl (orr ?_)
      exact decide_eq_true (mem_toFin.mp h)
  | botL h =>
      refine orl (orl ?_)
      exact decide_eq_true (mem_toFin.mp h)
  | @andR np _ A B dpa dpb =>
      have hexA : ∃ m, G4sh m (toFin Γ) A := ⟨np, dpa⟩
      have hexB : ∃ m, G4sh m (toFin Γ) B := ⟨np, dpb⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa; omega) Γ A fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        hctx hgoal.and_left
        (mkInv (by have := Nat.find_min' hexA dpa; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb; omega) Γ B fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        hctx hgoal.and_right
        (mkInv (by have := Nat.find_min' hexB dpb; omega)) hfuel'
      refine orl (orr ?_)
      exact andI hsA hsB
  | @orR1 np _ A B dp =>
      have hex : ∃ m, G4sh m (toFin Γ) A := ⟨np, dp⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp; omega) Γ A fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx hgoal.or_left
        (mkInv (by have := Nat.find_min' hex dp; omega)) hfuel'
      refine orl (orr ?_)
      exact orl hs
  | @orR2 np _ A B dp =>
      have hex : ∃ m, G4sh m (toFin Γ) B := ⟨np, dp⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp; omega) Γ B fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx hgoal.or_right
        (mkInv (by have := Nat.find_min' hex dp; omega)) hfuel'
      refine orl (orr ?_)
      exact orr hs
  | @impR np _ A B dp =>
      have dp' : G4sh np (toFin (A :: Γ)) B := by
        rw [toFin_cons]; exact dp
      have hex : ∃ m, G4sh m (toFin (A :: Γ)) B := ⟨np, dp'⟩
      have hctx' : ∀ F ∈ A :: Γ, InSpace W as F := by
        intro F hF
        rcases List.mem_cons.mp hF with rfl | hF'
        · exact hgoal.imp_left
        · exact hctx F hF'
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega) (A :: Γ) B fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx' hgoal.imp_right
        (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orl (orr ?_)
      exact hs
  | @laxR np _ A dp =>
      have hex : ∃ m, G4sh m (toFin Γ) A := ⟨np, dp⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp; omega) Γ A fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx hgoal.box
        (mkInv (by have := Nat.find_min' hex dp; omega)) hfuel'
      refine orl (orr ?_)
      exact orl hs
  | @laxL np _ A B h dp =>
      have dp' : G4sh np (toFin (A :: Γ)) B.somehow := by
        rw [toFin_cons]; exact dp
      have hex : ∃ m, G4sh m (toFin (A :: Γ)) B.somehow := ⟨np, dp'⟩
      have hctx' : ∀ F ∈ A :: Γ, InSpace W as F := by
        intro F hF
        rcases List.mem_cons.mp hF with rfl | hF'
        · exact (hctx _ (mem_toFin.mp h)).box
        · exact hctx F hF'
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega) (A :: Γ) B.somehow fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx' hgoal
        (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orl (orr ?_)
      refine orr ?_
      exact anyI (mem_toFin.mp h) hs
  | @andL np _ A B _ h dp =>
      have dp' : G4sh np (toFin (A :: B :: Γ)) C := by
        rw [toFin_cons, toFin_cons]; exact dp
      have hex : ∃ m, G4sh m (toFin (A :: B :: Γ)) C := ⟨np, dp'⟩
      have hctx' : ∀ F ∈ A :: B :: Γ, InSpace W as F := by
        intro F hF
        rcases List.mem_cons.mp hF with rfl | hF'
        · exact (hctx _ (mem_toFin.mp h)).and_left
        rcases List.mem_cons.mp hF' with rfl | hF''
        · exact (hctx _ (mem_toFin.mp h)).and_right
        · exact hctx F hF''
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega) (A :: B :: Γ) C fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx' hgoal
        (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orr ?_
      exact anyI (mem_toFin.mp h) hs
  | @orL np _ A B _ h dpa dpb =>
      have dpa' : G4sh np (toFin (A :: Γ)) C := by
        rw [toFin_cons]; exact dpa
      have dpb' : G4sh np (toFin (B :: Γ)) C := by
        rw [toFin_cons]; exact dpb
      have hexA : ∃ m, G4sh m (toFin (A :: Γ)) C := ⟨np, dpa'⟩
      have hexB : ∃ m, G4sh m (toFin (B :: Γ)) C := ⟨np, dpb'⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa'; omega) (A :: Γ) C fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).or_left
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexA dpa'; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb'; omega) (B :: Γ) C fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).or_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexB dpb'; omega)) hfuel'
      refine orr ?_
      exact anyI (mem_toFin.mp h) (andI hsA hsB)
  | @impLProp np _ a B _ h ha dp =>
      have dp' : G4sh np (toFin (B :: Γ)) C := by
        rw [toFin_cons]; exact dp
      have hex : ∃ m, G4sh m (toFin (B :: Γ)) C := ⟨np, dp'⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega) (B :: Γ) C fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).imp_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orr ?_
      refine anyI (mem_toFin.mp h) ?_
      exact andI (decide_eq_true (mem_toFin.mp ha)) hs
  | @impLAnd np _ A B D _ h dp =>
      have dp' : G4sh np (toFin (A.ifThen (B.ifThen D) :: Γ)) C := by
        rw [toFin_cons]; exact dp
      have hex : ∃ m, G4sh m (toFin (A.ifThen (B.ifThen D) :: Γ)) C :=
        ⟨np, dp'⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega)
        (A.ifThen (B.ifThen D) :: Γ) C fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).impAnd_piece
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orr ?_
      exact anyI (mem_toFin.mp h) hs
  | @impLOr np _ A B D _ h dp =>
      have dp' : G4sh np (toFin (A.ifThen D :: B.ifThen D :: Γ)) C := by
        rw [toFin_cons, toFin_cons]; exact dp
      have hex : ∃ m, G4sh m (toFin (A.ifThen D :: B.ifThen D :: Γ)) C :=
        ⟨np, dp'⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega)
        (A.ifThen D :: B.ifThen D :: Γ) C fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).impOr_piece₁
            rcases List.mem_cons.mp hF' with rfl | hF''
            · exact (hctx _ (mem_toFin.mp h)).impOr_piece₂
            · exact hctx F hF'')
        hgoal (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orr ?_
      exact anyI (mem_toFin.mp h) hs
  | @impLImp np _ A B D _ h dpa dpb =>
      have dpa' : G4sh np (toFin (B.ifThen D :: Γ)) (A.ifThen B) := by
        rw [toFin_cons]; exact dpa
      have dpb' : G4sh np (toFin (D :: Γ)) C := by
        rw [toFin_cons]; exact dpb
      have hexA : ∃ m, G4sh m (toFin (B.ifThen D :: Γ)) (A.ifThen B) :=
        ⟨np, dpa'⟩
      have hexB : ∃ m, G4sh m (toFin (D :: Γ)) C := ⟨np, dpb'⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa'; omega)
        (B.ifThen D :: Γ) (A.ifThen B) fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).impImp_piece
            · exact hctx F hF')
        (hctx _ (mem_toFin.mp h)).imp_left
        (mkInv (by have := Nat.find_min' hexA dpa'; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb'; omega) (D :: Γ) C fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).imp_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexB dpb'; omega)) hfuel'
      refine orr ?_
      exact anyI (mem_toFin.mp h) (andI hsA hsB)
  | @impLLax np _ A B _ h dpa dpb =>
      have dpb' : G4sh np (toFin (B :: Γ)) C := by
        rw [toFin_cons]; exact dpb
      have hexA : ∃ m, G4sh m (toFin Γ) A := ⟨np, dpa⟩
      have hexB : ∃ m, G4sh m (toFin (B :: Γ)) C := ⟨np, dpb'⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa; omega) Γ A fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        hctx ((hctx _ (mem_toFin.mp h)).imp_left).box
        (mkInv (by have := Nat.find_min' hexA dpa; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb'; omega) (B :: Γ) C fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).imp_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexB dpb'; omega)) hfuel'
      refine orr ?_
      refine anyI (mem_toFin.mp h) ?_
      exact orl (andI hsA hsB)
  | @impLLaxLax np _ A B X _ h hX dpa dpb =>
      have dpa' : G4sh np (toFin (X :: Γ)) A.somehow := by
        rw [toFin_cons]; exact dpa
      have dpb' : G4sh np (toFin (B :: Γ)) C := by
        rw [toFin_cons]; exact dpb
      have hexA : ∃ m, G4sh m (toFin (X :: Γ)) A.somehow := ⟨np, dpa'⟩
      have hexB : ∃ m, G4sh m (toFin (B :: Γ)) C := ⟨np, dpb'⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa'; omega) (X :: Γ) A.somehow fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp hX)).box
            · exact hctx F hF')
        (hctx _ (mem_toFin.mp h)).imp_left
        (mkInv (by have := Nat.find_min' hexA dpa'; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb'; omega) (B :: Γ) C fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (mem_toFin.mp h)).imp_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexB dpb'; omega)) hfuel'
      refine orr ?_
      refine anyI (mem_toFin.mp h) ?_
      refine orr ?_
      exact anyI (mem_toFin.mp hX) (andI hsA hsB)

/-- Legacy `toFinset`/`\`-phrased form, derived; statement-tainted
through `List.toFinset` and `seqEnum`. -/
theorem search_complete (W : Nat) (as : Finset String) :
    ∀ (n : Nat) (Γ : List PLLFormula) (C : PLLFormula) (fuel : Nat)
    (V : Finset (Finset PLLFormula × PLLFormula)),
    G4sh n Γ.toFinset C →
    (∀ m, G4sh m Γ.toFinset C → n ≤ m) →
    (∀ F ∈ Γ, InSpace W as F) → InSpace W as C →
    (∀ T ∈ V, ∀ m, G4sh m T.1 T.2 → n < m) →
    (seqEnum as W \ V).card < fuel →
    search W as fuel V Γ C = true := by
  intro n Γ C fuel V d hmin hctx hgoal hV hfuel
  refine search_complete' W as n Γ C fuel V ?_ ?_ hctx hgoal hV ?_
  · rw [toFin_eq_toFinset]; exact d
  · intro m dm
    exact hmin m (toFin_eq_toFinset Γ ▸ dm)
  · rwa [finSdiff_eq_sdiff, seqEnumF_eq_seqEnum]

/-! ### The decision procedure, packaged -/

/-- Weight bound of a list of formulas. -/
def listWeight (l : List PLLFormula) : Nat :=
  l.foldr (fun φ m => max φ.weight m) 0

theorem le_listWeight {φ : PLLFormula} {l : List PLLFormula} (h : φ ∈ l) :
    φ.weight ≤ listWeight l := by
  induction l with
  | nil => cases h
  | cons x l ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact le_trans (ih h') (Nat.le_max_right _ _)

/-- Atom alphabet of a list of formulas. -/
def listAtoms (l : List PLLFormula) : Finset String :=
  l.foldr (fun φ s => finUnion φ.atoms s) ∅

theorem subset_listAtoms {φ : PLLFormula} {l : List PLLFormula} (h : φ ∈ l) :
    φ.atoms ⊆ listAtoms l := by
  induction l with
  | nil => cases h
  | cons x l ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact fun a ha => mem_finUnion.mpr (.inl ha)
      · exact fun a ha => mem_finUnion.mpr (.inr (ih h' ha))

theorem seqEnum_card (as : Finset String) (W : Nat) :
    (seqEnum as W).card = 2 ^ (enum as W).card * (enum as W).card := by
  rw [seqEnum, Finset.card_product, Finset.card_powerset]

/-- Fuel sufficient for the whole space of the end-sequent, computed
arithmetically (the powerset is never constructed). -/
def decideFuel (Γ : List PLLFormula) (C : PLLFormula) : Nat :=
  2 ^ (enum (listAtoms (C :: Γ)) (listWeight (C :: Γ))).card
    * (enum (listAtoms (C :: Γ)) (listWeight (C :: Γ))).card + 1

/-- **The search decides `G4c`.** -/
theorem G4c_iff_search {Γ : List PLLFormula} {C : PLLFormula} :
    G4c Γ C ↔
    search (listWeight (C :: Γ)) (listAtoms (C :: Γ))
      (decideFuel Γ C) ∅ Γ C = true := by
  constructor
  · intro h
    obtain ⟨n₀, d₀⟩ := G4c.iff_setFin.mp h
    have hex : ∃ m, G4sh m (toFin Γ) C := ⟨n₀, d₀⟩
    refine search_complete' _ _ (Nat.find hex) Γ C _ ∅ (Nat.find_spec hex)
      (fun m dm => Nat.find_min' hex dm) ?_ ?_
      (fun T hT => absurd hT (Finset.notMem_empty T)) ?_
    · intro F hF
      exact ⟨le_listWeight (List.mem_cons_of_mem _ hF),
        subset_listAtoms (List.mem_cons_of_mem _ hF)⟩
    · exact ⟨le_listWeight (List.mem_cons_self),
        subset_listAtoms (List.mem_cons_self)⟩
    · rw [finSdiff_empty]
      exact Nat.lt_succ_of_le (seqEnumF_card_le _ _)
  · intro h
    exact G4c.iff_setFin.mpr ⟨_, search_sound' _ _ _ _ _ _ h⟩

/-- **The pigeonhole height bound, for free from the decider
round-trip**: every derivable sequent has a derivation of height at
most `decideFuel`.  This is what lets the Pitts interpolants be
defined by plain fuel recursion — no termination order on sequents is
needed, which is precisely the ingredient Iemhoff's method lacked for
retention calculi.  (Statement-tainted through `List.toFinset`; the
choice-free content is `search_sound'` composed with
`G4c_iff_search`.) -/
theorem height_bound {Γ : List PLLFormula} {C : PLLFormula}
    (h : G4c Γ C) : G4sh (decideFuel Γ C) Γ.toFinset C :=
  search_sound _ _ _ _ _ _ (G4c_iff_search.mp h)

/-- `G4c` — hence PLL — is decidable. -/
instance decidableG4c (Γ : List PLLFormula) (C : PLLFormula) :
    Decidable (G4c Γ C) :=
  decidable_of_iff _ G4c_iff_search.symm

/-- **F&M Theorem 2.8, decidability**: inhabitation of the PLL term
calculus is decidable — via the terminating, loop-checked backward
search for the complete calculus G4iLL″. -/
instance decidablePLL (Γ : List PLLFormula) (φ : PLLFormula) :
    Decidable (Nonempty (Tm Γ φ)) :=
  decidable_of_iff _ G4c.equiv_tm

-- ◯ admits no escape: the constraint stays.
/-- info: false -/
#guard_msgs in
#eval decide (G4c [(prop "p").somehow] (prop "p"))

-- …but the unit is there.
/-- info: true -/
#guard_msgs in
#eval decide (G4c [prop "p"] (prop "p").somehow)

/-- info: true -/
#guard_msgs in
#eval decide (G4c [] (falsePLL.ifThen falsePLL))

/-- info: false -/
#guard_msgs in
#eval decide (G4c [] (prop "p"))

-- The decision chain is choice-free: the executable layer runs on the
-- toolkit of `PLLFinsetKit.lean` and the minimal-height induction on
-- the decider `G4sh.dec`.  See the module docstring for the two legacy
-- statement-tainted wrappers.
/-- info: 'PLLND.G4c_iff_search' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms G4c_iff_search

/-- info: 'PLLND.decidableG4c' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decidableG4c

/-- info: 'PLLND.decidablePLL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decidablePLL

end PLLND
