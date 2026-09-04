import wip.witness

/-!
# A lower, uniformly-indexed family inside the landing ideal `L`

`L := {χ variable-free : ∀ k ≥ 1, χ ⊢ gap k}` is where a uniform
post-interpolant of any gap-entailing `φ` must live, so `hL` of
`no_post_interp_schema` asks a candidate `φ` to entail NO element of `L`.
The bigger and the LOWER the known part of `L`, the stronger that filter:
`L` is down-closed, so a lower `χ ∈ L` is entailed by more formulas and
therefore kills more candidates.

`wip/witness.lean` gives two elements: `rnSub 3` and
`w15 = gap 1 ∧ rnSub 6` (the latter needing the descent-inside-the-box
argument for its `k = 2` case).  Here is an ℕ-indexed family, obtained
with no descent argument at all:

    Vf n := (gap 1 ∧ … ∧ gap (n+1)) ∧ rnSub (2n+4)

— below `gap 1 … gap (n+1)` by projection, and below `gap k` for
`k ≥ n+2` because the EVEN rung `rnSub (2n+4) = rnSub (2(n+1)+2)` sits
under every odd rung `rnSub (2k+1)` with `k ≥ n+2` (`eo_le`), which in
turn sits under `gap k` (`rung_le_gap`).

`Vf 0 = gap 1 ∧ rnSub 4` is strictly lower than `w15 = gap 1 ∧ rnSub 6`
in the sense that matters for the filter: it uses the even rung two
levels down.  Every `Vf n` is variable-free (`Vf_atomFree`).
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-- `Gmeet m ⊢ gap j` for every `1 ≤ j ≤ m + 1`. -/
theorem Gmeet_le_gap : ∀ (m j : Nat), 1 ≤ j → j ≤ m + 1 →
    Deriv [Gmeet m] (gap j) := by
  intro m
  induction m with
  | zero =>
      intro j h1 h2
      have : j = 1 := by omega
      subst this
      exact Deriv.iden (.head _)
  | succ m ih =>
      intro j h1 h2
      rcases Nat.lt_or_ge j (m + 2) with hlt | hge
      · exact Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _)))
          (ih j h1 (by omega))
      · have : j = m + 2 := by omega
        subst this
        exact Deriv.andElim2 (Deriv.iden (.head _))

/-- **The `V` family**: `Vf n = gap 1 ∧ … ∧ gap (n+1) ∧ rnSub (2n+4)`. -/
def Vf (n : Nat) : PLLFormula := (Gmeet n).and (rnSub (2 * n + 4))

/-- `Gmeet` is variable-free. -/
theorem Gmeet_atomFree : ∀ n, atomFree (Gmeet n) = true := by
  intro n
  induction n with
  | zero => exact gap_atomFree 1
  | succ n ih =>
      show (atomFree (Gmeet n) && atomFree (gap (n + 2))) = true
      rw [ih, gap_atomFree]
      rfl

theorem Vf_atomFree (n : Nat) : atomFree (Vf n) = true := by
  show (atomFree (Gmeet n) && atomFree (rnSub (2 * n + 4))) = true
  rw [Gmeet_atomFree, rnSub_atomFree]
  rfl

/-- **`Vf n ∈ L`**: every member of the family is below the WHOLE gap
antichain.  No descent-inside-the-box argument is needed. -/
theorem Vf_in_L (n : Nat) : ∀ {k : Nat}, 1 ≤ k → Deriv [Vf n] (gap k) := by
  intro k hk
  rcases Nat.lt_or_ge k (n + 2) with hlt | hge
  · -- k ≤ n+1: project onto the meet
    exact Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _)))
      (Gmeet_le_gap n k hk (by omega))
  · -- k ≥ n+2: the even rung climbs to the odd rung, which climbs to gap k
    refine Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) ?_
    have hr : Deriv [rnSub (2 * (n + 1) + 2)] (rnSub (2 * k + 1)) :=
      rungD (eo_le (show n + 1 + 1 ≤ k from by omega))
    have he : 2 * (n + 1) + 2 = 2 * n + 4 := by omega
    rw [he] at hr
    exact Deriv.cutHead hr (rung_le_gap k)

/-- The floor `rnSub 3` of `wip/uiObstruct.lean` is under `Vf n`?  No —
the two are incomparable, so `Vf` genuinely enlarges the known part of
`L`.  What IS immediate: `Vf n` is entailed by `w`-style elements, since
`w15 ⊢ gap k` for all `k` and `w15 ⊢ rnSub 6`.  Recorded for `n = 1`. -/
theorem w15_le_Vf1 : Deriv [wC 1] (Vf 1) :=
  Deriv.andIntro
    (Deriv.andIntro (w15_below_all_gaps (le_refl 1))
      (w15_below_all_gaps (show 1 ≤ 2 from by omega)))
    (Deriv.andElim2 (Deriv.iden (.head _)))

/-! ## The instance filter, justified

The mechanical hunt's most productive filter is: *discard `φ` when some
variable-free instance `φ[p↦χ]` is a PLL theorem.*  Here is why that is
sound — and, more, why EVERY variable-free instance of a candidate must
itself lie in `L`. -/

/-- **Every variable-free instance of a gap-entailing `φ` lies in `L`.**
Substitution preserves derivability and fixes the (variable-free) gaps. -/
theorem inst_in_L {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) (χ : PLLFormula) :
    ∀ {k : Nat}, 1 ≤ k → Deriv [substP pv χ φ] (gap k) := by
  intro k hk
  have h := Deriv.substP' (Γ := [φ]) (φ := gap k) pv χ (hg k hk)
  rwa [show [φ].map (substP pv χ) = [substP pv χ φ] from rfl,
       substP_atomFree pv χ (gap k) (gap_atomFree k)] at h

/-- **No variable-free instance of a candidate can be a theorem.**  If
`⊢ φ[p↦χ]` and `φ` entails every gap, then `⊢ gap 2`, which collapses
`gap 2` to `⊤` against `gap_not_top`.  This is the filter that killed
every hand-designed near-miss of the 2026-08-04 sweep. -/
theorem no_theorem_instance {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) (χ : PLLFormula)
    (hthm : Deriv [] (substP pv χ φ)) : False := by
  have h2 : Deriv [] (gap 2) :=
    Deriv.cutHead hthm (inst_in_L hg χ (show 1 ≤ 2 from by omega))
  exact gap_not_top (le_refl 2)
    ⟨h2.rename (by simp), dTop⟩

/-- The `hL` reading: if `φ` entails one of its own variable-free
instances, it cannot be an `∃`-side UI witness — either `hg` or `hL`
fails.  (Here `hg` is assumed, so `hL` is what dies.) -/
theorem self_instance_kills {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) (χ : PLLFormula)
    (ha : atomFree (substP pv χ φ) = true)
    (hself : Deriv [φ] (substP pv χ φ)) :
    ¬ (∀ ψ, atomFree ψ = true → (∀ k, 1 ≤ k → Deriv [ψ] (gap k)) →
        ¬ Deriv [φ] ψ) := by
  intro hL
  exact hL (substP pv χ φ) ha (fun k hk => inst_in_L hg χ hk) hself

/-! ## The rung filter, justified in full generality

The mechanical sweep's dominant kill is *"φ entails some rung"*.  The
brief justified it only for the odd rungs and only informally.  Here it
is, as a theorem, for EVERY rung index and every `φ`. -/

/-- Every rung sits under every sufficiently high odd rung. -/
theorem rung_high (m k : Nat) (h : m ≤ k) : rungLe m (2 * k + 1) = true := by
  obtain ⟨a, ha | ha⟩ := Nat.even_or_odd' m
  · subst ha
    cases a with
    | zero => exact bot_le _
    | succ b =>
        have e : 2 * (b + 1) = 2 * b + 2 := by omega
        rw [e]
        exact eo_le (by omega)
  · subst ha
    exact oo_le (by omega)

/-- `rnSub m ⊢ gap k` for every `k ≥ m`. -/
theorem rung_le_gap_high (m k : Nat) (h : m ≤ k) : Deriv [rnSub m] (gap k) :=
  Deriv.cutHead (rungD (rung_high m k h)) (rung_le_gap k)

/-- A gap-entailing `φ` entails every partial meet. -/
theorem gmeet_of_hg {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) : ∀ m, Deriv [φ] (Gmeet m) := by
  intro m
  induction m with
  | zero => exact hg 1 (le_refl 1)
  | succ m ih => exact Deriv.andIntro ih (hg (m + 2) (by omega))

/-- **The rung companion**: `U m = gap 1 ∧ … ∧ gap (m+1) ∧ rnSub m`. -/
def Ufam (m : Nat) : PLLFormula := (Gmeet m).and (rnSub m)

theorem Ufam_atomFree (m : Nat) : atomFree (Ufam m) = true := by
  show (atomFree (Gmeet m) && atomFree (rnSub m)) = true
  rw [Gmeet_atomFree, rnSub_atomFree]
  rfl

/-- **`U m ∈ L`**: below `gap 1 … gap (m+1)` by projection, below
`gap k` for `k ≥ m` by `rung_le_gap_high`.  The two ranges overlap, so
the whole antichain is covered. -/
theorem Ufam_in_L (m : Nat) : ∀ {k : Nat}, 1 ≤ k → Deriv [Ufam m] (gap k) := by
  intro k hk
  rcases Nat.lt_or_ge k m with hlt | hge
  · exact Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _)))
      (Gmeet_le_gap m k hk (by omega))
  · exact Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _)))
      (rung_le_gap_high m k hge)

/-- **The rung filter, as a theorem.**  If `φ` entails every gap AND
entails a single rung `rnSub m` — of ANY index, odd or even — then `φ`
entails the variable-free `U m ∈ L`, so `hL` fails and `φ` is not an
`∃`-side UI witness.  Every candidate the 2026-08-04 size-≤8 sweep found
entailing `gap 1` was killed exactly here. -/
theorem rung_kills {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) (m : Nat)
    (hm : Deriv [φ] (rnSub m)) :
    ¬ (∀ ψ, atomFree ψ = true → (∀ k, 1 ≤ k → Deriv [ψ] (gap k)) →
        ¬ Deriv [φ] ψ) := by
  intro hL
  exact hL (Ufam m) (Ufam_atomFree m) (fun _ hk => Ufam_in_L m hk)
    (Deriv.andIntro (gmeet_of_hg hg m) hm)

/-- Packaged against the obstruction schema: a `φ` entailing every gap
and any one rung HAS a uniform post-interpolant candidate in `L`, so the
schema `no_post_interp_schema` cannot be applied to it. -/
theorem rung_blocks_schema {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) (m : Nat)
    (hm : Deriv [φ] (rnSub m)) :
    ∃ ψ, atomFree ψ = true ∧ (∀ k, 1 ≤ k → Deriv [ψ] (gap k)) ∧
      Deriv [φ] ψ :=
  ⟨Ufam m, Ufam_atomFree m, fun _ hk => Ufam_in_L m hk,
    Deriv.andIntro (gmeet_of_hg hg m) hm⟩

/-! ## Axiom audits -/

/-- info: 'PLLND.RNEmbed.Vf_in_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vf_in_L

/-- info: 'PLLND.RNEmbed.Vf_atomFree' does not depend on any axioms -/
#guard_msgs in
#print axioms Vf_atomFree

/-- info: 'PLLND.RNEmbed.w15_le_Vf1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms w15_le_Vf1

/-- info: 'PLLND.RNEmbed.inst_in_L' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inst_in_L

/-- info: 'PLLND.RNEmbed.no_theorem_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_theorem_instance

/-- info: 'PLLND.RNEmbed.self_instance_kills' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms self_instance_kills

/-- info: 'PLLND.RNEmbed.Ufam_in_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ufam_in_L

/-- info: 'PLLND.RNEmbed.rung_kills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rung_kills

/-- info: 'PLLND.RNEmbed.rung_blocks_schema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rung_blocks_schema

/-! ## Integration addendum: the sweep's frontier fact, hand-pinned

The frontier run discovered a proof of `gap 2 ⊢ gap 1` (2,934 search
nodes).  Pinned here by hand.  Consequence for the picture: the gap
family is an antichain only from `k = 2` (`gap_incomparable` requires
`2 ≤ k` on the failing side), and `g 1` sits STRICTLY below `g 2`
(strictness from `gap_incomparable` at `j = 1, k = 2`).  Whether
`g k ⊢ g 1` for `k ≥ 3` is OPEN (`g 1 ⊬ g k` is already pinned). -/

/-- **`gap 2 ⊢ gap 1`.**  Assume `c 1 = ◯t3`; ascend inside the box to
`c 2 = ◯t5`; `gap 2` yields `t5 = t3 ∨ t4`; the `t3`-branch closes, and
the `t4`-branch descends inside the box through `t4 = t3 ⊃ t1`, landing
on `t1 = ◯⊥` (definitionally `⊥.somehow`, so the box output IS the
rung), which climbs back to `t3` by rung order. -/
theorem gap_two_le_one : Deriv [gap 2] (gap 1) := by
  show Deriv [gap 2] ((chainF 1).ifThen (rnSub 3))
  refine Deriv.impIntro ?_
  -- [chainF 1, gap 2] ⊢ rnSub 3
  have hc2 : Deriv [chainF 1, gap 2] (chainF 2) := by
    refine dSomehowElim (Deriv.iden (.head _)) ?_
    exact dSomehowIntro
      (Deriv.cutHead (Deriv.iden (.head _))
        (rungD (oo_le (show 1 ≤ 2 from by omega))))
  have ht5 : Deriv [chainF 1, gap 2] (rnSub 5) :=
    Deriv.impElim (Deriv.iden (.tail _ (.head _))) hc2
  have hsplit : Deriv [chainF 1, gap 2] ((rnSub 3).or (rnSub 4)) := by
    rw [← (rnSub_odd_eq 1 : rnSub 5 = (rnSub 3).or (rnSub 4))]
    exact ht5
  refine Deriv.orElim hsplit (Deriv.iden (.head _)) ?_
  -- [rnSub 4, chainF 1, gap 2] ⊢ rnSub 3
  have h41 : Deriv [rnSub 4] ((rnSub 3).ifThen (rnSub 1)) := by
    rw [← (rnSub_even_eq 1 : rnSub 4 = (rnSub 3).ifThen (rnSub 1))]
    exact Deriv.iden (.head _)
  have ht4 : Deriv [rnSub 4, chainF 1, gap 2] ((rnSub 3).ifThen (rnSub 1)) :=
    Deriv.cutHead (Deriv.iden (.head _)) h41
  have hbox : Deriv [rnSub 4, chainF 1, gap 2] (rnSub 1) := by
    refine dSomehowElim (Deriv.iden (.tail _ (.head _))) ?_
    exact Deriv.impElim
      (Deriv.rename (fun χ hχ => .tail _ hχ) ht4) (Deriv.iden (.head _))
  exact Deriv.cutHead hbox (rungD (oo_le (show 0 ≤ 1 from by omega)))

/-- `g 1 ⊬ g 2` (instance of `gap_incomparable`): the climb is strict,
`g 1 < g 2`. -/
theorem gap_one_not_le_two : ¬ Deriv [gap 1] (gap 2) :=
  gap_incomparable (le_refl 2) (by omega)

/-- info: 'PLLND.RNEmbed.gap_two_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_two_le_one

/-- info: 'PLLND.RNEmbed.gap_one_not_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_one_not_le_two

end RNEmbed
end PLLND
