import wip.wlanding
import wip.rungbound
import wip.floor

/-!
# The COLLAPSE THEOREM: every gap-entailing formula entails a rung

Target (the ∃-side of the UI attack):

    hg : ∀ k ≥ 1, φ ⊢ gap k        ⟹        ∃ m, φ ⊢ rnSub m.

The proof is semantic and uniform in `φ` (no one-variable hypothesis).

**Rank.**  In a finite constraint model every world forces some
substituted odd rung (`exists_rung_of_finite`), so
`ρ w := min {k : w ⊩ t(2k+1)}` is well defined; it is antitone along
`Rᵢ` and `w ⊩ t(2k+1) ↔ ρ w ≤ k`.

**Rank descent** (`rho_descent`): if `ρ u = n ≥ 2` then some `v ≥ᵢ u`
has `ρ v = n − 2`.  (`u ⊮ t(2n−1)` forces `u ⊮ t(2n−2)`, and
`t(2n−2) = t(2n−3) ⊃ t(2n−5)` produces the witness.)

**Co-type.**  For a fixed subformula-closed `Φ ∋ ⊥` put

    S v := {B ∈ Φ : some Rₘ-successor of v forces B}.

**Edge surgery** (`surgery`).  Given `u` and a *descent map*
`x : W → W` with, for every `v ≥ᵢ u`,

    v Rᵢ x v,   S (x v) ⊆ S v,   ρ (x v) < ρ u,

add the `Rₘ`-edges `{(z,y) : ∃ v ≥ᵢ u, z Rₘ v ∧ x v Rₘ y}` and close
reflexively-transitively.  The condition `S (x v) ⊆ S v` makes the new
edges *invisible*: every `Rₘ'`-successor forcing a `B ∈ Φ` is matched
by an old `Rₘ`-successor forcing `B` (`surg_cotype`), so all of `Φ`
keeps its truth values (`surg_force`) — and, since `⊥ ∈ Φ`, so does
`◯⊥` and therefore every rung (`surg_rung`).  But now every `v ≥ᵢ u`
`Rₘ'`-sees `x v`, of rank `< ρ u`, so with `j := ρ u − 1 ≥ 1`

    u ⊩' ◯t(2j+1)   while   u ⊮' t(2j+1),

i.e. `gap j` FAILS at `u` — contradicting `hg` (as `u ⊩' φ`).

**The dichotomy.**  Call `v` *rigid* when no `y ≥ᵢ v` with
`S y ⊆ S v` has smaller rank.  If no `v ≥ᵢ u` of rank `ρ u` is rigid,
a descent map exists and the surgery fires.  So above every world of
rank ≥ 2 there is a rigid world of the same rank.

**The pigeonhole.**  Iterating (rank descent, then a rigid world of
that rank) produces `T + 1` rigid worlds `g 0 ≤ᵢ … ≤ᵢ g T` with
`ρ (g a) + 2a = n`, where `T := 2 ^ |Φ|` bounds the number of
co-types.  Two of them have equal co-type, `a < b`; then
`g b ≥ᵢ g a`, `S (g b) ⊆ S (g a)` and `ρ (g b) < ρ (g a)` — `g a` is
not rigid.  Contradiction.

Hence `ρ` is bounded by `2T + 2` at every `φ`-world of every finite
model, and the FMP turns that into `φ ⊢ t(2(2T+2)+1)`.
-/

open PLLFormula
open scoped Classical

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 0. Soundness in point form -/

/-- A one-premiss derivation transports forcing at a world. -/
theorem force_of_deriv1 {C : ConstraintModel} {A B : PLLFormula}
    (h : Deriv [A] B) {w : C.W} (hA : C.force w A) : C.force w B := by
  obtain ⟨d⟩ := h
  refine soundness d C w ?_
  intro ψ hψ
  cases hψ with
  | head => exact hA
  | tail _ h' => cases h'

/-! ## 1. The rung rank of a world -/

section Rank

variable (C : ConstraintModel) (hfin : Finite C.W)

/-- `ρ w = min {k : w ⊩ rnSub (2k+1)}`, well defined in a finite model
by `exists_rung_of_finite`. -/
noncomputable def rho (w : C.W) : Nat :=
  Nat.find (exists_rung_of_finite C hfin w)

variable {C hfin}

theorem rho_spec (w : C.W) : C.force w (rnSub (2 * rho C hfin w + 1)) :=
  Nat.find_spec (exists_rung_of_finite C hfin w)

theorem rho_min {w : C.W} {k : Nat} (h : C.force w (rnSub (2 * k + 1))) :
    rho C hfin w ≤ k :=
  Nat.find_min' (exists_rung_of_finite C hfin w) h

/-- Above the rank the rung is forced: `ρ w ≤ k → w ⊩ t(2k+1)`. -/
theorem force_of_rho_le {w : C.W} {k : Nat} (h : rho C hfin w ≤ k) :
    C.force w (rnSub (2 * k + 1)) :=
  force_of_deriv1 (rungD (oo_le h)) (rho_spec w)

/-- The exact characterisation. -/
theorem rho_le_iff {w : C.W} {k : Nat} :
    rho C hfin w ≤ k ↔ C.force w (rnSub (2 * k + 1)) :=
  ⟨force_of_rho_le, rho_min⟩

/-- Rank is antitone along `Rᵢ`. -/
theorem rho_anti {w v : C.W} (h : C.Ri w v) : rho C hfin v ≤ rho C hfin w :=
  rho_min (C.force_hered h (rho_spec w))

/-- **Rank descent**: from rank `n ≥ 2` one reaches rank `n − 2`. -/
theorem rho_descent {u : C.W} (h2 : 2 ≤ rho C hfin u) :
    ∃ v, C.Ri u v ∧ rho C hfin v = rho C hfin u - 2 := by
  set n := rho C hfin u with hn
  -- `u ⊮ t(2(n-1)+1)`
  have hne : ¬ C.force u (rnSub (2 * (n - 1) + 1)) := by
    intro hf
    have := rho_min (hfin := hfin) hf
    omega
  -- `t(2(n-1)+1) = t(2(n-2)+1) ∨ t(2(n-2)+2)`
  have hsplit : rnSub (2 * (n - 1) + 1)
      = (rnSub (2 * (n - 2) + 1)).or (rnSub (2 * (n - 2) + 2)) := by
    have e : 2 * (n - 1) + 1 = 2 * (n - 2) + 3 := by omega
    rw [e]
    exact rnSub_odd_eq (n - 2)
  have hnev : ¬ C.force u (rnSub (2 * (n - 2) + 2)) := by
    intro hf
    exact hne (by rw [hsplit]; exact Or.inr hf)
  -- `t(2(n-2)+2) = t(2(n-2)+1) ⊃ t(2(n-2)-1)`
  rw [rnSub_even_eq (n - 2)] at hnev
  have hex : ∃ v, C.Ri u v ∧ C.force v (rnSub (2 * (n - 2) + 1)) ∧
      ¬ C.force v (rnSub (2 * (n - 2) - 1)) := by
    by_contra hc
    push Not at hc
    exact hnev (fun v hv hA => hc v hv hA)
  obtain ⟨v, hv, hA, hB⟩ := hex
  refine ⟨v, hv, ?_⟩
  have hle : rho C hfin v ≤ n - 2 := rho_min hA
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · omega
  · -- `n ≥ 3`: `2(n-2)-1 = 2(n-3)+1`, so the rank is not below `n-2`
    have e : 2 * (n - 2) - 1 = 2 * (n - 3) + 1 := by omega
    rw [e] at hB
    have : ¬ rho C hfin v ≤ n - 3 := fun hc => hB (force_of_rho_le hc)
    omega

end Rank

/-! ## 2. Co-types and the surgery model -/

section Surgery

/-- The co-type of `v` relative to a formula set `Φ`: the members of
`Φ` forced at some `Rₘ`-successor of `v`. -/
noncomputable def cotype (C : ConstraintModel) (Φ : Finset PLLFormula)
    (v : C.W) : Finset PLLFormula :=
  Φ.filter (fun B => ∃ y, C.Rm v y ∧ C.force y B)

theorem mem_cotype {C : ConstraintModel} {Φ : Finset PLLFormula} {v : C.W}
    {B : PLLFormula} :
    B ∈ cotype C Φ v ↔ (B ∈ Φ ∧ ∃ y, C.Rm v y ∧ C.force y B) := by
  simp [cotype, Finset.mem_filter]

variable {C : ConstraintModel}

/-- The added `Rₘ`-edges: from every `Rₘ`-predecessor of a world
`v ≥ᵢ u` to every `Rₘ`-successor of the descent target `x v`.  The
`Rᵢ`-conjunct keeps the definition proof-free. -/
def surgN (C : ConstraintModel) (u : C.W) (x : C.W → C.W) :
    C.W → C.W → Prop :=
  fun z y => (∃ v, C.Ri u v ∧ C.Rm z v ∧ C.Rm (x v) y) ∧ C.Ri z y

/-- One step: an old edge or a new one. -/
def surgStep (C : ConstraintModel) (u : C.W) (x : C.W → C.W) :
    C.W → C.W → Prop :=
  fun z y => C.Rm z y ∨ surgN C u x z y

/-- The surgered modal relation. -/
def surgRm (C : ConstraintModel) (u : C.W) (x : C.W → C.W) :
    C.W → C.W → Prop :=
  Relation.ReflTransGen (surgStep C u x)

theorem surgRm_of_Rm {u : C.W} {x : C.W → C.W} {z y : C.W} (h : C.Rm z y) :
    surgRm C u x z y :=
  Relation.ReflTransGen.single (Or.inl h)

theorem surgRm_ri {u : C.W} {x : C.W → C.W} {z y : C.W}
    (h : surgRm C u x z y) : C.Ri z y := by
  induction h with
  | refl => exact C.refl_i z
  | tail _ hbc ih =>
      rcases hbc with hb | hb
      · exact C.trans_i ih (C.sub_mi hb)
      · exact C.trans_i ih hb.2

/-- **The surgered model**: same worlds, same `Rᵢ`, same fallibility and
valuation; `Rₘ` enlarged by the descent edges. -/
@[reducible] def surgery (C : ConstraintModel) (u : C.W) (x : C.W → C.W) :
    ConstraintModel where
  W := C.W
  Ri := C.Ri
  Rm := surgRm C u x
  F := C.F
  V := C.V
  refl_i := C.refl_i
  trans_i := C.trans_i
  refl_m _ := Relation.ReflTransGen.refl
  trans_m h h' := Relation.ReflTransGen.trans h h'
  sub_mi h := surgRm_ri h
  hered_F := C.hered_F
  hered_V := C.hered_V
  full_F := C.full_F

/-- **The new edges are invisible to `Φ`**: every `Rₘ'`-successor
carrying a `Φ`-formula is matched by an old `Rₘ`-successor.  This is
where the descent condition `S (x v) ⊆ S v` is spent. -/
theorem surg_cotype {Φ : Finset PLLFormula} {u : C.W} {x : C.W → C.W}
    (hx : ∀ v, C.Ri u v → cotype C Φ (x v) ⊆ cotype C Φ v) :
    ∀ {z y : C.W}, surgRm C u x z y → cotype C Φ y ⊆ cotype C Φ z := by
  intro z y h
  induction h with
  | refl => exact fun _ hB => hB
  | tail _ hbc ih =>
      refine subset_trans ?_ ih
      rename_i b c _
      intro B hB
      obtain ⟨hBΦ, y', hy', hfy'⟩ := mem_cotype.mp hB
      rcases hbc with hb | ⟨⟨v, hRiuv, hRmbv, hRmxv⟩, -⟩
      · exact mem_cotype.mpr ⟨hBΦ, y', C.trans_m hb hy', hfy'⟩
      · have hxv : B ∈ cotype C Φ (x v) :=
          mem_cotype.mpr ⟨hBΦ, y', C.trans_m hRmxv hy', hfy'⟩
        obtain ⟨-, y'', hy'', hfy''⟩ := mem_cotype.mp (hx v hRiuv hxv)
        exact mem_cotype.mpr ⟨hBΦ, y'', C.trans_m hRmbv hy'', hfy''⟩

/-- The `◯`-clause is unchanged whenever its body is in `Φ` and already
unchanged. -/
theorem surg_box {Φ : Finset PLLFormula} {u : C.W} {x : C.W → C.W}
    (hx : ∀ v, C.Ri u v → cotype C Φ (x v) ⊆ cotype C Φ v)
    {N : PLLFormula} (hN : N ∈ Φ)
    (hNf : ∀ z : C.W, (surgery C u x).force z N ↔ C.force z N) :
    ∀ z : C.W, (surgery C u x).force z N.somehow ↔ C.force z N.somehow := by
  intro z
  constructor
  · intro h v hv
    obtain ⟨y, hy, hfy⟩ := h v hv
    have hmem : N ∈ cotype C Φ y :=
      mem_cotype.mpr ⟨hN, y, C.refl_m y, (hNf y).mp hfy⟩
    obtain ⟨-, y', hy', hfy'⟩ := mem_cotype.mp (surg_cotype hx hy hmem)
    exact ⟨y', hy', hfy'⟩
  · intro h v hv
    obtain ⟨y, hy, hfy⟩ := h v hv
    exact ⟨y, surgRm_of_Rm hy, (hNf y).mpr hfy⟩

/-- **The surgery preserves every `Φ`-formula.** -/
theorem surg_force {Φ : Finset PLLFormula} (hΦ : SubClosed Φ) {u : C.W}
    {x : C.W → C.W}
    (hx : ∀ v, C.Ri u v → cotype C Φ (x v) ⊆ cotype C Φ v) :
    ∀ {B : PLLFormula}, B ∈ Φ → ∀ z : C.W,
      ((surgery C u x).force z B ↔ C.force z B) := by
  intro B
  induction B with
  | prop a => intro _ _; exact Iff.rfl
  | falsePLL => intro _ _; exact Iff.rfl
  | and A B ihA ihB =>
      intro hmem z
      exact and_congr (ihA (hΦ.and_left hmem) z) (ihB (hΦ.and_right hmem) z)
  | or A B ihA ihB =>
      intro hmem z
      exact or_congr (ihA (hΦ.or_left hmem) z) (ihB (hΦ.or_right hmem) z)
  | ifThen A B ihA ihB =>
      intro hmem z
      show (∀ v : C.W, C.Ri z v → (surgery C u x).force v A →
            (surgery C u x).force v B) ↔
        (∀ v : C.W, C.Ri z v → C.force v A → C.force v B)
      constructor
      · intro h v hv hA
        exact (ihB (hΦ.imp_right hmem) v).mp
          (h v hv ((ihA (hΦ.imp_left hmem) v).mpr hA))
      · intro h v hv hA
        exact (ihB (hΦ.imp_right hmem) v).mpr
          (h v hv ((ihA (hΦ.imp_left hmem) v).mp hA))
  | somehow N ih =>
      intro hmem z
      exact surg_box hx (hΦ.lax hmem) (ih (hΦ.lax hmem)) z

/-- `◯⊥` is preserved (only `⊥ ∈ Φ` is needed). -/
theorem surg_oBot {Φ : Finset PLLFormula} (hΦ : SubClosed Φ) {u : C.W}
    {x : C.W → C.W}
    (hx : ∀ v, C.Ri u v → cotype C Φ (x v) ⊆ cotype C Φ v) :
    ∀ z : C.W, ((surgery C u x).force z oBot ↔ C.force z oBot) :=
  surg_box hx hΦ.bot (fun _ => Iff.rfl)

/-- **The surgery preserves every `◯`-free substitution instance** — in
particular every rung.  The `◯⊥` atom is the only place the modality
enters, and it is preserved. -/
theorem surg_embed {Φ : Finset PLLFormula} (hΦ : SubClosed Φ) {u : C.W}
    {x : C.W → C.W}
    (hx : ∀ v, C.Ri u v → cotype C Φ (x v) ⊆ cotype C Φ v) :
    ∀ (A : PLLFormula), boxFree A = true → ∀ z : C.W,
      ((surgery C u x).force z (embed A) ↔ C.force z (embed A)) := by
  intro A
  induction A with
  | prop a =>
      intro _ z
      by_cases ha : a = pv
      · subst ha
        show ((surgery C u x).force z oBot ↔ C.force z oBot)
        exact surg_oBot hΦ hx z
      · have e : embed (PLLFormula.prop a) = PLLFormula.prop a := by
          show (if a = pv then oBot else PLLFormula.prop a) = _
          rw [if_neg ha]
        rw [e]
        exact Iff.rfl
  | falsePLL => intro _ _; exact Iff.rfl
  | and A B ihA ihB =>
      intro hbf z
      have h : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using hbf
      exact and_congr (ihA h.1 z) (ihB h.2 z)
  | or A B ihA ihB =>
      intro hbf z
      have h : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using hbf
      exact or_congr (ihA h.1 z) (ihB h.2 z)
  | ifThen A B ihA ihB =>
      intro hbf z
      have h : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using hbf
      show (∀ v : C.W, C.Ri z v → (surgery C u x).force v (embed A) →
            (surgery C u x).force v (embed B)) ↔
        (∀ v : C.W, C.Ri z v → C.force v (embed A) → C.force v (embed B))
      constructor
      · intro hh v hv hA
        exact (ihB h.2 v).mp (hh v hv ((ihA h.1 v).mpr hA))
      · intro hh v hv hA
        exact (ihB h.2 v).mpr (hh v hv ((ihA h.1 v).mp hA))
  | somehow A _ => intro hbf; exact absurd hbf (by simp [boxFree])

/-- Rungs keep their truth values under the surgery. -/
theorem surg_rung {Φ : Finset PLLFormula} (hΦ : SubClosed Φ) {u : C.W}
    {x : C.W → C.W}
    (hx : ∀ v, C.Ri u v → cotype C Φ (x v) ⊆ cotype C Φ v) (n : Nat) :
    ∀ z : C.W, ((surgery C u x).force z (rnSub n) ↔ C.force z (rnSub n)) :=
  surg_embed hΦ hx (rn n) (rn_boxFree n)

end Surgery

/-! ## 3. The dichotomy: rigid worlds, or a gap failure -/

section Dichotomy

variable {C : ConstraintModel} {hfin : Finite C.W} {Φ : Finset PLLFormula}

/-- `v` is **rigid**: no `Rᵢ`-successor with a smaller co-type has a
smaller rank. -/
def Rigid (C : ConstraintModel) (hfin : Finite C.W) (Φ : Finset PLLFormula)
    (v : C.W) : Prop :=
  ∀ y, C.Ri v y → cotype C Φ y ⊆ cotype C Φ v →
    rho C hfin v ≤ rho C hfin y

/-- **The surgery fires.**  A descent map at `u` makes `gap (ρu − 1)`
fail at `u` in the surgered model: every `v ≥ᵢ u` now `Rₘ'`-sees the
lower-rank world `x v`, so `◯t(2j+1)` holds at `u`, while the rungs are
untouched, so `t(2j+1)` still fails there. -/
theorem gap_fails_of_descent (hΦ : SubClosed Φ) {u : C.W}
    (h2 : 2 ≤ rho C hfin u) {x : C.W → C.W}
    (hxi : ∀ v, C.Ri u v → C.Ri v (x v))
    (hxc : ∀ v, C.Ri u v → cotype C Φ (x v) ⊆ cotype C Φ v)
    (hxr : ∀ v, C.Ri u v → rho C hfin (x v) < rho C hfin u) :
    ¬ (surgery C u x).force u (gap (rho C hfin u - 1)) := by
  intro hgap
  have hchain : (surgery C u x).force u (chainF (rho C hfin u - 1)) := by
    intro v hv
    refine ⟨x v, Relation.ReflTransGen.single
      (Or.inr ⟨⟨v, hv, C.refl_m v, C.refl_m (x v)⟩, hxi v hv⟩), ?_⟩
    refine (surg_rung hΦ hxc _ (x v)).mpr ?_
    have := hxr v hv
    exact force_of_rho_le (by omega)
  have hforced := hgap u (C.refl_i u) hchain
  have hno : ¬ C.force u (rnSub (2 * (rho C hfin u - 1) + 1)) := by
    intro hc
    have := rho_min (hfin := hfin) hc
    omega
  exact hno ((surg_rung hΦ hxc _ u).mp hforced)

/-- **Above every `φ`-world of rank ≥ 2 there is a rigid world of the
same rank.**  Otherwise every `v ≥ᵢ u` admits a co-type-shrinking
descent, the surgery fires, and `hg` is contradicted. -/
theorem exists_rigid (hΦ : SubClosed Φ) {φ : PLLFormula} (hφΦ : φ ∈ Φ)
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) {u : C.W} (hu : C.force u φ)
    (h2 : 2 ≤ rho C hfin u) :
    ∃ v, C.Ri u v ∧ rho C hfin v = rho C hfin u ∧ Rigid C hfin Φ v := by
  by_contra hcon
  push Not at hcon
  -- Build the descent map.
  have hdesc : ∀ v : C.W, ∃ y : C.W, C.Ri u v →
      (C.Ri v y ∧ cotype C Φ y ⊆ cotype C Φ v ∧
        rho C hfin y < rho C hfin u) := by
    intro v
    by_cases hv : C.Ri u v
    · by_cases hrank : rho C hfin v = rho C hfin u
      · have hnr : ¬ Rigid C hfin Φ v := hcon v hv hrank
        have hex : ∃ y, C.Ri v y ∧ cotype C Φ y ⊆ cotype C Φ v ∧
            rho C hfin y < rho C hfin v := by
          by_contra hcc
          push Not at hcc
          exact hnr (fun y hy hcy => by have := hcc y hy hcy; omega)
        obtain ⟨y, hy1, hy2, hy3⟩ := hex
        exact ⟨y, fun _ => ⟨hy1, hy2, by omega⟩⟩
      · refine ⟨v, fun _ => ⟨C.refl_i v, subset_rfl, ?_⟩⟩
        have := rho_anti (hfin := hfin) hv
        omega
    · exact ⟨v, fun h => absurd h hv⟩
  choose x hx using hdesc
  have hxi : ∀ v, C.Ri u v → C.Ri v (x v) := fun v hv => (hx v hv).1
  have hxc : ∀ v, C.Ri u v → cotype C Φ (x v) ⊆ cotype C Φ v :=
    fun v hv => (hx v hv).2.1
  have hxr : ∀ v, C.Ri u v → rho C hfin (x v) < rho C hfin u :=
    fun v hv => (hx v hv).2.2
  refine gap_fails_of_descent hΦ h2 hxi hxc hxr ?_
  -- but `φ` survives the surgery, and `φ ⊢ gap (ρu − 1)`
  obtain ⟨d⟩ := hg (rho C hfin u - 1) (by omega)
  refine soundness d (surgery C u x) u ?_
  intro ψ hψ
  have e : ψ = φ := by
    cases hψ with
    | head => rfl
    | tail _ h' => cases h'
  subst e
  exact (surg_force hΦ hxc hφΦ u).mpr hu

end Dichotomy

/-! ## 4. The pigeonhole: rank is bounded at every `φ`-world -/

section Bound

variable {C : ConstraintModel} {hfin : Finite C.W} {Φ : Finset PLLFormula}

/-- The chain of rigid worlds, built by alternating rank descent with
`exists_rigid`. -/
theorem rigid_chain (hΦ : SubClosed Φ) {φ : PLLFormula} (hφΦ : φ ∈ Φ)
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) {w : C.W} (hw : C.force w φ)
    (T : Nat) (hbig : 2 * T + 2 ≤ rho C hfin w) :
    ∀ i : Nat, i ≤ T → ∃ g : Nat → C.W,
      (∀ a b : Nat, a ≤ b → b ≤ i → C.Ri (g a) (g b)) ∧
      (∀ a : Nat, a ≤ i → C.Ri w (g a) ∧ Rigid C hfin Φ (g a) ∧
        rho C hfin (g a) + 2 * a = rho C hfin w) := by
  intro i
  induction i with
  | zero =>
      intro _
      obtain ⟨v, hv, hrv, hrig⟩ :=
        exists_rigid hΦ hφΦ hg hw (u := w) (by omega)
      refine ⟨fun _ => v, fun a b _ _ => C.refl_i v, fun a ha => ?_⟩
      have : a = 0 := by omega
      subst this
      exact ⟨hv, hrig, by omega⟩
  | succ i ih =>
      intro hi
      obtain ⟨g, hmono, hprop⟩ := ih (by omega)
      obtain ⟨hwg, hrig, hrank⟩ := hprop i (le_refl i)
      -- descend two ranks
      have h2 : 2 ≤ rho C hfin (g i) := by omega
      obtain ⟨u', hu', hru'⟩ := rho_descent (hfin := hfin) h2
      have hwu' : C.Ri w u' := C.trans_i hwg hu'
      have hu'φ : C.force u' φ := C.force_hered hwu' hw
      have hru'2 : rho C hfin u' + 2 * (i + 1) = rho C hfin w := by omega
      obtain ⟨v, hv, hrv, hrigv⟩ :=
        exists_rigid hΦ hφΦ hg hu'φ (u := u') (by omega)
      refine ⟨fun a => if a ≤ i then g a else v, ?_, ?_⟩
      · intro a b hab hbi
        by_cases hb : b ≤ i
        · simp only [if_pos hb, if_pos (show a ≤ i by omega)]
          exact hmono a b hab hb
        · simp only [if_neg hb]
          by_cases ha : a ≤ i
          · simp only [if_pos ha]
            exact C.trans_i (hmono a i ha (le_refl i)) (C.trans_i hu' hv)
          · simp only [if_neg ha]
            exact C.refl_i v
      · intro a ha
        by_cases hai : a ≤ i
        · simp only [if_pos hai]
          exact hprop a hai
        · simp only [if_neg hai]
          have hea : a = i + 1 := by omega
          subst hea
          exact ⟨C.trans_i hwu' hv, hrigv, by omega⟩

/-- **The rank bound.**  At every world of every finite model forcing a
gap-entailing `φ`, the rung rank is below `2·2^|Φ| + 2`. -/
theorem rho_bounded (hΦ : SubClosed Φ) {φ : PLLFormula} (hφΦ : φ ∈ Φ)
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) {w : C.W} (hw : C.force w φ) :
    rho C hfin w < 2 * 2 ^ Φ.card + 2 := by
  by_contra hcon
  push Not at hcon
  set T := 2 ^ Φ.card with hT
  obtain ⟨g, hmono, hprop⟩ :=
    rigid_chain hΦ hφΦ hg hw T (by omega) T (le_refl T)
  have hmaps : ∀ a ∈ Finset.range (T + 1), cotype C Φ (g a) ∈ Φ.powerset := by
    intro a _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hcard : (Φ.powerset).card < (Finset.range (T + 1)).card := by
    rw [Finset.card_powerset, Finset.card_range]
    omega
  obtain ⟨a, ha, b, hb, hab, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  -- order the pair
  have key : ∀ p q : Nat, p < q → q ≤ T → cotype C Φ (g p) = cotype C Φ (g q) →
      False := by
    intro p q hpq hqT he
    obtain ⟨-, hrigp, hrp⟩ := hprop p (by omega)
    obtain ⟨-, -, hrq⟩ := hprop q hqT
    have hle := hrigp (g q) (hmono p q (by omega) hqT) (by rw [← he])
    omega
  rcases Nat.lt_or_ge a b with h | h
  · exact key a b h (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) heq
  · exact key b a (by omega)
      (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) heq.symm

end Bound

/-! ## 5. The collapse theorem -/

/-- Deduction: a failed entailment yields a finite countermodel world. -/
theorem countermodel_of_not_deriv {A B : PLLFormula} (h : ¬ Deriv [A] B) :
    ∃ (C : ConstraintModel) (_ : Finite C.W) (v : C.W),
      C.force v A ∧ ¬ C.force v B := by
  have hthm : ¬ Deriv [] (A.ifThen B) := by
    intro hd
    exact h (Deriv.impElim (hd.rename (by simp)) (Deriv.iden (.head _)))
  have hnv : ¬ ∀ (C : ConstraintModel), Finite C.W → ∀ w : C.W,
      C.force w (A.ifThen B) := fun hv => hthm (finite_model_property.mpr hv)
  push Not at hnv
  obtain ⟨C, hfin, w, hw⟩ := hnv
  have hex : ∃ v : C.W, C.Ri w v ∧ C.force v A ∧ ¬ C.force v B := by
    by_contra hc
    push Not at hc
    exact hw (fun v hv hA => hc v hv hA)
  obtain ⟨v, -, hA, hB⟩ := hex
  exact ⟨C, hfin, v, hA, hB⟩

/-- **THE COLLAPSE THEOREM.**  Every formula entailing the whole gap
antichain entails a substituted Rieger–Nishimura rung.  No hypothesis on
the atoms of `φ`: one variable, many, or none. -/
theorem collapse {φ : PLLFormula} (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) :
    ∃ m, Deriv [φ] (rnSub m) := by
  classical
  set Φ : Finset PLLFormula := insert PLLFormula.falsePLL (subF φ) with hΦdef
  have hΦ : SubClosed Φ := subClosed_insert_bot_subF φ
  have hφΦ : φ ∈ Φ := Finset.mem_insert_of_mem (self_mem_subF φ)
  set M : Nat := 2 * 2 ^ Φ.card + 2 with hM
  refine ⟨2 * M + 1, ?_⟩
  by_contra hno
  obtain ⟨C, hfin, v, hA, hB⟩ := countermodel_of_not_deriv hno
  have hrho : M < rho C hfin v := by
    by_contra hc
    exact hB (force_of_rho_le (by omega))
  have := rho_bounded (hfin := hfin) hΦ hφΦ hg hA
  omega

/-- **The `∃`-side obstruction schema is VACUOUS.**  Any gap-entailing
`φ` entails the variable-free `Ufam m ∈ L`, so `no_post_interp_schema`
cannot be instantiated at the gap antichain.  (Companion to
`pre_interp_schema_vacuous`, which closed the `∀`-side.) -/
theorem post_interp_schema_vacuous {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) :
    ¬ (∀ ψ, atomFree ψ = true → (∀ k, 1 ≤ k → Deriv [ψ] (gap k)) →
        ¬ Deriv [φ] ψ) := by
  obtain ⟨m, hm⟩ := collapse hg
  exact rung_kills hg m hm

/-- The positive form: every gap-entailing `φ` HAS a variable-free
gap-entailing consequence. -/
theorem post_interp_exists {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k)) :
    ∃ ψ, atomFree ψ = true ∧ (∀ k, 1 ≤ k → Deriv [ψ] (gap k)) ∧
      Deriv [φ] ψ := by
  obtain ⟨m, hm⟩ := collapse hg
  exact rung_blocks_schema hg m hm

/-- **The landing ideal is the union of the principal ideals of the
rung companions**: `φ ⊢ g k` for every `k ≥ 1` iff `φ ⊢ U m` for some
`m`, where `U m = g 1 ∧ … ∧ g (m+1) ∧ t m` is variable-free.  (The
converse direction is `Ufam_in_L`.) -/
theorem L_eq_union_Ufam {φ : PLLFormula} :
    (∀ k, 1 ≤ k → Deriv [φ] (gap k)) ↔ ∃ m, Deriv [φ] (Ufam m) := by
  constructor
  · intro hg
    obtain ⟨m, hm⟩ := collapse hg
    exact ⟨m, Deriv.andIntro (gmeet_of_hg hg m) hm⟩
  · rintro ⟨m, hm⟩ k hk
    exact Deriv.cutHead hm (Ufam_in_L m hk)

/-- **The `∃`-side schema's hypotheses are jointly contradictory** — the
exact shape of `no_post_interp_schema`'s premisses. -/
theorem no_post_interp_hyps {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k))
    (hL : ∀ χ, atomFree χ = true → (∀ k, 1 ≤ k → Deriv [χ] (gap k)) →
      ¬ Deriv [φ] χ) : False :=
  post_interp_schema_vacuous hg hL

/-! ## 6. Cross-check: the rung index cannot be uniform

`gap_no_glb` (wip/floor.lean) says the antichain has no greatest lower
bound.  Under `collapse` a uniform bound `M` on the rung index would
make `U M`-below-ness a greatest element of `L`; the `Wit` family
refutes it directly.  So the exponential dependence of the bound
`2·2^|Φ| + 2` on `φ` is not an artefact of the proof: SOME growth is
forced. -/

/-- **The collapse index is not uniform in `φ`.**  Witness: `Wit M`
entails every gap and is forced at plain-ladder world `M+3`, while a
rung of index `≤ M` has truth set inside `[0, M]`. -/
theorem collapse_bound_not_uniform :
    ¬ ∃ M : Nat, ∀ φ : PLLFormula, (∀ k, 1 ≤ k → Deriv [φ] (gap k)) →
      ∃ m, m ≤ M ∧ Deriv [φ] (rnSub m) := by
  rintro ⟨M, hM⟩
  obtain ⟨m, hmM, hd⟩ := hM (Wit M) (fun _ hk => Wit_below_all_gaps M hk)
  obtain ⟨d⟩ := hd
  have hs := soundness d ladder.cm (some (M + 3)) (fun ψ hψ => by
    have e : ψ = Wit M := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact Wit_force_high M)
  have hb := rungMem_bound
    ((sat_rung m (M + 3)).mp ((ladder.transfer (rn_boxFree m) (M + 3)).mp hs))
  omega

/-! ## Non-vacuity: the hypothesis IS satisfiable

`Ufam 5 = g 1 ∧ … ∧ g 6 ∧ t 5` entails every gap (`Ufam_in_L`), so the
collapse theorem is applied to a real formula here — and the rung it
produces is not `⊥` (`Ufam 5 ⊬ ⊥`, since `t 5` is consistent). -/

example : ∃ m, Deriv [Ufam 5] (rnSub m) := collapse (fun _ hk => Ufam_in_L 5 hk)

/-! ## Axiom audit — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.rho_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rho_descent

/-- info: 'PLLND.RNEmbed.surg_force' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surg_force

/-- info: 'PLLND.RNEmbed.surg_rung' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surg_rung

/-- info: 'PLLND.RNEmbed.gap_fails_of_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_fails_of_descent

/-- info: 'PLLND.RNEmbed.exists_rigid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_rigid

/-- info: 'PLLND.RNEmbed.rigid_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rigid_chain

/-- info: 'PLLND.RNEmbed.rho_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rho_bounded

/-- info: 'PLLND.RNEmbed.countermodel_of_not_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countermodel_of_not_deriv

/-- info: 'PLLND.RNEmbed.collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms collapse

/-- info: 'PLLND.RNEmbed.post_interp_schema_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_interp_schema_vacuous

/-- info: 'PLLND.RNEmbed.post_interp_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_interp_exists

/-- info: 'PLLND.RNEmbed.L_eq_union_Ufam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms L_eq_union_Ufam

/-- info: 'PLLND.RNEmbed.no_post_interp_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_post_interp_hyps

/-- info: 'PLLND.RNEmbed.collapse_bound_not_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms collapse_bound_not_uniform

end RNEmbed
end PLLND
