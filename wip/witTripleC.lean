import LaxLogic.PLLSemUIHenkin
import wip.canonFinC

/-!
# `WitTripleC` — the witnessing triple over the confluent canonical model

Branch `ui-confluence`.  The amalgamation (Lemma 5.4 shape) re-indexed onto
the confluent finite canonical model `canonFinC`, with the ◯-cases resolved
by BARE POSSIBILITY.  Everything below is sorry-free; the single remaining
obligation is the displayed Prop `MforthResidue`, and all consumers take it
as a hypothesis.

## The design (2026-07-25 revision)

* **Budgets** are the original Litak–Visser slope: base link at `2d`,
  reservoir at `2d+1`, `d = canonDepthC Δ`.  (The earlier `crankC`
  recalibration to `(d, d+1)` was a miscalibration: the slope pays for
  re-financing BOTH links of a triple out of one spend, not for the crank
  of ◯.  With slope 2 the ledger closes exactly: a strict `Rₘ`-descent
  hands `Z (2d−1)`, and the successor needs `2d′+1 ≤ 2(d−1)+1 = 2d−1`.)
* **Triples are an inductive with a `top` constructor**: fallible escapes
  land on canonical worlds validating `⊥` paired with fallible M-worlds.
  Every step lemma and the truth lemma are trivial there.  (2026-07-27:
  the classical K-side edge `hik : k' Rᵢ k` is reinstated — see the
  constructor docstring.)
* **Same-trace ◯-moves are matched REFLEXIVELY**: `RmC` is reflexive, so an
  M-move `m ⟶Rₘ u` whose canonical theory does not grow is answered by
  `Δ′ = Δ`; the base link for `(·, u)` is regenerated from the reservoir by
  `B.iback` along `Rᵢ m′ u` (using `Rₘ ⊆ Rᵢ`), at cost exactly 1 — which
  the reservoir's surplus covers.  The previously recorded wall
  ("same-theory + ◯ is unfinanceable") dissolves: same-theory M-side moves
  are free, and same-theory K-side ◯-moves never arise (a K-side ◯-move is
  taken only towards a witness for a formula the theory lacks, so the trace
  strictly grows).
* **The truth lemma's ◯-forward direction is definitional**: `RmC`'s second
  clause says every validated formula of an `Rₘ`-successor is
  ◯-anticipated at the source, so an amalgam row-witness for `ψ` puts
  `◯ψ` in `val` outright.  The ◯-backward direction uses bare possibility
  in `K` plus the WITNESS-form m-clause `B.mwit` (financed by strict
  growth), never a transfer.  Only `K` need be confluent; `M` is
  arbitrary.  (2026-07-26: the input format is `LayeredBisimWit` — the
  E-form with `mforth` weakened to choice-freedom, which is all the
  development ever consumed.)

## The residue

`MforthResidue` is the ONE open case: an M-side ◯-move at a proper triple
where the reservoir's `iback`-partner strictly grows the trace while the
base's `mback`-partner keeps it — two K-side partners for `u`, one with the
right trace one level short, one at the right level with the wrong trace.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU
open SetDeriv

variable {p : String} {K M : ConstraintModel}

/-! ## The K-side trace is backed (confluent soundness) -/

/-- The trace `traceT K cl k` is `Backed` when `K` is mutually confluent. -/
theorem trace_backed {K : ConstraintModel} (hK : MutuallyConfluent K)
    {cl : Finset PLLFormula} (k : K.W) : Backed cl (traceT K cl k) := by
  refine ⟨{φ | K.force k φ}, ?_, ?_, ?_⟩
  · rintro χ ⟨Γ, hΓ, hd⟩
    exact derivU_sound hd hK k hΓ
  · intro A B hAB
    exact hAB
  · intro φ hφcl
    rw [mem_traceT_val]
    exact ⟨fun h => h.2, fun h => ⟨hφcl, h⟩⟩

/-- The **confluent** descriptions functor: the trace as a world of
`canonFinC` (a backed `WC cl`). -/
noncomputable def traceC {K : ConstraintModel} (hK : MutuallyConfluent K)
    (cl : Finset PLLFormula) (k : K.W) : (canonFinC cl).W :=
  ⟨traceT K cl k, traceT_maxIn K cl k, trace_backed hK k⟩

/-- **The confluent `trace_mforth`**: a `K`-`Rₘ`-move gives the canonical
`RmC`-move between traces.  `val` moves by persistence; the `obInv`
(`boxOf`) clause is bare possibility — `force κ χ` with `k Rₘ κ` yields
`force k (◯χ)` directly (and `◯◯ → ◯` on boxes via `trans_m`). -/
theorem traceC_mforth {K : ConstraintModel} (hK : MutuallyConfluent K)
    {cl : Finset PLLFormula} {k κ : K.W} (h : K.Rm k κ) :
    (canonFinC cl).Rm (traceC hK cl k) (traceC hK cl κ) := by
  refine ⟨fun χ hχ => ?_, fun χ hbcl hχ => ?_⟩
  · obtain ⟨hcl, hf⟩ := mem_traceT_val.mp hχ
    exact mem_traceT_val.mpr ⟨hcl, K.force_hered (K.sub_mi h) hf⟩
  · obtain ⟨hcl, hf⟩ := mem_traceT_val.mp hχ
    refine mem_traceT_val.mpr ⟨hbcl, ?_⟩
    cases χ with
    | somehow χ' =>
        rw [boxOf_somehow, force_somehow_iff_of_confluent hK]
        rw [force_somehow_iff_of_confluent hK] at hf
        obtain ⟨w', hw', hfw'⟩ := hf
        exact ⟨w', K.trans_m h hw', hfw'⟩
    | prop a =>
        show K.force k (PLLFormula.somehow (PLLFormula.prop a))
        rw [force_somehow_iff_of_confluent hK]; exact ⟨κ, h, hf⟩
    | falsePLL =>
        show K.force k (PLLFormula.somehow PLLFormula.falsePLL)
        rw [force_somehow_iff_of_confluent hK]; exact ⟨κ, h, hf⟩
    | and a b =>
        show K.force k (PLLFormula.somehow (PLLFormula.and a b))
        rw [force_somehow_iff_of_confluent hK]; exact ⟨κ, h, hf⟩
    | or a b =>
        show K.force k (PLLFormula.somehow (PLLFormula.or a b))
        rw [force_somehow_iff_of_confluent hK]; exact ⟨κ, h, hf⟩
    | ifThen a b =>
        show K.force k (PLLFormula.somehow (PLLFormula.ifThen a b))
        rw [force_somehow_iff_of_confluent hK]; exact ⟨κ, h, hf⟩

#print axioms trace_backed
#print axioms traceC_mforth

/-! ## Depth and the canonical top -/

/-- Depth in the confluent finite model (same formula as `canonDepth`). -/
def canonDepthC (cl : Finset PLLFormula) (Δ : (canonFinC cl).W) : Nat :=
  cl.card - Δ.1.val.card

theorem canonDepthC_le (cl : Finset PLLFormula) (Δ : (canonFinC cl).W) :
    canonDepthC cl Δ ≤ cl.card := Nat.sub_le _ _

/-- Strict `val`-growth strictly drops the confluent depth. -/
theorem canonDepthC_lt {cl : Finset PLLFormula} {Δ Δ' : (canonFinC cl).W}
    (hsub : Δ.1.val ⊆ Δ'.1.val) (hne : Δ.1.val ≠ Δ'.1.val) :
    canonDepthC cl Δ' < canonDepthC cl Δ := by
  have hlt : Δ.1.val.card < Δ'.1.val.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hle : Δ'.1.val.card ≤ cl.card := Finset.card_le_card Δ'.2.1.2.1.1
  unfold canonDepthC
  omega

/-- A world not validating `⊥` has positive depth (`⊥ ∈ cl`). -/
theorem canonDepthC_pos {cl : Finset PLLFormula} (hcl : SubClosed cl)
    {Δ : (canonFinC cl).W} (hbot : PLLFormula.falsePLL ∉ Δ.1.val) :
    1 ≤ canonDepthC cl Δ := by
  have hne : Δ.1.val ≠ cl := fun h => hbot (by rw [h]; exact hcl.bot)
  have hlt : Δ.1.val.card < cl.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Δ.2.1.2.1.1, hne⟩)
  unfold canonDepthC
  omega

/-- **The confluent canonical top**: everything validated, backed by the
full theory.  Where fallible escapes land. -/
def canonTopC (cl : Finset PLLFormula) : WC cl :=
  ⟨⟨cl, ∅, ∅⟩,
   ⟨cons_of_empty_falm rfl rfl,
    ⟨subset_rfl, Finset.empty_subset _, Finset.empty_subset _⟩,
    fun _φ hφ => .inl hφ⟩,
   ⟨Set.univ, fun _χ _ => Set.mem_univ _, fun A _B _ => .inl (Set.mem_univ A),
    fun φ hφ => ⟨fun _ => Set.mem_univ φ, fun _ => hφ⟩⟩⟩

/-- Every canonical world sits below the top along `Rᵢ`. -/
theorem ri_canonTopC {cl : Finset PLLFormula} (Δ : (canonFinC cl).W) :
    (canonFinC cl).Ri Δ (canonTopC cl) :=
  fun _χ hχ => Δ.2.1.2.1.1 hχ

/-! ## The witness form of the layered link -/

/-- **The witness form** — `LayeredBisimE` with the `mforth` clause
weakened to CHOICE-FREEDOM: the K-side ◯-obligation is demanded only
for SOME row-witness of a given formula, not for every row-move.  This
is exactly what the development consumes: the E-form's `mforth` was
spent at a single site (the ◯-backward direction of the truth lemma),
where the K-side witness is ours to choose.  The adversarial `iback`
is unchanged — the amalgam must answer every M-side i-move.  The
adversarial `mback` (2026-07-26, witness-form OUTPUT refactor) is NO
LONGER A FIELD: the only consumer was the adversarial ◯-maintenance
`witTriple_mforth`, which now takes it as the optional side condition
`LayeredBisimWit.MBack`; the witness-form maintenance
(`witTriple_mwit`, wip/witOut.lean) instead consumes the strictly
weaker M-side witness clause `MWitM`.  Every `LayeredBisimE` is a
`LayeredBisimWit` (`LayeredBisimE.toWit`, with `toWit_mback` restoring
the side condition); the converse fails, so the pillar-2 obligation is
strictly weakened. -/
structure LayeredBisimWit (A : String → Prop) (K M : ConstraintModel) where
  Z : Nat → K.W → M.W → Prop
  mono : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → Z n w w'
  atoms : ∀ {n : Nat} {w w'}, Z n w w' → ∀ a, A a → (w ∈ K.V a ↔ w' ∈ M.V a)
  fall : ∀ {n : Nat} {w w'}, Z n w w' → (w ∈ K.F ↔ w' ∈ M.F)
  iforth : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {v}, K.Ri w v →
    (∃ v', M.Ri w' v' ∧ Z n v v') ∨ v ∈ K.F
  iback : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {v'}, M.Ri w' v' →
    (∃ v, K.Ri w v ∧ Z n v v') ∨ v' ∈ M.F
  mwit : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {ψ : PLLFormula},
    (∃ κ, K.Rm w κ ∧ K.force κ ψ) →
      ∃ κ u', K.Rm w κ ∧ K.force κ ψ ∧ M.Rm w' u' ∧
        (Z n κ u' ∨ (κ ∈ K.F ∧ u' ∈ M.F))

theorem LayeredBisimWit.mono_le {A : String → Prop}
    (B : LayeredBisimWit A K M) :
    ∀ {m n : Nat}, m ≤ n → ∀ {w w'}, B.Z n w w' → B.Z m w w' := by
  intro m n h
  induction h with
  | refl => exact fun h => h
  | step _ ih => exact fun h => ih (B.mono h)

/-- **The adversarial M-side ◯-clause**, demoted from a structure field
to an optional side condition (2026-07-26): the development consumes it
at exactly one site — the adversarial ◯-maintenance `witTriple_mforth`
— and the witness-form maintenance (`witTriple_mwit`) replaces it by
the strictly weaker `MWitM` below. -/
def LayeredBisimWit.MBack {A : String → Prop}
    (B : LayeredBisimWit A K M) : Prop :=
  ∀ {n : Nat} {w : K.W} {w' : M.W}, B.Z (n + 1) w w' →
    ∀ {u' : M.W}, M.Rm w' u' →
      ∃ u, K.Rm w u ∧ (B.Z n u u' ∨ (u ∈ K.F ∧ u' ∈ M.F))

/-- **The M-side WITNESS ◯-clause**: an M-row witness for `ψ` is
answered by SOME M-row witness for `ψ` with a K-side `Rₘ`-partner —
the mirror image of `mwit`, and all the witness-form output ever
demands of the M side.  Strictly weaker than `MBack`
(`mwitM_of_mback`): the adversary no longer chooses the world, only
the formula. -/
def LayeredBisimWit.MWitM {A : String → Prop}
    (B : LayeredBisimWit A K M) : Prop :=
  ∀ {n : Nat} {w : K.W} {w' : M.W}, B.Z (n + 1) w w' →
    ∀ {ψ : PLLFormula}, (∃ u', M.Rm w' u' ∧ M.force u' ψ) →
      ∃ u' u, M.Rm w' u' ∧ M.force u' ψ ∧ K.Rm w u ∧
        (B.Z n u u' ∨ (u ∈ K.F ∧ u' ∈ M.F))

/-- Answering the given witness adversarially discharges the witness
clause: `MBack ⇒ MWitM`. -/
theorem LayeredBisimWit.mwitM_of_mback {A : String → Prop}
    {B : LayeredBisimWit A K M} (h : B.MBack) : B.MWitM := by
  intro n w w' hZ ψ hex
  obtain ⟨u', hu', hψ⟩ := hex
  obtain ⟨u, hu, hres⟩ := h hZ hu'
  exact ⟨u', u, hu', hψ, hu, hres⟩

/-- Every E-form link is a witness-form link: apply `mforth` to the
given witness. -/
def _root_.PLLND.SemUI.LayeredBisimE.toWit {A : String → Prop}
    {K M : ConstraintModel} (B : LayeredBisimE A K M) :
    LayeredBisimWit A K M where
  Z := B.Z
  mono := B.mono
  atoms := B.atoms
  fall := B.fall
  iforth := B.iforth
  iback := B.iback
  mwit := by
    intro n w w' hZ ψ h
    obtain ⟨κ, hkκ, hκψ⟩ := h
    obtain ⟨u', hu', hres⟩ := B.mforth hZ hkκ
    exact ⟨κ, u', hkκ, hκψ, hu', hres⟩

/-- The E-form's `mback` restores the adversarial side condition. -/
theorem _root_.PLLND.SemUI.LayeredBisimE.toWit_mback {A : String → Prop}
    {K M : ConstraintModel} (B : LayeredBisimE A K M) : B.toWit.MBack := by
  intro n w w' hZ u' hu'
  exact B.mback hZ hu'

/-! ## The witnessing triple -/

/-- **Witnessing triple** over the confluent canonical model.  `proper`:
worlds `k′, k` of `K` tracing (on `val`) to `Δ`, a shadow `m′ ≼ᵢ m`, with
the reservoir link `k′ Z_{2d+1} m′` and the base link `k Z_{2d} m`
(`d = canonDepthC Δ`).  `top`: a canonical world validating `⊥` paired
with a fallible M-world — where every fallible escape lands, and where all
maintenance is trivial.  (2026-07-27: the classical K-side edge
`k′ ≼ᵢ k` is REINSTATED as `hik` — maintainable through every
constructor in use, and it enables the square-descent saturation of
wip/rankGapPoint.lean: boxes at `k'` push row-witnesses into `row(k)`.) -/
inductive WitTripleC (cl : Finset PLLFormula)
    (B : LayeredBisimWit (fun a => a ≠ p) K M) :
    (canonFinC cl).W → M.W → Prop where
  | proper {Δ : (canonFinC cl).W} {m : M.W} (k' k : K.W) (m' : M.W)
      (hΔk : (traceT K cl k).val = Δ.1.val)
      (hΔk' : (traceT K cl k').val = Δ.1.val)
      (him : M.Ri m' m)
      (hZ' : B.Z (2 * canonDepthC cl Δ + 1) k' m')
      (hZ : B.Z (2 * canonDepthC cl Δ) k m)
      (hik : K.Ri k' k) :
      WitTripleC cl B Δ m
  | top {Δ : (canonFinC cl).W} {m : M.W}
      (hbot : PLLFormula.falsePLL ∈ Δ.1.val) (hmF : m ∈ M.F) :
      WitTripleC cl B Δ m

variable (cl : Finset PLLFormula) (B : LayeredBisimWit (fun a => a ≠ p) K M)

/-! ## The amalgam -/

/-- The amalgam over the confluent triples (frame data as in `witAmalgam`;
only the admissibility predicate changes). -/
def witAmalgamC : ConstraintModel where
  W := {q : (canonFinC cl).W × M.W // WitTripleC cl B q.1 q.2}
  Ri := fun a b => (canonFinC cl).Ri a.1.1 b.1.1 ∧ M.Ri a.1.2 b.1.2
  Rm := fun a b => (canonFinC cl).Rm a.1.1 b.1.1 ∧ M.Rm a.1.2 b.1.2
  F := fun a => a.1.2 ∈ M.F
  V := fun x a =>
    if x = p then a.1.1 ∈ (canonFinC cl).V x ∨ a.1.2 ∈ M.F
    else a.1.2 ∈ M.V x
  refl_i := fun a => ⟨(canonFinC cl).refl_i _, M.refl_i _⟩
  trans_i := fun h₁ h₂ =>
    ⟨(canonFinC cl).trans_i h₁.1 h₂.1, M.trans_i h₁.2 h₂.2⟩
  refl_m := fun a => ⟨(canonFinC cl).refl_m _, M.refl_m _⟩
  trans_m := fun h₁ h₂ =>
    ⟨(canonFinC cl).trans_m h₁.1 h₂.1, M.trans_m h₁.2 h₂.2⟩
  sub_mi := fun h => ⟨(canonFinC cl).sub_mi h.1, M.sub_mi h.2⟩
  hered_F := fun h hF => M.hered_F h.2 hF
  hered_V := by
    intro x a b h hv
    have hv' : (if x = p then a.1.1 ∈ (canonFinC cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x) := hv
    show (if x = p then b.1.1 ∈ (canonFinC cl).V x ∨ b.1.2 ∈ M.F
        else b.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx] at hv' ⊢
      rcases hv' with hΔ | hm
      · exact Or.inl ((canonFinC cl).hered_V h.1 hΔ)
      · exact Or.inr (M.hered_F h.2 hm)
    · rw [if_neg hx] at hv' ⊢
      exact M.hered_V h.2 hv'
  full_F := by
    intro x a hF
    show (if x = p then a.1.1 ∈ (canonFinC cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx]
      exact Or.inr hF
    · rw [if_neg hx]
      exact M.full_F hF

/-! ## The residue — the single open obligation -/

/-- **The promise-pair residue (OPEN)** — the one unproved case of the
◯-maintenance.  Configuration: a proper triple at `(Δ, m)` (with
`⊥ ∉ val Δ`, so `d ≥ 1`), an M-move `m ⟶Rₘ u` with `u` not fallible, and
the two spends both degenerate:

* the reservoir's `iback`-partner `kv` (`Rᵢ k′ kv`, level `2d`) STRICTLY
  GROWS the trace — so it cannot serve a same-trace base — while
* the base's `mback`-partner `κ` (`Rₘ k κ`, level `2d−1`) KEEPS the trace —
  so its level is one short of a same-trace base, and the grown answer
  `traceC κ` is unavailable (no growth to finance the fresh triple).

Wanted: SOME canonical `RmC`-successor of `Δ` carrying a triple for `u`.
Every other case of `witTriple_mforth` is proved below; every consumer
takes this Prop as a hypothesis. -/
def MforthResidue : Prop :=
  ∀ (_hK : MutuallyConfluent K)
    {Δ : (canonFinC cl).W} {k' k kv κ : K.W} {m' m u : M.W},
    SubClosed cl →
    PLLFormula.falsePLL ∉ Δ.1.val →
    (traceT K cl k).val = Δ.1.val →
    (traceT K cl k').val = Δ.1.val →
    K.Ri k' k →
    M.Ri m' m → M.Rm m u → u ∉ M.F →
    B.Z (2 * canonDepthC cl Δ + 1) k' m' →
    B.Z (2 * canonDepthC cl Δ) k m →
    K.Ri k' kv → B.Z (2 * canonDepthC cl Δ) kv u →
    (traceT K cl kv).val ≠ Δ.1.val →
    K.Rm k κ → B.Z (2 * canonDepthC cl Δ - 1) κ u →
    (traceT K cl κ).val = Δ.1.val →
    ∃ Δ' : (canonFinC cl).W, (canonFinC cl).Rm Δ Δ' ∧ WitTripleC cl B Δ' u

/-- **The same-trace-base sufficient condition** for the residue: if, in
every residue configuration, SOME K-world with the same trace carries a
level-`2d` link to `u`, then the residue holds — the reflexive canonical
move answers, with the old reservoir intact.  (The probe's rescue R1;
this bridge makes its statistic a Lean-checkable target.) -/
theorem mforthResidue_of_sameTraceBase
    (h : ∀ (_hK : MutuallyConfluent K)
      {Δ : (canonFinC cl).W} {k' k kv κ : K.W} {m' m u : M.W},
      PLLFormula.falsePLL ∉ Δ.1.val →
      (traceT K cl k).val = Δ.1.val →
      (traceT K cl k').val = Δ.1.val →
      K.Ri k' k →
      M.Ri m' m → M.Rm m u → u ∉ M.F →
      B.Z (2 * canonDepthC cl Δ + 1) k' m' →
      B.Z (2 * canonDepthC cl Δ) k m →
      K.Ri k' kv → B.Z (2 * canonDepthC cl Δ) kv u →
      (traceT K cl kv).val ≠ Δ.1.val →
      K.Rm k κ → B.Z (2 * canonDepthC cl Δ - 1) κ u →
      (traceT K cl κ).val = Δ.1.val →
      ∃ kb : K.W, (traceT K cl kb).val = Δ.1.val ∧ K.Ri k' kb ∧
        B.Z (2 * canonDepthC cl Δ) kb u) :
    MforthResidue cl B := by
  intro hK Δ k' k kv κ m' m u _hcl hbot hΔk hΔk' hik him hmu huF hZ' hZ hk'kv hZkv
    hsame hkκ hZκ hκsame
  obtain ⟨kb, hΔkb, hikb, hZkb⟩ := h hK hbot hΔk hΔk' hik him hmu huF hZ' hZ hk'kv hZkv
    hsame hkκ hZκ hκsame
  exact ⟨Δ, (canonFinC cl).refl_m Δ,
    .proper k' kb m' hΔkb hΔk' (M.trans_i him (M.sub_mi hmu)) hZ' hZkb hikb⟩

/-- **The grown-base sufficient condition** for the residue (the probe's
rescue R2): a K-world `kb` whose trace strictly grows, carrying links at
`2·d(kb)` and `2·d(kb)+1` to `u`, and whose growth is ◯-ANTICIPATED at `Δ`
(every tracked formula it forces has its collapsed box in `val Δ`),
discharges the residue — `traceC kb` answers, with `(kb, u)` serving as
both base and its own reservoir. -/
theorem mforthResidue_of_grownBase
    (h : ∀ (_hK : MutuallyConfluent K)
      {Δ : (canonFinC cl).W} {k' k kv κ : K.W} {m' m u : M.W},
      PLLFormula.falsePLL ∉ Δ.1.val →
      (traceT K cl k).val = Δ.1.val →
      (traceT K cl k').val = Δ.1.val →
      K.Ri k' k →
      M.Ri m' m → M.Rm m u → u ∉ M.F →
      B.Z (2 * canonDepthC cl Δ + 1) k' m' →
      B.Z (2 * canonDepthC cl Δ) k m →
      K.Ri k' kv → B.Z (2 * canonDepthC cl Δ) kv u →
      (traceT K cl kv).val ≠ Δ.1.val →
      K.Rm k κ → B.Z (2 * canonDepthC cl Δ - 1) κ u →
      (traceT K cl κ).val = Δ.1.val →
      ∃ kb : K.W, Δ.1.val ⊆ (traceT K cl kb).val ∧
        (∀ χ : PLLFormula, boxOf χ ∈ cl → χ ∈ (traceT K cl kb).val →
          boxOf χ ∈ Δ.1.val) ∧
        B.Z (2 * canonDepthC cl (⟨traceT K cl kb, traceT_maxIn K cl kb,
          trace_backed _hK kb⟩ : (canonFinC cl).W) + 1) kb u) :
    MforthResidue cl B := by
  intro hK Δ k' k kv κ m' m u _hcl hbot hΔk hΔk' hik him hmu huF hZ' hZ hk'kv hZkv
    hsame hkκ hZκ hκsame
  obtain ⟨kb, hsub, hant, hZkb⟩ := h hK hbot hΔk hΔk' hik him hmu huF hZ' hZ
    hk'kv hZkv hsame hkκ hZκ hκsame
  exact ⟨traceC hK cl kb, ⟨hsub, hant⟩,
    .proper kb kb u rfl rfl (M.refl_i u) hZkb (B.mono (B.mono_le le_rfl hZkb))
      (K.refl_i kb)⟩

/-- **The vacuity route** to the residue (what the structural probe
supports: 0 configurations over 438,075 confluent pairs, with growth
PROPAGATING — whenever the reservoir's `iback`-partner grows, every
`mback`-partner of the base grows too): if the configuration is
impossible, the residue holds outright. -/
theorem mforthResidue_of_config_absurd
    (h : ∀ (_hK : MutuallyConfluent K)
      {Δ : (canonFinC cl).W} {k' k kv κ : K.W} {m' m u : M.W},
      SubClosed cl →
      PLLFormula.falsePLL ∉ Δ.1.val →
      (traceT K cl k).val = Δ.1.val →
      (traceT K cl k').val = Δ.1.val →
      K.Ri k' k →
      M.Ri m' m → M.Rm m u → u ∉ M.F →
      B.Z (2 * canonDepthC cl Δ + 1) k' m' →
      B.Z (2 * canonDepthC cl Δ) k m →
      K.Ri k' kv → B.Z (2 * canonDepthC cl Δ) kv u →
      (traceT K cl kv).val ≠ Δ.1.val →
      K.Rm k κ → B.Z (2 * canonDepthC cl Δ - 1) κ u →
      (traceT K cl κ).val = Δ.1.val →
      False) :
    MforthResidue cl B := by
  intro hK Δ k' k kv κ m' m u hcl hbot hΔk hΔk' hik him hmu huF hZ' hZ hk'kv hZkv
    hsame hkκ hZκ hκsame
  exact absurd hκsame (fun hκ => h hK hcl hbot hΔk hΔk' hik him hmu huF hZ' hZ
    hk'kv hZkv hsame hkκ hZκ hκ)

/-! ## The step lemmas -/

/-- **The financed `iforth` maintenance**: an M-move `m ⟶Rᵢ v` is matched
by a canonical `Rᵢ`-move carrying a fresh triple.  Same trace: `Δ′ = Δ`,
the reservoir regenerates the base by `B.iback` (cost 1, surplus 1).
Strict: the depth drop finances a fresh reflexive triple.  Fallible
escape: the canonical top.  Sorry-free. -/
theorem witTriple_iforth (hcl : SubClosed cl) (hK : MutuallyConfluent K)
    {Δ : (canonFinC cl).W} {m : M.W} (ht : WitTripleC cl B Δ m)
    {v : M.W} (hmv : M.Ri m v) :
    ∃ Δ' : (canonFinC cl).W, (canonFinC cl).Ri Δ Δ' ∧ WitTripleC cl B Δ' v := by
  cases ht with
  | top hbot hmF =>
      exact ⟨Δ, (canonFinC cl).refl_i Δ, .top hbot (M.hered_F hmv hmF)⟩
  | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
      have hm'v : M.Ri m' v := M.trans_i him hmv
      rcases B.iback hZ' hm'v with ⟨kv, hk'kv, hZkv⟩ | hvF
      · by_cases hsame : (traceT K cl kv).val = Δ.1.val
        · -- same trace: reflexive canonical move, base regenerated
          exact ⟨Δ, (canonFinC cl).refl_i Δ,
            .proper k' kv m' hsame hΔk' hm'v hZ' hZkv hk'kv⟩
        · -- strict: Δ' = traceC kv, financed by the depth drop
          have hRi : Δ.1.val ⊆ (traceC hK cl kv).1.val := by
            intro φ hφ
            rw [← hΔk'] at hφ
            obtain ⟨hφcl, hf⟩ := mem_traceT_val.mp hφ
            exact mem_traceT_val.mpr ⟨hφcl, K.force_hered hk'kv hf⟩
          have hlt : canonDepthC cl (traceC hK cl kv) < canonDepthC cl Δ :=
            canonDepthC_lt hRi (fun h => hsame h.symm)
          exact ⟨traceC hK cl kv, hRi,
            .proper kv kv v rfl rfl (M.refl_i v)
              (B.mono_le (by omega) hZkv) (B.mono_le (by omega) hZkv)
              (K.refl_i kv)⟩
      · -- fallible escape: the canonical top
        exact ⟨canonTopC cl, ri_canonTopC Δ, .top hcl.bot hvF⟩

/-- **The financed `mforth` maintenance** (the ◯-move): an M-move
`m ⟶Rₘ u` is matched by a canonical `RmC`-move carrying a triple.
Same trace (`iback`-partner keeps the trace): `RmC` is REFLEXIVE, so the
answer is `Δ` itself with the base regenerated — the previously
"unfinanceable" same-theory ◯-move costs nothing.  Strict
(`mback`-partner grows the trace): `Δ′ = traceC κ` by `traceC_mforth`,
`Z (2d−1)` finances the reflexive successor since `2d′+1 ≤ 2d−1`.
Fallible: `fall` at the spent link + `traceC` of the fallible partner.
The one remaining configuration is `MforthResidue`.  (Takes the
adversarial side condition `MBack` — the only site consuming it.) -/
theorem witTriple_mforth (hcl : SubClosed cl) (hK : MutuallyConfluent K)
    (hmb : B.MBack) (hres : MforthResidue cl B)
    {Δ : (canonFinC cl).W} {m : M.W} (ht : WitTripleC cl B Δ m)
    {u : M.W} (hmu : M.Rm m u) :
    ∃ Δ' : (canonFinC cl).W, (canonFinC cl).Rm Δ Δ' ∧ WitTripleC cl B Δ' u := by
  cases ht with
  | top hbot hmF =>
      exact ⟨Δ, (canonFinC cl).refl_m Δ, .top hbot (M.hered_F (M.sub_mi hmu) hmF)⟩
  | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
      by_cases hbot : PLLFormula.falsePLL ∈ Δ.1.val
      · -- the top-val proper triple is secretly fallible on both sides
        have hkF : k ∈ K.F := by
          have hm : PLLFormula.falsePLL ∈ (traceT K cl k).val := by
            rw [hΔk]; exact hbot
          exact (mem_traceT_val.mp hm).2
        have hmF : m ∈ M.F := (B.fall hZ).mp hkF
        exact ⟨Δ, (canonFinC cl).refl_m Δ,
          .top hbot (M.hered_F (M.sub_mi hmu) hmF)⟩
      · have hd : 1 ≤ canonDepthC cl Δ := canonDepthC_pos hcl hbot
        -- the canonical RmC-move towards a partner κ, shared by three cases
        have hRmκ : ∀ κ : K.W, K.Rm k κ →
            (canonFinC cl).Rm Δ (traceC hK cl κ) := by
          intro κ hkκ
          have h := traceC_mforth (cl := cl) hK hkκ
          refine ⟨?_, ?_⟩
          · intro χ hχ
            rw [← hΔk] at hχ
            exact h.1 hχ
          · intro χ hbcl hχ
            rw [← hΔk]
            exact h.2 χ hbcl hχ
        -- a fallible partner lands the top-shaped triple at its trace
        have htopκ : ∀ κ : K.W, K.Rm k κ → κ ∈ K.F → u ∈ M.F →
            ∃ Δ' : (canonFinC cl).W,
              (canonFinC cl).Rm Δ Δ' ∧ WitTripleC cl B Δ' u := by
          intro κ hkκ hκF huF
          exact ⟨traceC hK cl κ, hRmκ κ hkκ,
            .top (mem_traceT_val.mpr ⟨hcl.bot, K.force_of_fallible hκF⟩) huF⟩
        have hZbase : B.Z (2 * canonDepthC cl Δ - 1 + 1) k m := by
          have : 2 * canonDepthC cl Δ - 1 + 1 = 2 * canonDepthC cl Δ := by omega
          rw [this]; exact hZ
        have hm'u : M.Ri m' u := M.trans_i him (M.sub_mi hmu)
        rcases B.iback hZ' hm'u with ⟨kv, hk'kv, hZkv⟩ | huF
        · by_cases hsame : (traceT K cl kv).val = Δ.1.val
          · -- CASE A: same-trace ◯-move, matched reflexively
            exact ⟨Δ, (canonFinC cl).refl_m Δ,
              .proper k' kv m' hsame hΔk' hm'u hZ' hZkv hk'kv⟩
          · -- the iback-partner grew: spend the base on mback
            rcases hmb hZbase hmu with ⟨κ, hkκ, hZκ | ⟨hκF, huF⟩⟩
            · by_cases huF : u ∈ M.F
              · exact htopκ κ hkκ ((B.fall hZκ).mpr huF) huF
              · by_cases hκsame : (traceT K cl κ).val = Δ.1.val
                · -- THE RESIDUE: both partners degenerate
                  exact hres hK hcl hbot hΔk hΔk' hik him hmu huF hZ' hZ
                    hk'kv hZkv hsame hkκ hZκ hκsame
                · -- strict growth via the mback-partner
                  have hsub : Δ.1.val ⊆ (traceC hK cl κ).1.val := by
                    intro φ hφ
                    rw [← hΔk] at hφ
                    obtain ⟨hφcl, hf⟩ := mem_traceT_val.mp hφ
                    exact mem_traceT_val.mpr
                      ⟨hφcl, K.force_hered (K.sub_mi hkκ) hf⟩
                  have hlt : canonDepthC cl (traceC hK cl κ) < canonDepthC cl Δ :=
                    canonDepthC_lt hsub (fun h => hκsame h.symm)
                  exact ⟨traceC hK cl κ, hRmκ κ hkκ,
                    .proper κ κ u rfl rfl (M.refl_i u)
                      (B.mono_le (by omega) hZκ) (B.mono_le (by omega) hZκ)
                      (K.refl_i κ)⟩
            · exact htopκ κ hkκ hκF huF
        · -- iback escape (u fallible): mback supplies the fallible K-partner
          rcases hmb hZbase hmu with ⟨κ, hkκ, hZκ | ⟨hκF, _⟩⟩
          · exact htopκ κ hkκ ((B.fall hZκ).mpr huF) huF
          · exact htopκ κ hkκ hκF huF

/-! ## Claim 1: the amalgam is a p-variant of M -/

/-- **The projection PBisim** — sorry-free modulo `MforthResidue`.  The
M-to-amalgam zigzags are the step lemmas; the amalgam-to-M directions are
projections; atoms off `p` and fallibility are definitional. -/
theorem wit_pbisimC (hcl : SubClosed cl) (hK : MutuallyConfluent K)
    (hmb : B.MBack) (hres : MforthResidue cl B) :
    ∃ C : PBisim p M (witAmalgamC cl B),
      ∀ (q : (witAmalgamC cl B).W), C.Z q.1.2 q := by
  refine ⟨⟨fun m q => q.1.2 = m, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => rfl⟩
  · -- atoms off p
    rintro m q rfl a ha
    show q.1.2 ∈ M.V a ↔ (if a = p then q.1.1 ∈ (canonFinC cl).V a ∨ q.1.2 ∈ M.F
        else q.1.2 ∈ M.V a)
    rw [if_neg ha]
  · -- fall
    rintro m q rfl
    exact Iff.rfl
  · -- iforth: an M-move, matched through the triple
    rintro m q rfl v hmv
    obtain ⟨Δ', hRi, htrip⟩ := witTriple_iforth cl B hcl hK q.2 hmv
    exact ⟨⟨(Δ', v), htrip⟩, ⟨hRi, hmv⟩, rfl⟩
  · -- iback: projection
    rintro m q rfl q' hq'
    exact ⟨q'.1.2, hq'.2, rfl⟩
  · -- mforth: the ◯-move, matched through the triple
    rintro m q rfl u hmu
    obtain ⟨Δ', hRm, htrip⟩ := witTriple_mforth cl B hcl hK hmb hres q.2 hmu
    exact ⟨⟨(Δ', u), htrip⟩, ⟨hRm, hmu⟩, rfl⟩
  · -- mback: projection
    rintro m q rfl q' hq'
    exact ⟨q'.1.2, hq'.2, rfl⟩

/-! ## Claim 2: the truth lemma for the amalgam -/

/-- At a `⊥`-validating canonical coordinate with a fallible M-coordinate,
both sides of the truth lemma hold outright. -/
theorem wit_force_top
    (q : (witAmalgamC cl B).W) (hbot : PLLFormula.falsePLL ∈ q.1.1.1.val)
    (hmF : q.1.2 ∈ M.F) {φ : PLLFormula} (hφ : φ ∈ cl) :
    (witAmalgamC cl B).force q φ ∧ φ ∈ q.1.1.1.val :=
  ⟨(witAmalgamC cl B).force_of_fallible hmF,
   q.1.1.2.1.ded_closed hφ (falso _ (SetDeriv.of_mem (Finset.mem_coe.mpr hbot)))⟩

/-- **The truth lemma** — sorry-free modulo `MforthResidue`: an amalgam
world forces a closure formula iff its canonical coordinate validates it.
The ◯-forward direction is definitional through `RmC`'s anticipation
clause; ◯-backward is bare possibility in `K` + `B.mforth`, financed by
strict growth; ⊃-backward is the K-side refuter + `B.iforth`, financed by
strict growth.  Only `K` need be confluent. -/
theorem wit_forceC (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) :
    ∀ (φ : PLLFormula), φ ∈ cl → ∀ (q : (witAmalgamC cl B).W),
      ((witAmalgamC cl B).force q φ ↔ φ ∈ q.1.1.1.val) := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ q
      obtain ⟨⟨Δ, m⟩, htrip⟩ := q
      cases htrip with
      | top hbot hmF =>
          obtain ⟨hf, hm⟩ :=
            wit_force_top cl B ⟨(Δ, m), .top hbot hmF⟩ hbot hmF hφ
          exact ⟨fun _ => hm, fun _ => hf⟩
      | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
          have hmem : PLLFormula.prop a ∈ Δ.1.val ↔ k ∈ K.V a := by
            rw [← hΔk, mem_traceT_val]
            exact ⟨fun h => h.2, fun h => ⟨hφ, h⟩⟩
          by_cases hap : a = p
          · subst hap
            constructor
            · intro hf
              have hf' : Δ ∈ (canonFinC cl).V a ∨ m ∈ M.F := by
                have := (show (if a = a then Δ ∈ (canonFinC cl).V a ∨ m ∈ M.F
                    else m ∈ M.V a) from hf)
                rwa [if_pos rfl] at this
              rcases hf' with (hout | hv) | hmF
              · exact absurd hφ hout
              · exact hv
              · -- fallibility pushes p into the trace through the link
                have hkF : k ∈ K.F := (B.fall hZ).mpr hmF
                have : PLLFormula.prop a ∈ (traceT K cl k).val :=
                  mem_traceT_val.mpr ⟨hφ, K.force_of_fallible hkF⟩
                rw [hΔk] at this
                exact this
            · intro hv
              show (if a = a then Δ ∈ (canonFinC cl).V a ∨ m ∈ M.F
                  else m ∈ M.V a)
              rw [if_pos rfl]
              exact Or.inl (Or.inr hv)
          · constructor
            · intro hf
              have hm : m ∈ M.V a := by
                have := (show (if a = p then Δ ∈ (canonFinC cl).V a ∨ m ∈ M.F
                    else m ∈ M.V a) from hf)
                rwa [if_neg hap] at this
              exact hmem.mpr ((B.atoms hZ a hap).mpr hm)
            · intro hv
              show (if a = p then Δ ∈ (canonFinC cl).V a ∨ m ∈ M.F
                  else m ∈ M.V a)
              rw [if_neg hap]
              exact (B.atoms hZ a hap).mp (hmem.mp hv)
  | falsePLL =>
      intro hφ q
      obtain ⟨⟨Δ, m⟩, htrip⟩ := q
      cases htrip with
      | top hbot hmF => exact ⟨fun _ => hbot, fun _ => hmF⟩
      | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
          constructor
          · intro hf
            have hkF : k ∈ K.F := (B.fall hZ).mpr hf
            rw [← hΔk]
            exact mem_traceT_val.mpr ⟨hφ, hkF⟩
          · intro hv
            have hkF : k ∈ K.F := by
              have : PLLFormula.falsePLL ∈ (traceT K cl k).val := by
                rw [hΔk]; exact hv
              exact (mem_traceT_val.mp this).2
            exact (B.fall hZ).mp hkF
  | and φ ψ ihφ ihψ =>
      intro hφ q
      have hφ₁ := hcl.and_left hφ
      have hψ₁ := hcl.and_right hφ
      constructor
      · rintro ⟨h₁, h₂⟩
        refine q.1.1.2.1.ded_closed hφ ?_
        exact SetDeriv.map₂ (fun p₁ p₂ => .andIntro p₁ p₂)
          (SetDeriv.of_mem (Finset.mem_coe.mpr ((ihφ hφ₁ q).mp h₁)))
          (SetDeriv.of_mem (Finset.mem_coe.mpr ((ihψ hψ₁ q).mp h₂)))
      · intro h
        have h₁ : φ ∈ q.1.1.1.val := q.1.1.2.1.ded_closed hφ₁
          (SetDeriv.map (fun p => .andElim1 p)
            (SetDeriv.of_mem (Finset.mem_coe.mpr h)))
        have h₂ : ψ ∈ q.1.1.1.val := q.1.1.2.1.ded_closed hψ₁
          (SetDeriv.map (fun p => .andElim2 p)
            (SetDeriv.of_mem (Finset.mem_coe.mpr h)))
        exact ⟨(ihφ hφ₁ q).mpr h₁, (ihψ hψ₁ q).mpr h₂⟩
  | or φ ψ ihφ ihψ =>
      intro hφ q
      have hφ₁ := hcl.or_left hφ
      have hψ₁ := hcl.or_right hφ
      constructor
      · rintro (h | h)
        · exact q.1.1.2.1.ded_closed hφ
            (SetDeriv.orL _ (SetDeriv.of_mem (Finset.mem_coe.mpr
              ((ihφ hφ₁ q).mp h))))
        · exact q.1.1.2.1.ded_closed hφ
            (SetDeriv.orR _ (SetDeriv.of_mem (Finset.mem_coe.mpr
              ((ihψ hψ₁ q).mp h))))
      · intro h
        rcases q.1.1.2.1.or_mem hcl h with h' | h'
        · exact Or.inl ((ihφ hφ₁ q).mpr h')
        · exact Or.inr ((ihψ hψ₁ q).mpr h')
  | ifThen φ ψ ihφ ihψ =>
      intro hφ q
      have hφ₁ := hcl.imp_left hφ
      have hψ₁ := hcl.imp_right hφ
      constructor
      · -- backward (¬∈ ⇒ ¬force), by contraposition
        intro hf
        by_contra hnv
        obtain ⟨⟨Δ, m⟩, htrip⟩ := q
        cases htrip with
        | top hbot hmF =>
            exact hnv (wit_force_top cl B ⟨(Δ, m), .top hbot hmF⟩ hbot hmF hφ).2
        | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
            by_cases hbot : PLLFormula.falsePLL ∈ Δ.1.val
            · exact hnv (Δ.2.1.ded_closed hφ (falso _
                (SetDeriv.of_mem (Finset.mem_coe.mpr hbot))))
            · have hd : 1 ≤ canonDepthC cl Δ := canonDepthC_pos hcl hbot
              by_cases hA : φ ∈ Δ.1.val
              · -- refute in place
                have hB : ψ ∉ Δ.1.val := fun hψv => hnv
                  (Δ.2.1.ded_closed hφ (SetDeriv.deduct (SetDeriv.of_mem
                    (Set.mem_insert_of_mem _ (Finset.mem_coe.mpr hψv)))))
                have := hf ⟨(Δ, m), .proper k' k m' hΔk hΔk' him hZ' hZ hik⟩
                  ((witAmalgamC cl B).refl_i _)
                  ((ihφ hφ₁ _).mpr hA)
                exact hB ((ihψ hψ₁ _).mp this)
              · -- the K-side refuter, pushed through B.iforth
                have hnk : ¬ K.force k (φ.ifThen ψ) := by
                  intro hforce
                  have : φ.ifThen ψ ∈ (traceT K cl k).val :=
                    mem_traceT_val.mpr ⟨hφ, hforce⟩
                  rw [hΔk] at this
                  exact hnv this
                have hk₁ : ∃ k₁, K.Ri k k₁ ∧ K.force k₁ φ ∧ ¬ K.force k₁ ψ := by
                  by_contra hno
                  push_neg at hno
                  exact hnk (fun v hv hφv => hno v hv hφv)
                obtain ⟨k₁, hkk₁, hφk₁, hψk₁⟩ := hk₁
                have hZbase : B.Z (2 * canonDepthC cl Δ - 1 + 1) k m := by
                  have : 2 * canonDepthC cl Δ - 1 + 1 = 2 * canonDepthC cl Δ := by
                    omega
                  rw [this]; exact hZ
                rcases B.iforth hZbase hkk₁ with ⟨v, hmv, hZ₁⟩ | hk₁F
                · have hsub : Δ.1.val ⊆ (traceC hK cl k₁).1.val := by
                    intro χ hχ
                    rw [← hΔk] at hχ
                    obtain ⟨hχcl, hfχ⟩ := mem_traceT_val.mp hχ
                    exact mem_traceT_val.mpr ⟨hχcl, K.force_hered hkk₁ hfχ⟩
                  have hne : Δ.1.val ≠ (traceC hK cl k₁).1.val := by
                    intro hEq
                    exact hA (by
                      rw [hEq]
                      exact mem_traceT_val.mpr ⟨hφ₁, hφk₁⟩)
                  have hlt : canonDepthC cl (traceC hK cl k₁) < canonDepthC cl Δ :=
                    canonDepthC_lt hsub hne
                  have htrip₁ : WitTripleC cl B (traceC hK cl k₁) v :=
                    .proper k₁ k₁ v rfl rfl (M.refl_i v)
                      (B.mono_le (by omega) hZ₁) (B.mono_le (by omega) hZ₁)
                      (K.refl_i k₁)
                  have hforceψ := hf ⟨(traceC hK cl k₁, v), htrip₁⟩
                    ⟨hsub, hmv⟩
                    ((ihφ hφ₁ _).mpr (mem_traceT_val.mpr ⟨hφ₁, hφk₁⟩))
                  have : ψ ∈ (traceT K cl k₁).val := (ihψ hψ₁ _).mp hforceψ
                  exact hψk₁ (mem_traceT_val.mp this).2
                · exact hψk₁ (K.force_of_fallible hk₁F)
      · -- forward (∈ ⇒ force): persistence + deductive closure
        intro h q' hq' hφ'
        have hval : φ.ifThen ψ ∈ q'.1.1.1.val := hq'.1 h
        have hφv : φ ∈ q'.1.1.1.val := (ihφ hφ₁ q').mp hφ'
        have hψv : ψ ∈ q'.1.1.1.val := q'.1.1.2.1.ded_closed hψ₁
          (SetDeriv.mp (SetDeriv.of_mem (Finset.mem_coe.mpr hval))
            (SetDeriv.of_mem (Finset.mem_coe.mpr hφv)))
        exact (ihψ hψ₁ q').mpr hψv
  | somehow ψ ihψ =>
      intro hφ q
      have hψ₁ : ψ ∈ cl := hcl.lax hφ
      constructor
      · -- forward: instantiate at q itself; RmC anticipates
        intro hf
        obtain ⟨q₂, hRm, hfψ⟩ := hf q ((witAmalgamC cl B).refl_i q)
        have hψv : ψ ∈ q₂.1.1.1.val := (ihψ hψ₁ q₂).mp hfψ
        have hbox : boxOf ψ ∈ q.1.1.1.val :=
          hRm.1.2 ψ (hadeq ψ hψ₁) hψv
        exact somehow_mem_of_boxOf_mem (w := ⟨q.1.1.1, q.1.1.2.1⟩) hφ hbox
      · -- backward: bare possibility in K + B.mforth at every i-successor
        intro h q₁ hq₁
        obtain ⟨⟨Δ₁, m₁⟩, htrip₁⟩ := q₁
        have hval₁ : PLLFormula.somehow ψ ∈ Δ₁.1.val := hq₁.1 h
        cases htrip₁ with
        | top hbot hmF =>
            exact ⟨⟨(Δ₁, m₁), .top hbot hmF⟩,
              (witAmalgamC cl B).refl_m _,
              (witAmalgamC cl B).force_of_fallible hmF⟩
        | proper k₁' k₁ m₁' hΔk₁ hΔk₁' him₁ hZ'₁ hZ₁ hik₁ =>
            by_cases hbot₁ : PLLFormula.falsePLL ∈ Δ₁.1.val
            · have hkF : k₁ ∈ K.F := by
                have hm : PLLFormula.falsePLL ∈ (traceT K cl k₁).val := by
                  rw [hΔk₁]; exact hbot₁
                exact (mem_traceT_val.mp hm).2
              have hmF : m₁ ∈ M.F := (B.fall hZ₁).mp hkF
              exact ⟨⟨(Δ₁, m₁), .proper k₁' k₁ m₁' hΔk₁ hΔk₁' him₁ hZ'₁ hZ₁ hik₁⟩,
                (witAmalgamC cl B).refl_m _,
                (witAmalgamC cl B).force_of_fallible hmF⟩
            · have hd₁ : 1 ≤ canonDepthC cl Δ₁ := canonDepthC_pos hcl hbot₁
              by_cases hψΔ₁ : ψ ∈ Δ₁.1.val
              · -- the world is its own row-witness
                exact ⟨⟨(Δ₁, m₁), .proper k₁' k₁ m₁' hΔk₁ hΔk₁' him₁ hZ'₁ hZ₁ hik₁⟩,
                  (witAmalgamC cl B).refl_m _,
                  (ihψ hψ₁ _).mpr hψΔ₁⟩
              · -- bare possibility in K supplies a strictly growing witness
                have hfk₁ : K.force k₁ (PLLFormula.somehow ψ) := by
                  have : PLLFormula.somehow ψ ∈ (traceT K cl k₁).val := by
                    rw [hΔk₁]; exact hval₁
                  exact (mem_traceT_val.mp this).2
                rw [force_somehow_iff_of_confluent hK] at hfk₁
                have hZbase₁ : B.Z (2 * canonDepthC cl Δ₁ - 1 + 1) k₁ m₁ := by
                  have : 2 * canonDepthC cl Δ₁ - 1 + 1 = 2 * canonDepthC cl Δ₁ := by
                    omega
                  rw [this]; exact hZ₁
                obtain ⟨κ, u', hk₁κ, hκψ, hm₁u', hresκ⟩ := B.mwit hZbase₁ hfk₁
                have hRmΔ₁ : (canonFinC cl).Rm Δ₁ (traceC hK cl κ) := by
                  have hh := traceC_mforth (cl := cl) hK hk₁κ
                  refine ⟨?_, ?_⟩
                  · intro χ hχ
                    rw [← hΔk₁] at hχ
                    exact hh.1 hχ
                  · intro χ hbcl hχ
                    rw [← hΔk₁]
                    exact hh.2 χ hbcl hχ
                have hsub : Δ₁.1.val ⊆ (traceC hK cl κ).1.val := by
                  intro χ hχ
                  rw [← hΔk₁] at hχ
                  obtain ⟨hχcl, hfχ⟩ := mem_traceT_val.mp hχ
                  exact mem_traceT_val.mpr
                    ⟨hχcl, K.force_hered (K.sub_mi hk₁κ) hfχ⟩
                have hne : Δ₁.1.val ≠ (traceC hK cl κ).1.val := by
                  intro hEq
                  exact hψΔ₁ (by
                    rw [hEq]
                    exact mem_traceT_val.mpr ⟨hψ₁, hκψ⟩)
                have hlt : canonDepthC cl (traceC hK cl κ) < canonDepthC cl Δ₁ :=
                  canonDepthC_lt hsub hne
                rcases hresκ with hZκ | ⟨hκF, hu'F⟩
                · have htrip₂ : WitTripleC cl B (traceC hK cl κ) u' :=
                    .proper κ κ u' rfl rfl (M.refl_i u')
                      (B.mono_le (by omega) hZκ) (B.mono_le (by omega) hZκ)
                      (K.refl_i κ)
                  exact ⟨⟨(traceC hK cl κ, u'), htrip₂⟩, ⟨hRmΔ₁, hm₁u'⟩,
                    (ihψ hψ₁ _).mpr (mem_traceT_val.mpr ⟨hψ₁, hκψ⟩)⟩
                · exact ⟨⟨(traceC hK cl κ, u'),
                    .top (mem_traceT_val.mpr
                      ⟨hcl.bot, K.force_of_fallible hκF⟩) hu'F⟩,
                    ⟨hRmΔ₁, hm₁u'⟩,
                    (witAmalgamC cl B).force_of_fallible hu'F⟩

/-! ## The assembly -/

/-- **The amalgamation, assembled** — sorry-free modulo `MforthResidue`:
from a layered link of budget `2·cl.card + 1` between `k₀` and `m₀`, a
p-variant of `M` whose distinguished world agrees with `k₀` on the whole
closure.  Only `K` need be confluent. -/
theorem amalgamation_assembledC (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hmb : B.MBack) (hres : MforthResidue cl B)
    (k₀ : K.W) (m₀ : M.W)
    (hB : B.Z (2 * cl.card + 1) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) := by
  classical
  set Δ₀ : (canonFinC cl).W := traceC hK cl k₀ with hΔ₀
  have hd₀ := canonDepthC_le cl Δ₀
  have htrip : WitTripleC cl B Δ₀ m₀ :=
    .proper k₀ k₀ m₀ rfl rfl (M.refl_i m₀)
      (B.mono_le (by omega) hB) (B.mono_le (by omega) hB) (K.refl_i k₀)
  obtain ⟨C, hC⟩ := wit_pbisimC cl B hcl hK hmb hres
  refine ⟨witAmalgamC cl B, C, ⟨(Δ₀, m₀), htrip⟩,
    hC ⟨(Δ₀, m₀), htrip⟩, ?_⟩
  intro φ hφ
  rw [wit_forceC cl B hcl hadeq hK φ hφ ⟨(Δ₀, m₀), htrip⟩]
  constructor
  · intro h
    exact (mem_traceT_val.mp h).2
  · intro h
    exact mem_traceT_val.mpr ⟨hφ, h⟩

/-! ## Axiom audit — everything below is sorry-free; the only open
obligation is the hypothesis `MforthResidue`. -/

/--
info: 'PLLND.SemUI.witTriple_iforth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms witTriple_iforth

/--
info: 'PLLND.SemUI.witTriple_mforth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms witTriple_mforth

/--
info: 'PLLND.SemUI.wit_pbisimC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wit_pbisimC

/--
info: 'PLLND.SemUI.wit_forceC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wit_forceC

/--
info: 'PLLND.SemUI.amalgamation_assembledC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms amalgamation_assembledC

end SemUI
end PLLND
