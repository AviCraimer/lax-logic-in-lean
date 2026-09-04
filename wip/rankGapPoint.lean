import wip.rankedResidue

/-!
# The pointwise attack on `RankGap`

Branch `ui-confluence`.  Four results toward the open Prop, driven by
the deep-probe finding (PROGRESS §51: the descending window is clean,
with full-rank same-trace partners existing POINTWISE).

## 1. The square descent — a genuinely new transfer move

Every previous transfer moved formulas ACROSS a link and produced
witnesses in the row of the link's own world; the residue needs
witnesses in the row of `m`, one i-step BELOW the reservoir.  The
move: a box forced at the reservoir's K-side world `k'` (bare
possibility over `k'`'s row) crosses the reservoir link at its FULL
rank `rslope (2d+1) = 2·rslope (2d) + 3`; bare possibility in `M`
realises it in `row(m')`; and the confluence square over
(`Rₘ m' u₀`, `Rᵢ m' m`) pushes the witness DOWN into `row(m)`,
persistence carrying the character.  "Descent" = push-down of a
row-witness along `Rᵢ` through a confluence square — CONFLUENCE-
NATIVE, consuming no ∀-half of ◯'s `∀∃` clause (the register note on
`reservoir_row_cover` records why that matters).
`reservoir_row_cover`: every world of `row(k')` has its positive
rank-α character realised by a member of `row(m)`, for α up to
`rslope (2d+1) − 3` — far ABOVE the missing window.
`reservoir_row_cover_witness` merges the covering witness with the
ψ-witness by a second square (persistence keeps both).
`row_push_down`: the K-side mirror enabled by the reinstated triple
edge `k' Rᵢ k` — `row(k')`-witnesses push into `row(k)` with NO link
crossing at all (all ranks at once, pure persistence).

## 2. What is now PROVED

* `rankGap_of_rowRigid`: over a ROW-RIGID base (every infallible
  ◯-move is reflexive — e.g. every lifted ladder of the deep battery),
  `RankGap` holds outright: the witness is `m` itself and `kb := k`
  closes by the base link.  With the bridge, `MwitResidue` for the
  ranked link is PROVED over row-rigid bases — the entire live-window
  evidence class of PROGRESS §51 is now theorem, not observation.
* `rankGap_of_witnessTypeStable` / the case split `rankGap_of_grow`:
  if SOME ψ-witness in `m`'s row adds nothing to `m`'s variable-free
  rank-`rslope (2d)` theory, `kb := k` closes by transitivity through
  the base link.  Hence the open Prop shrinks to `RankGapGrow` — the
  configurations in which EVERY ψ-witness strictly grows the
  rank-`rslope (2d)` variable-free theory of `m`.

## 3. The sharpened geography of `RankGapGrow`

In the grow case, each witness `u''` forces some variable-free rep
`D₀` with `m ⊬ D₀`; bare possibility in `M` puts `◯D₀` at `m`, and
`crank (◯D₀) ≤ rslope (2d) + 2` — one to two connectives ABOVE the
base link's rank, so the growth is exactly RANKED-INVISIBLE (the
M-row mirror of `residue_growth_boundary`'s wall).  Meanwhile §1
covers `row(k')`-types at ranks far above the window, but its output
cannot be reflected back (the backward leg would need a box at `m'`,
and boxes at `m'` need witnesses in `row(m')`, which the
configuration does not supply).  2026-07-27 afternoon: the K-side
edge `k' Rᵢ k` IS REINSTATED in `WitTripleC` (threaded through every
constructor, residue Prop and bridge; whole tree green), and the
two-sided saturation is packaged as `config_two_sided_saturation`:
over a residue configuration, every world of `row(k')` is pushed into
`row(k)` (K-side square) AND covered inside `row(m)` by a ψ-carrying
witness (reservoir crossing + M-side squares), at every rank up to
`rslope (2d+1) − 3`.  What is still missing for an exact-type match —
and hence all that now stands between `RankGapGrow` and closure — is
the BACKWARD leg: reflecting `row(m)`-types into `row(k')`.  Probe
note: the configuration funnels of wip/mwit_probe.lean and
wip/mwit_deep.lean do not test `k' Rᵢ k`, so their clean verdicts
cover a SUPERSET of the reinstated configurations a fortiori.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-! ## 0. Agreement composes through a middle world -/

/-- Cross-model transitivity of band agreement through a world of `M`. -/
theorem bandAgree_trans_mid {r : Nat} {k : K.W} {m u : M.W}
    (h1 : bandAgree r K M k m) (h2 : bandAgree r M M m u) :
    bandAgree r K M k u :=
  fun ρ hρ hc => (h1 ρ hρ hc).trans (h2 ρ hρ hc)

/-- Agreement composes through a shared M-witness into K-INTERNAL
agreement. -/
theorem bandAgree_internal {r : Nat} {x y : K.W} {u : M.W}
    (h1 : bandAgree r K M x u) (h2 : bandAgree r K M y u) :
    bandAgree r K K x y :=
  fun ρ hρ hc => (h1 ρ hρ hc).trans (h2 ρ hρ hc).symm

/-- **The promotion reduction**: with the kv-partner at full rank
(`hZkv`), promotion of any K-world's link to `u'` across the window
is EXACTLY a K-internal question — its full-rank agreement with the
grown `kv`.  The M side drops out.  Consequence for the theorem
hunt: "pointwise promotion AT κ" would assert that the same-trace
mwitM-partner and the grown iback-partner agree at full rank INSIDE
`K` — refutable in isolation on ladder models (worlds agreeing to
rank `rslope (2d−1)` but not `rslope (2d)` exist at every depth,
fragment infinitude), so the honest theorem target is `RankGap`'s
existential form: SOME same-trace `kb` at full rank, guided by the
all-grow probe's winning-answer distribution. -/
theorem promotion_iff_internal {r : Nat} {κ kv : K.W} {u' : M.W}
    (hZkv : bandAgree r K M kv u') :
    bandAgree r K M κ u' ↔ bandAgree r K K κ kv :=
  ⟨fun h => bandAgree_internal h hZkv,
   fun h ρ hρ hc => (h ρ hρ hc).trans (hZkv ρ hρ hc)⟩

/-! ## 1. The ∀∃-descent -/

/-- **The square descent** (the row push-down): a positive character
boxed at the reservoir's K-side world crosses the reservoir link at
its full rank, BARE POSSIBILITY in `M` realises it in `row(m')`, and
the confluence square over (`Rₘ m' u₀`, `Rᵢ m' m`) pushes the witness
down into `row(m)`, persistence carrying the character — realising
every `row(k')`-type inside `row(m)`.

REGISTER NOTE (Matthew's design constraint, 2026-07-27): the same
conclusion follows in one step from the raw ∀-half of ◯'s `∀∃` clause
applied at the successor `m` — but that clause is exactly the
adversarial quantifier the PCLL/confluent programme exists to avoid
(it is the UI-killing mechanism of S4/iK4), and a proof consuming it
irreducibly would hold over the WRONG model class.  This proof
consumes only bare possibility, one confluence square, and
persistence — confluence-native, like every other transfer in the
route.  "Descent" means, precisely: push-down of a row-witness along
`Rᵢ` through a confluence square. -/
theorem reservoir_row_cover {α β : Nat} (hαβ : α + 3 ≤ β)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {k' : K.W} {m' m : M.W}
    (hZ' : bandAgree β K M k' m') (him : M.Ri m' m)
    {L : List PLLFormula}
    (hL : ∀ D ∈ L, crank D ≤ α ∧ ∀ a ∈ D.atoms, a ∈ (∅ : Finset String))
    {x : K.W} (hx : K.Rm k' x) :
    ∃ y : M.W, M.Rm m y ∧ ∀ D ∈ L, K.force x D → M.force y D := by
  classical
  set χ : PLLFormula := charPos K x L with hχdef
  have hχa : χ.atoms = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun a ha =>
      Finset.notMem_empty a
        (atoms_charPos (fun D hD => (hL D hD).2) a ha))
  have hχc : crank χ ≤ α + 1 :=
    crank_charPos_le (fun D hD => (hL D hD).1)
  have hk'box : K.force k' (PLLFormula.somehow χ) := by
    rw [force_somehow_iff_of_confluent hK]
    exact ⟨x, hx, force_charPos K x L⟩
  have hm'box : M.force m' (PLLFormula.somehow χ) := by
    refine (hZ' (PLLFormula.somehow χ) ?_ ?_).mp hk'box
    · show χ.atoms = ∅
      exact hχa
    · show crank χ + 2 ≤ β
      omega
  -- bare possibility in M: a χ-witness in m''s row
  rw [force_somehow_iff_of_confluent hM] at hm'box
  obtain ⟨u₀, hm'u₀, hu₀χ⟩ := hm'box
  -- the confluence square pushes it down into m's row
  obtain ⟨y, hu₀y, hmy⟩ := hM hm'u₀ him
  refine ⟨y, hmy, fun D hD hxD => ?_⟩
  exact M.force_hered hu₀y
    ((force_bigAnd_iff M u₀ _).mp hu₀χ D
      (List.mem_filter.mpr ⟨hD, decide_eq_true hxD⟩))

/-- The ∀∃-descent, merged with the ψ-witness by the confluence square
in `M`: the covering row-member can be taken to force ψ as well
(persistence keeps both along the square). -/
theorem reservoir_row_cover_witness {α β : Nat} (hαβ : α + 3 ≤ β)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {k' : K.W} {m' m u' : M.W} {ψ : PLLFormula}
    (hZ' : bandAgree β K M k' m') (him : M.Ri m' m)
    (hmu' : M.Rm m u') (hψ : M.force u' ψ)
    {L : List PLLFormula}
    (hL : ∀ D ∈ L, crank D ≤ α ∧ ∀ a ∈ D.atoms, a ∈ (∅ : Finset String))
    {x : K.W} (hx : K.Rm k' x) :
    ∃ y : M.W, M.Rm m y ∧ M.force y ψ ∧
      ∀ D ∈ L, K.force x D → M.force y D := by
  obtain ⟨y0, hmy0, hcov⟩ := reservoir_row_cover hαβ hK hM hZ' him hL hx
  obtain ⟨y, hy0y, hu'y⟩ := hM hmy0 (M.sub_mi hmu')
  exact ⟨y, M.trans_m hmu' hu'y,
    M.force_hered (M.sub_mi hu'y) hψ,
    fun D hD hxD => M.force_hered hy0y (hcov D hD hxD)⟩

/-- **The K-side push-down**: with the reinstated triple edge
`k' Rᵢ k`, every `row(k')`-witness pushes into `row(k)` by one
confluence square — no link crossing, no rank cap, pure persistence
along `Rᵢ x z`. -/
theorem row_push_down {C : ConstraintModel} (hC : MutuallyConfluent C)
    {k' k x : C.W} (hik : C.Ri k' k) (hx : C.Rm k' x) :
    ∃ z : C.W, C.Rm k z ∧ C.Ri x z := by
  obtain ⟨z, hxz, hkz⟩ := hC hx hik
  exact ⟨z, hkz, hxz⟩

/-- **The two-sided saturation** (enabled by the reinstated edge): in
a ranked residue configuration, every world of `row(k')` is
simultaneously pushed into `row(k)` by the K-side square AND covered
inside `row(m)` by a ψ-carrying witness, at every rank
`α ≤ rslope (2d+1) − 3`.  Both rows saturate over `row(k')`'s types —
the geometry the maximal-type ascent needs; the missing exact-match
ingredient (the backward leg) is now the entire content of
`RankGapGrow`. -/
theorem config_two_sided_saturation {α : Nat}
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {cl : Finset PLLFormula} {Δ : (canonFinC cl).W}
    {k' k : K.W} {m' m u' : M.W} {ψ : PLLFormula}
    (hik : K.Ri k' k) (him : M.Ri m' m)
    (hmu' : M.Rm m u') (hψ : M.force u' ψ)
    (hαβ : α + 3 ≤ rslope (2 * canonDepthC cl Δ + 1))
    (hZ' : bandAgree (rslope (2 * canonDepthC cl Δ + 1)) K M k' m')
    {L : List PLLFormula}
    (hL : ∀ D ∈ L, crank D ≤ α ∧ ∀ a ∈ D.atoms, a ∈ (∅ : Finset String))
    {x : K.W} (hx : K.Rm k' x) :
    (∃ z : K.W, K.Rm k z ∧ K.Ri x z) ∧
    (∃ y : M.W, M.Rm m y ∧ M.force y ψ ∧
      ∀ D ∈ L, K.force x D → M.force y D) :=
  ⟨row_push_down hK hik hx,
   reservoir_row_cover_witness hαβ hK hM hZ' him hmu' hψ hL hx⟩

/-! ## 2. Proved cases of `RankGap` -/

/-- A base is **row-rigid** when every infallible ◯-move is reflexive
(the lifted ladders of the deep battery are; so is every model whose
`Rₘ` is the identity plus fallible promotions). -/
def RowRigid (M : ConstraintModel) : Prop :=
  ∀ ⦃w u : M.W⦄, M.Rm w u → u ∉ M.F → u = w

/-- **`RankGap` over a row-rigid base** — the deep-probe live class as
a theorem: the given witness IS `m`, and `kb := k` closes by the base
link. -/
theorem rankGap_of_rowRigid (cl : Finset PLLFormula) (hrr : RowRigid M) :
    RankGap K M cl := by
  intro Δ k' k kv κ m' m u' ψ _hbot hΔk _hΔk' hik _him hmu' hψ hu'F _hZ' hZ
    _hk'kv _hZkv _hsame _hkκ _hZκ _hκsame
  have hum : u' = m := hrr hmu' hu'F
  subst hum
  exact ⟨k, u', hΔk, hik, hmu', hψ, hZ⟩

/-- `MwitResidue` for the ranked link over a row-rigid base — PROVED. -/
theorem mwitResidue_ranked_of_rowRigid (hPK : POnly p K) (hPM : POnly p M)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (cl : Finset PLLFormula) (hrr : RowRigid M) :
    MwitResidue cl (rankedB hPK hPM hK hM) :=
  mwitResidue_ranked_of_gap hPK hPM hK hM cl (rankGap_of_rowRigid cl hrr)

/-- **The window fact** (the cl-side mirror of
`residue_growth_boundary`, at the ranked slope): in a residue
configuration, the witness's cl-VISIBLE variable-free growth at
window-floor rank is EMPTY — every variable-free `D ∈ cl` of crank
`≤ rslope (2d − 1)` forced by `u'` already lies in `Δ.val` (the
κ-partner forces it too and its trace keeps `Δ`).  Consequences:
(a) any witness growth that could finance a GROWN answer through a
closure enlarged with low-rank representatives is already absent —
the enlargement bootstrap also fails for a second reason: the rank it
needs (`rslope (2·|cl|)`) grows faster in `|cl|` than any finite
representative stock can close (the fragment is infinite, two fresh
classes per crank); (b) with `rankGap_of_grow`, EVERY attack now
reduces to the single window `(rslope (2d−1), rslope (2d)]`: the
backward reflection is capped at `rslope (2d) − 3` by the base link,
witness growth below the window is contradictory (this lemma), and a
base-spend same-trace answer would need `b − 1 ≥ b`.  The window is
scale-invariant across all routes — either it is uncrossable and
`RankGapGrow` has a countermodel (necessarily with NON-ROW-RIGID
`M`-rows and deep variable-free structure: note the §51 battery was
row-rigid, so the grow case is EMPTY there and untested), or crossing
it needs machinery not yet in the toolbox. -/
theorem residue_window {cl : Finset PLLFormula}
    {Δ : (canonFinC cl).W} {k κ : K.W} {m u' : M.W}
    (hΔk : (traceT K cl k).val = Δ.1.val)
    (hZκ : bandAgree (rslope (2 * canonDepthC cl Δ - 1)) K M κ u')
    (hκsame : (traceT K cl κ).val = Δ.1.val)
    {D : PLLFormula} (hDcl : D ∈ cl) (hDa : D.atoms = ∅)
    (hDc : crank D ≤ rslope (2 * canonDepthC cl Δ - 1))
    (hu'D : M.force u' D) : D ∈ Δ.1.val := by
  have hκD : K.force κ D := (hZκ D hDa hDc).mpr hu'D
  have : D ∈ (traceT K cl κ).val := mem_traceT_val.mpr ⟨hDcl, hκD⟩
  rw [hκsame] at this
  exact this

/-! ## 3. The case split: the open Prop shrinks to the grow case -/

/-- **The residual open Prop**: the configurations in which EVERY
ψ-witness in `m`'s row strictly grows `m`'s variable-free theory at
rank `rslope (2d)`.  (If some witness adds nothing, `kb := k` closes
by transitivity through the base link — `rankGap_of_grow`.) -/
def RankGapGrow (K M : ConstraintModel) (cl : Finset PLLFormula) : Prop :=
  ∀ {Δ : (canonFinC cl).W} {k' k kv κ : K.W} {m' m u' : M.W}
    {ψ : PLLFormula},
    PLLFormula.falsePLL ∉ Δ.1.val →
    (traceT K cl k).val = Δ.1.val →
    (traceT K cl k').val = Δ.1.val →
    K.Ri k' k →
    M.Ri m' m → M.Rm m u' → M.force u' ψ → u' ∉ M.F →
    bandAgree (rslope (2 * canonDepthC cl Δ + 1)) K M k' m' →
    bandAgree (rslope (2 * canonDepthC cl Δ)) K M k m →
    K.Ri k' kv →
    bandAgree (rslope (2 * canonDepthC cl Δ)) K M kv u' →
    (traceT K cl kv).val ≠ Δ.1.val →
    K.Rm k κ →
    bandAgree (rslope (2 * canonDepthC cl Δ - 1)) K M κ u' →
    (traceT K cl κ).val = Δ.1.val →
    (∀ u'' : M.W, M.Rm m u'' → M.force u'' ψ →
      bandAgree (rslope (2 * canonDepthC cl Δ)) M M m u'' → False) →
    ∃ (kb : K.W) (u'' : M.W),
      (traceT K cl kb).val = Δ.1.val ∧ K.Ri k' kb ∧
      M.Rm m u'' ∧ M.force u'' ψ ∧
      bandAgree (rslope (2 * canonDepthC cl Δ)) K M kb u''

/-- **The case split**: a handler for the grow case yields the full
gap — in the stable case some witness adds nothing at rank
`rslope (2d)` and `kb := k` closes through the base link. -/
theorem rankGap_of_grow (cl : Finset PLLFormula)
    (h : RankGapGrow K M cl) : RankGap K M cl := by
  intro Δ k' k kv κ m' m u' ψ hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ
    hk'kv hZkv hsame hkκ hZκ hκsame
  by_cases hstab : ∃ u'' : M.W, M.Rm m u'' ∧ M.force u'' ψ ∧
      bandAgree (rslope (2 * canonDepthC cl Δ)) M M m u''
  · obtain ⟨u'', h1, h2, h3⟩ := hstab
    exact ⟨k, u'', hΔk, hik, h1, h2, bandAgree_trans_mid hZ h3⟩
  · exact h hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ hk'kv hZkv hsame hkκ hZκ
      hκsame (fun u'' h1 h2 h3 => hstab ⟨u'', h1, h2, h3⟩)

/-- **The stable-witness Prop** — the form the all-grow probe singles
out (2026-07-27 evening: its negation-shaped hypothesis fired on ZERO
of 258M instances across 31M configurations): in every residue
configuration, SOME ψ-witness in `m`'s row adds nothing to `m`'s
variable-free theory at rank `rslope (2d)`.  M-INTERNAL: no K-side
vocabulary in the conclusion. -/
def StableWitness (K M : ConstraintModel) (cl : Finset PLLFormula) : Prop :=
  ∀ {Δ : (canonFinC cl).W} {k' k kv κ : K.W} {m' m u' : M.W}
    {ψ : PLLFormula},
    PLLFormula.falsePLL ∉ Δ.1.val →
    (traceT K cl k).val = Δ.1.val →
    (traceT K cl k').val = Δ.1.val →
    K.Ri k' k →
    M.Ri m' m → M.Rm m u' → M.force u' ψ → u' ∉ M.F →
    bandAgree (rslope (2 * canonDepthC cl Δ + 1)) K M k' m' →
    bandAgree (rslope (2 * canonDepthC cl Δ)) K M k m →
    K.Ri k' kv →
    bandAgree (rslope (2 * canonDepthC cl Δ)) K M kv u' →
    (traceT K cl kv).val ≠ Δ.1.val →
    K.Rm k κ →
    bandAgree (rslope (2 * canonDepthC cl Δ - 1)) K M κ u' →
    (traceT K cl κ).val = Δ.1.val →
    ∃ u'' : M.W, M.Rm m u'' ∧ M.force u'' ψ ∧
      bandAgree (rslope (2 * canonDepthC cl Δ)) M M m u''

/-- **`RankGap` from the stable witness**: `kb := k` closes by
transitivity through the base link — the positive branch of the case
split, now fed by the empirically universal Prop. -/
theorem rankGap_of_stableWitness (cl : Finset PLLFormula)
    (h : StableWitness K M cl) : RankGap K M cl := by
  intro Δ k' k kv κ m' m u' ψ hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ
    hk'kv hZkv hsame hkκ hZκ hκsame
  obtain ⟨u'', h1, h2, h3⟩ :=
    h hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ hk'kv hZkv hsame hkκ hZκ hκsame
  exact ⟨k, u'', hΔk, hik, h1, h2, bandAgree_trans_mid hZ h3⟩

/-- **The forced inclusion**: in a residue configuration everything
`k` forces at full rank transfers to `kv` — persistence in `M` along
`Rₘ m u'` (so `type u' ⊇ type m`), transported through the two
full-rank links.  Half of the given witness's stability is free. -/
theorem internal_inclusion {r : Nat} {k kv : K.W} {m u' : M.W}
    (hZ : bandAgree r K M k m) (hZkv : bandAgree r K M kv u')
    (hmu' : M.Rm m u') :
    ∀ ρ : PLLFormula, ρ.atoms = ∅ → crank ρ ≤ r →
      K.force k ρ → K.force kv ρ := by
  intro ρ hρ hc hk
  exact (hZkv ρ hρ hc).mpr
    (M.force_hered (M.sub_mi hmu') ((hZ ρ hρ hc).mp hk))

/-- **The given witness's stability is K-internal**: `u'` adds nothing
to `m` at rank `r` iff `kv` adds nothing to `k` — the M side drops
out entirely, and `internal_inclusion` already forces one direction.
The minimal-type construction thereby reduces to THE GROWN PARTNER'S
VARIABLE-FREE INVISIBILITY: `kv`'s vf theory at rank `rslope (2d)`
equals `k`'s, its cl-trace growth being vf-invisible (p-laden).
Probe support: 258M/258M instances; a countermodel needs a
same-cl-trace, vf-differing K-pair COMPLETING to a full configuration
— the config-completion probe is the designed falsifier. -/
theorem stable_given_iff_internal {r : Nat} {k kv : K.W} {m u' : M.W}
    (hZ : bandAgree r K M k m) (hZkv : bandAgree r K M kv u') :
    bandAgree r M M m u' ↔ bandAgree r K K k kv :=
  ⟨fun h ρ hρ hc =>
    ((hZ ρ hρ hc).trans (h ρ hρ hc)).trans (hZkv ρ hρ hc).symm,
   fun h ρ hρ hc =>
    ((hZ ρ hρ hc).symm.trans (h ρ hρ hc)).trans (hZkv ρ hρ hc)⟩

/-- **`StableWitness` from the grown partner's invisibility**: if in
every configuration `kv` vf-agrees with `k` at full rank, the GIVEN
witness is stable and the whole chain closes. -/
theorem stableWitness_of_kvInvisible (cl : Finset PLLFormula)
    (h : ∀ {Δ : (canonFinC cl).W} {k' k kv κ : K.W} {m' m u' : M.W}
      {ψ : PLLFormula},
      PLLFormula.falsePLL ∉ Δ.1.val →
      (traceT K cl k).val = Δ.1.val →
      (traceT K cl k').val = Δ.1.val →
      K.Ri k' k →
      M.Ri m' m → M.Rm m u' → M.force u' ψ → u' ∉ M.F →
      bandAgree (rslope (2 * canonDepthC cl Δ + 1)) K M k' m' →
      bandAgree (rslope (2 * canonDepthC cl Δ)) K M k m →
      K.Ri k' kv →
      bandAgree (rslope (2 * canonDepthC cl Δ)) K M kv u' →
      (traceT K cl kv).val ≠ Δ.1.val →
      K.Rm k κ →
      bandAgree (rslope (2 * canonDepthC cl Δ - 1)) K M κ u' →
      (traceT K cl κ).val = Δ.1.val →
      bandAgree (rslope (2 * canonDepthC cl Δ)) K K k kv) :
    StableWitness K M cl := by
  intro Δ k' k kv κ m' m u' ψ hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ
    hk'kv hZkv hsame hkκ hZκ hκsame
  exact ⟨u', hmu', hψ,
    (stable_given_iff_internal hZ hZkv).mpr
      (h hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ hk'kv hZkv hsame hkκ
        hZκ hκsame)⟩

/-- The end-to-end summary: the grow case is all that separates the
ranked link from a residue-free amalgamation. -/
theorem mwitResidue_ranked_of_grow (hPK : POnly p K) (hPM : POnly p M)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (cl : Finset PLLFormula) (h : RankGapGrow K M cl) :
    MwitResidue cl (rankedB hPK hPM hK hM) :=
  mwitResidue_ranked_of_gap hPK hPM hK hM cl (rankGap_of_grow cl h)

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.reservoir_row_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reservoir_row_cover

/--
info: 'PLLND.SemUI.reservoir_row_cover_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reservoir_row_cover_witness

/--
info: 'PLLND.SemUI.config_two_sided_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms config_two_sided_saturation

/--
info: 'PLLND.SemUI.rankGap_of_rowRigid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rankGap_of_rowRigid

/--
info: 'PLLND.SemUI.mwitResidue_ranked_of_rowRigid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mwitResidue_ranked_of_rowRigid

/--
info: 'PLLND.SemUI.promotion_iff_internal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms promotion_iff_internal

/--
info: 'PLLND.SemUI.residue_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms residue_window

/--
info: 'PLLND.SemUI.rankGap_of_grow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rankGap_of_grow

/--
info: 'PLLND.SemUI.rankGap_of_stableWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rankGap_of_stableWitness

/--
info: 'PLLND.SemUI.stable_given_iff_internal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms stable_given_iff_internal

/--
info: 'PLLND.SemUI.stableWitness_of_kvInvisible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stableWitness_of_kvInvisible

/--
info: 'PLLND.SemUI.mwitResidue_ranked_of_grow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mwitResidue_ranked_of_grow

end SemUI
end PLLND
