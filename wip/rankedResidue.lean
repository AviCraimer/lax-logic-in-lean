import wip.rankedM
import wip.witOut

/-!
# The block on the key lemma: `MwitResidue` for the ranked link

Branch `ui-confluence`.  The direct attempt on

    theorem mwitResidue_ranked :
      MwitResidue cl (rankedB hPK hPM hK hM)

reaches, after introductions (and with the `Z`-hypotheses displayed as
the band agreements they definitionally are), the following proof
state — THE BLOCK (captured verbatim from the attempt, `d`
abbreviating `canonDepthC cl Δ`):

    hΔk  : (traceT K cl k).val  = Δ.val      hbot : ⊥ ∉ Δ.val
    hΔk' : (traceT K cl k').val = Δ.val
    him  : M.Ri m' m     hmu' : M.Rm m u'
    hψ   : M.force u' ψ  hu'F : u' ∉ M.F
    hk'kv : K.Ri k' kv   hsame : (traceT K cl kv).val ≠ Δ.val
    hkκ   : K.Rm k κ     hκsame : (traceT K cl κ).val = Δ.val
    hZ'  : bandAgree (rslope (2d + 1)) K M k' m'
    hZ   : bandAgree (rslope (2d))     K M k  m
    hZkv : bandAgree (rslope (2d))     K M kv u'
    hZκ  : bandAgree (rslope (2d − 1)) K M κ  u'
    ⊢ ∃ u'' Δ', M.Rm m u'' ∧ M.force u'' ψ ∧
        (canonFinC cl).Rm Δ Δ' ∧ WitTripleC cl (rankedB …) Δ' u''

## Why each available move fails (the ledger)

The conclusion space is EXACTLY: (i) proper-triple answers, which are
trace-realised — a K-world `kb` with `(traceT kb).val = Δ.val` (a
reflexive canonical move, reusing the reservoir) or a strictly grown
trace financed by a depth drop; and (ii) top answers, which need
`⊥ ∈ Δ'.val` and hence FULL ◯-anticipation of `cl` at `Δ` (rare).
A same-trace proper answer needs a base link at rank `rslope (2d)`.

* The κ-partner (`hZκ`) has the right trace but rank
  `rslope (2d − 1)` — the window `(rslope (2d−1), rslope (2d)]` is
  exactly what is missing.  Promotion across the window is the
  stabilisation question; the fragment is INFINITE
  (wip/rnEmbed.lean), so no global promotion exists.
* The kv-partner (`hZkv`) has full rank but the wrong trace, and
  being an i-successor of `k'` it finances no canonical `Rₘ`-move
  (no anticipation).
* Every witness-clause spend (`rankedMwit`/`rankedMwitM`) at the base
  returns partners at rank `rslope (2d) − 3`-worth — i.e. level
  `2d − 1` — one short, structurally: a same-trace answer financed by
  a base-level spend would need `b(d) − 1 ≥ b(d)`.  Iterated spends
  strictly descend (each step burns `+3` of rank), while a fresh
  triple even after a depth DROP needs `rslope (2(d−1) + 1)
  = rslope (2d − 1)` — the whole starting rank, so not one step of
  walk is affordable.
* The reservoir spend (`B.iback` at `hZ'`) DOES return full-level
  partners (that is where `kv` came from), but their traces are
  adversarial; the residue hypothesis is precisely that they grow.

## What this file proves

The block is EXTRACTED as the displayed Prop `RankGap` — in every
configuration, SOME same-trace K-world and SOME ψ-row-witness agree at
the full rank — and:

* `mwitResidue_ranked_of_gap` (PROVED): `RankGap ⟹ MwitResidue` for
  the ranked link.  So the ONE open Prop of the route is now the pure
  two-sorted matching statement `RankGap`, with no canonical-model
  vocabulary on the obligation side beyond the traces.
* `rankGap_of_promotion` (PROVED): pointwise promotion of the
  κ-partner across the window implies `RankGap` — the regime of ALL
  probe evidence (~330M instances, every configuration inside it).

## Status of the evidence (PROGRESS §50)

Both probe families resolved every configuration at the given witness
via stabilised links; the live (descending) window was EMPTY on the
battery, and by the ladder-needs-depth fact, genuine descent at the
financed levels needs large models.  So the evidence supports
`RankGap` exactly as far as stabilisation reaches, and says nothing
yet about the descending regime — the deep-model probe
(wip/mwit_deep.lean) hunts precisely there.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-- **The extracted block**: in every ranked residue configuration,
some same-trace K-world and some ψ-row-witness agree at the FULL rank
`rslope (2d)`.  (The probe evidence verifies this with `kb := κ`,
`u'' := u'` wherever the link chain has stabilised.) -/
def RankGap (K M : ConstraintModel) (cl : Finset PLLFormula) : Prop :=
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
    ∃ (kb : K.W) (u'' : M.W),
      (traceT K cl kb).val = Δ.1.val ∧ K.Ri k' kb ∧
      M.Rm m u'' ∧ M.force u'' ψ ∧
      bandAgree (rslope (2 * canonDepthC cl Δ)) K M kb u''

/-- **The bridge**: the gap pays the residue — the reflexive canonical
answer with the reservoir reused and `(kb, u'')` as the fresh base. -/
theorem mwitResidue_ranked_of_gap (hPK : POnly p K) (hPM : POnly p M)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (cl : Finset PLLFormula) (hgap : RankGap K M cl) :
    MwitResidue cl (rankedB hPK hPM hK hM) := by
  intro _hK' Δ k' k kv κ m' m u' ψ _hcl hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ
    hk'kv hZkv hsame hkκ hZκ hκsame
  obtain ⟨kb, u'', hkb, hikb, hmu'', hψ'', hagr⟩ :=
    hgap hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ hk'kv hZkv hsame hkκ hZκ hκsame
  exact ⟨u'', Δ, hmu'', hψ'', (canonFinC cl).refl_m Δ,
    .proper k' kb m' hkb hΔk' (M.trans_i him (M.sub_mi hmu'')) hZ' hagr hikb⟩

/-- **The promotion bridge** — the regime of all probe evidence:
pointwise promotion of the κ-partner across the missing rank window
implies the gap, with `kb := κ` and `u'' := u'`. -/
theorem rankGap_of_promotion (cl : Finset PLLFormula)
    (h : ∀ {Δ : (canonFinC cl).W} {κ : K.W} {u : M.W},
      bandAgree (rslope (2 * canonDepthC cl Δ - 1)) K M κ u →
      bandAgree (rslope (2 * canonDepthC cl Δ)) K M κ u) :
    RankGap K M cl := by
  intro Δ k' k kv κ m' m u' ψ _hbot _hΔk _hΔk' hik _him hmu' hψ _hu'F _hZ' _hZ
    _hk'kv _hZkv _hsame hkκ hZκ hκsame
  exact ⟨κ, u', hκsame, K.trans_i hik (K.sub_mi hkκ), hmu', hψ, h hZκ⟩

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.mwitResidue_ranked_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mwitResidue_ranked_of_gap

/--
info: 'PLLND.SemUI.rankGap_of_promotion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rankGap_of_promotion

end SemUI
end PLLND
