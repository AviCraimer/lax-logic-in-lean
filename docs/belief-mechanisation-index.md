# Belief-in-Lax-Logic: machine-checked results index

*Status 2026-07-16. Every mathematical claim the paper states as established is
backed by a `sorry`-free, axiom-audited Lean file on branch
`claude/belief-lax-logic-handover-f331bf` (worktree). Audit key: **clean** =
`[propext, Classical.choice, Quot.sound]`. Nothing is committed — the files are
untracked, for review.*

*Policy (Matthew, 2026-07-16): nothing in `wip/` is ever claimed as formally
proved; claimable results live in the `LaxLogic/` library. The belief files
below were promoted accordingly on 2026-07-16 (with `closedNucleus` /
`nucleus_eq_sup_bot` deduplicated into the shared base `BeliefCollapse`).*

| file | key results | audit | paper § |
|---|---|---|---|
| [`LaxLogic/BeliefCollapse.lean`](../LaxLogic/BeliefCollapse.lean) | `closedNucleus` (shared base); `nucleus_eq_sup_bot` (`j x = x ⊔ j⊥`); `eq_id_of_bot_eq_bot` (sceptic); `eq_top_of_bot_eq_top` (credulous) | clean | §2A / §3b-1 |
| [`LaxLogic/BeliefBooleanIso.lean`](../LaxLogic/BeliefBooleanIso.lean) | `nucleusOrderIsoBot : Nucleus B ≃o B` — the sharp `N(B) ≅ B` via `j ↦ j⊥` | clean | §2A / §3b-1 |
| [`LaxLogic/BeliefNormality.lean`](../LaxLogic/BeliefNormality.lean) | `nucleus_himp_le` (K axiom `◯(A→B)→(◯A→◯B)`); `nucleus_top` (`◯⊤=⊤`) | clean | §2 — `◯` is a *normal* modality (corrects the earlier "not normal") |
| [`LaxLogic/BeliefIdealisation.lean`](../LaxLogic/BeliefIdealisation.lean) | `belief_introspection` (`◯◯M⊣⊢◯M`); `belief_consequence` (`Γ⊢M ⟹ ◯Γ⊢◯M`, logical omniscience); `belief_necessitation`; `nucleus_listInf` (`⋀◯Γ=◯⋀Γ`) | clean | §2E |
| [`LaxLogic/BeliefOpenClosed.lean`](../LaxLogic/BeliefOpenClosed.lean) | `openNucleus`; `openNucleus_eq_closedNucleus` (BA: open = closed); `em_of_openNucleus_eq_closedNucleus` (open=closed ⇒ EM at `a`); `open_ne_closed_Fin3` (separation) | clean | §2B / §3b-2 |
| [`LaxLogic/BeliefFalsum.lean`](../LaxLogic/BeliefFalsum.lean) | `belief_no_D` (`⊬¬◯⊥`); `belief_bot_not_provable` (`⊬◯⊥`); `belief_credulous` (`◯⊥⊢◯M`) | clean | §2E / §3b-4 |
| [`LaxLogic/BeliefExamples.lean`](../LaxLogic/BeliefExamples.lean) | `chain3_card=4` (+ sceptic/credulous/closed/open exhibited, `chain3_open_ne_closed`); `chain4_card=8`; `boolean22_card=4` | 3-chain clean; `chain4_card`,`boolean22_card` add `ofReduceBool` (native_decide) | §5 / §3b-5 |
| [`LaxLogic/BeliefRealisability.lean`](../LaxLogic/BeliefRealisability.lean) *(promoted from `wip/` 2026-07-18, D1)* | `realU`/`realS` + heredity/fallible saturation; the four separations (`bite_uniform_split`, `uniform_dist_valid`, `strategy_realises_obAB`/`strategy_dist_refuted`, `impdist_not_uniform`); local-operator laws incl. `ob_strength`; `force_somehow_iff_notnot`; `Poly.abs_spec`; extraction `extract_sound`/`extractS_sound`; **the obstruction `realS_fullness_obstruction`** | 31 audits pinned in-file; obstruction + `Poly.abs_spec` **[p,Q]** (no choice); separations/extraction clean; `uniform_dist_valid`, `ob_*`, heredity axiom-free | paper §5, §7 |

## Added 2026-08-07 — the closed-fragment ladder (paper §3.1)

*Every result below is `sorry`-free with its `#print axioms` pinned in-file.
**They are nevertheless NOT yet claimable** under the 2026-07-16 policy above:
all but `varfree_dichotomy` live in `wip/`. Promotion to `LaxLogic/` is a
precondition for the paper §3.1 text that cites them.*

**Which command checks what — corrected 2026-08-07.** `lakefile.toml` sets
`defaultTargets = ["LaxLogic"]`, so plain **`lake build` does NOT check any
`wip/` module**, including the `wipshared` glob. It builds 8663 jobs, all of
them `LaxLogic/`. The `wip/` pins are run by

```
lake build wipshared
```

which is 3126 jobs and is green as of 2026-08-07. An earlier version of this
section credited the `wip/` rows to `lake build`; that was wrong. The rows now
say which command actually runs them.

| file | key results | audit | build path | paper § |
|---|---|---|---|---|
| `wip/linear.lean` | `varfree_exactly_six` (+`_wem0`), `six_pairwise`, `box_nobot`, `dist_of_lin`, `wem_of_lin`, `derivLin_iff_valid` (completeness for connected models), `canonL_connected`, `truthL` | clean | `lake build wipshared` | §3.1 Thm, Props |
| `wip/classical.lean` | `varfree_exactly_four` (+`_em0`), `four_distinct`, `box_nobot_em`, `box_trivial` (F&M p. 6, machine-checked), `K_does_not_force_dist`, `nucleus_eq_closed`, `nucleus_not_closed_Fin3` | clean | `lake build wipshared` | §3.1 Thm, Props |
| `wip/schemeext.lean` | `DerivX`/`Interd` — the scheme-extension harness both rungs run on (`chain_classify`, `combine`, `dich_*`) | (no pins in-file) | `lake build wipshared` | §3.1 infrastructure |
| `wip/depth.lean`, `depth2.lean`, `depth3.lean` | `depth_box_gap_one_exact` (class depth of `◯g₁` is exactly 3, so `D₂ ⊊ D₃`), `depth_three_is_inhabited`, `not_derivU_box_atom` | `[propext]` / `[propext, Quot.sound]` / clean | `lake build wipshared` | §3.1 depth para |
| `wip/visible.lean` | `Visible`; `visible_top`, `visible_rnSub_{one,two,four,six}`, `visible_gap_zero`; `not_joinPrime_rnSub_odd` (whole odd family from `t₃`); the PLL Harrop lemma | clean / `[propext, Quot.sound]` | **NOT on the build path** — needs `rnEmbed.olean` on `LEAN_PATH` (see note) | §3.1 visibility para |
| `wip/converseK.lean` | `converseK_fails_infallible`, `converseK_fails_fallible` (`◯A ⊃ ◯B ⊬ ◯(A ⊃ B)`; the first model is linear) | `[propext, Quot.sound]` | not registered; checks standalone | §3.1 Prop (dist) |
| `wip/negFour.lean` *(new 2026-08-07)* | `neg_exactly_four` — for every variable-free `A`, `¬A ⊣⊢` one of `⊥`, `¬◯⊥`, `¬¬◯⊥`, `⊤`. Since `𝔟⊥` (the regular elements) is the **image of `¬`**, this bounds the booleanization of RN(◯,{}) at four. Holds over an arbitrary axiom set `X`. | clean | `lake build wipshared` (registered) | candidate §3.1 |
| [`LaxLogic/PLLNoFall.lean`](../LaxLogic/PLLNoFall.lean) | `varfree_dichotomy` — the two-element rung; already in the library | clean | `lake build` | §3.1 Thm cl. (4) |

**Two facts recorded on measurement, 2026-08-07.**

1. `wip/visible.lean` is **not checked by `lake build`**. It imports `rnEmbed`
   (root-level module name), not `wip.rnEmbed`, so the `wipshared` glob does not
   cover it and its 25 audit blocks are never exercised by a normal build. It
   does check clean, via
   `lake env sh -c 'LEAN_PATH="$LEAN_PATH:<dir>" lean wip/rnEmbed.lean -o <dir>/rnEmbed.olean'`
   then the same for `wip/visible.lean`. Either the import should be renamed and
   the module registered, or the recipe recorded, before anything in the paper
   leans on it.
2. `visible_gap_zero` is **not a sixth visible class**: `interd_gap_zero_top`
   proves `g 0 ⊣⊢ ⊤`, so it is ⊤'s class. Five distinct interderivability
   classes are proved visible (`⊤`, `t₁`, `t₂`, `t₄`, `t₆`). `docs/rn-explorer.html`
   v12 says "six points PROVED visible" and should be corrected to five.

**Prior results reused** (from `main`, promoted to the library 2026-07-16):
`thm6` (context completeness — §6), `closed_lax_infinite` (infinite closed
fragment — §2B/§5), `thm2_boolean_algebra`, `corollary10` — now in
[`LaxLogic/PLLCtxCompleteness.lean`](../LaxLogic/PLLCtxCompleteness.lean) and
[`LaxLogic/PLLLaxInfinite.lean`](../LaxLogic/PLLLaxInfinite.lean).
Object-logic `◯`-laws cited: `somehowR`/`somehowM`/`somehowS`/`somehowFunctor`
(`PLLTheorems.lean`), `not_provable_not_somehow_false` (`PLLFrames.lean`).

**Literature sources** (prose, verified citations):
`docs/iel-justification-lit.md` — IEL⁻ / justification-logic positioning (§8);
`docs/realisability-modal-lit.md` — realisability model-theory direction (§9), incl.
the four-frameworks comparison, the metatheory-vs-object-theory verdict, and the
local-nucleus-stability analysis.

**Consolidation note — RESOLVED (2026-07-16).** The formerly duplicated
`closedNucleus`/`closedNucleus_apply` and `nucleus_eq_sup_bot` now live once, in
the shared base `BeliefCollapse`, imported by `BeliefBooleanIso` and
`BeliefOpenClosed`; all nine belief/Curry modules are imported by the library
root `LaxLogic.lean`, so `lake build` checks everything.
