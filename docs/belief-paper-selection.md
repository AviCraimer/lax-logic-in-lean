# Belief in Lax Logic — theorem selection for the 12-page submission

*Drafted 2026-07-18 against draft revision 2 (`docs/belief-paper-draft.md` at
`fb7f61c`), the statement ledger (`docs/pll-formalisation-ledger.md`), the
mechanisation index (`docs/belief-mechanisation-index.md`), the annotated
walk-throughs (`docs/annotated/`), and the bibliography map
(`docs/belief-bib-map.md`, 119 entries). This is an editorial cut plan for
Matthew's sign-off: every mechanised result the paper touches, with a proposed
display form, an appendix architecture, and a page budget. Decisions the
assistant should not make alone are collected in §6.*

**Display forms.**

| code | meaning |
|---|---|
| **thm** | numbered, displayed statement in the main text |
| **prose** | asserted in running text with its Lean name; no displayed statement |
| **app** | formal statement (Lean, verbatim) in an appendix |
| **omit** | not in the paper |

Combinations mean both (e.g. **thm+app** = numbered informal statement in the
text, exact Lean statement in the appendix). Audit key as in the ledger:
**none** ⊂ **[p]** ⊂ **[p,Q]** (no choice) ⊂ **clean**
(`[propext, Classical.choice, Quot.sound]`); ‡ = statement-tainted
(`List.toFinset`/`Finset.toList` in the statement vocabulary — cannot audit
below clean by any proof).

---

## 0. Constraints the selection works under

1. **The machine-checked mandate** (handover §0(a)): a result is citable as
   established only if its Lean proof is `sorry`-free, axiom-audited, **and in
   the `LaxLogic/` library** — the promotion policy of 2026-07-16 explicitly
   excludes `wip/` from claimability. See the blocker in §1.
2. **Page limit.** Working assumption, per Matthew: 12 pages of main text, with
   references and appendices outside the limit (CPP practice; verify against
   the CPP 2027 call when it appears, including whether reviewers are told
   appendices are optional reading).
3. **Current size.** Draft rev 2 is ~7,900 words + 20 displayed Lean/output
   blocks. Rough two-column estimate: ~8 pp of prose + ~2.5–3 pp of displays
   and headings ≈ **11–12.5 pp main matter before any changes** — i.e. at the
   limit with no room for the additions below unless §6–§7 are compressed.
   Word weight by section: §6 completeness 2,428 w and §7 theory-run 1,350 w
   together carry half the paper; §8 related work (204 w) is under-built
   relative to the bib map and must grow. The TeX skeleton (next step after
   this table is agreed) turns these estimates into real numbers.

---

## 1. ~~BLOCKER~~ RESOLVED (2026-07-18, D1 executed) — the `wip/` results are promoted

The whole of §5 as drafted, plus three results cited in §7–§8, lived only in
`wip/belief_realisability.lean`. Promoted 2026-07-18 to
[`LaxLogic/BeliefRealisability.lean`](../LaxLogic/BeliefRealisability.lean)
(root-imported; the file uses the library's `Pca`/`Evidence` from
`PLLEvidence.lean` — no duplication), with **all 31 audits measured and
`#guard_msgs`-pinned in-file**. Measured audits of the paper-cited results:

| draft cite | Lean name | measured audit |
|---|---|---|
| §5 the bite | `bite_uniform_split` | clean |
| §5 uniform validates distribution | `uniform_dist_valid` | **none** (axiom-free) |
| §5 strategy realises ◯(A∨B) | `strategy_realises_obAB` | clean |
| §5 distribution refuted for ⊩ˢ | `strategy_dist_refuted` | clean |
| §5 the ⊃-barrier | `impdist_not_uniform` | clean |
| §5 the obstruction (→ Thm 5.2) | `realS_fullness_obstruction` | **[p,Q]** — matches the draft's claim |
| §7 uniform extraction | `extract_sound` | clean |
| §7 strength / ordered composition | `ob_strength` | **none** (axiom-free) |
| §8 double-negation believer | `force_somehow_iff_notnot` | clean |

No draft claim is falsified: the draft asserts a specific audit only for the
obstruction (`[propext, Quot.sound]` — confirmed). §9's "no choice … for the
obstruction" stands. Everything the draft asserts is now in the library.

---

## 2. Selection table

### §2 The mechanised base

The section's job is one paragraph of systems + one display of the semantics.
Everything formal goes to Appendix A — which, note, is **already drafted**: the
ledger's Part II is precisely the definitions-and-statements appendix, needing
only trimming and renumbering.

| result | Lean name | audit | draft now | proposed |
|---|---|---|---|---|
| ND / sequent / Hilbert / term calculi + equivalences | `LaxND`, `SC`, `Hd`, `Tm`; `cutElimination`, `hd_iff_ND`, `G4c.equiv_tm` | [p,Q] ([p] Hilbert) | prose | prose+app |
| Cut admissibility, disjunction property, ◯-reflection | `SC.cut`, `disjunction_property`, `somehow_reflection` | [p,Q] | prose | prose+app |
| Conservativity over IPL | `conservativity_IPL` | [p,Q] | **absent** | **add**: prose clause+app (the believer extends the intuitionist conservatively — one sentence, doxastically apt) |
| Strong extensionality (F&M 2.5) | `strong_extensionality` | [p,Q] | absent | omit (or app-only; nothing in the belief argument uses it) |
| SN of β + let-assoc (⊤⊤-lifting) | `strong_normalisation`, `Tm.normalize_spec` | clean | prose | prose+app (App D); priority sentence now sourced — see §3 below |
| Decidability via repaired G4 | `decidablePLL`, `decidableG4c` | [p,Q] | prose | prose+app |
| Naive G4iLL incomplete (gap + repair) | `sep_SC`, `sep_not_G4`, `contraction_not_admissible`, `cut_not_admissible` | clean/[p] | prose | prose+app (gap sequent displayed in App A) |
| **Craig interpolation** | `craig_interpolation'`, `craig_implication'` (choice-free after the D4 scrub; `∪`/`∩` wrappers kept) | **[p,Q]** | **absent** | **add**: prose sentence in §2 + app statement (primed forms) — no audit caveat needed |
| Constraint models + forcing (Defs 3.1–3.2) | `ConstraintModel`, `force` | (defs) | displayed | keep abbreviated display; full structure in App A |
| Soundness | `soundness` | [p] | prose | prose+app |
| Classical completeness (Zorn foil) | `completeness` | clean | prose | prose+app |

### §3 Classical collapse; constructive richness; the doxastic profile

| result | Lean name | audit | draft now | proposed |
|---|---|---|---|---|
| **Thm 3.1** collapse + N(B) ≅ B | `nucleus_eq_sup_bot`, `nucleusOrderIsoBot` | clean | thm | thm+app (App B) |
| **Thm 3.2** open=closed ⇔ EM at a; infinite closed fragment | `openNucleus_eq_closedNucleus`, `em_of_openNucleus_eq_closedNucleus`, `open_ne_closed_Fin3`, `closed_lax_infinite` | clean | thm | thm+app |
| **Thm 3.3** context completeness + no finite constraint set | `Ctx.thm6`, `Ctx.corollary10` | clean | thm | thm+app |
| Sceptic / credulous poles | `eq_id_of_bot_eq_bot`, `eq_top_of_bot_eq_top` | clean | prose | prose+app |
| Normality (K), ◯⊤=⊤ | `nucleus_himp_le`, `nucleus_top` | clean | prose (§9 mentions the refuted "not normal") | prose+app |
| Introspection ◯◯M ⊣⊢ ◯M; omniscience Γ⊢M ⟹ ◯Γ⊢◯M; necessitation | `belief_introspection`, `belief_consequence`, `belief_necessitation` | clean | prose | **candidate promotion to a numbered Proposition 3.4** ("the doxastic profile", bundled with the row below) — D2 |
| No D; ◯⊥ unprovable; credulous collapse | `belief_no_D` (= `not_provable_not_somehow_false`), `belief_bot_not_provable`, `belief_credulous` | clean / [p,Q] | prose | same bundle — D2 |
| Believer enumerations on small algebras | `chain3_card = 4` (+ menagerie, `chain3_open_ne_closed`); `chain4_card = 8`, `boolean22_card = 4` | clean; native_decide flagged | **absent** | **add**: short §3 paragraph or table for the 3-chain (clean); D3 decides the rest |
| The constraint algebra 𝕊 is Boolean | `Ctx.thm2_boolean_algebra` | [p,Q] | absent | **add**: one prose sentence (suggested home §6.2 or §3 close): *constructive* belief over a *Boolean* algebra of grounds — the contrast is exact. D5 |

### §4 Evidence

| result | Lean name | audit | draft now | proposed |
|---|---|---|---|---|
| Applicative structure; evidence assignments | `Pca`, `Evidence` | (defs) | displayed (abbrev.) | keep abbreviated; full defs App B |
| The three clause families ⊩ᵘ ⊩ˢ ⊩ᵖ | `realU`, `realS`, `realP` | (defs) | ⊩ᵘ prose-displayed, ⊩ˢ/⊩ᵖ Lean-displayed | keep the two Lean displays (they carry §5); all three in full in App B |
| Heredity; fallible fullness | `realU_hered`, `realS_hered`, `realP` analogues, `*_of_fallible` | in-file | prose ("heredity … is a theorem") | prose+app |

### §5 Separations and the obstruction *(all rows: promotion blocker, §1)*

| result | Lean name | draft now | proposed |
|---|---|---|---|
| The bite: truth outruns rigid evidence | `bite_uniform_split` | prose | **Thm 5.1(i)** — D2 |
| ⊩ᵘ validates ◯(A∨B)⊃(◯A∨◯B); PLL does not | `uniform_dist_valid` + `not_provable_somehow_or_dist` | prose | **Thm 5.1(ii)** |
| Strategy restores both | `strategy_realises_obAB`, `strategy_dist_refuted` | prose | **Thm 5.1(iii)** |
| The ⊃-barrier | `impdist_not_uniform` | prose | **Thm 5.1(iv)** |
| **The obstruction** | `realS_fullness_obstruction` | thm (5.1) + full proof in text | **Thm 5.2** + keep the in-text proof (it is the paper's pivot and fits in ~⅓ page); Lean statement already displayed — keep; App B carries the frame data |

Rationale for numbering the triptych: the four separations are the evidence
for the section's moral and are currently invisible in the theorem inventory a
referee skims. One numbered theorem with four parts costs ~6 lines.

### §6 Completeness *(compression target: −0.5 pp)*

| result | Lean name | audit | draft now | proposed |
|---|---|---|---|---|
| Checked finite frames; reflection | `FinCM`, `forceB`, `force_iff` | [p,Q] | prose | prose+app (App C) |
| **Thm 6.1** adequacy + fullness | `realP_adequate_and_full` | [p,Q] | thm + Lean display + ~600 w proof sketch | keep thm + display; **cut the ∨/◯ case detail** to App C (keep the ⊃ case and the "witness is a function of worlds" remark — they answer the obstruction); −0.3 pp |
| The squeeze (open + closed forms) | `realP_refutes_sequent`, `realP_refutes_sequent_tbl` | [p,Q] | prose | prose+app |
| Table algebra discharging the capacities | `Tbl`, `tblPca` | [p] | prose | prose+app |
| Consistency is one decidable check | `cons_iff_rep` (clean twin `cons_iff_check`‡) | [p,Q] | prose | prose+app — cite the primed form; D4 |
| Decided Lindenbaum | `extendStep`, `lindenbaum` | [p,Q] | `extendStep` displayed | keep display (the emblem of the method); `lindenbaum` statement App C |
| Totality simplifies the maximal-theory suite | `MaxIn.*` | [p,Q] | prose (the primeness example) | keep the primeness example; rest App C |
| **Thm 6.2** truth lemma | `truth_lemma` | [p,Q] | thm + three-case narrative | keep thm; compress the three cases by ~⅓ (full walk-through is App C / `finite-truth-lemma.md`) |
| **Cor 6.3** finite countermodels as checker data | `finite_canonical_countermodel`, `emitter_completeness` | [p,Q] | cor | cor+app |
| Audit discussion (toFinset taint; "no Gödelian obstruction") | — | ~250 w in §6.2 | move the Mathlib-taint paragraph to §9 (method) or a footnote; keep the oracle point — D9 |
| Remark 6.4 (the apparent circle) | — | ~420 w | keep, trimmed ~25% (it is distinctive; the import-graph point is the part a CPP audience will quote) — D6 |
| **Thm 6.5** the crown | `derivable_iff_no_realP_refutation` | [p,Q] | thm + Lean display | keep exactly as is |

### §7 The theory, run *(compression target: −0.5 pp)*

| result | Lean name | audit | draft now | proposed |
|---|---|---|---|---|
| ◯p ⊬ p executable countermodel | `somehow_p_not_p`, `demoM` | [p,Q] | displayed cert + prose | keep |
| Distribution: 20-world emitted model, printout | emitter output | — | verbatim printout | keep printout, halve the surrounding prose |
| Minimisation to the split model; attribute cleaning | `emitMin`, `emitMinClean` + pinned guards | [p,Q] | ~250 w | compress to ~120 w; pinned-guard details App C or artefact note |
| Remark 7.1 (preorder, not partial order) | `riEquiv`/`rmEquiv` guards | [p,Q] | ~420 w | trim ~40% (keep: same-belief twins, promise-refinement obstruction observation; cut: quotient/poset generalities) — D6 |
| Positive direction: extraction | `extract_sound` *(wip — §1)*, `ob_strength` *(wip)* | in-file | prose + term display | keep; statements App B |
| μ/η non-invertibility; not convertible | `mu_eta_not_mutually_inverse`, `eta_mu_not_conv_id` (+ `confluence`) | [p] / clean | prose | prose+app (App D); a candidate **Prop 7.2** if a number helps the referee — D2 |
| Frame-uniform vs frame-aware remark | — | ~130 w | keep verbatim (it earns its length) |

### §8–§10

| item | draft now | proposed |
|---|---|---|
| §8 related work | 204 w — too thin | grow to ~450–500 w from the bib map: IEL⁻/`HagemeierKirst2022`; justification-logic factivity; `Valliappan2026`; + the two strongest hidden connections (D7): authorization logic's `says` (`Abadi2006`, `GargAbadi2008` — published doxastic gloss of a lax modality) and topological evidence models (`BaltagBezhanishviliOzgunSmets2016` — Thm 3.1 explains their need for topology) |
| §9 method | 485 w | keep; add one sourced sentence: the artefact appears to be the **first mechanised ⊤⊤-lifting with sums** — sole prior mechanisation `DoczkalSchwinghammer2009` (Isabelle, core calculus, no sums), paper-form `Lindley2005` (η, no sums) — and one sentence on the choice-free surgery (handover A1) |
| §10 conclusion + open problems | 202 w | keep; open list stays: PLLᵘ axiomatisation, IEL⁻+idempotence conjecture, Kleene-algebra instantiation, tripos formulation, uniform interpolation (OPEN — distinct from the mechanised Craig) |
| Kleene–Brouwer well-foundedness | axiom-free standalone | stays a §9 half-sentence (as drafted); app statement only if App D has room |

---

## 3. Additions summary (new to the draft)

1. **Craig interpolation** — mechanised, absent from the draft. One §2
   sentence + App A statement. It also sharpens §10: uniform interpolation
   remains OPEN *while ordinary interpolation is settled*.
2. **Conservativity over IPL** — one §2 clause + App A.
3. **Small-algebra believer enumerations** — §3 paragraph (3-chain now;
   handover §3b-5 wants the 5-element non-linear Heyting algebra and
   `decide`-grade 4-chain/2×2 — **OPEN, new mechanisation**, D3).
4. **𝕊 is Boolean** — one sentence (D5).
5. **SN priority claim** — §9 sentence, now properly sourced by the bib
   update (`Lindley2005`, `DoczkalSchwinghammer2009`, `Prawitz1971`,
   `deGroote2002`).

## 4. Appendix architecture

| appendix | content | source (mostly written already) |
|---|---|---|
| **A. The mechanised base** | language, `LaxND`, `SCh`/`SC`, Hilbert schemes, `ConstraintModel`/`force`, soundness/completeness, decidability + gap sequent, conservativity, Craig | ledger **Part II** §II.1–II.6, II.8, II.11–II.12 — trim, renumber, de-link |
| **B. Evidence** | `Pca`, `Evidence`, ⊩ᵘ/⊩ˢ/⊩ᵖ in full, heredity, separation statements, obstruction statement + frame | `fullness-obstruction.md` + `PLLEvidence.lean` |
| **C. The finite canonical model** | `FTheory`, consistency formula, `extendStep`/`lindenbaum`, `MaxIn` suite, `canonFin`, truth lemma, `emitter_completeness` | `finite-truth-lemma.md`, `adequacy-fullness.md` (case detail cut from §6.1) |
| **D. The term calculus** | `Tm`/`Step` sketch, SN, normaliser, confluence, μ/η statements | ledger §II.7 + `strong-normalisation.md` (statements only — the walk-through stays repo-side) |
| **E. Artefact guide** (optional, D8) | file map, condensed audit table (ledger Part I), re-audit instructions | ledger Part I |

Resolution of the annotated-docs ownership question: `contraction.md` stays
with the companion paper; `strong-normalisation.md` serves both (belief paper
takes statements only); the three belief walk-throughs are cited as artefact
documentation, with App B/C carrying self-contained distillations.

## 5. Page budget

**MEASURED (2026-07-19, first TeX pour — `paper/belief.tex`, acmart
sigplan/screen/review, LuaLaTeX):** the full rev-2 draft typesets to
**≈8.7 pp of main matter** (§1 p1, §2–§3 p2, §4–§5 p3, §6 to p7, §7
p7–8, §8 p8, §9–§10 end p9), + appendix stubs and a 9-entry reference
list to p10. So there is **≈3.3 pp of headroom** under the 12-page
limit — the §6/§7 compressions below are now quality choices, not
page-forced, and the additions (§8 growth, §3 examples + Prop 3.4,
Thm 5.1 display, Craig sentence) fit comfortably. Caveats: prose
mathematics is still pour-time Unicode substitution (proper display
math will grow it somewhat), listings are `\footnotesize`, and the full
bibliography will add 1.5–2 pp of references (outside the limit on the
working assumption). The pre-TeX estimates below are retained for the
record; the measured column supersedes them.

### (superseded) working targets from the markdown estimate

| section | words now | target pp | note |
|---|---|---|---|
| abstract + §1 | 966 | 1.25 | trim abstract to ~250 w |
| §2 | 399 | 0.75 | +Craig, +conservativity sentences |
| §3 | 421 | 1.25 | +examples paragraph, +Prop 3.4 |
| §4 | 545 | 1.0 | |
| §5 | 774 | 1.5 | +Thm 5.1 display |
| §6 | 2,428 | 3.0 | −case detail, −audit paragraph, −6.4 trim |
| §7 | 1,350 | 1.75 | −minimisation prose, −7.1 trim |
| §8 | 204 | 0.5 | grows |
| §9 | 485 | 0.75 | +2 sentences |
| §10 | 202 | 0.25 | |
| **total** | | **≈ 12.0** | refs + App A–E outside the limit |

## 6½. MERGE PASS EXECUTED (2026-07-19, in `paper/`)

All rulings below are now applied to the TeX (which is the working
master; the markdown draft carries a supersession note): Craig +
conservativity in §2; 3-chain, 𝕊-Boolean and Prop 3.4 in §3; Thm 5.1
(separations, four parts) + Thm 5.2 (obstruction) in §5; §6.1 ∨/◯ case
detail moved to App C; taint paragraph moved §6.2→§9; Remarks 6.4/7.1
trimmed; Prop 7.2 in §7; §8 grown (KD45 baseline, topological evidence
models, authorization logic, mechanised neighbours); §9 audit-wrapper
wording + choice-surgery + SN-priority sentences; §10 Craig contrast.
Appendices A–E written in full (App A base, App B evidence/separations/
obstruction, App C canonical model + decoration witnesses, App D term
calculus, App E artefact guide). **Measured: 14 pp total — main matter
§1–§10 ends p9 (≈9.3 pp, ≈2.7 pp headroom), App A–E pp10–13,
references pp13–14; 0 missing glyphs, 0 undefined citations; automatic
counters reproduce 3.1–3.4, 5.1–5.2, 6.1–6.5, 7.1–7.2.** Polish round
DONE (2026-07-19 later): reflow complete (1 residual overfull, 1.7pt);
prose-math conversion (pour-time chains merged into real math, quotes
curled, "credulist" normalised); citation sweep to 44 cited entries;
countermodel diagrams inserted (Figs. 1–2, TikZ from PLLDiagram.lean);
the timing work (PLLTiming/PLLTimingAdder,
falsePath/skip_beats_topological AXIOM-FREE) claimed in §7.
CORRECTION (Matthew, 2026-07-19): that claim overstated — what exists
is the DELAY-ALGEBRA HALF only; Study 1 as specified (netlists+specs
formalised in the Route B evidence semantics, components composed
under a formally combined spec, ◯(out=spec) proved there, evidence
extracted via O3) is NOT completed — the realiser layer E is designed
but unimplemented. §7 reworded to claim exactly the half that is
proved; the applications draft gains Matthew's composition
requirement + a five-stage design brief for E (Study 1 (c′)).
FURTHER (2026-07-19 late): confluent-frame COMPLETENESS proved on
Matthew's ask — derivU_iff_confluent_valid (PLLConfluentComplete.lean,
clean-classical, pinned): PLL + ◯(A∨B)⊃(◯A∨◯B) sound+complete for
mutually confluent models; §10 claims both sides, open problem narrows
to PLLᵘ =? PLL + scheme.
Main matter now ends p10 (~9.8pp); App A–E pp11–13 (scriptsize
listings); references pp14–15. Two-column stays for camera-ready
(acmart/TAPS constraint); wide material's escape hatch is figure*.

## 6. Decisions — Matthew ruled 2026-07-18

- **D1 — promote now: YES. DONE** (see §1; audits pinned, root import added,
  `lake build` green).
- **D2 — numbering: all three ADOPTED.** Separations become displayed
  **Thm 5.1(i)–(iv)**; the obstruction becomes **Thm 5.2**; doxastic profile
  becomes **Prop 3.4**; μ/η non-isomorphism becomes **Prop 7.2**. To be
  implemented in the draft during the merge pass.
- **D3 — examples: RULED 2026-07-19 — 3-chain only.** The clean-audit
  3-chain enumeration is in §3; the `native_decide`-flagged 4-chain/2×2
  counts and the 5-element Heyting algebra are OUT (no new mechanisation).
- **D4 — try the scrub: ADOPTED — and DONE (2026-07-18), full success.**
  `PLLCraig.lean` rebuilt on `finUnion` + membership-form lemmas:
  `SCh.maehara`, `SC.maehara'`, `craig_interpolation'`, `craig_implication'`
  now audit **[propext, Quot.sound]** (pinned); the `∪`/`∩`-phrased originals
  are kept as two-line wrappers (clean‡ by statement vocabulary). Taint
  sources found and removed: `atomsList` built on Mathlib `∪`
  (choice-tainted at definition level), the Mathlib `Finset` union/inter
  lemma suite, and — measured, not guessed — **`tauto`, which is classical**
  (every use replaced by an explicit constructive term). Consequence for
  §2: the sentence "the entire proof-theoretic chain audits at
  `[propext, Quot.sound]`" **survives with Craig included**, citing the
  primed forms; no rewording needed.
- **D5 — 𝕊-Boolean sentence: IN**, as proposed (home §6.2, where the
  constraint algebra is on stage; a §3-close echo optional at merge time).
- **D6 — trims of Remarks 6.4 / 7.1: ADOPTED** as proposed.
- **D7 — related-work growth: ADOPTED** — both hidden connections
  (authorization logic's `says`; topological evidence models) go in.
- **D8 — Appendix E artefact guide: IN**, condensed from ledger Part I.
- **D9 — Mathlib-taint paragraph: RELOCATE** to §9, as proposed.
