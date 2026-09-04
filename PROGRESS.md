# PROGRESS — uniform interpolation for PLL, the one-variable programme

2026-07-15 · live session log (Fable 5) · updated in place while work continues.
Read top-down: §1 is the mathematics, §2–4 the tooling questions you asked,
§5 the manual-oracle recipe, §6 the running status line.

---

## 1. Where the mathematics stands

### 1.1 The target

The whole uniform-interpolation development has ONE open `sorry`:
`cascade_low_pos_box` (`wip/absorb_base.lean`), already reduced in
`wip/onevar.lean` (sorry-free reduction) to the semantic residual

> **descent_forcing.**  In every constraint model M, at every world w,
> for one-variable S, Γ, g (all atoms ⊆ {p}), past the threshold
> defect(S,Γ) · (J+2) ≤ c :
>
>   force w (itpA p S fuel (c+1) Γ g)  →  force w (itpA p S fuel c Γ g)

Equivalently (by the mechanised completeness): the derivability
`itpA (c+1) ⊢ itpA c` — the **budget descent**. The ascent
`itpA c ⊢ itpA (c+1)` is already a library theorem (`itp_budget_mono`),
so the descent says: *the ascending budget sequence has stabilised by the
threshold*.

### 1.2 Evidence (oracle-sound, i.e. every `true` is a genuine derivation)

* 24 configurations (natural, rich, adversarial): descent TRUE at every
  b ≥ 1. No counterexample.
* **3-chain confinement REFUTED**: with ⊥ ∈ S (natural — any negation puts
  ⊥ in the subformula space) the interpolants ESCAPE {⊥, ◯⊥, ⊤}: configs
  reaching ¬◯⊥ (stable), and one — **X9** — that CLIMBS:
  S = {⊥, ◯⊥, ¬◯⊥, p, ◯p}, Γ = [¬◯⊥], g = ◯p gives normal-form weights
  1, 2, 39, 143, 566 at b = 0..4, still growing.
* **X9 VERDICT (deep run, oracle-sound): the counterexample candidate is
  DEAD.** With the truncation absorption (§1.3½) + canonicalisation, the
  X9 interpolant classes are

  | b | 0 | 1 | 2 | 3 … 9 (checked) |
  |---|---|---|---|---|
  | ∀-interpolant | ⊥ | ◯⊥ | ◯(¬◯⊥ ⊃ ◯¬¬◯⊥) | **same class** |
  | ∃-interpolant | ⊤ | ¬◯⊥ | same | **same class** |

  Stabilisation at **b = 2**, versus threshold **16** — fourteen levels of
  slack. The earlier "climb" (nf weights 39, 143, 566, …) was pure
  syntactic bloat of one constant equivalence class. Strongest datum: the
  canonical dictionary stays at **5 classes** ({⊥, ⊤, ◯⊥, ¬◯⊥,
  ◯(¬◯⊥ ⊃ ◯¬¬◯⊥)}) across ALL budgets and ALL sub-contexts of the
  recursion — the entire X9 recursion lives in a 5-element state space.
  Total oracle work: 23 identification calls (the memo did the rest).
  En route the oracle certified the RN(◯,{}) collapse
  ¬◯¬¬◯⊥ ≡ ¬◯⊥ (and (¬a ⊃ a) ≡ ¬¬a does the rest by hand).
  H2 (∃-side stabilisation) is empirically TRUE for X9 from b = 1.

### 1.3 The Lean proof development (`wip/onevar_descent_dev.lean`)

Statement under attack (syntactic form; `descent_forcing` follows by
soundness):

> **itpA_descent.**  For all fuel, b, Γ, C, past threshold, one variable:
> G4c [itpA p S fuel (b+1) Γ C] (itpA p S fuel b Γ C)

Proved / reduced so far (file compiles, `sorry`-count = 1 → being split):

1. **∃-side descent is FREE.** `[itpE (b+1)] ⊢ itpE b` is exactly
   `itp_budget_mono.1` — no threshold, no one-variable hypothesis needed.
2. **Base case done** (`itpA 0 = ⊥`).
3. **Successor case reduced** (via `itpA_succ` + `orAll_elim`) to the
   per-disjunct obligation: each disjunct of the (b+1)-table entails the
   b-table.
4. **Key structural discovery** (from reading the ascent's combinator
   `itpAfull_map`): the ◯-goal *truncation disjunct* transfers if and only
   if we can supply
   > **itpE stabilisation (the distilled core).**  Past threshold:
   > G4c [itpE p S fuel b Γ] (itpE p S fuel (b+1) Γ)
   — the ∃-ascent, i.e. the ∃-side has ALSO stabilised. (The free
   direction is the reverse.) With that lemma, the library combinator
   `itpAfull_map` closes the ◯-goal case including all its edge cases.

So the open mathematics compresses to **two pieces**:
   (a) *mechanical bulk*: the per-disjunct map for the non-truncation
       clauses — a ~500-line mirror of `itp_budget_mono`'s clause walk,
       with threshold bookkeeping at the jump clauses;
   (b) *itpE stabilisation at threshold* — the distilled semantic core.

**Honest flag on (a):** jump clauses that do NOT grow Γ (the budget-gated
clauses at the same context) drop the budget without dropping the defect,
so the plain threshold `defect·(J+2) ≤ b` does not rethread through the
induction there. The full cascade in `wip/absorb_base.lean` handles exactly
this with a *seen-set* refinement ((jumpGoals S \ seen).card bookkeeping).
The one-variable statement will need the same refinement — OR this is
precisely where a counterexample would live if the bookkeeping cannot
close. This is the current front line of both the proof AND the refutation
search, and the deep-X9 probe (§3) tests piece (b) directly.

### 1.3½ DISCOVERY (from the shape diagnosis): the X9 recursion + the absorption law

Printing the pure-nf interpolant values (no oracle) exposed a clean
recursion.  Writing g := ◯⊥, n := ¬◯⊥, the X9 interpolants satisfy

    A₁ = g,   E₁ = n,
    E_{b+1} = ¬◯(E_b ⊃ A_b),
    A_{b+1} = P_b ∨ ◯(E_b ⊃ P_b)     where  P_b = ◯¬E_b ∨ ◯(E_b ⊃ A_b).

And the growth-killer, provable in two lines from the ◯-unit:

> **Truncation absorption.**  For every o ∈ others:
> o ⊢ orAll others ⊢ (E ⊃ orAll others) ⊢ ◯(E ⊃ orAll others), hence
>     orAll (others ++ [◯(E ⊃ orAll others)]) ≡ ◯(E ⊃ orAll others).
> The ◯-goal truncation disjunct absorbs its whole disjunct table.

Consequences:
* applied at the assembly site, it kills the ~7×/step raw growth
  (X9 b=2: weight 39 → 22, oracle-confirmed still ≡ the library value);
* it collapses A_{b+1} ≡ ◯(E_b ⊃ P_b) — with the further hand-collapse
  (¬a ⊃ a) ≡ ¬¬a giving P₁ ≡ ◯¬¬◯⊥: these values live in small RN(◯,{})
  territory after all;
* proof-relevant: for ◯-goals the whole `itpAfull` table is ≡ its
  truncation disjunct alone — a derived lemma that could reroute the H1
  clause walk for ◯-goals entirely through the (now H2-fed) guard.

### 1.4 Session steps (brief, chronological)

1. Redirect accepted: back to UI-for-PLL, prove-or-refute at one variable.
2. Probe harness built (`wip/onevar_probe.lean`): efficient oracle + sound
   syntactic simplifier `nf` (raw interpolants blow up ~8×/budget step; nf
   collapses e.g. weight 9,128,167 → 2).
3. 24-config sweep: descent true everywhere at b ≥ 1; interpolants seemed
   confined to {⊥, ◯⊥, ⊤} — then the ⊥∈S configs refuted that confinement
   and produced the X9 climb (sub-threshold, see §1.2).
4. Actual Lean development started (`wip/onevar_descent_dev.lean`), state
   as in §1.3: base + ∃-half closed, successor reduced per-disjunct,
   truncation disjunct isolated, itpE-stabilisation identified as the core.
5. NOW: (i) canonicalising simplifier-as-you-go (§3) to probe X9 past its
   threshold 16 — direct test of the distilled core; (ii) dev file being
   restructured around `itpAfull_map` + the two named holes.

---

## 2. Oracle — state and inefficiencies

**What it is.** `PLLND.search W as fuel V Γ C : Bool`
(`LaxLogic/PLLG4Dec.lean:63`) — backward proof search for the complete
calculus G4c, loop-checked by a visited set V.
* `search … = true` ⇒ genuine derivation, at ANY fuel (`search_sound`).
  Kernel-grade yes.
* `search … = false` ⇒ "not found within fuel" — NOT a certified no.
  (Certified no needs the exponential `decide (G4c …)` or a countermodel.)
* Efficient use = hand fuel: `PLLND.find Γ C` (fuel 10 000,
  `PLLDemos.lean:103`) — the exponential cost of `decide` lives ONLY in
  the `decideFuel` completeness packaging, never in the search itself.
  Measured: weight-6 goal 39 ms via `find` vs >90 s aborted via `decide`.

**Inefficiencies (confirmed this session).**
1. **No cross-call caching.** Every `entails` call recomputes from
   scratch; dedup loops are O(n²)·oracle. Fix: a result cache keyed on
   (Γ, C) at the probe layer — cheap, planned.
2. **Visited set is a `Finset (Finset PLLFormula × PLLFormula)`** —
   set-of-sets comparisons on big formulas; no hashing. Costs dominate
   precisely on the bloated interpolants. Mitigation: simplify BEFORE
   searching (nf/canon), keeping the space tiny.
3. **The space cap W = input weight**: search space scales with formula
   bloat — same mitigation.
4. **The fast memoised searcher (`g4B`/`g4bud`, `wip/g4ill_probe.lean`)
   decides the WRONG calculus** (Iemhoff's G4iLL, which is incomplete for
   PLL — machine-checked gap). Porting its HashMap memoisation to G4c is
   the right medium-term investment (relates to pending task #16).
5. **Raw interpolant construction explodes** (~7×/budget step) — at X9,
   b ≥ 6 is unbuildable even before any oracle call. Hence §3.

---

## 3. Simplification as you go (being built now: `wip/slick_probe.lean`)

**Why it is sound.** The `itpE`/`itpA` clause guards test membership of
*context* formulas (A ∈ Γ, A ∈ S) only — they never inspect interpolant
values. Interpolants are only *assembled* by ∧, ∨, ⊃, ◯. Since PLL-
equivalence is a congruence for these connectives, replacing every
recursive interpolant return by ANY equivalent formula yields an
end-result equivalent to the library's. So a simplifier applied at each
clause return preserves the interpolant's equivalence class — exactly the
object `descent_forcing` speaks about. (Cross-checked against the library
`itpA` by oracle at small budgets.)

**Design.** Two layers:
* `nf` — the syntactic rewriter already in use (Heyting ⊥/⊤ laws, ◯⊤ = ⊤,
  ◯◯ = ◯; each rewrite an equivalence).
* `canon` — oracle-backed canonicalisation: keep a growing dictionary of
  representatives; each new value is nf-ed then identified (entails both
  ways) with an existing representative or added. A syntactic memo avoids
  repeated oracle calls.

**Payoff.**
* *Refutation search:* interpolants stay dictionary-small at EVERY budget,
  so X9 can be probed to b = 18 > threshold 16 — the direct test of the
  distilled core (§1.3(b)). A new dictionary entry appearing past
  threshold = counterexample alarm; freezing = strong support.
* *Proof:* the dictionary that canon builds is a candidate for the finite
  invariant the induction needs (the sublattice the one-variable
  interpolants actually inhabit). If the reachable classes are finite and
  computable, the stabilisation argument has a concrete carrier.

---

## 4. Driving the oracle manually (recipe)

Scratch-file route (recommended). Create e.g. `wip/scratch.lean`:

```lean
import LaxLogic.PLLG4Dec
import LaxLogic.PLLDemos
open PLLFormula PLLND

-- formulas: prop "p", falsePLL, .and, .or, .ifThen, .somehow
def X : PLLFormula := (prop "p").somehow.ifThen (prop "p")   -- ◯p ⊃ p

#eval find [] X                     -- ⊢ X ?         (fuel 10000)
#eval find [X] (prop "p")           -- X ⊢ p ?
#eval search (listWeight [X]) (listAtoms [X]) 3000 ∅ [] X   -- explicit fuel
```

Run with:  `lake env lean wip/scratch.lean`

**Long-running probes — streaming gotcha.** `#eval someIOAction` buffers ALL
its output until the action completes (it goes through Lean's message
stream), so a hung probe looks totally silent. For anything long, define
`def main : IO Unit := …` at top level and run
`lake env lean --run wip/<file>.lean` — that streams to real stdout as it
goes. (This explained every "silent hang" in this session; compile time of
even the big probe file is only ~5 s.)

Reading the answers:
* `true`  — PROVED: a genuine G4c/PLL derivation exists (`search_sound`;
  no fuel caveat on the yes side).
* `false` — not found within the fuel; raise the fuel to gain confidence;
  a *certified* no needs `#eval decide (G4c Γ C)` (exponential — only for
  small weights) or a countermodel.

CLI route: `scripts/laxrun.sh help` (compiled `lake exe laxrun`; drivers
`runSearch`/`runQuant`/`runZoo` in `LaxLogic/PLLExec.lean`) — good for the
packaged demos; the scratch file is more flexible for ad-hoc sequents.

---

## 5. Files

| File | Role |
|---|---|
| `wip/onevar.lean` | sorry-free reduction of the open lemma to `descent_forcing` (1 sorry = the target) |
| `wip/onevar_descent_dev.lean` | the live proof development (§1.3) |
| `wip/onevar_probe.lean` | probe harness: nf simplifier + oracle sweeps (24 configs, X-configs, X9) |
| `wip/slick_probe.lean` | (being written) canon-as-you-go interpolants + deep X9 |
| `wip/lattice_cmp.lean` | RN(◯,{}) toolkit: `entails`/`equiv`/dedup/enumeration |
| `LaxLogic/PLLG4Dec.lean` | the oracle (`search`, soundness/completeness, `decide`) |
| `LaxLogic/PLLG4UITrunc.lean` | interpolants `itpE`/`itpA`, ascent `itp_budget_mono`, combinator `itpAfull_map` |

## 6. Status line (updated as work proceeds)

* [x] PROGRESS.md written
* [x] dev file restructured: compiles with EXACTLY TWO sorries —
      `itpE_stab` (H2, the distilled core) and the `hoth` clause walk (H1).
      The ◯-goal truncation case is CLOSED modulo H2 via `itpAfull_map`
      (guard arithmetic discharged; a `subst`-eliminates-the-wrong-variable
      trap cost three compile cycles, fixed with `rw`).
* [x] canon-as-you-go probe built + cross-checked vs library (all six
      cross-checks TRUE, including the weight-39 X9 value)
* [x] **deep X9 verdict: stabilises at b = 2 ≪ threshold 16; dictionary
      frozen at 5 classes through b = 9; counterexample candidate DEAD;
      H2 empirically true from b = 1** (see §1.2)
* [x] memory + this file updated with the outcome

**Where this leaves the mathematics.**  No counterexample survives at one
variable: every configuration probed (24 broad + X-escapes + X9 deep)
stabilises well below its threshold. The proof of the one-variable descent
is reduced to (H1) the mechanical clause walk and (H2) `itpE_stab`, with
two brand-new handles: the *truncation absorption law* (mechanisable in a
few lines; it collapses the ◯-goal table to its guard disjunct, the very
disjunct H2 feeds) and the *finite-class invariant* the canonical
dictionary exhibits (the induction's candidate carrier). Next session:
mechanise the absorption law, then attack H2 with the seen-set threshold,
then the H1 walk; independently, the 2-variable probe (each quantifier one
free variable) is ready to run on this harness.

---

## 7. 2026-07-18 addendum (from the belief-paper session)

The instruments changed while this file slept; the mathematics above is
untouched. In one line each — details and file pointers in
`docs/ui-notes-belief-session.md`:

* the oracle is **two-sided** now: `G4cTm.find` (fuel-free, returns
  kernel-checkable proof terms) on the yes-side, and
  `CounterEmit.emit` → verified `checkB` → `not_provable_of_check`
  giving *certified* underivability on the no-side — a refuted H1/H2
  instance can be cashed as a machine-checked countermodel, not a fuel
  timeout;
* `emitMin`/`emitMinClean` shrink countermodels (20 → 3 recovers F&M
  Fig. 3, pinned) and `PLLDiagram.lean` draws them (TikZ/SVG);
* the finitised canonical model + truth lemma + enumeration landed
  constructively (`PLLFinComp.lean`, `[propext, Quot.sound]`) — a
  Ghilardi-style semantic route to UI is now attemptable, and
  refutation search over a closure is complete, not merely sound;
* toolchain `v4.31.0` on `main`: native ≈22× the old interpreter.

---

## 8. 2026-07-19 addendum (semantic-route session, worktree branch)

The semantic route (task #33) moved past its universal-property layer;
the mathematics of §1–6 (syntactic route) is untouched. Full statements
and file anchors in `docs/semantic-ui-route.md` §0; everything below is
machine-checked in `LaxLogic/PLLSemUI.lean` (the file's only sorries
remain the two definability targets).

* **The essential-fibre conjecture is PROVED, as an iff.** For p-free ξ:
  ξ is the ∀p-value of some formula in which p is essential iff ⊬ ξ
  (witness `ξ ∨ p`); dually for ∃p iff ξ ⊬ ⊥ (witness `ξ ∧ p`). On the
  closed fragment: essential ∀p-image = RN(◯,{}) ∖ {⊤}, essential
  ∃p-image = RN(◯,{}) ∖ {⊥}. The two exercise lemmas
  (`IsSemAll p M ⊤ → ⊢ M`, `IsSemEx p M ⊥ → M ⊢ ⊥`) are the ⊤/⊥
  exclusions.
* **Certificate method for definability**: substitution instances
  (via truth-set redecorations) and the lower transform of the DOUBLED
  model (two copies stacked on the 2-chain) turn oracle-checkable
  derivability facts into `IsSemAll`/`IsSemEx` proofs. First values
  beyond substitution: ∀p.(p∨¬p) = ∀p.(◯p⊃p) = ∀p.(¬¬p⊃p) = ⊥ —
  with a machine-checked proof that substitution certificates alone
  cannot reach the first.
* **Value-table probe COMPLETE** (`wip/semui_probe.lean`, table +
  analysis in `docs/semantic-ui-1pv-table.md`): ALL 25 one-variable
  classes (weight ≤ 5 + extras) certified on BOTH sides by the
  three-generator basis; every candidate a unique max/min over the
  7-class ladder; values attained {⊥, ◯⊥, ⊤, ¬◯⊥, ◯¬◯⊥}; a fourth
  generator (sideways/Löb) needed exactly at the ◯-guarded classical
  schemata; first ∃-side beyond-substitution value ∃p.(¬◯p ∨ ◯p) = ⊤
  (proved: `semEx_wem_box`). Definability at 1 pv = empirically
  complete conjecture with a uniform syntactic proof target (see the
  table doc). Oracle warning: failing `search` cost is UNPREDICTABLE in
  fuel (non-monotone); cap weights and order cheap attempts first.

### §8 continued — overnight 2026-07-19 (same branch)

* **The reconstruction reduction (PROVED)**: definability follows if
  the generator conjunction (∀-side) / disjunction (∃-side)
  reconstructs M — `isSemAll/isSemEx_of_reconstruction`,
  `semAll/semEx_definable_of_reconstruction`.
* **Fixed bases REFUTED, machine-checked, both sides**: ∀-side at the
  Peirce family — the exhaustive weight-≤7 sweep (2758 formulas) has
  exactly 8 failures, all `(X⊃p)⊃Y` with X ∈ {◯⊥,◯p,◯◯⊥,◯◯p}; Lean
  witness `∀p.((◯⊥⊃p)⊃p) = ◯⊥` (`semAll_peirce`, `allRec_fails`).
  ∃-side at the biconditional `(¬◯⊥⊃p)∧(p⊃¬◯⊥)` (weight 14):
  `∃p = ⊤` (`semEx_bicond_top`, `exRec_fails`); oracle finds the next
  escape at the ◯¬◯⊥-biconditional (weight 16).
* **Repairs oracle-verified everywhere**: ladder-rung substitutions
  (◯⊥ for ∀; ¬◯⊥/◯¬◯⊥ for ∃) fix every found failure; iterated Löb
  to depth 4 reconstructs without new frame constructions.
* **The per-instance support law**: generator pool = substitutions
  over the closed-fragment rungs occurring in M + lowT + sideT.
  Converges with the corrected-Cor-10 constraint-transfer analysis:
  the canonical descriptions must record exactly the ladder rungs of
  cl(M) — the promise/Θ data.

## 9. 2026-07-19 (day session): graduation, the sandwich, the two-sided oracle

* **Graduation**: the theory file is now `LaxLogic/PLLSemUI.lean`
  (root-registered, sorry-free; definability = `Prop`-level conjectures
  `SemExDefinable`/`SemAllDefinable`; 27 flagship audits clean).
* **The constraint–ladder comparison (Matthew's equivalence question),
  PROVED as the sandwich** (`LaxLogic/PLLSemUICtx.lean`, instantiated
  with the packaged tower quantifiers in `wip/semui_ctx_equiv.lean`,
  no sorryAx):

      ξ^C ⊢ᴵᴾᶜ ∀ᴵᴾᶜp.(M^C) ⊢ᴵᴾᶜ (M[p:=χ])^C   (all χ; dually for ∃)

  Bridge lemma `subC_substP`: `(M[p:=χ])^C = (M^C)[p:=χ^C]` for
  p-free C.  So the constraint route = the substitution fragment of
  the ladder route, exactly; the frozen-C failure (§0(j) oracle
  witness ◯p⊃p) is the lowT/sideT gap, now provably so.  A constraint
  -models theorem = closing that gap with per-M constraint families
  (OPEN; fallibility prediction is the first test).
* **The two-sided oracle packaged** (`wip/oracle2.lean`): staged
  decide2 = cheap search → verified battery sweep (FinCM.checkB) →
  deep search → gated emit → UNKNOWN.  Benchmarks below.
* **oracle2 benchmarks** (10 cases: 5 provable incl. weight-34
  reconstruction rows, 5 refutable incl. the weight-40 Peirce
  reconstruction failure): 10/10 correct verdicts, EVERY case 0 ms
  (interpreted); compiled suite 0.02 s CPU total.  Contrast: plain
  one-sided `search` on `allCand(peirce) ⊢ peirce` @fuel 400 grinds
  >100 s interpreted AND >120 s native (both killed) — the
  countermodel stage, not compilation, is what beats the unpredictable
  failing-search cost.  Countermodels arrive minimal (1–3 worlds,
  verified by `FinCM.checkB`).  Correction to the recorded pathology:
  bare `¬¬◯⊥ ⊢ ◯⊥` @500 is 0 ms — the recorded minutes-case had a
  larger antecedent; non-monotonicity itself stands as documented.
* **Toolchain**: this branch is on v4.31.0 — `lean_exe` builds run
  fine (~10 s incremental; stale lakefile segfault comment fixed);
  `lake exe oracle2` is a compiled decision tool.

## 10. 2026-07-19 (afternoon, Matthew's follow-ups): fuel demoted, compiled probes, the prediction lands

* **"Are you using the most efficient versions?" — no, and now yes.**
  The fuel-free `G4cTm.find` (built 2026-07-18, left on the shelf)
  decides the ENTIRE oracle2 benchmark at 0 ms in find-only mode —
  including failing fast on the refutables where fueled `search`
  ground for minutes.  The unpredictable failing cost was an artifact of the
  fueled engine, not the problem.  oracle2 v3: nf preprocessing (the
  built simplifier), battery first, find as the positive engine; fuel
  appears nowhere in the decision path.
* **Compiled probes** (`lake exe ctxprobe/ctxrel/ctxcert`): the
  stalled §0(j) rows ran.  Full chain2 table (9/9) + chain3 (8/9):
  every substitution row commutes, the failures are exactly the
  frame-changing rows (`◯p⊃p` LOW, `◯(◯p⊃p)` SIDE — the latter a NEW
  frozen-C failure), as the sandwich mandates.
* **The fallibility prediction (was OPEN)**: chain2 rel-comm HOLDS
  (all rows, find-term grade); chain3 rel-comm FAILS at both ◯-rows,
  **certified by checkB-verified ONE-WORLD countermodels** — the
  single non-fallible world with only `a0` true, i.e. the α-top
  residue world of the §0(j) analysis, now machine-checked.  Frame
  theories over the same names provably cannot close the lowT/sideT
  gap; the constraint pool itself must grow.  Fork: BOTH ◯-rows certified-refuted by the same one-world model (§0(m)); prediction confirmed on all three test models.

## 11. 2026-07-19 (evening, Matthew's instruction): the general fails-half PROVED

`LaxLogic/PLLSemUIRes.lean` (library, audited; the collapse lemma at
[propext] alone): residue model + ResiduePair (the Lemma-7 shape at a
non-fallible Rₘ-stable world) + the collapse `residue_applyC` (C[x] ↔ x
at the residue point) + diagram derivations `diag_row1/row2` (via
completeness) + engine `residue_obstruction` + headlines
`fails_half_boxp_imp_p` / `fails_half_box_lob`: for EVERY such
constraint, EVERY IsIPCAll-value of the two frame-changing rows, and
EVERY n₀-avoiding frame theory of negated atoms, A :: Θ cannot derive
the translated PLL value.  chain3's §0(m) certificate re-derived as
corollary `chain3_fails_half`.  The fails-half of the fallibility
prediction is now a general THEOREM; the holds-half (chain2 direction)
remains OPEN as a general law.

## 12. 2026-07-19 (late): the holds-half PROVED — the dichotomy closes

Same file (PLLSemUIRes.lean).  ThetaNamed (all pair-names Θ-negated =
all stable worlds fallible) → theta_applyC ([propext]): Θ derives
every C[x] → holds_half_boxp_imp_p (choice-free): every IsIPCAll-value
A of (◯p⊃p)^C is Θ-equivalent to ⊥ (A,Θ ⊢ p by lower+theta_applyC,
then substND p:=⊥); holds_half_box_lob: A ≡_Θ (◯⊥)^C (Θ derives the
value outright and A via greatest at ⋀Θ).  chain2 verdict = corollary
chain2_holds_half.  With §11's fails-half the Lemma-7 dichotomy is a
pair of theorems: commutes iff no Θ-avoiding pair-name — the
fallibility prediction PROVED both ways at the constraint level.

## 13. 2026-07-19: the dichotomy lifted to models — c0Of in the library

FinModel tables + c0Of (Lemma-7 recipe, naming parametric) + falAxioms;
shape lifts c0Of_thetaNamed / c0Of_residuePair (only Rᵢ-reflexivity
needed); model_dichotomy_boxp_imp_p / model_dichotomy_box_lob: for any
finite model, injective p-avoiding naming, any IsIPCAll-value A of the
translated frame-changing row: A ⊢_Θ value ⟺ all Rₘ-stable worlds
fallible.  decide-pins: c0Of reproduces the probes' chain2C/chain3C.
The fallibility prediction is a machine-checked iff at model level.

## 14. 2026-07-19: the pool experiment — disjoint-alphabet saturations REFUTED (certified)

Pools {c0Of m, c0Of double(m), c0Of lob3(m)} on alphabets a/b/c, value
= meet of relative tower ∀-values, target = translated PLL value under
the joint fallibility theory.  chain3, BOTH frame-changing rows: every
sub-pool REFUTED by a one-world checkB-verified countermodel forcing
ALL residue names at once (a0, b3, c0).  Mechanism: interpolants are
alphabet-local, so the joint residue defeats each conjunct
independently; Cmeet-concatenation already dead by the proved
fails-half (combined constraint keeps a residue pair).  Consequence:
frame-changing content is unreachable from the constraint side —
the routes factor (constraints = substitution fragment, exactly;
transforms lowT/sideT = frame content, irreplaceably).  Capstone
target: set-valued residue ⟹ general disjoint-pool obstruction.
Harness note: certified verdicts at sequent weight ~10⁶ in ms.

## 15. 2026-07-19 midnight: frontier row settled — ∀-law REFUTED in Lean

((p⊃◯⊥)⊃p)⊃p: instances all ⊤; lowT ≡ sideT ≡ ¬¬◯⊥; value = ◯⊥;
certified 4-chain countermodel (Rₘ = id ∪ {2→3}, top fallible,
p at {1,2,3}) — pool forced at root, row refuted.  Kernel-decide pins
in PLLSemUILaw: poolAll_insufficient_frontier + reconLawAll_refuted
(¬ ReconLawAll).  ∃-law untouched.  Third generator (depth-3 levelled
construction descending to ◯⊥) is now the named mainline target;
chain4 frame added to Search.defaultFrames + probe battery.  Also:
PLLSearchEx (Hilbert axioms via PLLSearch, answers→decisions, both
#guard-verified; WF-recursion kernel-reduction limitation documented).

## 16. 2026-07-20 overnight: split variant MECHANISED — frontier value PROVED

LaxLogic/PLLSemUISplit.lean (sorry-free, audits pinned at
[propext, Classical.choice, Quot.sound]).  t₃ = the split: duplicate
the Rᵢ-cluster of z isomorphically strictly above itself (whole
cluster, not one point — the pointwise m-zigzag forces this in
non-antisymmetric preorders; on posets = the one-point §0(u) form),
copies carry internal Rₘ and escape only to strict Rₘ-successors, p
on copies ∪ strict cone ∪ F.  Projection = total PBisim.  Payoffs:
semAll_frontier `∀p.(((p⊃◯⊥)⊃p)⊃p) = ◯⊥` (upper half: no ◯⊥ ⇒ some
future has fallibility-free Rₘ-row ⇒ split there refutes the row);
boxBot_derives_frontier; poolAll_not_derives_value (pool provably
below the value it cannot reach); semAll_em_p_via_split (split
subsumes the doubling on ∀p.(p∨¬p) = ⊥).  Fourth machine-checked
modal quantifier value; first beyond the whole transform pool.
OPEN: iterated splits vs the levelled row ◯(◯p⊃p); syntactic splT
(cluster-anchored ⊃-clauses obstruct a naive formula transform;
canonical model is a poset — trivial-cluster form may suffice);
graded law.

## 17. 2026-07-20 overnight: ◯-free fragment AGREES with IPC; split tower ≠ levelled

(1) Matthew's fragment test: PLLSemUIOFree.lean — fallible-top graft
topExt (◯-free forcing unchanged, ◯⊥ global) + flat models (¬◯⊥
global) ⇒ BOTH cone exclusions PROVED: underivable ◯-free M has no
lower bound in cone(◯⊥) ∪ cone(¬◯⊥); ⊤-half + conditional collapse
semAll_value_bot_of_cones (+ ∃-side duals).  Sweep (ofreesweep,
w ≤ 8, 1,758 rows): 0 escapes, 0 unknowns — allCandP ⊢ ⊥ on every
underivable row, exCandP derivable on every consistent row, 7/7 rungs
two-cone covered.  RN({p}) values stay {⊥,⊤} = Pitts.  FV-climb not
blocked at the base; next rung: one ◯, two variables.  OPEN: two-cone
coverage of RN(◯,{})∖{⊥} for the unconditional collapse.
(2) Iterated splits do NOT reach ◯(◯p⊃p): RmClusterInternal invariant
(split + redecorate preserve; forces ◯A⊃A globally) ⇒
splitTower_oneW_forces_lob (AXIOM-FREE) — no split-tower variant of
oneW refutes the Löb row, sideways Rₘ-creation is essential; basis
needs both surgeries.

## 18. 2026-07-20: sufficiency PROVED — RN({p}) definable, Pitts values

ofree_semAll_definable / ofree_semEx_definable (PLLSemUIOFree.lean):
every ◯-free 1-var M has definable semantic quantifiers with values
in {⊤,⊥} — unconditional (classical em on derivability only).
Engine: flatten (non-fallible part; ◯-free forcing preserved at
non-fallible worlds; output flat) + ofreeGraft (fibre flat
countermodel over arbitrary C; projection = total PBisim; fibre
forcing = K-forcing at non-fallible fibres).  Both = semantic
conservativity (Matthew's q_M-atomisation, model-side).  One uniform
construction covers the whole fragment: surgery proliferation is a
◯-depth phenomenon.  ⊤/⊥ halves (derivable/inconsistent) hold for
arbitrary M.

## 19. 2026-07-20 afternoon: parametric point-adjunction — surgeries unified

PLLSemUIAdjoin.lean: adjoin N n₀ U R (anchored point; U = cone, R =
constraint escapes) + ABisim.comp + adjoin_pbisim (AXIOM-FREE): any
PBisim extends along an anchored pair given five cover conditions; Z
accumulates so adjunctions iterate; mback_cover = the promise
mechanism (⋆ may reach any world Z-equivalent to an anchor-successor).
Cores re-derived: adjoinAtP_not_em (doubling), adjoinAtP_not_frontier
(split), lobTower_not_lob (levelled, two-storey tower, sideways
R = {⋆₁}); adjoin_reaches_lob at oneW = exact contrast with
splitTower_oneW_forces_lob.  Global surgeries = uniformizations over
cluster/level multiplicities; one construction, changing parameters.
Merged Matthew's parallel BLL branch (nucleus join + belief paper).

## 20. 2026-07-20: amalgamation reduction — the variable-induction skeleton

PLLSemUIAmalg.lean: relGraft (graft ALONG a bisimulation: fibres =
B₀-related pairs over flatten C; p from K, other atoms pointwise,
agreement by B₀.atoms; fallible-base re-entries only) + pbisim +
force_iff (◯-free, ANY atoms).  Reduction theorems
isSemAll_of_flatAmalg / isSemEx_of_flatAmalgEx: for ◯-free M in any
variables, the PLL semantic spec = two derivability facts + a purely
IPC-side flat amalgamation property (FlatAmalgAll/Ex).  Fallibility +
◯ discharged once; the variable induction lives inside IPC.
flatAmalgAll_bot + semAll_ofree_bot': the 1-var case re-derived as an
instance — "both steps collapse to one".  OPEN: FlatAmalgAll for
Pitts interpolants at ≥2 variables (Ghilardi descriptions / finite
canonical model).

## 21. 2026-07-20: box-commutation law + one-◯ two-variable sweep clean

PLLSemUIBox.lean: semAll_box / semEx_box — IsSem{All,Ex} p φ ψ +
BoxRowAmalg{All,Ex} ⇒ IsSem{All,Ex} p ◯φ ◯ψ; free halves
unconditional (semEx_box choice-free); residues = pure ∀∃-amalgamation
statements (quantifier machinery discharged).  ◯-clause of the
definability induction reduced to residues; ⊃/∨ remain the hard
connectives (as in IPC).  Sweep (oneboxsweep, w ≤ 5, 214 p-rows,
24-slice): 0 anomalies of any kind — fragment preserved, values
compositional (box-commutation on ◯-heads + pointwise laws:
∀p.(◯p∨q)=◯⊥∨q, ∀p.(q⊃◯p)=q⊃◯⊥, ∀p.(◯q⊃p)=¬◯q), current transform
stock covers everything at this weight.  Harness: refute?-first +
23-frame battery + gated decide2 + monotone pruning (matrix 16.8s →
143ms); repeated find-grind lesson → node-budget chip spawned.

## 22. 2026-07-20: residues attacked — promise class discharged, law generates values

PLLSemUIBox extended: Lob0Refutes (level-0/"all promises withheld"
refutation class) + boxRowAmalgAll_lob0 (∀-residue discharged there,
value ⊥) + instances (p, p∨¬p, ¬¬p⊃p) ⇒ FIRST LAW-GENERATED VALUES:
∀p.◯(p∨¬p) = ◯⊥, ∀p.◯(¬¬p⊃p) = ◯⊥ (new), ∀p.◯p = ◯⊥ (re-derived,
consistency).  ∃-side: boxRowAmalgEx_prop ⇒ ∃p.◯p = ◯⊤.  Honest
gap: ◯p⊃p not Lob0 (vacuous at promise-free rows) — general residues
need the canonical-cone graft (second wave).

## 23. 2026-07-20: second wave landed — the description graft complete

PLLSemUIDesc.lean: DescPack (realisation relation; atoms only on
tracked alphabet — filtration problem dissolved by reading protected
atoms from the base) + descGraft (paired fibres; relaxed Rᵢ into
fallible K-worlds, strictly paired Rₘ) + descGraft_pbisim +
descGraft_force_iff (◯ INCLUDED; two fallibility absorptions) +
boxRowAmalg{All,Ex}_of_desc.  The ◯-step of the definability
induction now = finite combinatorics: closure triple with ◯φ ∈
fal/val realised over x by a pack into canonFin cl (truth lemma
bridges membership to forcing).  Open centre: the descriptions
functor and its m-clauses — decidable per closure, oracle-probeable.
Merged: node-budgeted search (chip; find is partial-with-visited-set,
not WF — PLLSearchEx note carries stale attribution, flagged).

## 24. 2026-07-20 pm: descriptions functor built and measured — route corrected, gap row probe-discharged

trace C cl c mechanised (PLLSemUITrace.lean, sorry-free): consistency
by soundness-at-c; clauses atoms/fall/iforth/mforth PROVED (mforth =
the mfal design validation), kback/mback REFUTED machine-checked.
Pack clauses positive in R ⇒ largest pack Realises (axiom-free
union lemma); residue discharges reduce to per-(C,x) triple
realisation.  Pre-triple sandwich PROVED: residue ⟹
Cons⟨pfval(x), {◯φ}∪pffal(x), pfmfal(x)⟩ ⟹ canonical candidate
exists; realised candidate ⟹ residue.  PROBES (desc_probe,
resid_probe, both compiled): full-canonFin target DEAD (gfp empty on
all ∀-instances; kill-chain = promise-forgetting extensions + T⊥ on
F-free rows; rank-stratified dies by round 3, formula-independently)
— but the residues themselves are TRUE on the whole battery by SMALL
GADGETS: proved rows at k ≤ 1, and the GAP ROW ∀p.◯(◯p⊃p) at
k ≤ 2 (47/47: 9 redecorate, 18 one-point, 20 two-point tail with
in-chain Rm and sideways m-exit — lobTowerBase shape).  Corrected
ledger: canonical triples CLASSIFY (consistency crux necessary,
proved), adjunction tails KILL.  Next: mechanise the gap row's
3-case discharge as a Lob0-style class lemma ⇒ ∀p.◯(◯p⊃p) = ◯⊥.
Frame hygiene: onebox fork frames not transitively closed as listed;
probes close on intake (sweeps unaffected — unclosed members cannot
certify).

## 25. 2026-07-20 eve: literature sweep + the Litak–Visser skeleton

Three-agent sweep (standard vocabulary): Visser 1996 = our
construction with the right budget bookkeeping (witnessing triples,
Henkin-depth-financed layered bisimulation — explains the dead
canonical-target gfp exactly); Litak–Visser 2404.11969 = semantic UI
for iSL (coreflection like PLL) — the closest template, §5.1 read in
full; Iemhoff's published UIP claim = the G4iLL paper whose
completeness we machine-refuted; algebra side (amalgamation, model
completion for nuclear Heyting algebras) OPEN in print — our result
would settle it.  Papers in papers/ (untracked).  NEW FILE
PLLSemUILayered.lean: crank (◯ costs 2 under the ∀∃-clause),
LayeredBisim, rank-preservation PROVED (+ consistency corollary
recovering unbounded invariance), sorried pillars: frag_reps_exist,
layered_of_frag_agree (characters), amalgamation (Lemma 5.4 PLL-form
with their proof shape + PLL additions documented).  The official
interpolant construction reinstated: ∀p.M = join of rank-bounded
p-free derivers.  Oracle test (wip/rank_join.lean): the join for
◯(◯p⊃p) certified = ◯⊥, zero unknowns after adding the F-free
3-chain with rigid bottom row (battery gap — the residue probe's own
gadget was the missing countermodel frame).

## 26. 2026-07-20 night: pillar attack begun — Henkin amalgam scaffold

Pillar 1 (frag_reps_exist) delegated to a worktree agent with the
full DNF-over-components blueprint (comps recursion, nonempty
conjunct-lists since truePLL = ⊥→⊥ has crank 1, canonicalisation via
filter-sublists).  Pillar 3 scaffold LANDED (PLLSemUIHenkin.lean):
canonDepth := cl.card − val.card with strict drop PROVED; WitTriple
(Litak–Visser Lemma 5.4 triples, budget 2·depth+1); witAmalgam
(componentwise relations — canonical side carries promise-aware Rₘ —
fallibility from the theory coordinate, atoms from the union) with
ALL frame legality proved; amalgamation_assembled PROVED modulo the
two claims wit_pbisim (projection is the p-variant bisimulation; the
two-case budget argument, Henkin-side moves = trace_iforth /
trace_mforth) and wit_force (pair forces φ ∈ cl iff φ ∈ Δ.val;
◯-case = i-zigzag + m-zigzag + fallible absorption).  When the claims
land, the Layered interface `amalgamation` retires in favour of the
assembled card-budget form.  Pillar 2 (characters, Thm 4.7) queued
behind the agent's bigAnd/bigOr calculus.

## 27. 2026-07-20 late: pillar 2 obstruction MACHINE-CHECKED

layered_of_frag_agree_refuted PROVED (pins standard three): the
Litak–Visser Thm 4.7 form is FALSE over constraint models — chainF
(two-point chain, fallible top, trivial rows) agrees with oneW on
every variable-free formula of complexity ≤ 1 (chainF_oneW_agree,
conservativity: the fallible top forces everything so never blocks an
implication; ◯ needs complexity 2), yet iforth at the fallible top
demands a fallible partner that oneW lacks.  Redesign boundary fixed
in the file: escape-iforth (partner OR fallible successor, DescPack
style) survives the character argument — non-fallible successors
refute their θ⁻ — so pillar 2's open content is exactly the
m-clauses: which row-zigzag weakening is agreement-derivable AND
strong enough for wit_pbisim's budget argument.

## 28. 2026-07-20 night II: forth-m probe clean + the repaired layered form PROVED

wip/mforth_probe.lean: 24 closed frames, 90 systematically generated
variable-free formulas, 2324 agreeing pointed pairs — forth-m
candidates = 0 (a violation would have been an a-fortiori
counterexample to the repaired pillar 2; clean pass = supporting
evidence).  LayeredBisimE mechanised (PLLSemUILayered §3′): the
DescPack clause shape — i-zigzags escape at fallible targets,
m-zigzags may pair fallible witnesses; LayeredBisim.toE embedding;
**force_iff_of_layeredE PROVED first-try** (every escape absorbs by
force_of_fallible, mirroring descGraft_force_iff).  PLLSemUIHenkin
switched to consume LayeredBisimE throughout (WitTriple, witAmalgam,
claims, assembly) — full library green.  Remaining pillar-2 content:
characters for the E-form (agreement ⇒ LayeredBisimE, probe-backed);
then wit_pbisim/wit_force.

## 29. 2026-07-20 night III: character LEGO proved

PLLSemUIChar.lean (sorry-free, pins standard three): force_bigAnd_iff
/ force_bigOr_of_mem (semantic forcing of the finite connectives);
charPos/charNeg (θ± as classical filters over a representative list);
force_charPos; not_force_charNeg (non-fallible worlds refute their
negative character — the fallibility hypothesis is exactly where the
machine-checked obstruction lives); agree_of_char (character
transfer: forcing θ⁺ and refuting θ⁻ yields full list agreement).
Remaining pillar-2 content is now ONE induction: Z α := rank-α
agreement satisfies the LayeredBisimE clauses (escape-iforth via
not_force_charNeg at non-fallible targets; forth-m probe-backed),
with slack bookkeeping for the crank-1 ⊤.

## 30. 2026-07-20 night IV: the m-escape geography MACHINE-CHECKED, axiom-free

Probe extension: fallible-PAIR escape fails on 82 of 2324 agreeing
pairs (non-fallible clause still 0).  Both boundaries now theorems,
ALL AXIOM-FREE: weak_escape_breaks_force_iff (weak m-escape kills
rank preservation — chainFM bottom forces ◯⊥ through its fallible
row-member, oneW cannot); forkF_agree (the fork's bottom agrees with
the lone point on EVERY formula — unconditional, all atoms) +
pair_escape_not_from_agreement (yet no pair-escape layered
bisimulation links them) — incidentally separating logical
indistinguishability from escape-bisimilarity in PLL outright.
SETTLED DESIGN: two relations — LayeredBisimE (pair escape, 4.6-valid,
the OUTPUT format) and NEW LayeredBisimW (weak escape, the INPUT
format agreement can deliver; force_iff provably fails for it);
repaired pillar 2 stated as layered_of_frag_agree_W (sorried,
probe-backed); the amalgamation must bridge E/W inside the amalgam by
routing its ◯-case through the canonical promise components (mfal) —
the structural reason F&M theories carry promises.

## 31. 2026-07-20 night V: the i-clauses of the repaired pillar 2 PROVED

agree_iforth / agree_iback PROVED sorry-free (pins standard three):
the character argument lands for PLL — for a NON-fallible successor
v, the implication charPos(v) ⊃ charNeg(v) fails at the base world (v
witnesses it, via sub_mi for the m-case's future use), its complexity
fits the budget 2α+2 (crank_charPos_le r+1 absorbing the crank-1 ⊤,
crank_charNeg_le r), agreement transfers the failure across, and the
failing instance is the partner — full rank-2α agreement through
frag_reps_exist' + soundness-at-a-point (force_of_deriv).
layered_of_frag_agree_W ASSEMBLED in PLLSemUIChar: Z α := agreement
at rank 2α; mono/atoms/fall/iforth/iback/root all proved;
sorry-footprint EXACTLY the two weak m-clauses (probe: 2324/0).
Pillar 2 is now: two m-clause character derivations away.

## 32. 2026-07-20 close: the m-clause hunt at scale

mforth_probe extended with 240 pseudorandom frames (4–6 worlds,
closed random relations, up-closed fallible sets; fingerprints
precomputed): 746,108 agreeing pairs — NON-fallible forth-m
violations: 0 (the W-form m-clause is now backed at scale; the pure
statement of resolution (a) very plausibly TRUE, proof still open);
fallible-PAIR failures: 22,506 (the machine-checked boundary of
§30 confirmed en masse).  Ledger at close: pillar 1 PROVED; pillar 2
= i-clauses PROVED + two probe-backed m-sorries with the ∀∃ analysis
recorded (§0(gg)); pillar 3 scaffolded to wit_pbisim/wit_force with
the promise-routed ◯-case as the designed bridge.  Next session:
wit_force's ◯-case via canonical promises (trace_mforth prototype),
then wit_pbisim's two-case budget argument, then Thm 5.1 assembly ⇒
∀p.◯(◯p⊃p) = ◯⊥.

## 33. 2026-07-20 late: Lemma 5.4 mechanics extracted; canonical LEGO PROVED; same-trace no-descent REFUTED

Re-read Litak–Visser pp. 21–23 line by line.  Their proof balances on
(1) strict theory growth for every K-side-first truth-lemma move (the
⊃ ψ-trick, which ports; the Lewis-arrow <-maximality trick, which
needs Löb well-foundedness and does NOT port — PLL's reflexive Rᵢ
means a ◯χ-refuter can never force ◯χ), and (2) the primed pair as a
reusable reservoir financing same-theory moves whose M-side is given
(links are propositions, not resources).  The one combination their
bookkeeping cannot finance is same-theory + K-side-first — exactly
PLL's ◯-case.

Canonical LEGO PROVED and pinned in PLLSemUIHenkin.lean (8 lemmas):
canon_box_dichotomy (validated ◯χ: the world is its own row-witness
by reflexivity of Rₘ, or the witness strictly grows the theory —
[propext, Quot.sound]); trace_box_refuter + promise_blocks_row (a
◯χ-refuting world has a successor promising χ, and promises are
validated by NO canonical Rₘ-successor — the amalgam refutes ◯χ with
no Rₘ-move in M; choice-free); imp_unval_cases + traceT_val_ssubset
(the ⊃-split with guaranteed strictness); traceT_mfal_empty_of_fallible
+ canonTop + rm_canonTop_iff (fallible row-members erase promises;
escapes land on the canonical top).  Library green, 3001 jobs; only
wit_pbisim/wit_force remain sorried.

THE WALL, isolated: the forward ◯-case at a same-val-trace successor
needs an unprimed link at 2d; every spend yields 2d−1.  Candidate
repair (same-trace no-descent: closure-trace-equal i-moves keep the
rank) probed in wip/samval_probe.lean, two passes.  Variable-free:
CLEAN (0 failures; needed cases vanish as the closure grows: 109/5/0).
One-atom (650 hereditarily-decorated models, 2,377,307 agreeing
pairs): REFUTED — 499/44/12 failures over [⊥,q] / [⊥,q,◯q] /
Sub(◯q⊃q)∪{⊥}.  Decoded by hand: the moved world is a rigid dead-end
(q ∧ ¬◯⊥, crank 3); the partner model lacks dead-ends above w′; the
roots agree low because dead-end-absence registers only at ¬¬◯⊥
(crank 4).  The one-level descent of agree_iforth is SHARP under
closure-trace-equality; every decoded failure involves a dead-end
successor (the rigid postponement points of §0(ee)).  Open design
question for next session: the promise-pair invariant with a degraded
link, or a dedicated dead-end clause.  Route doc §0(hh).

## 34. 2026-07-25: the confluent amalgamation CLOSED modulo ONE Prop — the same-theory wall dissolves

`wip/witTripleC.lean` (ui-confluence, b10d274+) is sorry-free with
`#guard_msgs`-pinned audits: `witTriple_iforth`, `witTriple_mforth`,
`wit_pbisimC` (Claim 1), `wit_forceC` (Claim 2 — the full truth
lemma), `amalgamation_assembledC` — all conditional on the single
displayed Prop `MforthResidue`.  The two bare sorries that were "the
open mathematics" of Lemma 5.4 are gone as separate problems.

The two mechanisms: (1) same-trace ◯-moves are matched REFLEXIVELY
(`RmC_refl`) with the base regenerated from the reservoir by
`B.iback` along `Rₘ ⊆ Rᵢ` — §33's wall assumed the ◯-move must be
consumed by `mback`, and it need not be; K-side same-theory ◯-moves
never arise (the witness's trace strictly grows or the world is its
own row-witness).  (2) The truth lemma's ◯-forward direction is
DEFINITIONAL through `RmC`'s anticipation clause (`χ ∈ val Δ₂ →
boxOf χ ∈ val Δ`); ◯-backward is bare possibility in K + `B.mforth`,
strictly financed; ⊃-backward is the K-refuter + `B.iforth`.  No
transfer, no promise component: `mfal` is dead weight in the
confluent route.

Definitions: budgets restored to (2d, 2d+1) — the (d, d+1) `crankC`
recalibration was a MISCALIBRATION (slope 2 refinances two links per
one-level spend; forced, not chosen); `hik` dropped (consumed by
nothing); confluence of M dropped (only K need be confluent); triples
now an inductive with a `top` constructor absorbing every fallible
escape.  Consumption inventory exact: all four E-clauses + atoms +
fall + mono — so pillar 2 still owes the E-form m-clauses.

The residue: an M-side ◯-move at an infallible target where the
reservoir's iback-partner grows the trace (right level 2d, wrong
trace) while the base's mback-partner keeps it (right trace, level
2d−1, one short).  `mforthResidue_of_sameTraceBase` (PROVED) reduces
it to same-trace-partner existence; a structural probe of the exact
configuration is in flight (bii_probe worktree agent), old
samval-failures as negative control.  Route doc §0(ii).  Semantic UI
for PCLL now rests on exactly TWO open obligations, both
m-clause-shaped: pillar 2's agreement-side m-clauses and this
residue.  Cross-route: v2quant re-running with the §33 battery/budget
fixes (second worktree agent); X9 match test pending.

## 35. 2026-07-25 later: probe verdicts land — the residue never arises on the battery; THE X9 CROSS-ROUTE MATCH IS CERTIFIED

**b.ii probe** (wip/bii_probe.lean, exe biiprobe; battery 825 one-atom
models, 531 confluent as K, 438,075 confluent pairs, six ◯-adequate
closures; negative control PASSED — the §33 refuted clause fails ~50k
times per closure in the same approximants): **0 residue
configurations**.  Funnel: 13,204 candidates reach a grown
iback-partner; at every one the mback-partner set is nonempty and
consists ENTIRELY of grown-trace worlds — growth propagates, b.i
always applies.  Counterfactual rescues: R1 (same-trace) 0/13,204, R2
(grown, RmC-financed) 13,204/13,204 — the load-bearing repair is
growth-shaped.  Low-depth impossibility decoded paper-level (d ≤ 2
shut; open region d ≥ 3 with a crank-2d distinguisher, beyond the
battery's stabilisation depth).  Lean: mforthResidue_of_config_absurd
pins the vacuity route; MforthResidue weakened to carry SubClosed cl
(verifier finding).

**v2quant completion** (wip/v2quant_probe.lean + out3; 24-frame sweep
battery incl. the F-free 3-chain + resid-probe gadgets, scan at
findBudget 2000 with skip-counting, match tests at 40000): every
pending row stabilises at r ≤ 4 against budgets 5–11.  **THE X9 MATCH
TEST PASSES, proof-certified in BOTH directions**:
∀p(¬◯⊥⊃◯p) ≡ ◯(¬◯⊥⊃◯¬¬◯⊥) ≡ ¬◯⊥⊃◯⊥ (one RN(◯,{}) class, ¬¬◯⊥) —
the syntactic H2 stabilisation and the semantic rank-descent compute
the same object; per the §33 ledger, one proof now pays three debts.
Also certified: ∀p(gap row) ≡ ◯⊥, ∀p(◯p) ≡ ◯⊥.  ONE undecided cell in
the whole experiment: D₆ = ◯¬◯⊥⊃(◯⊥∨¬◯⊥) vs ◯(◯p⊃p) (the recorded
staller; killed at 2000 and 40000 nodes) — if D₆ ⊢ ◯(◯p⊃p) the
gap-row join would climb at r=6.

**Verification fan-out** (4 adversarial agents): could not refute the
closure claim.  Quote discipline: "the amalgamation THEOREMS are
sorry-free and axiom-clean" (the import chain retains the sorried
general wit_pbisim/wit_force, provably not depended on).  Recorded
gaps: entry budget 2·cl.card+1 coarser than 2·nu+1 (interpolant rank
recalibrates); E-form input not agreement-derivable in general — BUT
the no-go counterexample (forkF) is NOT mutually confluent, so over
confluent models E-form delivery is OPEN, a new pillar-2 opening.

## 36. 2026-07-25 afternoon: growth propagation SPLIT — boundary theorem proved; the configuration is satisfiable (vacuity route dead)

wip/residueGrowth.lean (913b4d3), three theorems, #guard_msgs-pinned
[propext, Classical.choice, Quot.sound]:

* `residue_growth_boundary` PROVED: over a `Ranked` link (level-n
  links transfer p-free formulas of crankC ≤ n — definitional for
  agreement-built links), every p-FREE formula in a residue
  configuration's growth tr(kv)∖val Δ has crankC ≥ 2d.  Sub-boundary
  protected growth crosses to u (level 2d) and back to κ (level
  2d−1), contradicting tr(κ) = val Δ.  So the residue's
  distinguishing formulas are p-laden or boundary-crank — the
  machine-checked location of the S4/K4-style failure mechanism
  (bisimulation rank outrunning interpolant rank), and of the samval
  sharpness decode.

* `residue_config_satisfiable` PROVED: the b.ii configuration IS
  satisfiable — chainP (2-point confluent chain, p at top, no
  fallibles, Rm = Ri) with the FULL link family (a lawful
  LayeredBisimE off p: atoms clause only sees protected atoms) and
  the ◯-adequate closure {⊥,p,◯⊥,◯p}; growth {p,◯p} is PURE-p,
  invisible to the atoms clause.  CORRECTION of §35: the first
  probe's "0 configurations" was an artifact — its closures contained
  no p.  The vacuity route (mforthResidue_of_config_absurd) is dead
  as a general strategy.

* `residue_config_example_resolves` PROVED: in that instance the
  conclusion holds — the growth is ◯-ANTICIPATED (◯p ∈ val Δ), so
  the grown answer works with (kv,u) as its own base and reservoir.
  MforthResidue is therefore CONTENTFUL and OPEN exactly at: growth
  whose ◯-anticipation fails.

Corrected probe IN FLIGHT (bii_p_probe worktree agent): p-containing
closures, p UNPROTECTED in the approximants, two-atom decorations,
full conclusion search at every configuration; failures would be
counterexamples to MforthResidue forcing a triple redesign.  Also
explored and recorded here: the degraded-triple calculus (base 2d−1
after a mismatch) closes the first mismatch but regresses at
b.ii-from-degraded — degradation alone cannot serve the unbounded
bisimulation game; it becomes viable only combined with growth
propagation or an anticipation lemma.

## 37. 2026-07-25 latest: the last v2quant cell decided — D₆ ⊬ ◯(◯q⊃q); the gap row is fully certified at ◯⊥

The §35 undecided cell is REFUTED: `◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥) ⊢ ◯(◯q⊃q)` is
underivable in plain LaxND, countermodel-certified in the kernel
(wip/d6_gap_cell.lean; all pinned theorems axiom-clean, `[propext,
Quot.sound]`).  The countermodel is `defaultFrames` item 6 decorated
p@{2} — the 3-chain with rigid first Rₘ-step and fallible top — and a
fallible-free twin (chain3F, p@{2}) certifies too, since every
fallible-free model forces D₆ everywhere.  Consequence: the gap-row
∀-join does NOT climb at r=6; all 15 dictionary classes are
certificate-decided on that row's ∀-side, so the rank-bounded
`∀p.◯(◯p⊃p)` = ◯⊥ from r=2 through r=9, matching the §35 match test
(≡ ◯⊥ proved both ways).  No anomaly against the rank-2 stabilisation
pattern remains anywhere in the experiment's ∀-tables.

Post-mortem: the recorded 6-hour/10-minute grinds were the ∃-side call
`◯(◯p⊃p) ⊢ D₆` (no battery frame refutes it), misattributed to the
∀-side, which the battery had refuted all along; the forced skip then
swallowed both sides.  Correction noted at `skipCells` in
wip/v2quant_probe.lean.  Bonus: the gap row's crank≤5 ∃-side skip
`◯(◯p⊃p) ⊢ (◯¬◯⊥) ∨ ¬¬◯⊥` is also REFUTED (4-fork frame, pinned in
the same file); the two D₆-family ∃-cells remain OPEN and touch only
the ∃-meet, whose value ⊤ is unchanged.

## 38. 2026-07-26 night: corrected probe verdict — 0/36.6M failures; the open zone is exactly the strictly-descending regime

Corrected b.ii probe (wip/bii_p_probe.lean, p-containing closures, p
UNPROTECTED, exhaustive conclusion search; 1603 models, 1,739,255
pairs, 56 s): control PASSES (finds the chainP instance; note the
growth there is {p}, not {p,◯p} — ◯p ∈ val Δ already, by pointwise
χ⊃◯χ, which is precisely the anticipation the resolution uses).
**36,588,835 configurations, 0 failures.**  Growth composition: 100%
pure-p-laden, 0 protected members at ANY crank (the boundary theorem
is empirically loose: protected growth never occurs at all in the
fixpoint regime, since a fixpoint E-link over both-confluent models
transfers every protected formula).  Resolution: EVERY config
resolves by a SAME-TRACE answer — the battery's Z-hierarchies
stabilise by level 3, so the level-(2d−1) link at κ already holds at
2d (fixpoint collapse) and κ is its own rescue; grown answers exist
at exactly the ~4% whose growth is ◯-anticipated; grown-ONLY 0.
Also: empirical crankC-rankedness clean on confluent×confluent pairs
only (33k–72k violations with M non-confluent — crankC transfer
needs both models confluent, as force_iff_of_layeredC says).

Lean: `mforthResidue_of_stabilised` PROVED (+audit) — pointwise
level-collapse at the mback-partner's link discharges the residue;
the machine-checked name of the fixpoint-regime rescue.  MforthResidue
remains OPEN, unrefuted, with the danger zone now pinned exactly:
links strictly below the Z-stabilisation level at small canonical
depth = long strictly-descending bisimulation hierarchies = the
◯⊃-alternation towers of the cross-route experiment (X9/D₆
territory).  Small batteries cannot reach it (Z stabilises too fast);
the syntactic route reaches it as the D₆ cell.

## 39. 2026-07-26: THE STABILISATION LEMMA mechanised — the residue is PAID in the one-variable setting

wip/stabilise.lean (68996ab), sorry-free, #guard_msgs-pinned, every
theorem conditional only on `D : RNDict` (the certified variable-free
dictionary interface; instantiation from the v2quant closure tables in
flight as wip/rnDict.lean).  The cross-route plan as a theorem chain:

* `RNDict`: finitely many variable-free reps + crank bound + certified
  connective-closure tables up to `Interd` (PLLSemUIFrag's calculus).
* `dict_collapse` PROVED: structural induction with the Interd
  congruences — EVERY variable-free formula is interderivable with a
  rep.  The finite closure certificate decides the WHOLE fragment;
  this resolves the 2026-07-13 objection ("finitely many probes cannot
  settle the fragment's infinitude"): closure under the generating
  connectives can, and the probe's round-6 fixpoint was exactly that.
* `dict_agree_stab` PROVED — THE STABILISATION LEMMA: variable-free
  agreement at rank crankBound is agreement at every rank.
* `vfB` PROVED (m-clauses as hypotheses VfMforth/VfMback): the
  CONSTANT family Z n := vfAgree is a lawful LayeredBisimE between
  p-pure models; i-clauses = agree_iforth/agree_iback at alphabet ∅,
  the 2α+2 character budget ABSORBED by stabilisation; atoms by
  p-purity; fall at rank 0.
* `vfB_mforthResidue` PROVED: constant family ⇒ level-collapse
  hypothesis is `id` ⇒ MforthResidue holds.  THE RESIDUE IS PAID.
* `restricted_amalgamation_oneVar` PROVED: for p-pure confluent K and
  p-pure M, root agreement at rank crankBound (fixed, closure-
  independent!) yields the full p-variant conclusion — no residue
  hypothesis, entry budget crankBound instead of 2·cl.card+1.

Status of one-variable PCLL semantic UI after this: pillar 3 fully
paid; the ONLY remaining obligation is VfMforth/VfMback — the two
m-clauses of pillar 2 for the constant variable-free-agreement link —
plus the Thm 5.1 wrapper.  Note the contrast with IPC: the one-variable
p-free fragment there is the (infinite) Rieger–Nishimura lattice, so
no constant-link shortcut exists; PLL's variable-free fragment is
FINITE (the ◯⊥-ladder stabilises) — the modality is what makes the
restricted case easier, not harder.

## 40. 2026-07-26: the 15-class closure is REFUTED — the dictionary premise falls, the stabilisation chain stands

The rnDict instantiation agent's verdict, consolidated (d37f9c0):
**the RN(◯,{}) dictionary is NOT connective-closed at 15 classes.**
wip/rnDictRefute.lean proves, axiom-clean [propext, Quot.sound] and
#guard_msgs-pinned:

  refute_cAnd_8_10  : ∀ k : Fin 15, ¬ Interd (q8.and q10)     (rep15 k)
  refute_cImp_9_4   : ∀ k : Fin 15, ¬ Interd (q9.ifThen q4)   (rep15 k)
  refute_cImp_12_4  : ∀ k : Fin 15, ¬ Interd (q12.ifThen q4)  (rep15 k)
  refute_cImp_14_4  : ∀ k : Fin 15, ¬ Interd (q14.ifThen q4)  (rep15 k)

each candidate eliminated by a checkB-certified countermodel (the
refuting battery COMPLETE for variable-free refutation at ≤ 4 worlds).
All four witnesses are X9-tower combinations of size 20–23 — beyond
v2quant's SZMAX = 16 candidate cap.  "Closure at round 6" was closure
of the size-≤16 QUOTIENT.  Kernel-checked consequence: RN(◯,{}) has
**≥ 16 classes** (≥ 19 if the four witnesses are pairwise distinct —
not yet pinned).  rnDict15 is UNCOMPLETABLE as an instantiation; its
603/690 certified cells (236 emitted G4cTm terms via rnDictGen, 367
generic Interd laws, rnDictBase) are kept as raw material for the
enlarged dictionary.  83 further cells OPEN (unprovable by both
searchers, unrefuted at ≤ 4 worlds; per-cell candidate shortlists
recorded — ⊤-vs-tower ambiguities needing ≥ 5-world countermodels or
deeper proofs).

CONSEQUENCES.  (1) The variable-free fragment-finiteness question is
REOPENED, now leaning infinite (the tower splits past every cap so
far) — supporting the Curry-problem thread's RN(◯,{})-infinite
direction, and giving the nucleus/assembly thread its first
kernel-checked lower bound on the RN(◯,{}) size.  (2) The
stabilisation chain (wip/stabilise.lean) is UNTOUCHED and now carries
the question precisely: by dict_collapse, an RNDict exists iff the
fragment is finite; restricted_amalgamation_oneVar is blocked pending
that.  (3) The v2quant r-tables were computed over the truncated
quotient: every certified derivability (incl. the X9 match and
D₆ ⊬ gap row) STANDS, but the "join" columns are joins over the
15-class scan — computed join ⊢ true join; per-row values could rise
if a new class derives a row.  Re-audit needed over the enlarged
dictionary.  (4) The correct fallback for one-variable UI is the
rank-relative form (per-rank finiteness = frag_reps_exist', PROVED):
IPC's precedent says UI can hold over an infinite one-variable
fragment (Pitts over the Rieger–Nishimura lattice) — global collapse
was a shortcut, not a necessity.

## 41. 2026-07-26: the RANK-RELATIVE stabilisation lemma — band collapse; the open core is a plateau

wip/bandStabilise.lean (9dcda2c), sorry-free, pinned.  The finite
dictionary was certification apparatus only; the chain needs one Prop:
`BandCollapse R E` (every variable-free formula of crank ≤ E
interderivable with one of crank ≤ R), with E = 2R+2 dictated by the
character budget.  PROVED: band_agree_stab (CHOICE-FREE
[propext, Quot.sound]); bandB (constant family Z n := bandAgree R, a
lawful LayeredBisimE between p-pure models — i-clauses upgrade across
the band then spend agree_iforth/iback); bandB_mforthResidue (residue
paid); restricted_amalgamation_oneVar_band (one-variable amalgamation
at entry rank R from BandCollapse R (2R+2) + BandMforth/BandMback);
bandCollapse_of_dict (the global constant-link theorem is the E-free
special case — "reinstated-if-closed" made precise).  OPEN CORE now:
exhibit ONE R with BandCollapse R (2R+2) — a PLATEAU of the
variable-free class-count function n(r) on [R, 2R+2].  Strictly weaker
than fragment finiteness: n may resume growing above the band; failure
for ALL R requires new classes at doubling density FOREVER (every
window [R, 2R+2] hits a new class) — the S4 signature.  Observed so
far: new classes at essentially every crank ≤ 7-8 (incl. the §40
witnesses at 6-7); the dictionary-mapping session's class-count curve
is exactly the data that locates or excludes a plateau.  Terminology
correction for §40's prose: the lattice whose size the literature
leaves open is RN(◯,{}) (variable-free PLL; ◯⊥ is not a free
generator); RN({p}) — Rieger–Nishimura proper — is classically
infinite (Rieger 1949, Nishimura 1960), and with ◯-free conservativity
the one-VARIABLE PLL fragment is infinite too; neither settles
RN(◯,{}).  Note the compatibility: the Curry-problem thread wants
RN(◯,{}) infinite, UI wants a plateau — both can hold.

## 42. 2026-07-26: the infallible collapse formalised; the m-clause positive half proved

wip/bandM.lean (sorry-free, pinned).  Matthew's observation — PLL+¬◯⊥
is complete for infallible constraint models, where ◯⊥ ≡ ⊥ and
RN(◯,{}) collapses to {⊥,⊤} — is now a theorem pair:
`infallible_amalgamation` (between p-pure INFALLIBLE models, K
confluent, the total link is a lawful LayeredBisimE — all eight
clauses trivial, m-clauses included — and the one-variable
amalgamation holds with NO agreement hypothesis; the first
UNCONDITIONAL instance of the whole amalgamation tower and a
constructive non-vacuity certificate), and `band_mforth_positive`
(general fallible case: the POSITIVE half of the banded m-forth
clause via charPos + bare possibility on both sides + band transfer
at α+3 ≤ R; the NEGATIVE half — no overshoot — is the isolated
remainder).  Reading: the m-clause difficulty, like the tower itself,
is EXACTLY fallibility-grading; over ¬◯⊥ everything trivialises, so
any PLL-UI proof factors its hard content through the fallibility
dimension.  PRECISION note on §40: "≥ 16 classes kernel-checked"
overstated — the four ∀k-refutations are fully pinned, but pairwise
distinctness of the 15 representatives (and of the 4 witnesses) is
probe-certified only, not yet Lean-pinned; the mapping session should
pin the separations.

## 43. 2026-07-26 evening: the two quotients computed — RN ≥ 16 PINNED, RNC first map; no plateau in sight; the gap row survives everything

Two independent certification streams landed and consolidate here.

**PLL (the dictionary-mapping session; wip/rnDict2Report.md, artifacts
rnSep/rnSepColl/rnDict2Hand/rnDict2/rnDictRefute2):** the four §40
witnesses are ONE class, q15 := q9⊃q4, kernel-pinned (two of the three
fusions AXIOM-FREE; the searcher could not find them — hand Deriv
terms; gap patterns catalogued).  The 15 base classes are NOW pairwise
distinct CERTIFIED (165 pinned countermodels; {q1,q11,q13} and
{q9,q12,q14} need 5 worlds — the ≤4-world battery cannot see them;
exhaustive ROOTED 5-world completeness by generated-submodel
reduction).  Aggregate `rep16_pairwise_distinct` [propext, Quot.sound]:
**RN(◯,{}) ≥ 16, fully pinned** (the §42 precision debt is paid).
The 16-class closure round FAILS massively: ~40 cells match no class
(⊃-block dominates; three pinned 6-WORLD models were needed — some
refutations invisible at ≤5 worlds); ∧-family spawns all-distinct.
Class count rises through every observed crank window: **no plateau
visible; BandCollapse unsupported below crank ~8.**
**THE GAP ROW SURVIVES THE FULL ENLARGEMENT**: among all 16 reps and
all 41 spawned-class witnesses, only ⊥ and ◯⊥ derive ◯(◯p⊃p) (pinned
countermodels for every other candidate) ⇒ ∀p.◯(◯p⊃p) = ◯⊥ stands
over everything now known.

**PCLL (the RNC probe, §consolidated 4f0cb6d):** distribution merges
q9 ≡ q12 and fuses the witness class (distF q3 q6 exactly), 19 → 15;
new reusable certificate theorem not_derivU_of_checkConf (confluent
countermodel ⇒ PCLL-underivability); but the RNC closure sweep spawns
26 new-class cells — **the tower continues past distribution**.  Sole
open matrix cell [q14] ⊢ q13 in both logics.

**Synthesis:** fragment-infinitude now the working picture for BOTH
quotients; the plateau (constant/band link) route is empirically dead
at accessible ranks; the PER-INSTANCE route is simultaneously
STRENGTHENED (the gap-row value certified against the entire
enlargement — B1 + per-instance-B2 evidence at its strongest).  Route
forward: the mforth choice-freedom refactor + the per-instance residue
treatment, over whichever of PLL/PCLL the Thm 5.1 assembly targets.

## 44. 2026-07-26 night: the 16-round is FULLY DECIDED — 58 spawned witnesses, exact families, RN(◯,{}) ≥ 25

Completion of the dictionary-mapping session (§43 reported it in
flight).  Every one of the 140 searched cells of the 16-class closure
round is now DECIDED — zero open cells:

  82 LANDED (19 searcher + 63 hand certificates — wip/rnDict2Hand.lean,
     the searcher-gap catalogue: ofImpTop order facts, ex falso inside
     ◯, ◯-intro under orElim, collapse-lemma cuts);
  58 NEW-CLASS witnesses (6 ∧, 15 ∨, 35 ⊃, 2 ◯), each with every
     candidate countermodel-eliminated; witness theorems over Fin 16
     in wip/rnDictRefute2.lean; wip/rnDict2.lean emits the partial
     rnDict16 : RNDict with exactly these 58 sorried cells.

FIVE pinned 6-world countermodels (extraCMs) decide candidates
invisible at ≤5 worlds — among them [q14] ⊬ q13 (§43's "sole open
matrix cell", now closed), ⊬ q8∨q10, [q13] ⊬ q5∨q8, [q13] ⊬ q8∨q12.

The spawned classes classify EXACTLY within the scanned families
(wip/xsep_*.txt + the 8 hand collapse certificates of
wip/rnSpawnColl.lean — ALL eight previously-open spawned pairs are
COLLAPSES, e.g. q8∨q10 ≡ q8∨q11 and the cross-shape q10⊃q4 ≡ q11⊃q7,
two pinned AXIOM-FREE):

  ∧-family: exactly 6 classes;  ∨-family: exactly 9;
  ⊃-family (scanned subset of 12): exactly 8;  ◯-column: 2;
  25 further ⊃-witnesses and all cross-family pairs unscanned.

CLASS-COUNT: rep16_pairwise_distinct pins ≥ 16 in the kernel; the
∨-family clique (9 spawned classes pairwise distinct and distinct
from all 16) lifts the certified count to **RN(◯,{}) ≥ 25**
(checkB-gated run-log countermodels, kernel-pinnable on demand); with
58 witnesses outstanding the true count is plausibly 40+.  The
class-count curve rises through every crank window observed (spawned
reps at crank 6–9) — the §41 plateau remains without support, and the
Curry-problem thread's RN(◯,{})-infinite direction strengthens again.

The gap-row audit of §43 stands unchanged over the completed round:
only ⊥ and ◯⊥ derive ◯(◯p⊃p); ∀p.◯(◯p⊃p) = ◯⊥.

Deliverables: wip/rnSep.lean (165 sep certificates), wip/rnSepColl.lean
(witness collapse + rep16 aggregate), wip/rnDict2Hand.lean (63 hand
cells), wip/rnDict2.lean (726/784 cells certified), 
wip/rnDictRefute2.lean (58 witness theorems), wip/rnSpawnColl.lean
(8 spawned collapses), wip/rnDict2Report.md (the class map), run
outputs wip/gen2logs/ + wip/xsep_*.txt + wip/gaprow_*.txt.

## 44. 2026-07-26 night: the mforth choice-freedom refactor — the input link is LayeredBisimWit

fc9ab18, whole chain green, audits unchanged.  The consumption audit
(§34's inventory) showed the E-form's mforth spent at ONE site — the
truth lemma's ◯-backward — where the K-side witness is chosen, not
given.  The input format is now `LayeredBisimWit`: mforth replaced by
the witness clause

  mwit : Z (n+1) k m → (∃ κ, Rm k κ ∧ force κ ψ) →
    ∃ κ u', Rm k κ ∧ force κ ψ ∧ Rm m u' ∧ (Z n κ u' ∨ pair-fallible)

(the ◯-obligation for SOME row-witness of the formula in play; the
prover picks).  `LayeredBisimE.toWit` embeds the old format — strictly
one-way, so pillar 2's debt is strictly weakened; the weakened Props
are `VfMwit`/`BandMwit` with `…_of_…forth` bridges.  Adversarial
clauses (iback, mback) unchanged; wit_pbisimC's OUTPUT is still a full
unbounded PBisim.  What this buys the negative half: the maximal-type
ascent arguments now have their proper home (the samval-decoded
unmatchable row-members — the dead-end partners no formula can force a
match for — no longer refute the obligation, since the prover may
choose a matchable witness).  What it does not buy: the crank
treadmill (matching at rank R needs characters boxed at R+3) stands;
the remaining depth is per-instance stabilisation, as §43 concluded.
Concurrent: the mapping session continues landing separation-scan
artifacts on this branch (be0ca34).

## 45. 2026-07-27: THE MAXIMAL-TYPE ASCENT — the witness-form m-clause PROVED under the band

wip/bandM.lean (d164be5), sorry-free, pinned:

  bandMwit_of_collapse : 1 ≤ R → BandCollapse R (2R+2) →
    MutuallyConfluent K → MutuallyConfluent M → BandMwit R K M

No fallible escape is consumed.  Engine (the ascent): a ψ-witness κ in
k's row boxes its rank-R positive character across the link — the band
collapse pulls ◯charPos (crank R+3) back under rank R, defeating the
crank treadmill — and bare possibility in M realises it at u′.  Exact
type match ⇒ rank-R agreement, done.  Overshoot at a representative D₀
⇒ the backward transfer returns κ′ ∈ row(k) covering u′'s type, and
the confluence square over (Rₘ k κ, Rᵢ k κ′) yields y ∈ row(k) that
keeps ψ (persistence along Rᵢ κ y) and swallows κ′'s type (persistence
along Rₘ κ′ y) — a ψ-witness with strictly larger type.  Finitely many
representatives ⇒ termination.  Supporting lemmas:
band_row_char_partner/_rev, private countP arithmetic.

New capstone `restricted_amalgamation_oneVar_band'`: the banded
one-variable amalgamation from BandCollapse R (2R+2) + BandMback ONLY.
LEDGER after tonight: the forth-side m-obligation is PAID (under the
band); remaining = the plateau itself (empirically unsupported at
accessible ranks, §43) and BandMback (adversarial; dead-end gap).
Matthew's observation recorded: mwit + ascent is a reducibility-
candidates-style move (System F SN) — quantify over observations
rather than raw moves, then saturate witnesses; kinship with the
repo's own ⊤⊤-lifting SN proof (biorthogonal closure) noted in the
session log.

## 46. 2026-07-27: Matthew's BandCollapse objection — correction of record; RN(PCLL,◯,{}) presented

**The correction.**  Matthew challenged `BandCollapse R (2R+2)`
("iterate it and everything collapses to crank 0 — absurd").  The
specific reductio fails — the band is anchored at R and gives no
descent below R — but the substance of the objection is RIGHT and the
§41/§45 record was WRONG on the key point: one band bootstraps
UPWARD.  By exactly the dict_collapse rebuild induction (collapse the
subformulas to rank ≤ R, reassemble with one connective: crank ≤ R+2
≤ 2R+2, collapse again), `BandCollapse R (2R+2)` implies collapse of
the WHOLE variable-free fragment to rank ≤ R.  So the band hypothesis
is EQUIVALENT to fragment finiteness (with a rank-R representative
bound) — NOT "strictly weaker: growth may resume above the band", and
the "failure needs doubling-density growth forever" characterisation
is retracted.  Consequences: (a) the ascent theorem
bandMwit_of_collapse and the banded amalgamation are conditional on
fragment finiteness, no less; (b) the plateau question and the
fragment-finiteness question are ONE question; (c) the injectivity
delegation (agent in flight: h : RN({p}) → RN(L,◯,{}) under p ↦ ◯⊥,
faithfulness for L ∈ {PLL, PCLL} via the fallible-top U-transfer
construction) would settle it NEGATIVELY for both logics, killing the
band route and crowning the per-instance ascent (the ascent proof
only uses finiteness + transferability of the TEST LIST, so it
relativises to finite test sets — the per-instance form is the
surviving shape).

**Class-count confirmations** (Matthew's notation RN(L,◯,{}) with the
logic as argument, ADOPTED): RN(PLL,◯,{}) ≥ 16, fully kernel-pinned
(rep16_pairwise_distinct).  RN(PCLL,◯,{}): the 19 candidates fall
into 15 classes — the 15 PLL base reps collapse to 14 (sole merge
q9 ≡ q12, via the single instance distF q3 q6), plus the fused
witness class w = q8∧q10 ≡ q9⊃q4 ≡ q12⊃q4 ≡ q14⊃q4 distinct from all
14.  Certification status: all separations pinned per-pair
(wip/rncCert.lean, confluent countermodels, [propext, Quot.sound]);
merges pinned (rncCertPos/rnSepColl — the witness fusions are
PLL-level, two of three axiom-free, hence PCLL); an AGGREGATE
pairwise-distinctness theorem for the 15 (analogue of
rep16_pairwise_distinct) is one decide-glue file away and not yet
written.  The raw probe matrix's "18 classes" line predates the
hand-certificate fusion layer.  Sole unknown cell of the 15×15
PCLL matrix: q14 ⊢ q13.  Hasse structure extracted and drawn
(session diagram): heights 0..6, q9* the only distribution-merge,
w incomparable to ◯¬◯⊥, covers as certified.

## §47 (2026-07-27) — The witness-form OUTPUT: force_iff_of_witOut, the re-typed projection, BandMback leaves the ledger

The candidates-lens conclusion of §46's session made Lean.  The
specification consumes exactly one property of the output p-variant
link — preservation of p-free formulas — and that property survives
weakening BOTH ◯-directions of the output to witness form, over a
confluent base.

**New structures** (wip/witTripleC.lean refactor + wip/witOut.lean,
all sorry-free, [propext, Classical.choice, Quot.sound] throughout):

* The input `LayeredBisimWit` loses its adversarial `mback` FIELD —
  demoted to the optional side condition `MBack`, consumed at exactly
  one site (`witTriple_mforth`); the refactor compiling IS the
  consumption audit.  New M-side WITNESS clause `MWitM` (the adversary
  picks the formula, not the world), strictly weaker (`mwitM_of_mback`).
* `ABisimWit`/`PBisimWit`: the unbounded witness-form output link.
  `force_iff_of_witOut` — THE LINCHPIN: a witness-form link between a
  MUTUALLY CONFLUENT base and an ARBITRARY variant transfers every
  protected formula at every rank.  ◯-forward extracts the base-row
  witness from the ∀∃ clause directly and pushes it through `mwit`;
  ◯-backward pulls the reflexive-successor witness through `mback` and
  rebuilds ∀∃ by bare possibility — the single use of confluence.
* `MwitResidue`: the witness-form residue, strictly weaker than
  `MforthResidue` on both sides (extra hypotheses: the partners come
  from the witness clause with a forcing fact riding along; weaker
  conclusion: ANY row-witness may answer).  Bridges:
  `mwitResidue_of_mforthResidue`, `mwitResidue_of_stabilised`.
* `witTriple_mwit` / `wit_pbisimW` / `amalgamation_assembledW`: the
  ◯-maintenance, projection, and assembly in witness form — no
  adversarial clause consumed anywhere; the assembly delivers closure
  agreement AND (over a confluent base) full p-free transfer at the
  root.

**The banded cascade** (wip/bandW.lean): `BandMwitM` discharged by the
MIRRORED maximal-type ascent (bandAgree is symmetric), so
`restricted_amalgamation_oneVar_wit` needs the band collapse and
NOTHING else — `BandMback`, the last unproved m-obligation of the §45
route, left the ledger.

## §48 (2026-07-27) — THE RANKED ASCENT: pillar 2 closes with no band and no finiteness

The decisive observation, minutes after §47: the ascent's finiteness
input is `frag_reps_exist'` — PER-RANK finiteness (pillar 1) — not
fragment finiteness.  The band entered §45's proof at exactly one
point: lifting link agreement to the boxed-character rank.  Supplying
that rank directly (wip/rankedM.lean, all sorry-free):

* `rankedMwit`: over mutually confluent models, variable-free
  agreement at rank α+3 answers every K-row ψ-witness by one whose
  M-partner agrees at rank α — NO escape, rank spend +3 (cheaper than
  the i-clauses' 2α+2 halving).  `rankedMwitM` by symmetry;
  `bandMwit_of_collapse'` refactors §45's ascent as stabilisation
  feeding the ranked clause.
* `rankedB`: Z n := agreement at rank `rslope n`
  (rslope(n+1) = 2·rslope n + 3) is a lawful `LayeredBisimWit` off p
  between one-variable mutually confluent models, plus `MWitM` —
  EVERY input clause of the witness pipeline from pure rank-bounded
  agreement.  **PILLAR 2 IS CLOSED in the ranked setting.**
* `restricted_amalgamation_oneVar_ranked`: the one-variable
  amalgamation from root agreement at the FIXED rank
  rslope(2·|cl|+1) (tower-exponential in the closure, but determined
  by it), modulo the ONE open Prop `MwitResidue` of the ranked link.
  The residue — whose geography §§40-42 already mapped
  (`residue_growth_boundary`: genuine configurations are p-laden or
  boundary-crank; the S4/K4 UI-killer mechanism) — is now the ENTIRE
  unproved content of the route.

## §49 (2026-07-27) — Fragment infinitude LANDS: the band is REFUTED, the dictionary impossible, the purity corrected

The injectivity delegation returned stronger than commissioned
(wip/rnEmbed.lean, cherry-picked; 1069 lines, 15 pinned audits): the
full Rieger–Nishimura ladder embeds under p ↦ ◯⊥ into BOTH quotients,
pairwise distinct at EVERY index — over the single infinite RN frame
on ℕ with closed-form rung truth sets, no decide budget.  Kernel-checked:
`varfree_no_finite_cover_pll/_pcll` (**both variable-free fragments
are INFINITE** — §46's "likely" upgraded to theorem, Nishimura not
consumed), `rank_escape_pll/_pcll` (every rank is escaped),
`rnSub_derivU_iff_deriv` (PCLL conservative over PLL on the embedded
ladder; image order = truth-set containment in both logics),
`crank_rnP_emb` (two fresh rungs per crank forever).

Consequences, mechanised the same night (wip/bandRefute.lean):

* `global_collapse_of_band` — §46's rebuild induction in Lean: one
  band `BandCollapse R E`, `E ≥ R+2`, bootstraps to global collapse
  at rank R.
* `bandCollapse_refuted` — **BandCollapse R E is FALSE for every R
  and every E ≥ R+2** (in particular the character width 2R+2).  The
  band route of §§43-45 and §47 is closed NEGATIVELY: those theorems
  keep their (true) conditional content with antecedents now known
  unsatisfiable.  The ranked route (§48), which never used the band,
  is the survivor — built hours before its rival died.
* `rnDict_false` — the `RNDict` interface is UNINSTANTIABLE; the
  dictionary-closure certification program (603/690 cells) cannot
  complete.  No further effort there.
* `ppure_ffree` (axiom-free) + `ppure_oneVar_trivial` — formulation
  audit: `full_F` forces `PPure` models infallible, so the p-pure
  one-variable amalgamation was UNCONDITIONALLY true
  (`infallible_amalgamation`), i.e. the p-pure hypotheses trivialised
  those statements.  Corrected purity `POnly` (V a ⊆ F off p) adopted
  by the ranked chain — fallible one-variable models genuinely in
  scope.

**The route, after tonight**: everything unconditional except ONE
displayed Prop — `MwitResidue` for the ranked link at slope
2s+3 — consumed at one site, bridged from stabilisation and from the
old residue, boundary-mapped, probe-populated.  Next: (i) decide
MwitResidue for ranked links (the boundary theorem constrains genuine
configurations to p-laden/boundary-crank growth whose ◯-anticipation
fails; the §42 probe battery re-aimed at the witness form); (ii) the
spec layer over PBisimWit (IsSemExW) and the PCLL UI statement it
feeds.

## §50 (2026-07-27) — The residue probe re-aimed at MwitResidue: clean at ~330M instances, and the open zone pinned to large models

wip/mwit_probe.lean (exe mwitprobe; output wip/mwit_out.txt; control =
the hand instance of residue_config_satisfiable, PASS).  The certified
b.ii funnel enriched by a ψ-loop and the witness-freedom verdict
(GIVEN / OTHER / FAIL per (configuration, ψ)), answer search extended
by the canonical-top answer, run over TWO link families:

* **mode R** — the RANKED family Z n := variable-free agreement at
  rank rslope n over a ◯⊥-alternation pool, POnly-corrected
  decorations, both models confluent — the exact link of the open
  Prop MwitResidue cl (rankedB …): 131,044 pairs, 4,314,267
  configurations per closure, 30–39M instances per closure —
  **GIVEN = 100%, OTHER = 0, FAIL = 0**; every pair's chain stabilises
  by level 2, live window EMPTY.
* **mode G** — the largest lawful layered family (hard mode,
  p unprotected), reproducing the §38 scan scale: 1,739,255 pairs,
  ~12.2M configurations per closure (×3 ≈ the old 36.5M), 85–109M
  instances per closure — **GIVEN = 100%, OTHER = 0, FAIL = 0**;
  stabilisation by level ≤ 3, live window EMPTY, 0 monotonicity
  violations.

READING (three facts, kept distinct): (1) MwitResidue is UNREFUTED at
~330M instances across both families — no counterexample candidate
exists at ≤7 worlds.  (2) The witness freedom was NEVER exercised
(OTHER = 0): at battery scale every configuration already resolves at
the given witness, so the probe shows the re-typing SAFE but not yet
NECESSARY — its value remains the strictly weaker Prop and the
BandMback elimination, plus whatever the large-model regime holds.
(3) The live window is empty in both modes: every reachable
configuration sits at stabilised link levels, where
mwitResidue_of_stabilised is a THEOREM — so the entire open content
of MwitResidue is confined to the strictly-descending regime, which
(by the ladder-needs-depth fact of wip/rnEmbed.lean: rung k needs
~k/2 worlds) requires models beyond any small battery.  The open Prop
stays OPEN with its geography sharpened: genuinely dangerous
configurations need LARGE confluent models whose variable-free
agreement chain still descends at the financed levels — the infinite
alternation-tower territory, exactly where a UI counterexample would
have to live.

Also this session: the parallel track's searcher optimisations merged
(cherry-picks 294251b/5413696 = order-canonical ckey + global failure
memo for the plain searcher, authorship preserved) and COMPOSED into
the bounded searcher (budget × memo × key; failures cached only with
budget remaining — sound because exhaustion is sticky); findBounded's
public signature unchanged; verified by the in-tree #guard gates plus
a 1100-sequent cross-check (0 mismatches).  Merge guidance recorded:
belief branch → main first, then ui-confluence, resolving
PLLG4Term.lean to the combined version; never rebase ui-confluence.

## §51 (2026-07-27) — The deep probe REACHES the descending regime: RankGap verified at 1.17M live instances

wip/mwit_deep.lean (exe mwitdeep; output wip/mwit_deep_out.txt).  On
the lifted ladder truncations (8/10/12 base worlds + fallible top) the
ranked chain is STILL DESCENDING at level 5 on every one of 17,424
confluent pairs (stab histogram: 5×17,424 — the rung-pool ceiling,
genuine descent through rslope 4 = 45).  For the first time the LIVE
window is occupied: 140,616 configurations with 2d−1 < stab (cl1;
first dump: d=2, stab=5 on the 8-world lifted ladder), carrying
1,174,068 (config,ψ) instances — GIVEN = 100%, OTHER = 0, FAIL = 0.
Total across modes: ~51M further instances, all clean.  (Gdeep: gfp
chains now stabilise as late as level 11 on the deep frames; its
configurations still all sit at stabilised levels.)

READING: RankGap now has direct evidence INSIDE the descending regime
— the previously untouched zone.  The live configurations resolve at
the given witness, meaning full-rank same-trace partners exist
pointwise even while the global agreement chain descends.  Open
remainder, sharpened once more: deeper d (live configs so far have
d=2), heterogeneous pairs, and the true infinite-model limit.  The
balance of evidence has shifted from "confined to stabilisation" to
"RankGap plausibly TRUE in general" — the proof attempt should target
a pointwise full-rank partner construction at residue configurations
(the ladder models suggest the same-trace κ-partner itself carries
full-rank agreement there), with the §50 boundary machinery
(pOnly_V_eq_F + residue_growth_boundary) as the tool.

## §52 (2026-07-27) — The pointwise attack: the ∀∃-descent, the row-rigid theorem, and the open Prop shrinks to RankGapGrow

wip/rankGapPoint.lean, all sorry-free, guards pinned:

* **The ∀∃-descent** (reservoir_row_cover / _witness) — a genuinely
  new transfer move: a positive character boxed at the reservoir's
  K-side world (bare possibility, K confluent) crosses the reservoir
  at its FULL rank rslope(2d+1) = 2·rslope(2d)+3, and the ∀∃ clause
  of ◯ at m' EVALUATES DOWNWARD at the i-successor m — realising
  every row(k')-type inside row(m), at ranks far ABOVE the missing
  window; the confluence square in M merges the cover with the
  ψ-witness.  First transfer in the whole development that lands
  inside m's row.
* **rankGap_of_rowRigid + mwitResidue_ranked_of_rowRigid**: over
  row-rigid bases (every infallible ◯-move reflexive — all lifted
  ladders of §51's battery), RankGap and hence the ranked MwitResidue
  are PROVED outright (the witness is m itself; kb := k closes by the
  base link).  The entire §51 live-window evidence class is now
  theorem.
* **rankGap_of_grow**: the case split — if SOME ψ-witness adds
  nothing to m's vf-theory at rank rslope(2d), kb := k closes by
  transitivity (bandAgree_trans_mid).  THE OPEN PROP SHRINKS TO
  RankGapGrow: configurations where EVERY ψ-witness strictly grows
  m's rank-rslope(2d) vf-theory.  Its geography: each witness's
  growth rep D₀ gives m ⊨ ◯D₀ at crank ≤ rslope(2d)+2 — one to two
  connectives above the base link, ranked-invisible (the M-row mirror
  of residue_growth_boundary).
* Designed next step recorded: reinstate the dropped K-side edge
  k' Rᵢ k in WitTripleC (maintainable through every constructor in
  use) — then boxes at k' also evaluate downward into row(k), giving
  the two-sided saturation the maximal-type ascent needs to terminate
  at an exact match in the grow case.

## §53 (2026-07-27) — hik REINSTATED; the square descent made confluence-native; the two-sided saturation packaged

Register point first (Matthew's design constraint): the §52 "∀∃-descent"
as first proved consumed the raw ∀-half of ◯'s ∀∃ clause — the exact
adversarial quantifier the PCLL/confluent programme exists to avoid
(the S4/iK4 UI-killing mechanism), and a proof consuming it
irreducibly would hold over the WRONG model class.  Matthew right in
principle; the move itself innocent: over the confluent class the same
conclusion follows from bare possibility + one confluence square +
persistence.  reservoir_row_cover REPROVED in that register (hM added;
register note in the docstring); "descent" now means precisely:
push-down of a row-witness along Rᵢ through a confluence square.

The classical K-side edge hik : k' Rᵢ k is REINSTATED in WitTripleC —
threaded through the constructor, every construction site
(witTriple_iforth/mforth/mwit, wit_forceC, both assemblies), both
residue Props (MforthResidue, MwitResidue), all bridges
(sameTraceBase's sufficient condition now supplies K.Ri k' kb;
stabilised bridges derive the edge by trans_i hik ∘ sub_mi), the
config-satisfiability witness, RankGap/RankGapGrow (hypothesis + the
K.Ri k' kb conjunct in the conclusion) and their proofs.  Whole tree
green, every #guard_msgs audit passing.  Probe note: the §50/§51
funnels do not test k' Rᵢ k, so their clean verdicts cover a SUPERSET
of the reinstated configurations a fortiori.

NEW: row_push_down (K-side square: row(k') pushes into row(k), no
link crossing, all ranks) and config_two_sided_saturation — in a
residue configuration, every world of row(k') is simultaneously
pushed into row(k) AND covered inside row(m) by a ψ-carrying witness,
at every rank α ≤ rslope(2d+1) − 3.  Both rows saturate over
row(k')'s types.  The single missing ingredient for an exact-type
match — now the entire distance between RankGapGrow and closure — is
the BACKWARD leg: reflecting row(m)-types into row(k').

## §54 (2026-07-27) — The backward leg: all routes converge on ONE window; residue_window PROVED; the grow case exposed as empirically untested

The backward-leg attempt (reflect row(m)-types into row(k')) reduces,
on every route tried, to the SAME obstruction — the rank window
(rslope(2d−1), rslope(2d)]:

* the (k,m)-link reflection is capped at rslope(2d)−3 (◯ξ costs +3);
* the reservoir reflection needs a box at m', i.e. a row(m')-witness
  the configuration lacks (and k' ⊨ ◯ξ ⟺ m' ⊨ ◯ξ across the link, so
  producing one is circular);
* CLOSURE ENLARGEMENT (add low-rank vf representatives to cl so that
  vf-growth becomes trace-visible and the grown case fires) fails
  twice: the bootstrap diverges (the needed rank rslope(2·|cl|) grows
  faster in |cl| than any finite representative stock, fragment
  infinite), AND residue_window (NEW, PROVED, wip/rankGapPoint.lean)
  shows the witness's cl-visible vf-growth at window-floor rank is
  EMPTY in every residue configuration — the κ-partner forces it and
  its trace keeps Δ;
* re-sloping the triple cannot help: any base-spend answer needs
  b − 1 ≥ b.

So RankGapGrow either has a countermodel or needs machinery not in
the toolbox; scale-invariance of the window across all routes is
itself evidence the question is sharp.  A countermodel must have
NON-ROW-RIGID M-rows (else rankGap_of_rowRigid applies) — and the §51
deep battery was entirely row-rigid, so THE GROW CASE HAS NEVER BEEN
EXERCISED empirically.  wip/mwit_deep.lean extended: non-row-rigid
lifted ladders (dense base Rₘ-chains), dense random frames, and a
u' ≠ m split in every verdict column — the first probe aimed at
RankGapGrow itself.

## §55 (2026-07-27) — The grow-case hunt: 4.2M non-rigid configurations, 1.8M in the descending window — all clean

wip/mwit_grow_out.txt (the §54-extended battery: 294 models, 174
confluent; non-row-rigid lifted ladders with dense base Rₘ-chains +
dense random frames).  Mode Rdeep (the exact ranked link): 6.9M/7.2M
configurations per closure with the LIVE window now MASSIVELY
occupied (5.33M live configs, cl1); the NON-RIGID class (u' ≠ m — the
only class where a RankGapGrow countermodel can live) holds 1,961,316
configurations per closure, 1,833,552 of them LIVE (cl1), carrying
16.0M/18.6M instances — GIVEN = 100%, OTHER = 0, FAIL = 0.  Gdeep
adds 2.24M non-rigid configurations per closure, likewise clean.
Every pair's ranked chain still descending at level 5 (pool ceiling).

READING: the first probe evidence in RankGapGrow's own territory —
non-reflexive witnesses, genuinely descending chains — and pointwise
promotion KEEPS HOLDING there (every given witness had a same-trace
full-rank partner).  Caveat kept distinct: u' ≠ m does not yet verify
RankGapGrow's FULL hypothesis (that every ψ-witness vf-grows m's
rank-rslope(2d) theory); a refinement flagging exactly the all-grow
configurations (computable against the rung pool) is the designed
next probe.  Balance of evidence: RankGap plausibly true outright;
the window (§54) remains the sole theoretical obstruction, now with
~230M clean instances around it.

## §56 (2026-07-27 night) — The all-grow flag NEVER FIRES: RankGapGrow's hypothesis empirically unsatisfiable; the open Prop becomes StableWitness

wip/mwit_ag_out.txt: across 31M configurations / 258M (config,ψ)
instances (both modes, both closures, including 4.2M non-rigid
configurations and 5.3M live ones), the ALL-GROW flag fired ZERO
times — every residue configuration contained a pool-stable ψ-witness
(one adding nothing to m's variable-free theory at rank rslope(2d)).
The winning-answer classification never ran for lack of subjects.

The promotion theorem, adjudicated: promotion_iff_internal (PROVED,
[propext, Quot.sound]) shows that with the kv-partner at full rank,
window promotion of ANY K-world's link is a K-INTERNAL question —
full-rank agreement with the grown kv — so "pointwise promotion at κ"
is refutable in isolation (ladder worlds agree to rslope(2d−1) but
not rslope(2d) at every depth) and is DEAD as a theorem target.  The
data instead singles out:

  StableWitness (NEW, the open Prop's working form): in every residue
  configuration, SOME ψ-witness in m's row adds nothing to m's
  variable-free theory at rank rslope(2d).  M-INTERNAL — no K-side
  vocabulary in the conclusion.  rankGap_of_stableWitness (PROVED):
  StableWitness ⟹ RankGap (kb := k through the base link).

Ledger after tonight: MwitResidue(ranked) ⟸ RankGap ⟸ StableWitness,
all bridges PROVED; StableWitness OPEN, supported at 258M/258M
instances, confined by residue_window to failures whose witness
growth lives strictly inside the rank window; RowRigid bases PROVED
outright.  Next: either prove StableWitness (an M-internal minimal-
witness construction — e.g. a ≤-minimal-type ψ-witness in the finite
row, needing that minimal witnesses add nothing at rank rslope(2d),
which residue_window supports for the cl-visible part), or hunt its
countermodel with a battery whose M-rows force GENUINE vf growth on
every witness (rows into strictly-higher ladder rungs — the current
batteries' rows aim at the fallible top or descend).

## §57 (2026-07-27 night) — The minimal-type construction collapses to ONE K-internal inclusion: the grown partner's vf-invisibility

The construction went further than a minimality argument.  The given
witness u' always satisfies type u' ⊇ type m (Rₘ ⊆ Rᵢ persistence),
so a MINIMAL witness adds nothing iff u'-style witnesses reach type m
— and for u' itself the question is settled by the links:

* internal_inclusion (PROVED): type_{r₂}(k) ⊆ type_{r₂}(kv) in every
  configuration — half of stability is free.
* stable_given_iff_internal (PROVED, [propext, Quot.sound]): the
  given witness is stable at rank r ⟺ kv vf-agrees with k at rank r.
  THE M SIDE DROPS OUT of StableWitness-via-u'.
* stableWitness_of_kvInvisible (PROVED): if in every configuration
  the grown iback-partner's variable-free theory at rank rslope(2d)
  equals the base's — its cl-trace growth being vf-INVISIBLE
  (p-laden) — then StableWitness holds and the entire chain
  MwitResidue(ranked) ⟸ RankGap ⟸ StableWitness closes.

THE OPEN KERNEL, in its sharpest form yet: kv's growth over k is
vf-invisible at rank rslope(2d).  Kernel-checked support: the
all-grow flag's 0/258M (which, unpacked, says exactly that u' never
pool-grew m — equivalently kv never pool-grew k); residue_window
covers the cl-visible part at rank ≤ rslope(2d−1).  Falsifier design
(next): the CONFIG-COMPLETION probe — enumerate same-cl-trace,
vf-differing K-pairs (they exist on p-decorated ladders: cl-trace
bands are height-intervals, rungs refine them) and test whether ANY
completes to a full configuration; whichever hypothesis blocks
completion is the proof's missing ingredient.

## §58 (2026-07-27 night) — Config-completion verdict: 0/7,362 complete; the WITNESS LINK does the protecting

wip/mwit_complete_out.txt (264 models, 162 confluent, 81 s):

  cl1: pairs 4,043; vf-VISIBLE 3,621 (kv-adds 3,564, kv-drops 0,
       mixed 57); blocking S0=190 S1=0 S2=0 S3=3,431 S4=0; COMPLETED 0.
  cl3: pairs 4,202; vf-VISIBLE 3,741 (3,705/0/36);
       blocking S0=184 S1=0 S2=0 S3=3,557 S4=0; COMPLETED 0.

Three readings.  (1) kvInvisible survives its direct assault: not one
visible pair completes to a configuration.  (2) internal_inclusion's
prediction confirmed exactly: kv-drops pairs are ABSENT even as
candidates (0/7,362 — persistence up Rᵢ from the common k' forbids
dropping).  (3) The protection is concentrated in ONE hypothesis: S3
— the witness link.  For 95% of visible pairs, k' exists, the
reservoir partner m' exists, the base partner m exists — and then NO
infallible u' in m's row realises kv's grown vf-type at rank
rslope(2d).  The reservoir and base stages never block (S1 = S2 = 0).

THE MECHANISM, named: witness-realisability.  A completing u' must
realise kv's exact pool-type inside the ◯-row of a base-type
realiser; on the batteries, grown types live at fixed ladder heights,
rows step by fixed strides, and the band/stride/type alignment never
occurs.  The two decisive next moves, in priority order:
(i) the HAND-ALIGNED countermodel attempt — engineer U, the
p-decoration and the Rₘ-stride so band boundary, vf-difference and
row-step coincide (if it completes, kvInvisible is dead and the
StableWitness/RankGap conclusions get their first genuine test);
(ii) the witness-realisability lemma — prove abstractly that an
infallible row-witness over a rank-rslope(2d)-agreeing base cannot
realise a vf-visibly grown type (this would close kvInvisible, hence
StableWitness, hence RankGap, hence the ranked MwitResidue — the
entire route).  The wall, if it is one, now has exactly one brick.

## §59 (2026-07-27 late) — Witness-realisability FALSE as a row-fact; the ranked route retired; the synthesis

The §58(ii) abstract lemma is dead before being stated: the canonical
model canonU itself contains infallible vf-VISIBLE row-risers.  Take a
prime theory T of the q5-class (◯¬◯⊥ ∈ T, ¬◯⊥ ∉ T, proper): obInv T
is a proper theory containing ¬◯⊥ — an infallible row-successor whose
variable-free type strictly grows, exactly what witness-realisability
must forbid.  The probes never saw it because (hand-check,
scratchpad/handcheck.lean) the aligned battery frames were silently
NON-CONFLUENT — the stride/parity split breaks the squares, and
mutConf filtered the whole class out.  Verdict on the §58 fork: the
hand-aligned countermodel is the LIVE branch (q5→q3 riser, D = ¬◯⊥,
crank 3, d = 2, links r₁ = 21 / r₂ = 45), and the lemma branch is
CLOSED.

Stepping back (the wood): every uniformly-quantified clause this route
posed was refuted by the ◯⊥-ladder — bandCollapse (E ≥ R+2),
rnDict_false, and now the residue's realisability core; every
formula-local, per-instance statement was PROVED or held at 100% over
~330M instances.  Fragment infinitude (rnEmbed, kernel-checked) is not
a nuisance in the bookkeeping, it IS the obstruction: no rank bound
uniform in the closure can survive, so the residue must be quantified
per interpolation instance (rank a function of φ), or the target logic
must lose the ladder.  Both moves now proceed in parallel; the second
is §60.

## §60 (2026-07-27 late) — PCLL+¬◯⊥ (the infallible system): variable-free collapse, 1-variable UI, sound+complete semantics, search commands — ALL PROVED

New library modules LaxLogic/PLLNoFall.lean, PLLSearchNoFall.lean
(imported from LaxLogic.lean; manual §6; demo §6 pinned).  The system:
DerivUNoFall Γ φ := DerivU (¬◯⊥ :: Γ) φ — axiom = persistent
hypothesis, legitimate because every rule carries its context and the
deduction theorem holds.  Results, all sorry-free and guard-pinned
clean-classical:

  varfree_dichotomy   every variable-free A: ⊢ A or A ⊢ ⊥.  The
                      ◯⊥-ladder collapses to {⊥,⊤}; the axiom is used
                      ONCE (◯-case: ◯A ⊢ ◯⊥ ⊢ ⊥); distribution is
                      never used, so PLL+¬◯⊥ inherits the proof.
  exUI / allUI        strongest variable-free consequence and weakest
                      variable-free antecedent exist for EVERY φ
                      (⊤/⊥ by consistency resp. derivability) — for
                      1-variable φ these are ∃p.φ / ∀p.φ of the
                      1-variable language.  UI(1pv) for PCLL+¬◯⊥ is
                      SETTLED (positively, and trivially — the right
                      kind of trivial: the ladder was the problem).
  consistent          [propext] only, one-world infallible model.
  derivUNoFall_iff_infallible_valid
                      sound and COMPLETE for mutually confluent
                      infallible models — canonU relativised to the
                      proper primes containing ¬◯⊥ (obInv preserves
                      both properties: unit gives ◯¬◯⊥, and ◯⊥ + ¬◯⊥
                      is inconsistent; prime_extension re-used as-is,
                      properness free from avoiding a formula).  The
                      "take as read" model theory is now a theorem.
  pcll_not_nobot      the extension is proper (0 ⊳ fallible 1, pinned
                      by decide).

Search: infB (no fallible worlds) joins confB as the battery filter;
#searchNF / #refuteNF mirror #search / #refuteConf; certificate
theorems not_derivUNoFall_of_check ([propext, Quot.sound], checked
context is Γ alone — infallible models force the axiom) and
derivUNoFall_of_nd ([propext]).  Showcase guard: ◯⊥ ⊢ ⊥ is
PLL-REFUTED and NF-PROVED.

Scope kept precise: exUI/allUI interpolate against VARIABLE-FREE ψ
(the 1-variable language's p-free formulas).  Against p-free ψ over
additional variables the property is not asserted — that is the
≥2-variable theatre, where the 1-variable fragment (still infinite:
the Rieger–Nishimura lattice survives ¬◯⊥) becomes the target.

## §61 (2026-07-28) — UI for PCLL+¬◯⊥, stage 1: the ◯-normalisation engine, the IPC calibration, and the divergence separator

Matthew's directive: prove UI completely for PCLL+¬◯⊥, then adapt to
PLL+¬◯⊥; probe only when stuck.  Route chosen: SYNTACTIC (Pitts-style
computation over a terminating calculus).  The semantic
bisimulation-quantifier route would re-meet the fragment-infinitude
wall one variable up (the 1-variable target fragment of the ≥2-variable
problem is Rieger–Nishimura-infinite even under ¬◯⊥); the syntactic
technology is exactly what handles infinite target fragments (IPC).

Landed tonight (LaxLogic/PLLNoFallNF.lean, PLLNoFallSep.lean; all
guard-pinned, [propext, Quot.sound] or clean-classical):

  * EquivNF congruence kit; the lattice-homomorphism laws: ◯ commutes
    with ∧ (strong monad), ∨ (distribution — its single use), ⊥ (the
    axiom), and is idempotent.
  * nf : every formula is interderivable (nf_equiv) with a ◯-NORMAL
    form — ◯ only on atoms and implications (nf_normal); derivability
    invariant under normalisation (nf_iff).  The calculus and the
    interpolant computation need only speak normal forms; the ◯∨/◯⊥
    cases are compiled away.
  * derivUNoFall_iff_IPLND: the ◯-free fragment of PCLL+¬◯⊥ is EXACTLY
    IPC (erasure kills the axiom and the distribution instances;
    IPLND embeds back).  Calibration: full UI here CONTAINS Pitts'
    theorem for IPC; nothing cheaper closes it.
  * THE SEPARATOR (sep_derivable / sep_not_pll_nofall, both by decide):
    ◯(a⊃(b∨c)), ◯a ⊢ ◯b∨◯c is ◯-normal, PCLL+¬◯⊥-derivable, and NOT
    PLL+¬◯⊥-derivable (five-world infallible ∀∃-countermodel,
    necessarily non-confluent).  So distribution is NOT admissible
    from ¬◯⊥ even on normal forms: the PCLL+¬◯⊥ calculus needs a
    distribution-aware ◯-rule (laxL with conclusions in the
    ∨-closure of ◯-formulas and ⊥ — sound by confluence + Rm ⊆ Ri,
    derives distribution, and its ⊥-case carries the density power),
    while PLL+¬◯⊥ keeps G4iLL″'s laxL.  The two Pitts computations
    will differ exactly there.

LITERATURE (checked tonight): Iemhoff, Proof Theory for Lax Logic
(arXiv:2209.08976) claims UI for PLL via G4iLL; its completeness
(Corollary 1, via Thm 1 of arXiv:2011.11847) is REFUTED
machine-checked in this repo (PLLG4Gap.lean: ◯G', F' ⇒ r with
F' = ◯p⊃r, G' = F'⊃◯p — Howe duplication straddling the box-opening).
So the published UI-for-PLL proof has a gap at its completeness step,
and this programme would repair a published result, not merely fill a
silence.

NEXT (stage 2): the calculus.  For PCLL+¬◯⊥: G4iLL″ with the widened
laxL/impLLaxLax conclusions (◯-disjunctive targets incl. ⊥), stated on
◯-normal sequents; prove sound for DerivUNoFall and complete (target:
via the canonN semantics or by adapting the G4c equiv_nd chain);
establish the termination order.  For PLL+¬◯⊥: G4iLL″ + nobot as
persistent hypothesis (complete by equiv_nd already — only the
◯⊥-absurdity needs building in or keeping as the hypothesis).  Then
stage 3: the Pitts computation by induction on the termination order,
following the mechanised-UI blueprint (Férée–van der Giessen–van
Gool–Shillito's Coq development for IPC/K/GL).

## §62 (2026-07-28) — Stage 2 design fork resolved: the PICLL calculus must be multi-succedent; PILL needs no new calculus

Working the cut cases of the planned single-succedent calculus (G4iLL″
with laxL conclusions widened to disjunctions of ◯-formulas and ⊥) BEFORE
building it exposed a genuine incompleteness: cut on a laxL-produced
disjunction cannot be pushed below the widened rule (its goal restriction
blocks the left commutation), and the obstruction is realised by a
concrete sequent, now PINNED (PLLNoFallSep.lean):

  ◯(a⊃(b∨c)), ◯a, ◯b⊃p, ◯c⊃p ⊢ p
    PICLL-derivable (cutNeed_derivable — through ◯b∨◯c, i.e. a cut)
    PILL-underivable (cutNeed_not_pll — p-decorated five-world model).

In any cut-free single-succedent derivation the goal must commit to ◯b
or ◯c before the box opens, and the b∨c case split happens inside the
box: the other branch strands.  Conclusion: the PICLL calculus carries a
MULTI-SUCCEDENT ◯-rule — from Γ, X ⊢ ◯B₁,…,◯Bₖ infer
Γ, ◯X ⊢ ◯B₁,…,◯Bₖ, Δ (k = 0 gives the density power; the ◯-succedent
travels through implication eliminations together) — over an m-G4ip
core (invertible ∨R with both disjuncts in the succedent; ⊃R and the
implication-proving premises single-succedent).  Open design points,
deliberately not baked in tonight: whether the LaxLax repair (Howe
duplication) is still required in m-form, and the exact premise shapes
of the ⊃◯-left rules; both need the g4p-ladder analysis re-run against
the m-format.

PILL, by contrast, needs NO new calculus: no distribution, so G4iLL″ +
¬◯⊥ as permanently inhabited context is complete (equiv_nd), has
admissible cut (SelfAbsorb chain), and a terminating decider (G4sh.dec)
— and nobot is variable-free, so the inhabited context never interferes
with p-freeness in an interpolant computation.

SEQUENCING RECOMMENDATION (within Matthew's "up to you" licence on the
calculus handling): run the Pitts computation FIRST for PILL on the
existing complete machinery — every interpolant clause is a template
for the PICLL version — THEN build the m-chain (def/perm/weaken/inv/
ctr/cut/comp, patterned on PLLG4H*) and port the computation.  The
PICLL-first order at the calculus stage would mean building the ~2.5k
line m-chain before any UI content exists to test it against.

## §63 (2026-07-28) — Iemhoff's interpolant assignment transcribed; the adaptation obstacle identified: G4iLL″ is not ≪-reductive, so the recursion must run on the cumulative-set formulation

Fetched and read Iemhoff, Proof Theory for Lax Logic (arXiv:2209.08976;
PDF in the session scratchpad).  Her G4iLL (Fig. 2.3) = G4ip + R◯, L◯,
R◯→, L◯→ — all four in CONSUMING form (L◯: Γ,ψ ⇒ ◯φ / Γ,◯ψ ⇒ ◯φ
replaces the box by its opening; L◯→ premise 1 = Γ,◯χ ⇒ ◯φ drops both
ψ and the implication).  The repo's repair keeps the box (membership)
and keeps the implication in premise 1 — the gap sequent showed the
consuming forms incomplete.

Her UI method (§§6.3–6.7), the shape to adapt:
  * interpolant assignment ι: to each rule instance R with conclusion S,
    p-free-of-lower-rank formulas ι∃ᵖRS, ι∀ᵖRS; to non-principal
    occurrences ι∃ᵖR̄S, ι∀ᵖR̄S; ∀pS ↦ ∀⁺ ∨ ∀⁻ ∨ ∀ᵃᵗ, ∃pS ↦ ∃⁺ ∧ ∃⁻ ∧ ∃ᵃᵗ
    (∀ᵃᵗ/∃ᵃᵗ the atom clauses); rewrite relation ⟶ confluent + SN by
    reductivity (her Lemma 2 ← Iemhoff 2019b Lemma 3).
  * three interpolant properties (∀l), (∃r), (∀∃) over p-partitions
    (Sʳ, Sⁱ); six inductive properties per rule (IPP/IPN × ∀/∃, DPP,
    DPN) with the induction along ≺; Theorem 5: balanced calculus +
    sound assignment ⟹ UI.
  * the standard assignment for the ◯-rules (her §6.6):
      R◯, L◯:  ι∃ = ◯∃pS₁, ι∀ = ◯∀pS₁; non-principal ⊤/⊥.
      R◯→:     ι∃ = ∃pS₁ ∧ (∀pS₁ → ∃pS₂); ι∀ = ∀pS₁ ∧ ∀pS₂;
               non-principal ∃ = ⊤ or ∃p(Sᵃ ⇒); ∀ = ⊥.
      L◯→:     ι∃ = ◯∃pS₁ ∧ (◯∀pS₁ → ∃pS₂); ι∀ = ◯∀pS₁ ∧ ∀pS₂;
               non-principal via Sᵞ: for γ = ◯α→β ∈ Sᵃ,
               Sᵞ⁰ = (Sᵃ\{γ} ⇒ ◯α), Sᵞ¹ = (Sᵃ\{γ}, β ⇒ Sˢ);
               ∃-side ⋀ over boxed members and such γ; ∀-side
               ⋁ ◯∀pSᵞ⁰ ∧ ∀pSᵞ¹.
    Soundness = her Lemmas 3–6 (templates for ours).

THE OBSTACLE (found by checking her side conditions against G4iLL″):
her whole recursion lives on the reductive order ≺ built from the
Dershowitz–Manna weight order ≪, and rule premises must be ≪-BELOW
their conclusions.  The repo's REPAIRED rules are not: laxL and L◯→″
keep their principals (membership) and add the opening, so the premise
multiset properly grows — G4iLL″ terminates by the finite-space
loop-check (G4s, the cumulative set calculus of PLLG4Set/PLLG4Dec),
not by ≪-descent.  Consequently the interpolant recursion for PILL
must run on the CUMULATIVE-SET formulation: sequents = (set context,
goal) inside the finite closure space; the measure = the decider's own
(remaining-space, …) order; the lower-rank side conditions of the
assignment become later-in-that-well-order conditions.  This is the
principled divergence from Iemhoff — the same spot as the
completeness repair, as expected.

NEXT (stage 3 concrete): (1) recon PLLG4Set's G4s rules + the exact
decreasing measure of G4sh.dec; (2) define the interpolant pair over
G4s-space by well-founded recursion on that measure, clauses = her
table with the keeping-form adjustments (premise-1 of L◯→″ keeps the
implication: its ι-clauses take S₁ = (X :: Γ ⇒ ◯A) with the
implication still inside — check rank/space side conditions); (3) the
six properties per rule, her Lemmas 3–6 adapted; (4) assemble
UI(PILL); then the m-chain for PICLL.

## §64 (2026-07-28) — The interpolant recursion design for G4iLL″: fuel-indexed over the finite sequent space

G4s recon (PLLG4Set): fully cumulative Finset contexts, every rule
inserts-and-keeps, G4c.iff_setFin, decider G4sh.dec structural on
height.  Working Iemhoff's assignment against it:

THE PRECISE BREAKAGE of her static order: within a FIXED context the
backward rule graph of the keeping-form calculus can revisit sequents
(a laxL whose opening is already present is a literal self-loop;
impLImp/impLLaxLax instances whose insertions are present jump the
goal to an antecedent of a context member, and goal chains can cycle).
So no static rank ≺ exists with all premises below their conclusions,
and her rewrite ⟶ would diverge.  What remains true: G4sh premises
sit at strictly smaller HEIGHT, and a minimal-height derivation never
repeats a sequent along a branch (a repeat is a removable detour), so
every minimal derivation has branch length ≤ |seqEnumF|.

THE DESIGN, replacing the static rank: FUEL-INDEXED interpolants

  I∀, I∃ : Nat → Seq → Formula
  I(0, S)     := neutral (⊥ for the ∀-disjunction, ⊤ for ∃)
  I(n+1, S)   := Iemhoff's per-rule combination (her §6.6 table with
                 the keeping-form premise shapes) applied to
                 I(n, premise)s, over all rule instances with
                 conclusion S, plus the atom clauses

with ∀pS := I∀(N, S), ∃pS := I∃(N, S) at N := |seqEnumF| + 1.  The
big disjunctions/conjunctions are finite because instances-with-
conclusion-S range over the finite context and subformula data ✓.
The three interpolant properties are then proved by induction on
minimal derivation height, which is ≤ N along every branch, matching
the fuel: her six per-rule inductive properties (Lemmas 3–6) become
lemmas about I(n+1, S) vs I(n, ·) with the derivability hypotheses at
minimal height.  The self-loop/cycle instances contribute neutral
elements at fuel 0 and are harmless precisely because minimal
derivations never use them (the detour-removal lemma is the new
plumbing obligation, alongside fuel-monotonicity of the properties —
NOT of the formulas: no I(n) ≡ I(n+1) stability needed if the
properties are proved directly at fuel N).

Candidate simplification to examine first: can laxL consume its box
(≪-style) with only impLLaxLax in keeping form, preserving
completeness?  The gap analysis blamed only L◯→'s consumed
implication; if consuming-laxL + repaired-L◯→ is still complete, the
cycle sources shrink (though impLLaxLax premise-1 goal-jump remains,
so the fuel design is needed regardless).

NEXT SESSION (stage 3 build order): (1) Seq/space plumbing: reuse
seqEnumF; instance enumeration per conclusion; (2) I∀/I∃ by fuel
recursion (computable, so the searcher can TEST the interpolant
properties on concrete sequents before any proof — cheap sanity per
Matthew's probe discipline, since a failed property here would be a
counterexample, not a probe); (3) detour-removal + minimal-height
lemmas; (4) the six properties per rule (12 core rules from her G3ip
lemmas + 4 lax rules from Lemmas 3–6, keeping-form-adjusted); (5)
assemble (∀l), (∃r), (∀∃) and UI for PLL — with UI for PILL as the
nobot-context instance (nobot variable-free: p-freeness untouched).

## §65 (2026-07-28) — THE RECORD CORRECTED: the syntactic tower already exists (July 8–11), assembled to the crown with ONE open kernel; §64's "fresh design" re-derived its architecture

Matthew: "the syntactic route was tried in a different session, which
ended a week ago."  Confirmed, and the trace IS in the repo — in wip/,
outside the lakefile globs and outside PROGRESS.md (which postdates
it), which is how the §61–64 survey missed it.  My memory thread
recorded only its endpoint ("UI proof effort STOPPED 2026-07-12,
budget stop" and the descent-probe redirect) without the tower itself
— a memory failure, now fixed.

The tower (commits ≤ b32ee91, 2026-07-11, all ancestors of HEAD):

  LaxLogic/PLLG4UITrunc.lean  base: weight/atoms, G4c/G4s/G4sh + cut,
                              defect/mu measures, the TRUNCATED
                              QUANTIFIER TABLES itpE/itpA (fuel- and
                              budget-indexed), itp_pfree, itp_sound.
                              Axiom-clean.
  wip/absorb_base.lean        kcap budget + absorption/stabilisation
                              ladder (itp_stab_le); THE open kernel
                              cascade_low_pos (sorry) — the only
                              sorryAx entry.
  wip/adequacy.lean           PieceClosed spaces; Pitts (iv)
                              itp_adequate (sorry-free in itself).
  wip/indiff.lean             FUEL INDIFFERENCE proved: above mu the
                              quantifiers are syntactically equal
                              across fuels.  (The §64 worry about
                              cross-fuel mismatch was solved here.)
  wip/spaceindiff.lean        space indifference proved.
  wip/packaging.lean          existsP/forallP; Pitts (i)–(iii)
                              outright; (iv)+factorisation modulo
                              hFI/hSI.
  wip/final.lean              discharges hFI/hSI; the crown
                              uniform_interpolation_PLL, pinned:
                              [propext, sorryAx, Classical.choice,
                              Quot.sound], sorryAx via exactly
                              cascade_low_pos.

  95480dc: the box-free instance cascade_low_pos_boxfree PROVED ⟹
  **uniform interpolation for IPC, sorry-free**, inside this repo.

THE OPEN KERNEL, precisely (absorb_base.lean:2259,
cascade_low_pos_box): a low-BUDGET descent for the ◯-involving case —
from G4c Δ (itpE p S fuel (c+1) Γ) and G4c Δ (itpA p S fh (c+1) Γ g)
(fh ≤ fuel, 1 ≤ defect S Γ, defect·(|jumpGoals|+2) ≤ c) conclude
G4c Δ (itpA p S fuel c Γ g).  Its docstring records: zoo-tested TRUE
at every probed instance; the known decompositions all fail (chains
hit the (◯-goal, 0) false point; the E-mate fails at 1; continuations
cannot cross seals); the semantics' mechanism at c = 1 is syntactic
starvation (b-gated tables at saturated contexts collapse to ⊥); the
proposed proof plan = starvation-collapse lemmas + a (defect, budget)-
lex landing map meeting the pigeonhole band from below —
"cascade_main-scale work, not attempted".

THE UNIFIED HISTORY, now visible: the tower stalled on
cascade_low_pos (budget stop 2026-07-12) → its 1-variable case was
proved TRUE (3322f22) and "reduced to a single semantic-stabilisation
descent" → that descent became the SEMANTIC campaign (semui files,
layered/ranked pipeline) → which died at witness-realisability
(§59).  One wall, two clothings: the ◯-case descent.  Matthew's
skepticism was exactly right in shape; what he remembered as "the
syntactic route led nowhere" is more precisely "the syntactic route
reached ONE lemma, whose semantic reformulation then also stalled".

REVISED PLAN (supersedes §64's from-scratch build): resurrect the
tower (verify it compiles on v4.31; wire the build), then attack
cascade_low_pos_box ON it, in order:
  (1) the docstring's own plan (starvation-collapse + (defect,budget)-
      lex landing map) — the prior session's named next step, never
      attempted;
  (2) the post-July-12 assets against it: the ◯-normalisation engine
      (obAnd/obOb + PLL-valid laws thin the ◯-case combinatorics),
      canonN-style completeness thinking, and the PILL reading (nobot
      in Γ: does infallibility shrink the starvation analysis? —
      Matthew's original hope, now with a precise target);
  (3) only if (1)+(2) fail: the consuming-laxL redesign / Iemhoff-
      faithful sequent order, checking completeness of consuming-laxL
      + repaired-L◯→ first.
The probe discipline: cascade_low_pos_box is zoo-TRUE, so this is
proof work, not probing; probes only if a sub-lemma of (1) looks
unsatisfiable.

## §66 (2026-07-28) — The kernel campaign opens: floor starvation pinned as theorems (wip/starve.lean)

Translating the tower's vocabulary to standard language as mandated:
the "zoo" = the exhaustive finite nucleus-model battery
(wip/refute4.lean, 34 pairs); a "seal" = one of the four branch shapes
whose box/⊃-introduction blocks the descent's continuations;
"starvation" = a quantifier table's clause list becoming empty, so the
table is literally ⊥ (orAll [] = ⊥).

First bricks PROVED ([propext, Quot.sound], first-compile): at budget
0 a ◯-shaped goal's table loses its goal clause and truncation
disjunct (itpAgoal_obGoal_floor, itpAfull_obGoal_floor), so it
normalises to its environment clauses alone (itpA_obGoal_floor), and
an empty environment table collapses it to ⊥ literally
(itpA_starve_floor) — the battery's unique false point of the bare
low-band descent, now a theorem boundary.

Campaign continuation (the kernel's own unattempted plan, now with
its base): (1) classify starved states ABOVE the floor — which
(Γ, goal, b) have empty tables at b ≥ 1 (the b-gated families vanish;
environment guards are decidable memberships); (2) the
(defect, budget)-lexicographic landing map for the c = 1 base meeting
the pigeonhole band from below; (3) lift the battery's proved-free
laws: the fresh-antecedent equality E@(c+1)(Γ) ⊓ E@c(C₁::Γ) =
E@(c+1)(C₁::Γ) (exact on every battery instance) and the
piece-closed-S goal-membership invariant (kills the fresh-antecedent
seal for the adequacy consumer's closed spaces — recorded by the
prior session as usable for the CONSUMER'S instance even though the
∀S interface keeps the seal).  The mutual-pair scheme stays dead
below budget 2 (the existential ascent E@c ⊢ E@(c+1) is
countermodel-refuted at c = 1), so the landing map must be
single-sided — that is the mathematical heart of what remains.

## §67 (2026-07-28) — Matthew's check executed: wip/G4conf.lean's assumed metatheory REFUTED kernel-checked; the inconsistency unwound

The rule added to G4c for confluence exists: wip/G4conf.lean (branch
ui-confluence, design docs/confluent-ui-plan.md) defines G4cf = the 17
G4iLL″ rules + distL (analytic left rule: from ◯(A∨B) ∈ Γ branch to
◯A resp. ◯B), with soundness PROVED and — under stated licence — four
sorried claims: G4c ⊆ G4cf (true, routine), distF derivable (true,
routine), completeness for confluent validity, and cut admissibility.

VERDICT of the check (wip/g4confGap.lean, all [propext, Quot.sound],
first-compile): **completeness-without-cut is FALSE and hence cut is
NOT admissible** (granted the two routine lemmas).  Witness = the §62
cut-necessity sequent ◯(a⊃(b∨c)), ◯a, ◯b⊃p, ◯c⊃p ⊢ p:
  * derivU_gapSeq — PCLL derives it (pinned searcher term through the
    cut formula ◯b∨◯c); confluent-valid by derivU_sound;
  * g4hf_to_g4h — on sequents with no subformula of shape ◯(A∨B)
    (invariant NoObOr, preserved by all 18 rules; distL can never
    fire), G4cf collapses to G4c;
  * pll_not_gapSeq — PLL refutes the sequent (five-world ∀∃
    countermodel, decide);
  * g4cf_not_gapSeq, g4cf_complete_refuted — the conclusions.
G4conf.lean's two false statements are REMOVED and replaced by an
adjudication block; the two true sorried lemmas remain, annotated.
No Lean file imported the false claims (blast radius: two docs).

THE UNWOUND ACCOUNT (correcting §§62–65's narrative and yesterday's
"nothing exists for PCLL"): a single-succedent confluence-extended
calculus DID exist in the repo, with its completeness and cut assumed.
The §62 stranding analysis, found independently this session, is
precisely the refuter of those assumptions — the two threads now agree,
adjudicated by the kernel: for the distributing systems (PCLL, PICLL),
an analytic hypothesis-keyed distribution rule cannot give a cut-free
complete single-succedent calculus; the repair must carry ◯-disjunctions
across implication eliminations (multi-succedent ◯-rule, or an
elimination rule internalising the case split).  The PLL tower (§65) is
untouched: it never used distL, and PLL never derives such sequents.

## §68 (2026-07-28) — Seal analysis with fresh eyes: the E-ascent is avoidable at seals; box_absurd (the starved-seal engine) PROVED; the candidate landing measure

Reading the four seal call sites (absorb_base 2605/2634/3142/3361)
and the guarded/consumed campaign record produced three observations,
the first two banked as theorems, the third as the design to build:

1. **The E-ascent is NOT needed inside a seal.**  The recorded failure
   ("the E-mate genuinely fails low", zoo-refuted at c = 1) closes off
   the mutual-pair scheme — but inside a seal the entire outer context
   crosses the box (laxL retains contexts), so the outer ambient
   E@(c+1) is available INSIDE, and firing the opened source guard
   needs only the DOWNWARD E@(c+1) ⊢ E@c (budget monotonicity), never
   the ascent.  The seal's residual obligation is then the pair
   descent one budget down at the same Γ — the same statement with
   c − 1 — plus room bookkeeping.  So the low-band knot is purely the
   TERMINATION of same-Γ seal chains, not the E-mate.

2. **Starved seals close** (wip/starve.lean, PROVED, first-compile):
   box_absurd — a boxed guarded implication whose value slot is ⊥,
   with a derivable guard, yields ANY ◯-conclusion (open, fire,
   explode).  Plus itpA_starve_elimAtom: the eliminated atom's goal
   clause is empty at EVERY budget, so its table collapses to literal
   ⊥ whenever the environment table is empty — starvation is not only
   a floor phenomenon.  Together: any seal whose inner partner
   starves is dispatched outright.

3. **The candidate landing measure** (to formalise next): strengthen
   the descent statement so seals recurse into IT rather than around
   it, with the lexicographic measure
       (defect S Γ, budget, unvisited jump goals, goal weight):
   growth moves drop defect (defect_lt_of_mem) and reset everything;
   seal moves drop budget at fixed defect (same Γ) and reset the rest;
   fresh jump moves drop the unvisited count; repeat jumps must close
   by splice from the in-context recorded value (the one step whose
   DIRECTION must be checked against cascade_main's actual splice —
   itp_budget_mono_le's orientation decides whether the splice works
   below the pigeonhole band or needs the starvation classification to
   discharge the low-budget repeats); decomposition drops weight.
   The room hypothesis defect·(J+2) ≤ c funds exactly J+2 seal-burns
   per defect level, which the measure consumes as budget-drops at
   fixed defect — the arithmetic to verify is that goal repeats within
   a fixed (defect, Γ) band arrive within J+2 burns (the pigeonhole
   the prior session ran OUTSIDE seals, now run inside the recursion).

NEXT ACTIONS: read cascade_main's splice case (the exact direction of
itp_budget_mono_le at repeats) and the four call sites' room
arithmetic; then draft the strengthened statement and run its measure
against each of the 10 move classes on paper before any Lean.

## §69 (2026-07-28) — The kernel's state graph mapped; the two reduction targets T1/T2

Monotonicity directions CONFIRMED in the tower: itp_budget_mono_le is
the free pair (E downward: [E@b] ⊢ E@b' for b' ≤ b; A upward:
[A@b'] ⊢ A@b), proved outright; itp_stab_le is the hard pair (E-ascent
+ A-descent), proved only above kcap via the cascade.  cascade_main's
continuations take g'-values at the entry budget and any superset
context; its E-half carries room J+3+defect·(J+2) ≤ c — consistent
with the zoo's bare-ascent refutation at c = 1.

THE SEAL STATE GRAPH (same Γ, kernel(c) := [E@(c+1), A@(c+1)(Γ,g)] ⊢
A@c(Γ,g), all moves verified against the clause tables):
  * goal-γ seal (g = ◯D): commit target ◯(E@(c-1) ⇢ A@(c-1)(Γ,D));
    inside: fire the source guard with E@c from the ambient by
    DOWNWARD mono (no ascent!), then kernel(c-1) at goal D — the
    goal UNBOXES: weight strictly drops.
  * clause-γ seal (env ◯⊃-family member ◯A₁⊃B): inner goal ◯A₁ —
    weight resets, but heads range over the FIXED finite γ-head set;
    cycles possible (the zoo's chained-d2 IS the 2-cycle
    ◯p ⇄ ◯r via ◯p⊃r, ◯r⊃s) — budget burns along the cycle.
  * truncation seal: same state, budget ↓.
  * fresh-antecedent seal: outside-S piece; dead for piece-closed S
    (the consumer's case).
  * non-seal moves: growth (defect ↓, room replenishes by J+2),
    decomposition (weight ↓), jump family (cascade_main's own
    pigeonhole, unsealed).
Termination resources: unboxing (weight), defect drops, SOURCE-side
starvation (box_absurd dispatches any branch whose source inner value
is ⊥ — with the guard from ambient downward mono), and the open
residue: non-starving γ-head cycles above the floor, where repeats
yield nothing (values lift UP, obligations point DOWN) — the
one-step budget stabilisation at low budget, once more.

REDUCTION TARGETS (bounded, plausibly provable now):
  T1 (seal one-step reduction): IF kernel(c−1) holds for all goals at
     this Γ THEN the four sealed branches of kernel(c) close — the
     plumbing is: orAll-intro the corresponding target disjunct, laxR
     wait laxL-commit on the source box, fire the guard by ambient
     downward mono (itp_budget_mono_le.1), impR, invoke kernel(c−1).
     Lands kernel = downward induction on c with a single base at the
     band floor, replacing "all c in the band" by "the floor c₀".
  T2 (starvation dispatch): integrate box_absurd + the starve
     classification: every sealed branch whose source inner table is
     empty closes outright; with itpA_starve_floor / _elimAtom this
     kills the x = 0-adjacent layer and every saturated-state branch.
After T1+T2 the open content is exactly: the floor instance of the
descent at non-starving cycling states — a finitely-generated family
per (S, Γ) — to be attacked by per-shape stabilisation (the state
graph at fixed Γ is finite; the conjecture is that within one full
γ-head cycle every branch either starves, unboxes, or grows).

## §70 (2026-07-28) — Call-site verification corrects the state graph: only clause-γ seals burn budget

Reading the four cascade_low call sites in cascade_main against the
clause tables corrects §69: the goal-γ disjunct of table@b is
◯(E@(b−1) ⇢ A@b(Γ, D)) — the VALUE component stays at budget b (only
the guard drops), so the goal-γ seal recurses at the SAME budget with
the goal UNBOXED (weight strictly ↓; call site 2634: cascade_low at
c'+1, goal D).  Likewise the truncation seal's inner sits at budget b
(site 3361, same budget), and the fresh-antecedent seal (2605) keeps
the budget.  ONLY the clause-γ (jump-family) seal burns: its table
entry pairs components at b−1 (site 3142: cascade_low at c', goal
◯A₁).  Consequences:

* The budget-burning moves and the goal-cycling moves COINCIDE
  (clause-γ jumps into the finite γ-head set) — the open residue is
  exactly: chains of clause-γ jumps at fixed Γ, one budget per jump,
  goals in the finite head set; everything else terminates by weight
  (goal-γ, decomposition), defect (growth), or dispatches by
  starvation (T2, gamma_seal_starved).
* Room arithmetic: the ledger funds J+2 burns per defect level, and a
  clause-γ chain repeats a head within J+1 jumps — the pigeonhole
  DOES arrive within the funded window; what fails at a repeat is
  only the closing step (values lift UP, the slot points DOWN).  So
  the entire kernel now rests on the single question: WHAT CLOSES A
  CLAUSE-γ HEAD REPEAT AT FIXED Γ.  Candidates, in order: (a) the
  trunc disjunct of the repeat target (re-enter the table one level
  in, where the first visit's value is spliceable by A-upward mono);
  (b) starvation of the repeat target's own γ-clause (the pair
  E-component at the floor guard may starve the b-gated families
  within J steps of the floor); (c) the fresh-antecedent equality
  law (battery-exact, unproven) applied at the repeat guard.
  Next action: hand-execute the ◯p ⇄ ◯r 2-cycle (the zoo's
  chained-d2, S = {◯p⊃r, r, ◯r⊃s, s}) through the tables at c = 2, 1
  and read off WHICH candidate actually closes it in the zoo — the
  battery says something closes it; the table trace will show what.

## §71 (2026-07-28) — THE TRACE DECIDES: every kernel branch has a designated closing mechanism; the build plan

Computed the chained-d2 configuration's actual tables (scratch
trace2cycle: S = {◯p⊃r, r, ◯r⊃s, s}, Γ = [◯p⊃r], budgets 0–3):

  A(◯p)@0 = A(◯r)@0 = [] (⊥), E@0 = [] (⊤);
  A(◯p)@b = [goal-γ ◯, clause-γ ∧, clause-γ ∧, trunc ◯] for all b ≥ 1;
  at the grown context r :: Γ: A(◯p) = [goal-γ, trunc] — the clause-γ
  family DIES after its consequent lands (guard `B ∈ Γ`).

Three corrections to §70, upgrading fears to mechanisms:

1. **Clause-γ second components are growth-financed**: the ∧-pair's
   continuation component lives at B :: Γ where the firing clause is
   dead — each burn permanently grows Γ and pays DEFECT (B ∈ S).  The
   feared same-Γ head cycle across DIFFERENT clauses does not exist:
   consequent-landing kills the clause.
2. **The true burner is the self-loop**: the clause-γ boxed component
   references its own head one budget down at the same Γ
   (◯(E@(b−1) ⇢ A@(b−1)(Γ, ◯A₁)) inside A(Γ, ◯A₁)'s own table via
   the clause ◯A₁⊃B).  This chain is structurally decreasing in the
   budget alone and BOTTOMS AT FLOOR STARVATION: at budget 1 the
   source's component is ◯(E@0 ⇢ A@0) with A@0 = ⊥ literally — and
   gamma_seal_starved (T2, PROVED) dispatches the branch.  No
   pigeonhole, no seen-set, no room consumption beyond the budget
   itself: the recursion is plain downward induction on c.
3. **First components at atom goals** either hit the eliminated atom
   (itpA_starve_elimAtom ⟹ starved ⟹ their pair disjunct is
   ⊥-conjuncted, handled by orAll-elim's absurdity) or decompose by
   weight.

CLOSING-MECHANISM TABLE (kernel(c) branch → mechanism):
  goal decomposition   → weight ↓ (fuel induction as in the bf clone)
  growth disjuncts     → defect ↓ (strong induction, room resets)
  jump first-components→ atom/starve or weight ↓
  clause-γ seal        → budget ↓ structural; base = T2 at the floor
  goal-γ seal          → same budget, weight ↓ (unboxing)
  trunc seal           → same budget, one-level table strip (inner
                         induction on the disjunct list)
  fresh-antecedent     → piece-closed S: dead (goal-membership
                         invariant); ∀S form: the residual hbox case
  starved source       → T2 outright

BUILD PLAN: clone cascade_main_bf's skeleton (929–2071, the shifted
ledger) for the ◯-involving case with the (defect, budget, fuel,
weight)-lex replacing the pigeonhole: no seen-sets, no continuations —
the seals recurse structurally on the budget with T2 as the base.
Estimated at bf-scale (~1,100 lines).  The unknowns left are
detail-level (the trunc strip's bookkeeping; the exact orAll plumbing
at ∧-pair branches; the ∀S fresh-antecedent case, which may keep a
piece-closure hypothesis — acceptable: thread PieceClosed through, the
consumer has it).  If this build closes, cascade_low_pos_box falls,
and with it the crown's sorryAx — uniform_interpolation_PLL complete.

## §72 (2026-07-28) — Second hand-execution: the budget-1 trunc-escape and the growth-first ordering

Re-running the §71 design by hand through the tables surfaced two
load-bearing details:

1. **The budget-1 escape is the truncation target.**  At kernel(1) on
   the self-loop head, the clause-γ target's boxed component is
   ◯(E@0 ⇢ A@0) with A@0 starved — underivable, so that target must
   NOT be chosen.  The branch closes by choosing the truncation
   disjunct of the target table instead: ◯(E@0 ⇢ orAll(others@1)) —
   its inner is obtained from the source value by orAll-elim, where
   the source's own truncation disjunct unwraps by box_fire with the
   guard E@0 supplied by ambient downward monotonicity (E@2 → E@0),
   and the remaining source disjuncts map to their others@1
   counterparts (goal-γ by unboxing/weight; clause-γ by the grown
   second component/defect; growth by defect).
2. **Growth-first ordering.**  At unsaturated contexts with ungated
   members (∧/∨/atom-⊃), A@0 is NOT starved (growth clauses are
   never gated), so the floor-starvation base only exists at
   growth-exhausted states.  The induction must therefore run the
   defect strong induction OUTERMOST — growth branches discharge
   first, at every budget including 0 — and the γ/seal analysis runs
   only at growth-exhausted residues, where env@0 is gated-only,
   A@0(·, ◯-goal) = ⊥ literally, and T2 fires.  This matches the
   bf-clone's shifted-ledger skeleton exactly; the ◯-case adds the
   trunc-escape at 1 and T2 at 0.

kernel(0) remains false (the zoo's point) and is never needed: every
branch that would descend to it is closed at 1 by the trunc-escape or
dispatched by T2 before the descent.

BUILD: wip/cascadeBox.lean — cascade_main_bf's skeleton with
(defect, budget, fuel, weight)-lex; T2 (gamma_seal_starved) and the
starve lemmas as the floor bases; no seen-sets, no continuations.
On completion, replace cascade_low_pos_box's sorry with the new
theorem, rebuild the tower (final.lean), and re-audit the crown.

## §73 (2026-07-28) — Third hand-execution: floor_absurd identified; the frontier is ONE branch shape

Grinding the budget-1 layer by hand once more:

* **floor_absurd** (new provable target): with an ambient existential
  table in context, every budget-0 universal value at a ◯-goal is
  refutable —  [E@y(Γ)], A@0(Γ,◯D)-value ⊢ ⊥ — by defect strong
  induction: gated arms are dead at 0; ∧-growth disjuncts recurse at
  the grown context; ∨-growth pair-disjuncts fire against the
  ambient's own ∨-conjunct (orElim, then each implication fires on
  its branch); atom-⊃ and ⊃-family analogously.  This generalises T2
  from literal starvation to derivable absurdity and dispatches every
  branch whose SOURCE inner sits at budget 0.
* **The self-loop trunc-escape confirmed again** at head = goal.
* **THE ONE STUCK SHAPE**: kernel(1), clause-γ source branch, head
  ◯A₁ ≠ goal g, growth-live Γ.  The pair target's boxed component
  ◯(E@0 ⇢ A@0) is underivable (A@0 is refutable, not derivable); the
  trunc-escape's inner others@1(Γ, g) is not directly reachable from
  the pair (component-1 is at the wrong head; component-2 lives at
  the grown context).  The zoo says the statement is TRUE there
  (S = {◯p⊃r, r}, head ◯p, goal ◯r, c = 1 probed), so a route
  exists; candidates to adjudicate IN LEAN when the build reaches
  this branch: (i) at budget 1 with growth live, commute the GROWTH
  disjuncts of the TARGET first (derive others@1's growth disjunct
  outright from the pair via the grown-context kernel at smaller
  defect — the growth disjunct's implication-pair may absorb the
  head-mismatch since its consequent slot is at the grown context
  where the clause is dead); (ii) the fresh-antecedent equality law
  (battery-exact) at the guard.  This branch is the entire remaining
  mathematical uncertainty of the kernel.

ORDER OF BUILD (wip/cascadeBox.lean): 1. floor_absurd + the
generalised dispatch gamma_seal_absurd; 2. the skeleton clone with
(defect, budget, fuel, weight)-lex; 3. the stuck shape adjudicated in
place — if (i) closes it, the kernel falls; if not, the shape is a
sharply-stated sub-lemma for Matthew, with the zoo already vouching
for its truth.

## §74 (2026-07-28) — Correction: floor_absurd is FALSE as stated; the ◯χ-env branches are box-growth; the build adjudicates the stuck shape directly

Fourth hand-pass, working the would-be floor_absurd through every
env@0 arm: the ∧/∨/atom-⊃/⊃∧/⊃∨/⊃⊃/◯⊃-filterMap arms all refute
against the ambient (each has a matching ambient conjunct to fire,
with only FREE-direction monotonicities needed — a viable family of
lemmas if ever wanted).  But the ◯χ-env arm of a ◯-goal contributes
the BARE box disjunct ◯(E@0(χ::Γ) ⇢ A@0(χ::Γ, ◯D)) — and a box is
never refutable in PLL (⊥ is not a ◯-goal, laxL cannot open it; the
fallible-top semantics agrees).  So floor_absurd is false whenever Γ
has a live ◯χ-member, and it is STRUCK as a target.  Correspondingly:

* The ◯χ-env branches of the descent close as BOX-GROWTH: source
  ◯(E@c(χ::Γ) ⇢ A@c(χ::Γ,◯D)) maps to target
  ◯(E@(c−1)(χ::Γ) ⇢ A@(c−1)(χ::Γ,◯D)) inside the box by the free
  directions (guard: E downward mono; value: the kernel at the
  χ-GROWN context — defect ↓, strong induction).  No absurdity
  needed, no budget burned.
* A@0-valued SOURCES never arise in the descent (table@(c+1)'s gated
  components sit at c ≥ 1 whenever the kernel is invoked with c ≥ 1),
  so nothing needed floor_absurd after all; T2 (literal starvation)
  remains the floor base where it applies.
* The §73 stuck shape (kernel(1), clause-γ, head ≠ goal, growth-live)
  stands as the single open branch, to be adjudicated in the build
  with candidates (i)/(ii) of §73.

The lesson logged: every base lemma gets a hand-execution against ALL
table arms before Lean effort — two design corrections (§72, §74)
have each been caught this way at zero proof cost.

## §75 (2026-07-28) — The mining instrument, and the ◯-clone's skeleton delta

MINING: the stuck shape is adjudicable by derivation-mining — the
kernel instance at a concrete configuration is a sequent of computable
formulas, and the G4c searcher (complete for the calculus) either
finds its derivation (revealing the route for the build) or exhausts
(suspicion of falsity → probe-licensed).  Two configurations queued:
A (zoo-covered, growth-dead: S = {◯p⊃r, r}, Γ = [◯p⊃r], goal ◯r,
c: 2→1, fuel 2) and B (growth-LIVE: add u∨v to S and Γ — possibly
OUTSIDE the zoo's coverage, so B doubles as a falsity check on the
stuck shape).  Background run in progress (findBounded 300k).

THE ◯-CLONE DELTA against cascade_main_bf's skeleton (read at 929–):
the bf clone already carries the shifted ledger (≤ c + (J+2)), the
piece-closure hypotheses (hand/hor/himp), and — decisively — the
goal/context S-membership invariants (hgS, hΓS), which is exactly
what kills the fresh-antecedent seal.  The ◯-clone (cascade_main_box):
  * hypotheses: piece-closure extended by ◯-pieces (hsome : ◯A ∈ S →
    A ∈ S); NO box-freeness;
  * induction: (defect strong, BUDGET strong, fuel) — the added budget
    tier funds the clause-γ seal recursion (c → c−1) structurally;
  * seal branches: clause-γ → budget-tier recursion, T2 +
    trunc-escape at the floor; goal-γ → same-budget unbox (weight,
    inner fuel induction); trunc → strip induction on the disjunct
    list; ◯χ-env → box-growth (defect tier + free-direction remaps);
    fresh-antecedent → dead by hgS/hΓS;
  * everything else verbatim from the bf clone (growth, jump
    pigeonhole, decomposition, the hambL lowered-ambient helper).
On completion: cascade_low_pos_box for piece-closed S := the clone's
entry; the ∀S residue keeps the hbox split (consumer unaffected);
rebuild the tower; re-audit the crown.

## §76 (2026-07-28) — Adjudication: mining infeasible (as the prior session warned), semantic zoo extended to growth-live — ZERO failures; build is GO

Config A's derivation-mining exhausted its 300k-node budget with no
verdict (weights 113/397/170) — consistent with the prior session's
HANDOFF warning that direct proof search on kernel instances is
infeasible and the zoo is the effective adjudicator.  So the zoo it
is: rebuilt the 7-algebra nucleus harness (v3probe2's AlgModel) over
the REAL itpE/itpA tables and checked the kernel entailment
  E@(c+1) ∧ A@(c+1)(Γ, ◯r)  ≤  A@c(Γ, ◯r)
pointwise over every algebra and valuation:
  config A (zoo-covered, growth-dead), c: 2→1:      0 failures
  config B (growth-LIVE, u∨v ∈ Γ — NEW coverage), c: 2→1: 0 failures
  config B, c: 3→2:                                  0 failures
The §73 stuck shape is zoo-true including the growth-live band the
original battery never probed.  No falsity suspicion remains anywhere
in the kernel; under the probe rule this closes the licensed probe and
returns the campaign to proof work.

BUILD ORDER (mandate-compliant, no sorried scaffolding): land the
branch-mechanism lemmas standalone, then assemble the clone:
  1. wksub — general subset-weakening for G4c (replicate absorb_base's
     private weaken_sub through the set calculus);
  2. box_remap_free — the free-directions box remap
     (dBox : ◯(E ⇢ A), guard conversion in context, value conversion
     in context ⟹ ◯(E′ ⇢ A′)) — closes the ◯χ box-growth branches and
     the clause-γ seal plumbing in one shape;
  3. the trunc-strip lemma; 4. the assembled clone per §75.

## §77 (2026-07-28) — Fifth correction: no truncation strip at non-◯ goals; truncations PAIR across the descent; the inner statement is the others-descent

Writing trunc_strip exposed its impossibility: unwrapping the source's
truncation box needs a ◯-conclusion for laxL, and the strip's
conclusion orAll(others) is not ◯-shaped — the seal restriction, one
level in.  The correct organisation, verified by hand at the elim:
the descent pairs trunc-to-trunc — the source-trunc branch commits the
TARGET truncation ◯(E@(c−1) ⇢ others@c) (a ◯-goal), opens the source
box inside it, and the residual obligation is the OTHERS-DESCENT
  [E-ambient, others@(c+1)-value] ⊢ orAll(others@c)
with no truncation on either side.  Consequences: (a) trunc_strip is
STRUCK; (b) the clone's inner statement is the others-descent (strip-
free tables both sides), with the full-table kernel as a two-branch
wrapper (trunc↦trunc, others↦others); (c) box_open (public box_fire)
PROVED and landed — the guard-fire step for every ◯-goal branch.

Five hand-caught corrections now (§§72, 74, 77 design; §71 upgrades);
the build's inner loop is the others-descent with: growth (defect),
box-growth ◯χ (defect, box_remap_free), goal-γ (unbox, weight),
clause-γ (budget tier + box_remap_free; floor by T2), jump family
(pigeonhole as in bf), decomposition (weight), atoms (starve/init).

## §78 (2026-07-28) — THE BUILD LANDS: wip/cascadeBox.lean — the others-descent ASSEMBLED sorry-free; the open content is exactly THREE interface Props (four stubs)

The §§71–77 design is now a compiled file (wip/cascadeBox.lean, 1,643
lines, four granular commits).  Structure and status:

* `desc_of_oth` — the §77 two-branch wrapper PROVED: source-trunc
  commits the TARGET truncation (present since the target others-table
  of a ◯-goal at budget ≥ 1 is nonempty by its goal clause — rfl),
  opens the source box with the guard fired from the ambient by
  downward monotonicity, and finishes by the inner others-descent;
  undecorated disjuncts route through the others-descent directly.
* `oth_descent` — THE ASSEMBLY, SORRY-FREE, pinned
  [propext, Classical.choice, Quot.sound]: (defect strong, budget
  strong, fuel structural) lexicographic induction.  Fuel-0 base
  closes outright (fuel-0 components are literally ⊥/⊤: explosion,
  guard-fire into ⊥, box_absurd against a committed ◯-target).  Step
  mechanisms, all landed as designed: decomposition and present-⊃
  goals by the fuel tier through the wrapper; growth arms by the
  defect tier with the ambient re-supplied from its own matching
  conjunct; goal-γ by same-budget box_remap_free with the value slot
  descending at the unboxed goal (hsome pays the S-membership); the
  ◯χ-env arm and the ◯x-driven γ-pairs by OPENING THE AMBIENT'S OWN
  BARE ◯-CONJUNCT against the committed target box, then
  box_remap_free with the defect tier at the grown context (no ascent
  anywhere — §74's box-growth, mechanised); gated γ/jump pairs at
  c ≥ 2 by the budget tier, their second components defect-financed
  with the grown ambient unlocked by firing the ambient's own clause
  conjunct with the FREE-direction fuel lift of the in-context first
  component (imp_fuel_lift / box_fuel_lift — new glue).
* `cascade_box` — the kernel entry in cascade_low_pos_box's shape
  (piece-closed S, goal/context in S, 1 ≤ c), sorry-free conditional
  on the three interfaces; `cascade_box_unconditional` consumes the
  stubs, taint pinned by guard to exactly [.., sorryAx, ..].

THE OPEN CONTENT (three Props, stubs clearly marked OPEN at EOF):
  1. AmbGuardAscent — the fresh-antecedent equality law (§66):
     E@(c+1)(Γ), E@c(X::Γ) ⊢ E@(c+1)(X::Γ) at a fresh space piece X.
     Consumed by ∨-growth, fresh-⊃-goal, fresh-jump first components
     — at EVERY budget: the build has no E-half, and the bf clone's
     E-ascent was room-funded, which the seal recursion breaks.  This
     surfaced as a BUILD finding: the growth mechanisms close without
     any ascent only for the ∧/atom-⊃/⊃∧/⊃∨/◯-arms; the three
     PAIRED-implication arms need exactly this law.
  2. GammaPairFloorA / GammaPairFloorBox — the §73 stuck shape at
     kernel(1) (gated γ-pair, target components at budget 0), stated
     branch-level with the defect-tier IH as a slot (the resource
     §73(i)'s target-growth commutation would consume).
  3. JumpPairFloor — the jump-family instance of the same floor
     (the seen-set pigeonhole cannot cross this build's boxed
     branches, as recorded since the July session).
Battery status of all three: true on every probed instance (§66 exact;
§76 zero failures incl. growth-live).  Next actions, in order: (a)
prove AmbGuardAscent as a fourth induction component (one-step ascent
at strictly smaller defect; its gated arms take the budget tier; its
floor lands in the same §73 shape — so (b) likely gates it); (b) the
§73 adjudication proper at the floor stubs, growth-first (at
growth-dead states the source pair components starve and dispatch —
itpA_starve_floor + box_absurd — so only growth-live states carry
content, exactly §73's residue).  On completion: wire
cascade_low_pos_box := cascade_box's entry (the ∀S form keeps the
piece-closure hypotheses; the adequacy consumer has them), rebuild
final.lean, re-audit the crown.

## §79 (2026-07-28, Opus) — Recovery + TWO KERNEL-CHECKED REFUTATIONS: the room-free reformulation is false; the tower's kernel survives; §71's "no room needed" is withdrawn

RECOVERY (Fable's session ended at its model limit): the others-descent
build is merged into ui-confluence (b0a1e81), wired into wipshared, and
compiles in the main tree — 4 sorries, all the marked interface stubs,
every #guard_msgs audit passing, oth_descent and cascade_box carrying
[propext, Classical.choice, Quot.sound] with NO sorryAx.

Then the interfaces were adjudicated — never done before — with two
refutations, both certified (wip/ascRefute.lean, [propext, Quot.sound],
choice-free, two-world infallible countermodels found by the battery):

1. **AmbGuardAscent is FALSE** (not_ambGuardAscent).  With
   S = {◯p⊃r, r, ◯r⊃s, s}, Γ = [◯p⊃r], fresh piece X = ◯r⊃s, budget 1:
   the ambient at Γ cannot finance the one-step existential ascent at
   X::Γ.  MECHANISM: a fresh piece of shape ◯A⊃B introduces a NEW
   budget-gated conjunct at the grown context; raising it from budget c
   to c+1 requires descending the universal table from c to c−1 — the
   kernel itself, one budget lower.  Stable at fuels 3,4,5; clean at
   budget ≥ 2.  CORRECTION TO THE RECORD: the July session's Z5 verdict
   ("the fresh-antecedent seal's law is semantically FREE, EQUALITY on
   the zoo at every probed instance") is WRONG — its probe family
   (C₁ ∈ {u, u⊃r, ◯u}) contains no ⊃◯-shaped piece, which is exactly
   where the law fails.
2. **The room-free descent is FALSE** (not_roomFreeDescent).  Same
   mechanism reaching the descent itself: with a goal whose antecedent
   is a ⊃◯-clause (g = (◯r⊃s)⊃t), the descent fails at budget 1.
   Fuel-stable (4,5,6 identical), clean at budget ≥ 2.

WHAT THIS DOES AND DOES NOT TOUCH:
* The tower's kernel `cascade_low_pos_box` is NOT refuted.  It carries
  the room hypothesis defect·(J+2) ≤ c, and both refuting instances need
  room 56 resp. 12 against budget 1 — vacuous there.  Indeed with
  1 ≤ defect the hypothesis forces c ≥ J+2 ≥ 2, so the kernel never
  operates at budget 1 with positive defect.
* `oth_descent`/`cascade_box` survive as CONDITIONAL theorems, but their
  four interfaces are jointly unsatisfiable, so they can never be
  discharged; `cascade_box_unconditional` must not be quoted as evidence.
* §71's central design conclusion — "no pigeonhole, no seen-set, no room
  consumption beyond the budget itself: the recursion is plain downward
  induction on c" — is WITHDRAWN.  The room ledger is load-bearing, and
  the two refutations are exactly the price of dropping it.

WHAT SURVIVES AND IS REUSABLE: the proved toolkit (wip/starve.lean:
floor starvation, box_absurd, gamma_seal_starved, wksub, box_open,
box_remap_free) and, from wip/cascadeBox.lean, the trunc-pairing wrapper
desc_of_oth, the fuel-0 base, and the branch mechanisms for growth,
box-growth (◯χ), goal-γ unboxing and decomposition — none of which used
the false interfaces.  Only the three implication-textured arms
(∨-growth, fresh-⊃-goal, jump/γ pairs) consumed them.

NEXT: rebuild the ◯-clone WITH the room hypothesis threaded (the shifted
ledger of cascade_main_bf), reusing the surviving mechanisms; the open
question returns to its sharpest form — whether the seen-set pigeonhole
can be carried across box introductions, now equipped with box_remap_free
and the trunc-pairing reformulation, which the July session lacked.

## §80 (2026-07-28, Opus) — The falsity boundary located exactly: budget 1, goals with a ⊃◯ ANTECEDENT; everything else survives

Systematic probing of the two refutations' neighbourhood (four spaces,
fuels 4–7, budgets 1–3, ⊃◯-clauses, shared consequents, growth-live
contexts, jump families) locates the boundary precisely:

  * **c ≥ 2: no failure anywhere probed.**  Every configuration that
    fails at budget 1 is clean at budget 2 and 3, at every fuel.
  * **c = 1: fails exactly when the goal is an implication whose
    ANTECEDENT is a ⊃◯-clause** (goal `(◯r⊃s)⊃t`: 3–9 failures).
    Contrast, same space and budget: goal `◯r⊃s` — a ⊃◯-clause as the
    goal itself, which is what jump branches generate — 0 failures;
    goals `r`, `◯r`, `◯s`, `t` — 0 failures; and the doubly-nested
    `((◯r⊃s)⊃t)⊃u`, whose antecedent is a ⊃⊃-clause — 0 failures.
    So the requirement does NOT grow with nesting depth.
  * **Raising the ambient does not help**: at the failing goal the
    descent fails identically with ambient at budgets 2, 3, 4, 5.  The
    obstruction is intrinsic to the target table, not a financing gap.

MECHANISM: the goal clause of `C₁ ⊃ C₂` is guarded by `E@c(C₁::Γ)`.
When `C₁` is a ⊃◯-clause, growing the context by it introduces a fresh
budget-gated conjunct in the existential table; at budget 1 that
conjunct's pair components sit at budget 0, where they are strictly
weaker than the source's at budget 1 — and the ambient at the ungrown
context, at any budget, says nothing about a clause it does not contain.

CONSEQUENCE FOR THE REBUILD: the corrected target is the descent at
`2 ≤ c` (uniform, no room), plus the budget-1 case restricted to goals
that are not ⊃◯-antecedent implications.  The recursion's own sub-goals
are safe at budget 1 — γ-heads are `A`/`◯A`, jump goals are `A⊃B` in
GOAL position — so the ledger's remaining job is only to keep
⊃◯-antecedent goals away from budget 1, which is a far weaker demand
than the defect·(J+2) tower.  This is the sharpest form the low-budget
question has taken; it replaces "prove the kernel" by "prove the
descent for c ≥ 2, and for c = 1 at safe goals".

## §81 (2026-07-29, Opus) — Matthew's correction: the budget must be MEASURED, not guessed; extraction instruments landed (wip/budgetfit.lean, wip/descent2.lean)

Matthew's three points, and what was done about each.

### (1) "How do you know your budgeting is accurate?"

Answer: I did not.  Three statements of the same lemma have carried
three different budget hypotheses, each chosen by hand and then defended
by probing around its edges:

| statement | budget hypothesis | how it was chosen |
|---|---|---|
| `cascade_low_pos_box` | `defect S Γ * (\|jumpGoals S\| + 2) ≤ c` | pigeonhole over-estimate: `J+1` jumps before a γ-head repeats, `+1` slack, once per defect level |
| `RoomFreeDescent` | `1 ≤ c` | conjectured from a probe family that could not see the budget (see (3)) |
| "the corrected target" | `2 ≤ c` | read off the boundary sweep of §80 — still a guess |

Matthew's proposal — keep the budget flexible until the required
function is discovered — is the constraint-extraction discipline the
repo already implements for timing (`LaxLogic/PLLConstraints.lean`,
after Mendler's *proofs-as-delays*: `◯` as a writer monad over the
delay algebra `(ℕ, 0, +, max)`, the constraint computed by the kernel
from the proof term rather than supplied to it).  Adopted, in two
halves.

**Half A — the budget as a parameter (`wip/descent2.lean`).**
`Need := Finset PLLFormula → List PLLFormula → PLLFormula → Nat` is
abstract; `Descends p need` is the target; the proof's branches will
deposit the laws `need` must satisfy instead of consuming an assumed
inequality.  Two things are already machine-checked, both
`[propext, Quot.sound]` (choice-free):

* `refutation_lower_bound` — **any** `need` supporting the descent has
  `2 ≤ need Sk Gk gk`.  This turns the §79 countermodel from a fact
  about one bespoke `Prop` into a constraint on the unknown function.
* `candidate_excluded` — the screen.  A proposed law is now tested by
  the kernel before any effort is spent on it: `needConst2` and
  `needGate` survive (`needConst2_survives`, `needGate_survives`,
  both by `decide`).

The arithmetic is worth recording plainly: at the refuting
configuration the tower's assumed law evaluates to
`needProduct Sk Gk gk = 56`, against a certified requirement of `2`.
The slack is not free — `kcap S = (2\|S\|+4)(\|S\|+2)` is what the
*caller* must climb to (`kcap_room`), i.e. 242 for that 9-piece space.
An over-estimated budget makes the lemma easier to state and the
stabilisation ladder harder to pay for.

**Half B — measurement (`wip/budgetfit.lean`, exe `budgetfit`).**
Threshold measurement over families of budget-gated pieces of growing
length, countermodel-first (the battery is a polynomial model check and
its hits are `checkB`-certified; proof search on these sequents is the
expensive half and runs only as a spot-check).

Measured, goal = the ⊃◯-antecedent implication, two fuels each,
identical at both:

| family | \|S\| | defect | \|jumpGoals\| | gated pieces | PRODUCT law | certified failures | threshold |
|---|---|---|---|---|---|---|---|
| chain1 | 7 | 6 | 3 | 2 | 30 | c ≤ 0 | 1 |
| chain2 | 10 | 9 | 5 | 3 | 63 | c ≤ 1 | 2 |
| chain3 | 13 | 12 | 7 | 4 | 108 | c ≤ 1 | 2 |

chain1 is the degenerate control: its goal's antecedent is already the
context formula, and it does not reproduce the failure — the failure
needs the antecedent to be a gated piece **not yet in Γ**.

The reading: the certified failure region is `c ≤ 1` and **does not
grow** with defect (6→12), with `\|jumpGoals\|` (3→7), with the gate
count (2→4), or with the product law (30→108).  `need = 2` is
consistent with every measurement; the product law sits two orders of
magnitude above the only certified lower bound.  Stated carefully: the
failures are certified, the clean cells are battery-clean (evidence,
not proof), so what is established is that **no probed growth of the
space moves the failure boundary**.

Safe goals, same families: an atom goal is derivable at *every* budget
including `c = 0`; a `◯` goal fails only at `c = 0`.  Consistent with
§80's boundary.

### (2) Which system — headline, and the jargon retired

`G4c` (= `∃n, G4h n`, `LaxLogic/PLLG4H.lean:97`) is the repaired
G4iLL″ for **plain PLL**, proved equivalent to natural deduction
(`equiv_nd`, `LaxLogic/PLLG4HComp.lean:109`).  So:

* **Route 1, syntactic tower → UI for PLL.**  Crown
  `uniform_interpolation_PLL` (`wip/final.lean:173`), general in `φ`,
  `C`, one eliminated variable.  Assembled; every layer axiom-clean;
  exactly one `sorry`, `cascade_low_pos_box`.  *This is where the
  rebuild is.*
* **Route 2, semantic → UI for PCLL** (`DerivU` = PLL + distribution;
  `MutuallyConfluent` models).  Pillar 1 proved; pillar 2 down to the
  m-clauses; witness-realisability refuted (§59).
* **Route 3, PICLL = PCLL + ¬◯⊥.**  Variable-free collapse, 1-variable
  UI, sound+complete infallible semantics, ◯-normal form, the
  IPC calibration and the distribution separator — all proved (§§60–61).

Internal vocabulary replaced by what it names:

| retired | means |
|---|---|
| growth branch | context-extension clause: `Γ` absorbs a space formula, `defect` strictly drops |
| box-growth | context extension *under* `◯` (the `◯χ ∈ Γ` clause, recursing at `χ :: Γ` inside `◯(−)`) |
| goal-γ | goal-decomposition clause: the disjunct generated by the shape of the goal `C` (`itpAgoal`) rather than by a context formula |
| decomposition | the same family, for `∧`/`∨`/`⊃` goals |
| seal | boxed-implication branch: the clause emits `◯(E ⇢ A)`, so the continuation is inside a box |
| starvation | empty clause list, so the table is literally `⊥` (`orAll [] = falsePLL`) |
| fresh-antecedent law | `E@(c+1)(Γ) ⊓ E@c(X::Γ) = E@(c+1)(X::Γ)` for `X ∈ S \ Γ`; `⊒` is free, `⊑` is `AmbGuardAscent` — **refuted** (§79) |

### (3) How the probe family is chosen — the process, and its repair

What went wrong is diagnosable and was diagnosed: the July family was
chosen by analogy with the *property under test* (freshness), not with
the *resource the law is about* (the budget).  `itpE`/`itpA` read `b` at
exactly two clause branches, driven by a formula of shape `(A⊃B)⊃D` or
`◯A⊃B`.  The family `{u, u⊃r, ◯u}` contains neither, so every instance
of it had the same value at every budget, and "equality on every probed
instance" was vacuous.

Repaired mechanically, in two orders:

* **Shape coverage** (`coverTags`, `missingTags`, `budgetBlind`).  The
  eleven clause branches are enumerated from the definition's case
  split; a family is *budget-blind* when it reaches neither gated
  branch.  Run on the July family: `BUDGET-BLIND = true`, misses
  8 of 11 branches.  Rule adopted: no claim about a budget law is
  recorded from a budget-blind family, and the coverage report is
  printed before the sweep.
* **Guard reachability** (`gateLive`).  Shape coverage is necessary, not
  sufficient: each gated branch also carries guard conditions, and the
  tables iterate over the **context**, not the space.  The `⊃⊃` family
  of §4 covers the shape and shows no failure at any budget — because
  its gate is never reached (`(A⊃B)⊃D` needs `B⊃D ∈ Γ`, which the
  family does not supply).  A dead gate is as uninformative as a blind
  family and much harder to spot by eye, so `gateLive` reports it per
  context formula.

### Status

`wip/descent2.lean` and `wip/budgetfit.lean` build; the descent2 audits
are choice-free.  The rebuild proceeds against `Descends p need` with
`need` open — `2 ≤ c` is recorded as the currently-best-supported
instantiation, not as the statement.

### §81 addendum — the skipped cells filled in; the two gates behave differently

`WEIGHT_CAP` had forced `c ≥ 2` to be skipped on the larger chains,
which is exactly where the question lives.  Re-run battery-only (the
positive stage cut to a token spot-check, so the polynomial model check
can reach weight-148,000 targets):

| family | \|S\| | defect | \|jumpGoals\| | PRODUCT law | certified failures | clean from |
|---|---|---|---|---|---|---|
| chain2 | 10 | 9 | 5 | 63 | c ≤ 1 | c = 2 |
| chain3 | 13 | 12 | 7 | 108 | c ≤ 1 | c = 2 |
| chain4 | 16 | 15 | 9 | 165 | c ≤ 1 | c = 2 |

The failure boundary is **fixed at c ≤ 1** while the space triples, the
defect goes 9 → 15, `|jumpGoals|` goes 5 → 9 and the assumed law goes
63 → 165.  Nothing in the measurement grows.  (Failures certified;
clean cells battery-clean.)

**The two gates are not alike.**  With its guard repaired — `B ⊃ D` put
into the context, which `gateLive` now confirms — the `⊃⊃` family fails
at `c = 0` and is clean from `c = 1` up: threshold **1**, against the
`◯⊃` gate's **2**.  Before the repair the same family showed no failure
at any budget, purely because its gate was dead.  So the extra budget
level is specifically the cost of the `◯A ⊃ B` clause, whose gated
sub-branch emits *two* paired conjuncts (the `◯`-guarded one included)
where the `⊃⊃` clause emits one.

`chainII2`'s gate is still dead (`gateLive = false`: the repair supplied
the last link's guard, not the first), so that row remains
uninformative and is not counted above.

### §81 addendum 2 — scope of the two refutations: NOT PLL-only

Prompted by the discovery-toolkit session's PLL/PCLL scope line (branch
`discovery-toolkit`, PR fairflow#11, unmerged): a countermodel to a
`G4c` sequent refutes PLL, and refutes PCLL only if it is mutually
confluent.  `RNC.confB` is already available here, so the question can
be settled without merging anything.

Both refuting models of §79 are **mutually confluent and infallible**
(`Mr_confluent`, `Mr_infallible`, `Mk_confluent`, `Mk_infallible` in
`wip/ascRefute.lean`, all by `decide`, `[propext, Quot.sound]` or
axiom-free).  They were built by hand for the PLL statements, so this
was not designed in.

Consequence: `AmbGuardAscent` and the room-free descent are false over
the mutually confluent infallible models too.  **The budget wall is not
an artefact of fallible worlds, nor of the missing distribution scheme**
— it survives into PCLL, PILL and PICLL alike.  That also means the
budget question cannot be dodged by moving to the infallible system,
which had been one of the standing hopes.

Nothing else in the toolkit branch bears on §81's numbers:
`wip/budgetfit.lean` reads only the verdict constructor and pins no
model shape, so the new simplifier (which shrinks returned models,
`checkB`-gated at every deletion) cannot move any cell of the tables.

## §82 (2026-07-29, Opus) — discovery-toolkit merged; the rebuild's TOP LEVEL proved, and the first extracted law screens out a candidate

### The merge

`discovery-toolkit` (PR fairflow#11) merged into `ui-confluence` at
Matthew's instruction.  Three conflicts, all in documentation, all
resolved by keeping both sides: the toolkit's §6 *Pictures* (`#draw`,
SVG/TikZ) and this branch's §6 *PCLL + ¬◯⊥* both wanted the same number,
so the latter is renumbered §7 and the tail bumped (§8 command-line
tools, §9 failure modes) in both `docs/search-manual.md` and
`LaxLogic/PLLSearchDemo.lean`.  The demo's remaining plain `#guard_msgs`
wrappers became `#guard_msgs_show`, matching the file's own prose and
making the whole tour visible in the info view.

One pinned output needed updating: `#refute` now prints a `scope` line.
Notably it was only *one* — the new countermodel simplifier did not
shrink any model this branch had pinned, because those were already
minimal.  `LaxLogic`, `wipshared` and `budgetfit` all build; the audits
of §§79–81 are unchanged.

### The rebuild: top level PROVED

`desc_of_oth` (the truncation-pairing wrapper of `wip/cascadeBox.lean`)
never touched the four refuted interfaces, so it is reused verbatim; it
and `desc_zero` are now public.  In `wip/descent2.lean`:

    OthDescends p need   -- the others-descent, budget abstract
    NeedFloor1 need := ∀ S Γ g, 1 ≤ need S Γ g

    descends_of_othDescends :
      NeedFloor1 need → OthDescends p need → Descends p need

PROVED, sorry-free, `[propext, Classical.choice, Quot.sound]`.  So the
whole rebuild now reduces to `OthDescends`, **for any budget law
satisfying one inequality**.  Nothing above that line is specific to
`2 ≤ c`: the budget enters only through `NeedFloor1`, so revising the
law costs no rework at this level.  That is the payoff of parametrising
rather than fixing the constant.

### The first extracted law, and what it kills

`NeedFloor1` is not assumed; it is what this branch *demanded* when run
against an abstract `need`.  Running the two surviving candidates
against it:

* `needConst2` satisfies it (`needConst2_floor1`);
* `needGate` **does not** (`needGate_not_floor1`): on a space with no
  budget-gated pieces it asks for nothing, but the truncation-pairing
  branch needs a floor of one whatever the space looks like.

So candidate B is eliminated — by the *proof's* demand, not by the data.
No countermodel could have produced this: it is a statement about all
spaces, including the degenerate ones the probe families never contain.
That is the extraction doing work the measurement cannot, and the two
sides now bracket `need` from opposite directions: measurement gives
lower bounds at concrete configurations, the proof gives laws over all
of them.

### Next

`OthDescends` is the whole remaining content.  Its branches will deposit
further laws; the budget is the supremum of those and of the measured
lower bounds, computed when the last branch lands.

## §83 — the budget tier of the descent has no base case (30 July)

`wip/floorRefute.lean`, PROVED sorry-free, `[propext, Quot.sound]`.

### The descent to budget `0` is FALSE

    not_floorDescent : ¬ FloorDescent "p" Sz

at the piece-closed configuration

    Sz = {◯(⊥⊃⊥), ⊥⊃⊥, ⊥},   Γ = [],   g = ◯(⊥⊃⊥) ∈ Sz,

where `FloorDescent p S` is the descent at target budget `0` carrying every
side condition the `oth_descent` interfaces carry (goal in the space,
context inside the space, head fuel below target fuel) — so refuting it
refutes every weakening.

The refutation needs **no countermodel search**.  The target table is
*literally* `⊥`: at the empty context the environment table is empty, and at
budget `0` both the `◯`-goal clause and the truncation disjunct are gated
off, so `itpA_starve_floor` (already in `wip/starve.lean`) applies.  The only
semantic input is that the two hypotheses are jointly consistent, which the
one-world model settles.

### Why this closes off the `cascadeBox` architecture

`oth_descent` is a three-tier induction: strong on the defect, strong on the
budget `c` (carrying `1 ≤ c`), structural on the source fuel.  Its three
floor interfaces (`GammaPairFloorA`, `GammaPairFloorBox`, `JumpPairFloor`)
exist because the *budget* tier has no recursive call at `c = 1`: a
budget-gated environment clause of the target table at budget `c` puts its
first component at `c − 1`, so that branch needs the descent at `(c → c−1)`,
which at `c = 1` is the descent to budget `0`.

Both bottom rungs are now refuted — target budget `0` here, target budget
`1` in `wip/ascRefute.lean` §2.  So **raising the floor does not supply a
base case**: a floor at `n` needs the descent at `n − 1`, and the
obstruction is the shape of the gated clause, not the numeral.  The
recursion must terminate on another measure — context growth (defect), or
the pigeonhole over `jumpGoals S` that `cascade_main` already implements.

This does not touch `Descends need` (`wip/descent2.lean`), which is the
target either way; it says the *proof* has to come from the defect side.
`descends_of_othDescends` remains valid and reusable, but `OthDescends`
should not be attacked by a budget induction.

### A second lower bound, and candidate B dead twice over

The same configuration is an instance of `Descends` at target budget `0`,
forcing

    gate_free_lower_bound : Descends "p" need → 1 ≤ need Sz [] gz

at a space whose **gated-piece count is zero** (`gateCount_Sz : gateCount Sz
= 0`).  So the gate-count law `needGate` is refuted by data
(`needGate_excluded`), not only by the proof obligation `NeedFloor1`
(`needGate_not_floor1` of §82).  The §82 elimination used the empty space and
could be dismissed as degenerate; `Sz` is piece-closed with a genuine
`◯`-goal.

Surviving candidates: `needConst2` (constant `2`) and `needProduct`
(`defect S Γ · (|jumpGoals S| + 2)`, the law the tower assumes).  Note
`needProduct Sz [] gz = 3 · 2 = 6 ≥ 1`, so it survives; `needConst2` gives
`2 ≥ 1`.

### Next

Build the starvation classification the residue's own failure analysis names
as step one — which `(Γ, g, b)` starve — and from it a
`(defect, budget)`-lexicographic landing map.  `wip/starve.lean` has four
bricks; the classification needs the *general* collapse lemmas (not just the
`◯`-goal floor) and the dual statement for `itpE`.

A running record of this away-run, written for a reader who was not present,
is at `docs/away-run-report.md`.

## §84 — the budget boundary does NOT climb with the space; the ledger law and the reduction that closes the tower (30 July)

Two things landed: a measurement that settles the shape of the budget law,
and the machine-checked reduction from the parametric descent to the
tower's holdout.

### The measurement (`wip/ascprobe.lean`, output `wip/ascprobe_out.txt`)

The question a constant budget law lives or dies by: **does the failure
boundary move as the space grows?**  `wip/budgetfit.lean` answered it for
the descent at one goal shape (flat at `2` for chains of length 2, 3, 4).
This probe extends it in the two directions the rebuild needs.

**The ambient-relative existential ascent** (`AmbGuardAscent`), never
probed before, at every position `X` along the chain:

| family | \|S\| | position `k` | live gates in `X::Γ` | defect | boundary |
|---|---|---|---|---|---|
| chain2 | 10 | 0 | — | 9 | 1 |
| chain2 | 10 | 1 | 2 | 8 | **2** |
| chain3 | 13 | 0 | — | 12 | 1 |
| chain3 | 13 | 1 | 2 | 11 | **2** |
| chain3 | 13 | 2 | 3 | 10 | **2** |
| chain4 | 16 | 0 | — | 15 | 1 |
| chain4 | 16 | 1 | 2 | 14 | **2** |
| chain4 | 16 | 2 | 3 | 13 | **2** |
| chain4 | 16 | 3 | 4 | 12 | 1 |

"Boundary `k`" = one past the last `checkB`-certified failure.  Every
certified failure is at `c ∈ {0, 1}`; there is **not one certified failure
at `c ≥ 2`** anywhere in the sweep, including at four live gates and
defect 15.  On the `⊃⊃`-gated chain the boundary is 1 (and one row shows no
certified failure at all).  So the ascent's boundary is flat at `≤ 2` and
does not track `|S|`, the defect, or the number of gates.

**The descent at jump goals** — the goals a budget-gated clause puts in
first-component position, i.e. exactly the goals the recursion enters:

| goal shape | example | verdict row (c = 0,1,2,3) | boundary |
|---|---|---|---|
| atom | `p`, `r`, `s` | `P P P P` | 0 |
| boxed atom | `◯p`, `◯r`, `◯s` | `R! ~ ~ ~` | 1 |
| `⊃◯`-implication | `◯r ⊃ s` | `~ ~ ~ ~` | 0 |

At **atom** goals the descent is *proved by search at every budget,
including `0`*.  At **boxed** goals it fails at `0` and only at `0` — which
is precisely `itpA_starve_floor` (§83): at budget `0` a `◯`-goal's table is
its environment table alone, and it can be empty.  Identical for chain2 and
chain3.

**Reading.**  The data is consistent with a *constant* law `need = 2`, and
inconsistent with any law that tracks the size of the space: the assumed
product would predict boundaries 63, 108, 165 for chain2/3/4 and the
measurement is flat.  It also refines the law by **goal shape**: 0 at
atoms, 1 at boxed goals, 2 in general.  `Need` is already a function of
`g`, so a shape-sensitive law is expressible.

### The ledger law, and the third constraint on `need`

The two screens so far constrain `need` from below (refutations) and from
the proof (`NeedFloor1`).  There is a third, from **above**: the caller has
to be able to pay.  The caller is the tower's stabilisation entry, running
under `kcap S < c + 2`, and `kcap_room` turns that into

    |jumpGoals S| + 1 + defect S Γ · (|jumpGoals S| + 2)  ≤  c

at every context.  In `wip/descent2.lean` §5 (with `kcap_room` reproved,
since `wip/absorb_base.lean` is not a lake library target):

* `needKcap` — the ledger law, and `needKcap_funded` : it is exactly what
  the entry condition pays;
* `needKcap_floor1` : it satisfies the first extracted law (the `+1` is
  unconditional), so it can be fed to `descends_of_othDescends` as it
  stands;
* `needProduct_not_floor1` : the tower's *bare product* cannot — at a
  saturated context (`defect = 0`) it asks for nothing.  That band is
  separately settled by `cascade_zero`, so this is a bookkeeping fact, not
  a refutation of the tower.

Scale at the `wip/ascRefute.lean` configuration: `needKcap = 62`,
`needProduct = 56`, `kcap = 242`, against a certified requirement of `2`.
So the ledger over-estimates by a factor of about 30 — affordable, but the
measurement says a constant would do.

### The reduction

    LedgerDescent p S  -- the descent at every ledger-funded configuration
                       -- (= cascade_low_pos_box's statement, restated)

    ledgerDescent_of_descends    : Descends p needKcap   → LedgerDescent p S
    ledgerDescent_of_othDescends : OthDescends p needKcap → LedgerDescent p S

PROVED, sorry-free, `[propext, Classical.choice, Quot.sound]`.  So the
whole remaining content of the tower is now **one statement**:
`OthDescends p needKcap`.  That is the first time the holdout has been
reduced to a single named proposition with a funded budget law.

### Next

The structural analysis, now backed by the measurement, isolates one
statement that everything else waits on: the **ambient-relative
existential ascent at budget `≥ 2`**.  It is consumed by three growth
branches of the others-descent; it is false at `c = 1` (`wip/ascRefute.lean`
§1) and has no certified failure at `c ≥ 2`.  Its own recursion needs the
descent at *jump goals* at target budget `c − 1 ≥ 1`, and the measurement
says that holds (boundary 1).  So the next target is the conditional
theorem

    JumpDescent p S  →  AmbGuardAscent (restricted to 2 ≤ c),

with `JumpDescent` named as an explicit hypothesis rather than assumed
silently.

## §85 — the goal side of the descent closes; the low-budget difficulty is entirely in the environment clauses (30 July)

`wip/goalDesc.lean` (new), `wip/descent2.lean` §6, `wip/jumpprobe.lean`
(new exe).  All sorry-free and axiom-pinned.

### A structural fact about the clause tables

An exhaustive transcription of `itpE`/`itpA` (`LaxLogic/PLLG4UITrunc.lean`,
all seven `match b with` sites) establishes:

> **every budget-decrementing recursive reference sits at the same context,
> and every context-growing reference sits at the same budget.**

The one apparent exception is the `C₁ ∈ Γ` branch of the `⊃`-goal clause,
whose reference is at `C₁ :: Γ` — a formula already in `Γ`, so the defect is
unchanged (`defect_cons_eq`).

Two consequences.

**(i) The recursion is well-founded on the lexicographic pair `(defect,
budget)`, with no pigeonhole argument.**  Each recursive call either drops
the defect at fixed budget or drops the budget at fixed defect.  So what the
seen-set/pigeonhole machinery of `cascade_main` is for is *not* termination —
it is the fact that the budget's base case is **false** (§83).  A proof must
show the low-budget instances actually reached are harmless; it does not
need to show the recursion stops.

**(ii) The budget tier is entered only at *jump goals*, and only one step.**
The only universal components at budget `b−1` anywhere in the tables are
`A@b'(Γ,A)`, `A@b'(Γ,A⊃B)` and `A@b'(Γ,◯A)`, from the two gated
*environment* clauses.  Every other `b'`-reference is existential.

### The goal side: six of seven families close

`wip/goalDesc.lean` states each goal family's requirement separately, with
the fuel and budget bookkeeping exposed:

| goal `g` | gated | mechanism | status |
|---|---|---|---|
| `prop q` | no | the source disjunct *is* the target disjunct | closed |
| `⊥` | no | no goal clause exists | vacuous |
| `C₁ ∧ C₂` | no | descent at `C₁`, `C₂` | closed |
| `C₁ ∨ C₂` | no | descent at `C₁` or `C₂` | closed |
| `C₁ ⊃ C₂`, `C₁ ∈ Γ` | yes | ambient ⇒ guard (`itp_congr`), descent at `C₂` | closed |
| `◯D` | yes | `box_open`, ambient ⇒ guard, descent at `D` | closed |
| `C₁ ⊃ C₂`, `C₁ ∉ Γ` | no | the ascent at a fresh antecedent | `FreshAntAscent` |

The two gated rows are the informative ones.  Both look as if they need the
descent one budget lower — at `c = 1` the refuted descent to budget `0`.
They do not: **a gated goal clause demotes only its existential component**
to `b−1`, keeping the universal one at `b`.  The demoted existential is then
supplied by the *ambient* at budget `c+1` through downward existential
monotonicity, which is free and unconditional (`ambE`, composing
`itp_fuel_mono`, `itp_budget_mono_le`, `itp_congr`).

So **no goal branch touches the budget-`0` base case at all**, and the whole
low-budget difficulty of the descent lives in the environment clauses.

Attribution: these six branches are already discharged inside `oth_descent`
(the `itpAgoal` half of its case analysis), and none of them consumes that
file's four interfaces.  What `wip/goalDesc.lean` adds is the public,
per-branch, standalone form — which is what makes the requirement table
above checkable rather than a reading of a thousand-line induction.

### The floor law was too strong; refined by goal shape

`desc_of_oth` carries `1 ≤ c`, and §82 extracted `NeedFloor1 need := ∀ S Γ g,
1 ≤ need S Γ g` from it.  That hypothesis is used in exactly one place: the
**truncation** disjunct, which `itpAfull` appends only for a `◯`-shaped goal.
`GoalDesc.desc_of_oth_nonbox` proves the wrapper for every other goal with
no budget hypothesis at all, so the law weakens to

    NeedBoxFloor1 need := ∀ S Γ D, 1 ≤ need S Γ (◯D)

and `descends_of_othDescends_shape` re-proves the rebuild's top level under
the weaker law.  This is not cosmetic: `NeedFloor1` forbids any law that
asks for `0` anywhere, and the measurement says the requirement is `0` at
atom goals.

### The measured law is a function of the goal shape

`wip/jumpprobe.lean` runs the **positive** side hard (proof search at
`findBudget` 20 000 and 200 000) on the cells that decide the recursion:

| jump-goal shape | budget `0` | budget `1` |
|---|---|---|
| atom `aᵢ` | **PROVED** (both budgets, chain2 and chain3) | **PROVED** |
| boxed atom `◯aᵢ` | **REFUTED** (certified) | inconclusive (200 000 exhausted) |
| `⊃`-shaped | inconclusive | inconclusive |

So `needShape` — `0` at atoms and `⊥`, `1` at boxed goals, `2` elsewhere —
is the law the data points to.  It satisfies `NeedBoxFloor1` exactly
(`needShape_boxFloor1`), fails `NeedFloor1` (`needShape_not_floor1`), and
survives both certified lower bounds with nothing to spare: `2` at the
`wip/ascRefute.lean` configuration (goal `(◯r ⊃ s) ⊃ t`, an implication) and
`1` at the `wip/floorRefute.lean` configuration (goal `◯(⊥⊃⊥)`, boxed).

### What remains, now precisely two things

Both are at target budget `1`, and both are environment-clause branches:

1. **The γ-clause's boxed disjunct** — the target needs
   `◯(E@0(Γ) ⊃ A@0(Γ,◯A))`, i.e. the descent to budget `0` at a *boxed*
   jump goal, which is certified false as a plain statement.  It must be
   routed through a different target disjunct.  This is
   `GammaPairFloorBox`, the §73 stuck shape, and it is the one branch for
   which no mechanism is known.
2. **The ascent at a fresh antecedent, at budget `1`** — refuted
   (`wip/ascRefute.lean` §1), so the fresh-antecedent goal branch has no
   route at `c = 1` either, and needs its own floor treatment.

`GammaPairFloorA` and `JumpPairFloor` (the atom and `⊃` jump goals at budget
`0`) are *not* in this list: the atom case is now proved by search at budget
`0`, so it is plausibly closable, and the `⊃` case is open but unrefuted.

That is a sharper statement of the residue than "four jointly unsatisfiable
interfaces": the four are unsatisfiable because two of them are, and the
other two look reachable.

## §86 — the three gated environment components close above the floor; the residue is ONE branch at ONE budget (30 July)

`wip/envDesc.lean` (new), `wip/sealprobe.lean`, `wip/sealprobe2.lean` (new
exes).  Lean content sorry-free and axiom-pinned.

### The three gated environment first components

§85 showed the goal side of the descent never reaches budget `0`, so the
whole low-budget difficulty is in the two budget-gated *environment* clauses.
Each contributes disjuncts (first component) ∧ (second component), the second
at the grown context and the same budget (defect tier), the first at the same
context one budget lower.  Three first components in all, and `wip/envDesc.lean`
proves **all three** close at target budget `c + 1` from the descent at the
corresponding jump goal at target budget `c`:

| clause | target first component at budget `c+1` | lemma |
|---|---|---|
| jump | `E@c(Γ) ⇢ A@c(Γ, A⊃B)` | `jump_of_desc` |
| γ, plain | `A@c(Γ, A)` | `gamma_plain_of_desc` |
| γ, boxed | `◯( E@c(Γ) ⇢ A@c(Γ, ◯A) )` | `gamma_boxed_of_desc` |

bundled as `gated_env_first`.  The mechanism is the same one that settled the
goal side, and it is worth stating plainly:

> the ambient sits at budget `c + 2`, i.e. **two** above the component's
> budget, so downward existential monotonicity alone supplies the guard
> `E@(c+1)(Γ)` needed to fire the source.

So no *ascent* is consumed — the refuted `AmbGuardAscent` does not appear in
any of the three.  What is consumed is the descent at a jump goal at target
budget `c`, needing `c ≥ 1`.  In particular **the boxed γ-component — the
"γ-seal" that `wip/absorb_base.lean`'s residue analysis lists as unreachable
by the continuation machinery — is reachable at every target budget `≥ 2`**,
by `box_remap_free` with the guard taken from the ambient and the value from
the descent one budget down.

### So the residue is one branch at one budget

Target budget `1`.  There the value conversion is the descent to budget `0` at
a boxed goal, and that is certified false.  Everything else in the descent
above budget `1` is either proved here, proved in `wip/goalDesc.lean`, or is
the defect tier.

### The floor case, and an honest caveat about the `◯⊥` route

At the floor the boxed target component is `◯(E@0(Γ) ⇢ A@0(Γ,◯A))`, and at
budget `0` a `◯`-goal's table is its environment table alone
(`itpA_obGoal_floor`), which can be **starved** — literally `⊥`.  When it is,
the component is `◯(E@0(Γ) ⇢ ⊥)` and **any derivation of `◯⊥` gives it**:
`boxed_target_of_starved` / `boxed_target_of_env_nil` (sorry-free).  No
descent and no ascent.

On the probed configuration that demand is met.  `wip/sealprobe2.lean`
reports, for `Γ = [◯p ⊃ r]`:

    A@0(Γ,◯p) = ⊥ ,  A@0(Γ,p) = ⊥ ,  E@0(Γ) = ⊤
    A@1(Γ,◯p)  ⊢  ◯⊥          PROVED

so the boxed branch *is* derivable there, by a route proof search does not
find (`wip/sealprobe.lean` returns `~` on the whole obligation at
`findBudget` 200 000, while the control `GammaPairFloorA` comes out `PROVED`
at every atom and boxed goal `C`).

**But the route is specific to the probe family, and this must not be
oversold.**  It works because the γ-clause of that family is `◯p ⊃ r`, whose
head is the *eliminated variable* `p` — and the goal clause of `p` is empty at
every budget, which is what forces the collapse to `◯⊥`.  With a γ-head
`A ≠ p` the collapse fails: `A@0(Γ,A)` then contains the disjunct `A` itself,
so it is not starved, and `A@1(Γ,◯A)` is satisfiable in an infallible model
while the target component `◯⊥` is not.  A general `A@b(Γ,◯D) ⊢ ◯⊥` is false
outright (take `Γ = []`, `D = ⊤`).

### Next

The analysis above predicts a **countermodel** to `GammaPairFloorBox` at a
configuration whose γ-head is not the eliminated variable: `Γ = [◯r ⊃ s]`,
`A = r`, with `r` false at the root and true at a `⊳`-successor, in an
infallible model.  If that lands, the interface is *individually* false, not
merely part of an unsatisfiable four, and the branch has to be re-cut rather
than proved.  That is the next probe, and it is the right order of work:
refute before attempting.

## §87 — NO UNIFORM ROUTE closes the boxed γ-branch at the floor (30 July)

`wip/sealRefute.lean` (new), `wip/sealprobe3.lean`, `wip/sealprobe4.lean` (new
exes), `docs/descent-problem.md` (new).  Lean content sorry-free,
`[propext, Quot.sound]`.

### The question, made finite

§86 left one branch at one budget.  At target budget `1` the target table
offers exactly three kinds of disjunct, and the branch's third hypothesis
`A@1(B::Γ,C)` is already the second conjunct of two of them.  So the branch
closes **iff one of**

    (a)  A@0(Γ, A)                      the plain γ-disjunct's first component
    (b)  ◯( E@0(Γ) ⇢ A@0(Γ, ◯A) )       the boxed one
    (c)  the goal clause of `C`

is derivable from `E@2(Γ)`, `◯(E@1(Γ) ⇢ A@1(Γ,◯A))`, `A@1(B::Γ,C)`.  That is a
finite question about three small sequents rather than one large one, and the
oracle can answer it.

### The answer: each route is individually FALSE

At the configuration

    S = {◯r ⊃ s, ◯r, r, s, p, z},  Γ = [◯r ⊃ s],  A = r,  B = s,  C = z

— a γ-head that is an **ordinary atom**, not the eliminated variable — all
three fail, kernel-checked:

| route | Lean name | refuting model |
|---|---|---|
| (a) `⊢ A@0(Γ,r)` | `not_route_a` | `0 ⊑ 1`, `0 ⊳ 1`, `r` at `1` only |
| (b) `⊢ ◯(E@0(Γ) ⇢ A@0(Γ,◯r))` | `not_route_b` | one reflexive world, all atoms forced |
| (b′) `⊢ ◯⊥` | `not_route_bot` | the same |

and both models are **infallible and mutually confluent**
(`Ma_infallible`/`Ma_confluent`, `Mb_infallible`/`Mb_confluent`), so the
refutations hold over PCLL, PILL and PICLL too.  Route (c) is `⊢ z`, which
fails in any model where `z` is false.

As universal statements: `not_uniformRouteA`, `not_uniformRouteB`.

### What this means

> **The branch cannot be closed by a uniform route.  It requires a case
> analysis over the target's disjuncts.**

This is why every mechanism surveyed in `wip/absorb_base.lean`'s residue
analysis failed — each of them is a *uniform* route (a single remap, a single
seal-crossing, a single collapse).  It also explains why no countermodel to the
branch obligation *itself* has been found in any probed configuration: in each
of the three refuting models a **different** route succeeds.  The obligation is
plausibly true; what is false is every attempt to prove it in one move.

It also retires the `◯⊥` collapse of §86 as a general mechanism.  That route
works on the chain families of `wip/budgetfit.lean` only because their γ-head
is the eliminated variable `p`, whose goal clause is empty at every budget, so
`A@0(Γ,p) = ⊥` and the component *is* `◯⊥`.  With an ordinary head
`A@0(Γ,r) = r ∨ ⊥` — satisfiable, not derivable — and `not_route_bot` closes
the collapse off.

### The shape of the missing proof

A case analysis, and the cases have to be read off the *model*, not the syntax
— which in a syntactic proof means splitting on a decidable syntactic condition
that implies the right route.  The three refuting models suggest what the
conditions are:

* route (a) is available when the plain component's own goal clause is
  derivable, i.e. when `A` is an atom forced by the hypotheses;
* route (b) is available when the boxed component starves and `◯⊥` follows —
  the `p`-headed case, `boxed_target_of_starved` (§86);
* route (c) is available when the second hypothesis `A@1(B::Γ,C)` collapses to
  `C`'s goal clause, which happens exactly when every environment clause of
  `B::Γ` is guard-dead (`wip/sealprobe3.lean` shows this is what makes the
  one-γ-clause families uninformative).

So the missing lemma is a **three-way starvation/liveness classification of
the pair (Γ, B::Γ)**, with one route per case.  That is the same
classification `wip/starve.lean` was begun for, and §87 fixes both its shape
(three cases) and its purpose (choosing a target disjunct, not crossing a
seal).

### Also landed

`docs/descent-problem.md` — a self-contained statement of the whole descent
problem: what it is for, the two termination measures, why the budget has no
base case, where the tier is entered, the goal side, the environment side, what
is left, and the budget law as a parameter.  Every claim is either a definition,
a named sorry-free Lean theorem, or explicitly labelled OPEN or a measurement.
This discharges part of the exposition debt recorded in memory.

## §88 — shortcuts checked and rejected (30 July)

Recorded so they are not retried.  Each was examined far enough to settle it.

**1. Completeness for the constraint semantics.**  `consequence_iff_derivable`
(`LaxLogic/PLLCompleteness.lean:634`) is full soundness *and* completeness for
the Fairtlough–Mendler constraint semantics, sorry-free, over list contexts.
With `G4c.equiv_nd` this lets any sequent about the tables be proved
semantically — attractive, because the descent's known obstruction is
proof-engineering (continuations cannot cross a `◯`-introduction) and semantics
has no continuations.

REJECTED.  Semantically the descent says a monotone iteration has reached its
fixed point by step `c`.  The iteration is over *hereditary sets of worlds*,
because the recursive references sit under `⊃` and `◯` and so are evaluated at
other worlds; a monotone iteration in that lattice has no finite bound.  The
syntactic pigeonhole works precisely because it counts *goals*, and goals live
in the finite set `jumpGoals S`.  Completeness remains a genuine escape hatch
for individual sequents, and it is what makes the countermodel oracle sound; it
is not a route to the general statement.

**2. Raising the budget floor.**  Refuted at `n − 1 ∈ {0, 1}` (§83), and the
obstruction is the shape of the gated clause rather than the numeral, so no
constant floor works.  `oth_descent`'s architecture (`wip/cascadeBox.lean`)
cannot be repaired this way.

**3. `itpE` budget-independence for gate-free spaces.**  Every budget-gated
clause of `itpE` carries an `∈ S` side condition on a *gated-shaped* driving
formula, so a space with no `(A⊃B)⊃D` and no `◯A⊃B` kills all of them.  One
might hope `itpE p S f b Γ` is then independent of `b`, which would make the
∃-ascent free and extend the proved region from box-free to gate-free spaces —
strictly larger, since a gate-free space may contain `◯A` and `A⊃B`.

REJECTED.  `itpE`'s *ungated* clauses reference `itpA` (rows 7b and 8b of the
clause table: `(E@b(B⊃D::Γ) ⇢ A@b(B⊃D::Γ, A⊃B)) ⇢ E@b(D::Γ)` and its γ
analogue), and `itpA` is budget-dependent for **every** space, because its
`◯`-goal clause, its truncation disjunct and its present-antecedent `⊃`-goal
clause are gated with no `∈ S` condition at all.  So the two tables are
mutually budget-dependent always, and the ∃-ascent is genuinely needed.

This also explains a fact that would otherwise look inconsistent:
`gate_free_lower_bound` (§83) shows the descent *fails* at budget `0` on the
gate-free space `{◯(⊥⊃⊥), ⊥⊃⊥, ⊥}`.  The failure comes from the goal side, not
the space.

**4. Pinning search-found proofs as theorems.**  `Verdict.proved` carries a
*typed* term `G4cTm Γ C`, and `G4cTm.toG4c` turns it into `G4c Γ C`, so a
found proof is already checked by Lean's typechecker at the moment it is built.
What is missing is a way to get that term into a *source file*: `#search` and
`#refute` are reporting macros, and running the searcher inside the kernel
(`decide`) is infeasible — the searcher is deliberately kernel-opaque.

NOT REJECTED, but not attempted: this needs a term-elaborating command that
runs the searcher at elaboration time and reflects the resulting `G4cTm` into
an `Expr`.  It would convert every "PROVED by search" in this development from
*evidence* into *theorem*, which the machine-checked mandate wants; it is the
single highest-value piece of tooling still missing.  Recorded as an
opportunity, with the mechanism identified.

## §89 — `#pinsrc`: search-found proofs become theorems (30 July)

`LaxLogic/PLLSearchPin.lean` (new, in the library), `wip/jumpPinned.lean`,
`wip/pinnedFacts.lean` (new).  All sorry-free.

### The gap this closes

The refutation side of the oracle has always produced *theorems*: a countermodel
is data, `FinCM.checkB M w Γ C = true` is a cheap kernel computation, and
`FinCM.not_provable_of_check` turns it into `¬ G4c Γ C`.  Every refutation in
this development is pinned that way.

The positive side did not, for a purely mechanical reason.  `Verdict.proved`
carries a **typed** term `t : G4cTm Γ C` — so Lean's typechecker has already
checked a derivation the moment the searcher builds one — but there was no way
to get `t` into a source file, and running the searcher in the kernel is
infeasible (it is deliberately kernel-opaque).  So every "PROVED by search" in
§§84–87 was *evidence*, which under the machine-checked mandate is not a
theorem.

### How

`#pinsrc Γ ⊢ C [with cfg]` prints `t` as pasteable Lean source.  The emitter
prints **no formulas at all**: every index is recovered by unification — `Γ` and
`C` from the type ascription, and each side formula from the *membership proof*,
emitted structurally as a `.tail _ (… (.head _))` chain at a computed position
in `Γ`.  So the output is proportional to the **derivation**, not to the
quantifier tables in the sequent, which here have weight in the hundreds.  The
chain is computed from the member's position rather than by recursion on the
membership proof, because `List.Mem` is `Prop`-valued and a `String`-valued
function cannot eliminate it.

Documented as `docs/search-manual.md` §10.  This completes the
"discover-then-pin" pipeline: probe → `#pinsrc` → generated source → kernel,
with nothing about the search trusted at the end.  For the two large terms the
generated source was written straight to a file rather than transcribed, so no
step is manual.

### Five facts promoted from evidence to theorem

| fact | nodes | Lean name |
|---|---|---|
| descent to budget `0` at the atom jump goal `p` | 7 | `JumpPinned.desc_zero_atom_p` |
| descent to budget `0` at the atom jump goal `r` | 12 | `JumpPinned.desc_zero_atom_r` |
| `A@1(Γ,◯p) ⊢ ◯⊥` (the collapse of §86) | 57 | `JumpPinned.boxbot_collapse` |
| descent to budget `0` at a `⊃`-shaped jump goal | 349 | `PinnedFacts.desc_zero_imp_jump` |
| `GammaPairFloorA` at one instance (the control of §87) | 104 | `PinnedFacts.gammaPairFloorA_instance` |

### What they settle

The budget tier of the descent is entered only at jump goals (§85).  Its base
case at budget `0` is now **proved** at both non-boxed jump-goal shapes — atom
and `⊃` — and **certified false** at the boxed shape.  So the boxed shape is not
merely the hardest case; it is the *only* one, and the localisation of §§86–87
rests on theorems rather than on how hard a search was pushed.

`gammaPairFloorA_instance` matters for the same reason: it is the control for
§87.  The plain γ-branch goes through where the boxed one has no uniform route,
so that distinction is a fact about the two branches and not about search
budgets.

## §90 — the boxed γ-branch CLOSED at one configuration, by case analysis (30 July)

`wip/envDesc.lean` §6 (`branch_of_cases`), `wip/boxedBranchS1.lean` (new),
`wip/sealprobe6.lean` (new exe).  All sorry-free.

### The mechanism the earlier survey missed

§87 refuted every uniform route.  The case analysis that must replace one is
available for nothing, and the reason it was overlooked is that the survey
looked at the source's *first* component and at the target's disjuncts.  The
branch's **second** hypothesis is itself a disjunction:

    A@1(B::Γ, C)  =  orAll (itpAfull p S F 1 (B::Γ) C)

so `orAll_elim` on it is a case analysis with one case per disjunct of the
grown-context table, and different cases may reach *different* target disjuncts
— which is precisely what §87 says the branch must do.

    branch_of_cases        : (∀ ψ ∈ itpAfull p S F 1 (B::Γ) C,
                                G4c (ψ :: Δ) (orAll (itpAoth p S fl 1 Γ C)))
                             → G4c Δ (itpA p S (F+1) 1 (B::Γ) C)
                             → G4c Δ (orAll (itpAoth p S fl 1 Γ C))

PROVED, sorry-free, `[propext, Quot.sound]`, together with a non-boxed-goal
variant.

### It is not a formality

`wip/sealprobe6.lean` asks the oracle for the whole obligation and for each case
separately, on the configuration

    S = {◯r ⊃ s, ◯r, r, s, z},  Γ = [◯r ⊃ s],  A = r,  B = s,  C = z

— γ-head an ordinary atom, so §87's refutations bite and §86's `◯⊥` collapse is
unavailable.  The result:

| what is asked | verdict |
|---|---|
| the whole obligation | `~` (search truncated at `findBudget` 40 000) |
| each of routes (a), (b), (b′) | **REFUTED** (§87) |
| the single case of the analysis | **PROVED**, 2 nodes |

So the case split turns an obligation that resists both proof search and every
one-move argument into one the searcher closes in two nodes.  That is a fair
diagnosis of the July survey's failure: it was looking for a uniform route, and
there is none.

### The branch, closed

`wip/boxedBranchS1.lean`:

    boxed_branch : G4c [amb, box, snd] (orAll (itpAoth "p" S1 3 1 G1 (prop "z")))

PROVED, sorry-free, `[propext, Quot.sound]`, by `branch_of_cases` with the
single case discharged by a `#pinsrc`-generated derivation (route (c): inject
the target's own goal clause for `z`, close by `init`).

**The residual branch of the descent is therefore closed at the configuration
its refutations single out.**

### What is not shown

One configuration is not the lemma.  The second component has a single disjunct
here because every environment clause of `s :: Γ` is guard-dead once `s` is in
the context.  A configuration whose *grown* context still has a live clause
gives several cases, each needing its own route — that is the two-γ-clause space
`S2`, which `wip/sealprobe6.lean` also runs.  The general lemma needs a route
assigned to each disjunct shape of `itpAfull p S F 1 (B::Γ) C`, i.e. a case
analysis over the clause table one level down.

That is now a *finite, enumerable* obligation of exactly the same kind as the
goal-side table of §85 — which is the first time the residue has had that shape.

## §91 — the universal table at an atom goal forces the atom (30 July)

`wip/atomForce.lean` (new), PROVED sorry-free,
`[propext, Classical.choice, Quot.sound]`.

    itpA_atom_forces :
      (∀ A B, A.or B ∉ S) → q ≠ p → (∀ Y ∈ Γ, Y ∈ S) →
      G4c [itpA p S f b Γ (prop q)] (prop q)

**at every fuel and every budget** — the budget plays no role, which is what
makes it usable at the floor where the descent itself fails.

### Where it came from

§90 closes the residual branch at one configuration by case analysis on the
second component, and every case closes the *same* way: the case's second
conjunct is a universal table at a **larger** context with the same goal, and at
the larger context it collapses to the goal clause.  Direct inspection of the
two-γ-clause configuration shows the three cases are

    z ,      (u ∨ ⊥) ∧ (z ∨ ⊥) ,      ◯((s ∧ ⊤) ⊃ ⊥) ∧ (z ∨ ⊥)

and each contains `z ∨ ⊥`.  Reading the environment clause table at an **atom**
goal `q ≠ p`, that is no accident: every clause either produces nothing or
produces a disjunct with a conjunct

    itpA p S f b Γ' (prop q)      at `Γ'` of strictly smaller defect,

with exactly one exception — the `∨`-clause, whose disjunct is a *conjunction of
implications* whose consequents cannot be extracted without their guards.  So
over contexts with no `∨`-shaped member the table collapses, by strong induction
on the defect.

The proof is that induction, over all ten environment clause shapes and every
guard branch, with `defect_lt_of_witness` supplying the decrease from a single
fresh `S`-member.

### What it settles

This is **the first general statement about the residue** — not a configuration,
not a measurement.  It is the engine of the case analysis of §90: in each case
the second conjunct is a table at a larger context, and this lemma turns it into
the atom, which is the target table's own goal clause.  So

> at an **atom** goal over a `∨`-free space, the residual branch closes
> uniformly in the configuration.

The two restrictions are exactly visible in the statement and both are real:

* **atom goal.**  At a compound goal the target's goal clause differs from the
  grown context's, so the case's conjunct no longer lands where it is needed.
* **`∨`-free.**  The `∨` environment clause is the one shape whose disjunct is a
  conjunction of implications.  Lifting this is the next question; note it is a
  restriction on the *space*, and the `∨`-clause is also the one place the
  descent's own analysis needs the existential ascent (§85's fresh-antecedent
  row), so the two open ends may be the same one.

### §91 addendum — all three floor branches close at an atom goal

`floor_branch_atom`, `floor_branch_atom_full` (`wip/atomForce.lean` §3), PROVED
sorry-free.

The three floor branches — plain γ-pair, boxed γ-pair, jump-pair — differ only
in their **first** component.  Their second components are all of the same kind:
a universal table at the grown context with the branch's own goal.  At an atom
goal §2 turns that into the atom, and the atom is the target table's own goal
clause.  So all three close at once, and **neither the ambient nor the first
component is used at all**:

    floor_branch_atom :
      (∀ A B, A.or B ∉ S) → q ≠ p → B ∈ S → (∀ Y ∈ Γ, Y ∈ S) →
      G4c Δ (itpA p S F b (B :: Γ) (prop q)) →
      G4c Δ (orAll (itpAoth p S fl b Γ (prop q)))

at every fuel and every budget, in particular at the floor.

**What this does to the residue.**  The budget tier is entered only at jump
goals (§85), and jump goals have three shapes: `A`, `◯A` and `A ⊃ B`.  The atom
shape is now closed *uniformly in the configuration* — §89 had it pinned at one
configuration; it is now a theorem.  So the residue narrows again:

> the floor branches at **boxed** and at **`⊃`-shaped** jump goals, over spaces
> that may contain `∨`.

**Why atoms are genuinely special, and not just easier.**  The route works
because `prop q` is a disjunct of the target table at *every* context, so a
statement proved at the grown context lands where it is needed.  Every other
goal shape's goal clause mentions the context (`◯D` gives
`◯(E@(b−1)(Γ) ⇢ A@b(Γ,D))`, an implication goal gives
`E@b(C₁::Γ) ⇢ A@b(C₁::Γ,C₂)`), so the same move would require shrinking a
context — which is unsound, since a table at a larger context has *more*
disjuncts and is therefore weaker.  So extending past atoms is not a matter of
pushing the same argument harder.

### Dating note for §§83–91

These entries were written in one continuous session beginning at 22:11 BST on
29 July 2026.  The "(30 July)" dates on them are approximate — the wall-clock
times were estimated while working and the early ones drifted by several hours.
The order of the entries is correct and nothing in their content depends on the
times.

## §92 — the residue is ONE goal shape: the boxed jump goal (30 July)

`wip/sealprobe7.lean` (new exe), `wip/floorImp.lean` (new).  Lean content
sorry-free.

### The route table

The budget tier of the descent is entered only at jump goals, of three shapes
(§85).  `wip/sealprobe7.lean` asks the oracle, for each shape and for **each
case** of the §90 analysis, which disjunct of the target table that case can
reach:

| goal shape | whole obligation | route the cases take |
|---|---|---|
| atom | **proved in general** (`AtomForce.floor_branch_atom`, §91) | the goal clause |
| `A ⊃ B` | **PROVED**, 9 nodes, both configurations | the goal clause (disjunct 0), 8 nodes |
| `◯A` | `~` | **no case reaches any target disjunct** |

Two configurations were run: one live γ-clause (`S1`) and two (`S2`, where the
grown context still has a live clause so the analysis genuinely branches — 4
cases at the boxed goal, 3 at the `⊃`-shaped one).

`wip/floorImp.lean` pins the two `⊃`-shaped instances, so the middle row is a
theorem: `floor_branch_imp_S1`, `floor_branch_imp_S2`, sorry-free,
`[propext, Quot.sound]`.

### So the residue is one goal shape

Every other part of the descent is now accounted for:

* the **goal side**: six of seven families proved, none reaching budget `0`
  (§85); the seventh reduces to the ∃-ascent;
* the **gated environment components at target budget ≥ 2**: proved (§86);
* the **floor at an atom jump goal**: proved in general (§91);
* the **floor at a `⊃`-shaped jump goal**: proved at two configurations, by the
  same route as atoms (§92);
* the **floor at a boxed jump goal**: OPEN, and no case of the analysis reaches
  any target disjunct.

> **The residue of uniform interpolation for PLL is the descent at target budget
> `1` at a boxed goal.**

That is a single statement about a single goal shape, and it is where every
thread of this session converges: the certified failure at budget `0`
(`wip/ascprobe.lean`), the three refuted uniform routes (§87), the `◯⊥` collapse
that works only for a `p`-headed γ-clause (§86), and now the empty row of the
route table.

### Why the boxed shape resists, precisely

At an atom goal the route works because `prop q` is a disjunct of the target
table at **every** context, so a fact proved at the grown context lands where it
is needed (§91).  At a `⊃`-shaped goal the goal clause does mention the context,
but the searcher still finds an 8-node derivation — worth understanding, and the
pinned terms are there to be read.  At a boxed goal the goal clause is

    ◯( E@(b−1)(Γ) ⇢ A@b(Γ, D) )

which mentions the context **under a `◯`**, so neither move applies: the guard
`E@(b−1)(Γ)` has to be produced inside the box, and at the floor `b − 1 = 0`.

### §92 addendum — integrity check, and one hazard removed

Every file added in this session is **sorry-free**: `wip/floorRefute.lean`,
`wip/goalDesc.lean`, `wip/envDesc.lean`, `wip/sealRefute.lean`,
`wip/jumpPinned.lean`, `wip/pinnedFacts.lean`, `wip/boxedBranchS1.lean`,
`wip/atomForce.lean`, `wip/floorImp.lean`, `LaxLogic/PLLSearchPin.lean`, plus the
additions to `wip/descent2.lean`.  `lake build LaxLogic wipshared` is clean and
reports `sorry` only in the files that carried one before this session.  Every
`#guard_msgs` axiom audit in the new files passes as written.

One hazard removed.  `#pinsrc`'s emitter had a fallback string containing the
word `sorry`, for the impossible case of a membership proof whose subject is not
found in the context.  Emitted source is meant to be *pasted into a file*, so a
fallback that elaborates to `sorry` could turn a broken emission into a silently
unsound theorem.  It now emits an unknown identifier, which fails loudly at
elaboration.

## §93 — the boxed floor branch needs genuine recursion, not one application of the defect tier (30 July)

`wip/sealprobe9.lean` (new exe).  A measurement, with a consequence worth
stating carefully.

### The extra family at a boxed goal does not help

At a boxed goal the universal table has one environment clause family that exists
at no other goal shape: for each `◯χ ∈ Γ` with `χ ∈ S ∖ Γ`,

    ◯( E@b(χ::Γ) ⇢ A@b(χ::Γ, C) )

Every configuration probed in §92 had **no** `◯χ` in the context, so that family
was empty — an obvious suspect for the missing route.  With `◯w` added to the
context the family is live and the target grows from 3 disjuncts to 5.  The route
table is unchanged: **every case still reaches NOTHING**, and the whole
obligation is still `~`.  The control row (same space, `◯w` removed from the
context) reproduces §92 exactly.

So across three configurations, two spaces and both with and without a boxed
context member, no case of the analysis reaches any target disjunct at a boxed
goal — while at atom and `⊃`-shaped goals every case reaches the goal clause in
under ten nodes.

### What that does and does not establish

It does **not** refute `GammaPairFloorBox`.  That interface carries the defect
tier as a *Lean-level* hypothesis (the descent at every strictly smaller defect),
and a countermodel to a sequent says nothing about a hypothesis that may simply
be false in that model.

What it does establish is sharper than a refutation would be, and is about proof
*shape*:

> the boxed floor branch cannot be closed by reaching a target disjunct from the
> ambient, the source's boxed component and the second component alone.  Any
> proof must apply the defect tier **again**, at a further-grown context — i.e.
> the case analysis has to recurse.

The material handed to the oracle is everything the branch has except Lean-level
recursion: the second component was supplied *already descended*, and from it the
budget-2 form and all of its disjuncts follow by monotonicity.  So the negative
result is not a budget artefact of what was offered.

### Contrast with the two closed shapes

At an atom goal one application suffices, because `prop q` is a disjunct of the
target at **every** context (§91).  At a `⊃`-shaped goal the searcher finds an
8-node route at two configurations (§92) — and it should be said plainly that
this is *not* yet a general lemma, and the pinned derivation is
configuration-specific: it reaches `prop s` from the introduced guard by firing
the γ-clause, which works because the goal's consequent happens to be the
γ-clause's consequent.

So the standing summary is:

| goal shape | status |
|---|---|
| atom | **proved in general** (∨-free space) |
| `A ⊃ B` | proved at two configurations; general lemma OPEN |
| `◯A` | OPEN, and now known to need a recursive case analysis |

### §93 addendum — correction: the residue is TWO branches, not one

§92's headline ("the residue is one goal shape") understated it, and the
consolidated table in `docs/away-run-report.md` has been corrected.  At target
budget `1` there are **two** open branches:

1. the **floor branch at a boxed jump goal** — the one this session narrowed
   (§§86-93);
2. the **fresh-antecedent goal branch** — its target clause is
   `E@1(C₁::Γ) ⇢ A@1(C₁::Γ,C₂)`, and firing the source's requires the ∃-ascent at
   budget `1` at the grown context, which is precisely what `not_ambGuardAscent`
   refutes.  This has been open since July and is untouched by this session.

Above budget `1` neither arises: the gated environment components have the ambient
two budgets up (§86), and the ascent has no certified failure at `c ≥ 2` in any
probed configuration (§84).

So the accurate statement is: **the descent is reduced to two branches, both at
target budget `1`.**  That is still a large advance on the position at the start
of the session — four jointly unsatisfiable interfaces with no localisation, and
a budget law guessed and refuted three times — but it is two branches, not one.

## §94 — the fresh-antecedent branch does not have to go through the ascent (30 July)

`wip/sealprobe10.lean`, `wip/sealprobe11.lean` (new exes), `wip/freshAnt.lean`
(new, sorry-free).

The second residual branch (§93 addendum) is the descent's goal-side clause for
`C = C₁ ⊃ C₂` with `C₁ ∉ Γ`.  The obvious route introduces the target's guard and
fires the source, needing `E@2(C₁::Γ)` from `E@1(C₁::Γ)` and the ambient at the
*ungrown* context — the ∃-ascent, refuted at budget `1`.  That is why the branch
has been open since July.

Examined disjunct by disjunct for the first time:

| configuration | whole target | goal clause (disjunct 0) | other disjuncts | ascent instance |
|---|---|---|---|---|
| `C = r ⊃ s`, `S1` | **PROVED**, 9 | **PROVED**, 8 | REFUTED | `~` |
| `C = r ⊃ s`, `S2` | **PROVED**, 9 | **PROVED**, 8 | REFUTED | `~` |
| `C = r ⊃ z`, `S1` | `~` | `~` | REFUTED | `~` |
| `C = r ⊃ z`, `S2` | `~` | `~` | REFUTED | `~` |

So at `C = r ⊃ s` **the branch closes in nine nodes while the ascent it was
thought to need is itself undecided by the same search.**  Pinned as
`FreshAnt.fresh_ant_S1`, `fresh_ant_S2` (sorry-free, `[propext, Quot.sound]`).

### What this changes

The second residual branch is **not known to depend on the refuted ascent**, and
sometimes demonstrably does not.  That is a change in the shape of the problem:
`not_ambGuardAscent` refutes a statement the branch *can* be routed through, not
one it *must* be.

### What it does not settle

The route found uses the link between the goal's consequent and the γ-clause's
consequent (`C₂ = s` is the consequent of `◯r ⊃ s`).  At `C = r ⊃ z`, with an
unrelated consequent, the goal clause is undecided and every other target disjunct
is **refuted** — so that cell is the one that decides whether a general lemma
exists, and `wip/sealprobe11.lean` pushes it at `findBudget` 200 000, 2 000 000
and `none`.

### Standing summary of the two residual branches

| branch | budget | status |
|---|---|---|
| floor, atom jump goal | 1 | **proved in general** (∨-free space) |
| floor, `⊃`-shaped jump goal | 1 | proved at two configurations |
| floor, **boxed** jump goal | 1 | OPEN; needs a *recursive* case analysis (§93) |
| fresh-antecedent goal | 1 | proved at two configurations, **without** the ascent; general lemma OPEN |

## §95 — the fresh-antecedent branch closes at the DECIDING cell, still without the ascent (30 July)

`wip/sealprobe11.lean`.

§94 found the branch closing in 9 nodes at `C = r ⊃ s`, and flagged the honest
caveat: the route used the link between the goal's consequent and the γ-clause's
consequent, so `C = r ⊃ z` — consequent unrelated to anything in the context —
was the cell that would decide whether a general lemma exists.  There every
non-goal target disjunct is *refuted*, so the goal clause was the only candidate,
and it was undecided at `findBudget` 20 000.

Pushed:

| cell | verdict |
|---|---|
| `C = r ⊃ z`, goal clause, `findBudget` 200 000 | **PROVED, 56 nodes** |
| `C = r ⊃ z`, goal clause, `findBudget` 2 000 000 | **PROVED, 56 nodes** |
| `C = r ⊃ z`, goal clause, `findBudget := none` (exhaustive) | **PROVED, 56 nodes** |
| the ∃-ascent instance `E@1(r::Γ) + ambient ⊢ E@2(r::Γ)` | `~` at 200 000 (26 s) |

So at the configuration designed to be the hard one, **the fresh-antecedent goal
branch closes without the existential ascent** — and the ascent instance the
"natural" route would have needed is *still* undecided by a search a hundred
times larger than the one that found the branch's proof.

### What this means

`not_ambGuardAscent` refutes a statement the branch **can** be routed through, not
one it **must** be.  The second residual branch is therefore not known to depend
on anything refuted, and at every cell probed so far it closes.  That is a
different position from "open since July because the ascent is false": the
obstruction there was an artefact of the route chosen in `wip/cascadeBox.lean`, not
of the branch.

The 56-node derivation is long enough to be worth reading rather than guessed at
— it goes through `impLOr`, `impLProp` and `impLAnd` on the introduced guard,
i.e. it takes apart the *existential table at the grown context* rather than
trying to strengthen it.  That is precisely the move the ascent was standing in
for, done by cases instead.

### Standing summary

| branch | budget | status |
|---|---|---|
| floor, atom jump goal | 1 | **proved in general** (∨-free space) |
| floor, `⊃`-shaped jump goal | 1 | proved at two configurations |
| floor, **boxed** jump goal | 1 | OPEN; needs a recursive case analysis (§93) |
| fresh-antecedent goal | 1 | proved at **three** configurations including the deciding one, **without** the ascent; general lemma OPEN |

So the one branch with no positive evidence anywhere is the boxed floor branch.

## §96 — a methodological correction to §§92–93

§92's route table and §93's conclusion both rested on cells reading `~` at
`findBudget` **20 000**.  §95 then showed the fresh-antecedent branch needs
**200 000** nodes to turn up a derivation that is only 56 nodes long — the proof
is short, the search space is wide.

So the boxed row of §92's table, and §93's inference from it, are **not
established**.  Specifically:

* §92 said "no case reaches any target disjunct" at a boxed goal.  What was
  observed is "no case reaches any target disjunct *within 20 000 nodes*", and
  `Reason.budgetExhausted` asserts nothing at all — the file's own documentation
  says so.
* §93 concluded that any proof of the boxed branch "must apply the defect tier
  again, at a further-grown context".  That inference used the same cells and
  therefore does not stand either.  Its stated reason — that the material offered
  was everything except Lean-level recursion — was sound, but it is only relevant
  once the search has actually been given enough budget to look.

`wip/sealprobe12.lean` re-runs every boxed cell at 200 000 and 2 000 000, per case
and per target disjunct, at both configurations.

What is *not* affected: everything proved (§§85, 86, 90, 91, 94), everything
refuted (§§83, 87 — refutations are `checkB`-certified and budget-independent),
and the measurements whose content is a *certified failure* rather than an absence
(§84).  The affected claims are exactly those that read a `~` as information.

This is worth recording as a discipline and not only as a fix: the probe harness
prints `~` with the reason attached precisely so that this mistake is visible, and
I made it anyway by comparing a `~` row against `PROVED` rows found at the same
budget.  A `~` may only ever be compared with another `~`.

## §97 — the boxed floor branch CLOSED at the exemplar configuration (30 July)

`wip/boxedS1b.lean` (new), PROVED sorry-free,
`[propext, Classical.choice, Quot.sound]`.

`wip/sealprobe12.lean` leaves every boxed-goal cell `~` even at `findBudget`
2 000 000.  Per §96 that is not evidence.  A hand computation on the smallest
configuration said the branch should close, by a route proof search is badly
placed to find — and it does.

### The route

Configuration as in `wip/sealRefute.lean` (γ-head an ordinary atom, so that
file's refutations bite and §86's `◯⊥` collapse is unavailable):

    S = {◯r ⊃ s, ◯r, r, s, z},  Γ = [◯r ⊃ s],  A = r,  B = s,  C = ◯s

The **ambient** `E@2(Γ)` is a conjunction, and one of its conjuncts is

    ◯( E@1(Γ) ⇢ A@1(Γ,◯r) )  ⇢  E@2(s::Γ)

whose antecedent is *the branch's own boxed component*.  Fire it: the grown
existential table `E@2(s::Γ)` follows, and its **atom** conjuncts include `s`,
because `s` is now in the context.  From `s`, the target's goal clause
`◯(E@0(Γ) ⇢ A@1(Γ,s))` follows by `laxR`, `impR`, and injecting `s` as the goal
clause of the atom `s` inside `A@1(Γ,s)`.

    s_of_amb_box    : G4c [amb, box] (prop "s")
    boxed_branch_b  : G4c [amb, box] (orAll (itpAoth "p" S1 3 1 G1 (◯s)))

So the branch closes using **only the ambient and the boxed component**.  The
second component is not needed; neither is a descent, an ascent, or a case
analysis.

### Why this was invisible

The decisive step is a *projection out of the ambient*, and the ambient at this
configuration is a conjunction of weight ≈ 490.  Proof search has to guess which
conjunct to project and then fire it against another hypothesis; it does not, even
at two million nodes.  And the earlier route taxonomy (§87) enumerated what the
branch could aim *at* without noticing that the ambient's γ-conjunct has the
branch's own hypothesis as its *antecedent* — the ambient is not just a source of
weaker tables by monotonicity, it is a source of **implications whose antecedents
the branch already has**.

That is a mechanism worth naming, because §86's `gated_env_first` uses the ambient
only through downward monotonicity, and this is a second, stronger use of it.

### Status of the residue

Every branch now has positive evidence:

| branch | budget | status |
|---|---|---|
| floor, atom jump goal | 1 | **proved in general** (`∨`-free space) |
| floor, `⊃`-shaped jump goal | 1 | proved at two configurations |
| floor, **boxed** jump goal | 1 | **proved at the exemplar configuration** (§97) |
| fresh-antecedent goal | 1 | proved at three configurations, incl. the deciding one |

§§92–93's negative framing is now fully retracted: it rested on `~` cells at a
budget ten to a hundred times too small (§96), and the branch it declared
unreachable is derivable.

What remains is **generality**: each of the last three rows is a finite set of
configurations, and the general lemmas are open.  The atom row is the only one
proved uniformly in the configuration, and its route (`itpA_atom_forces`) is also
the only one whose mechanism does not depend on a coincidence between the goal and
the context — which is a fair statement of where the remaining mathematics is.

## §98 — the ambient fires the boxed component: the grown ambient, in general (30 July)

`wip/envDesc.lean` §7.  PROVED sorry-free,
`[propext, Classical.choice, Quot.sound]`.

§97's key step generalises, and this is it stated once and for all.

The ambient `E@(c+2)(Γ)` is a **conjunction**, and for a γ-clause
`◯A ⊃ B ∈ Γ ∩ S` with `B ∈ S ∖ Γ` two of its conjuncts are

    A@(c+1)(Γ,A)                      ⇢  E@(c+2)(B::Γ)
    ◯( E@(c+1)(Γ) ⇢ A@(c+1)(Γ,◯A) )   ⇢  E@(c+2)(B::Γ)

and the antecedents are **exactly the two first components of the source's
γ-disjuncts** — the plain one and the boxed one.  So:

    grownAmb_of_box   : ambient + boxed first component  ⊢  E@(c+2)(B::Γ)
    grownAmb_of_plain : ambient + plain first component  ⊢  E@(c+2)(B::Γ)

### Why this matters

`E@(c+2)(B::Γ)` is the **grown ambient**.  It is precisely the object
`AmbGuardAscent` was introduced to produce, and it is obtained here with no
ascent, no descent, no case analysis and nothing refuted — the γ-branch had it all
along, sitting in its own hypotheses.

This is a second and stronger use of the ambient than §4's.  There
(`gated_env_first`) the ambient supplies *weaker tables by downward
monotonicity*.  Here it supplies *implications whose antecedents the branch
already has*.  The July route survey missed it because it asked what the branch
could aim **at**, and never asked what the ambient could be fired **with**.

### What it unlocks

The defect tier's hypothesis at a grown context needs the ambient there.  With
`grownAmb_of_box`/`grownAmb_of_plain` the γ-branch can now apply the defect tier at
`B::Γ` properly, rather than being handed a pre-descended second component.  That
is the "genuine recursion" §93 was reaching for, and it is available without any of
the machinery §93 supposed would be needed.

The restriction is that the growth is by `B`, the γ-clause's own consequent.  The
fresh-antecedent branch grows by `C₁` instead, so this does not serve it directly —
but §§94–95 show that branch closing by a different route anyway.

## §99 — correction to §97: `◯B` is not a jump goal

`BoxedS1b.boxed_branch_b` (§97) is a true, sorry-free theorem and a genuine
instance of `GammaPairFloorBox`'s statement, which quantifies over all `g ∈ S`.
But it is at `C = ◯s`, and `s` is the γ-clause's **consequent** `B`, so `C = ◯B`.

The budget tier of the descent is entered only at **jump goals** (§85), and for a
space whose γ-clause is `◯A ⊃ B` the jump goals are

    A   and   ◯A          — *not*  ◯B.

So `C = ◯B` is not a goal the descent's recursion ever reaches, and §97 does not
close an instance the residue consists of.  Every earlier boxed-goal probe
(§§92, 93, 96) used the same `C = ◯s` and inherits the same objection: they were
measuring a configuration off the recursion's path.

Nor is §97's *route* available at the goals that are on it.  It works because the
grown ambient `E@2(B::Γ)` has `prop B` among its atom conjuncts — `B` is in the
context after growth — and at `C = ◯B` the target's goal clause reduces to `◯B`,
which follows from `B` by `laxR`.  At `C = ◯A` the target's goal clause needs
`A@1(Γ,A)`, whose goal clause is `prop A`, and the grown ambient supplies `prop B`,
not `prop A`.

`wip/sealprobe13.lean` re-runs the boxed cells at `C = ◯r`, the actual boxed jump
goal, with and without the grown ambient supplied as a hint (it is *derivable* from
the ambient and the boxed component by §98's `grownAmb_of_box`, so supplying it
cannot change derivability — only what the searcher finds).

### What survives §97 and §98

* `grownAmb_of_box`, `grownAmb_of_plain` (§98) are **general** and unaffected: the
  ambient plus either γ first component yields the grown ambient, at every budget
  and configuration.  That is the substantive discovery, and it stands.
* `s_of_amb_box` and `boxed_branch_b` (§97) are true instances, and they are the
  worked example that led to §98.  They are not instances of the residue.

So the honest statement of the boxed row is: **open at the goals the recursion
reaches**, with a general new resource (§98) in hand and the route at `◯B`
understood.

## §100 — the boxed floor branch closed at the goal the descent actually reaches (30 July)

`wip/boxedOnPath.lean` (new), PROVED sorry-free,
`[propext, Classical.choice, Quot.sound]`.

§99 pointed out that §97's instance was at `C = ◯B`, off the recursion's path.
This closes the branch at `C = ◯A` — the actual boxed jump goal.

### The route, and how it was found

At `C = ◯r` the target has three disjuncts and two are **refuted**
(`wip/sealprobe13.lean`), so the goal clause `◯(E@0(Γ) ⇢ A@1(Γ,r))` is the only
candidate.  The decisive measurement:

| sequent | verdict |
|---|---|
| `[snd, s] ⊢ ⋁ itpAoth …` | **PROVED, 36 nodes** |
| `[snd] ⊢ ⋁ itpAoth …` (no `s`) | **REFUTED** |
| `[amb, box, snd, s] ⊢ ⋁ itpAoth …` | `~` at 200 000 |

So `prop s` is exactly the missing ingredient — and `prop s` is derivable from the
ambient and the boxed component alone, which is §98's discovery specialised
(`BoxedS1b.s_of_amb_box`).  `boxed_onpath` composes the two.

Semantically: `snd = A@1(s::Γ,◯r)` yields, under `◯`, the implication
`E@0(s::Γ) ⇢ A@1(s::Γ,r)`, whose antecedent contains the atom `s`; the grown
ambient supplies `s`; so `A@1(s::Γ,r)` — which is `r` — follows at the
`⊳`-successor, and that is the target's goal clause.

### A note on the searcher, worth keeping

`[amb, box, snd, s] ⊢ target` is **not** found at 200 000 nodes while
`[snd, s] ⊢ target` is found in 36.  Adding *derivable* hypotheses cannot change
derivability, but it widens the search.  So the productive pattern is: find the
minimal hypothesis set that makes a cell searchable, pin that, and compose the
rest in Lean.  Three of this session's results were obtained that way.

### Where the descent now stands

All four branch shapes have a **closed on-path instance**:

| branch, at target budget `1` | status |
|---|---|
| floor, atom jump goal | **proved in general** (`∨`-free space) |
| floor, `⊃`-shaped jump goal | proved at two configurations |
| floor, **boxed** jump goal `◯A` | **proved at an on-path configuration** (§100) |
| fresh-antecedent goal | proved at three configurations incl. the deciding one |

and nothing in the descent is now known to be blocked.  What remains is
**generality**: one row is uniform in the configuration, three are finite sets of
instances.  That is a research problem of an ordinary kind — find the general
lemma each route is an instance of — rather than an obstruction with refutations
across it, which is what the session began with.

## §101 — §100's route is configuration-dependent: it does not extend to the branching space

A measurement, and a `REFUTED` rather than a `~`, so it is budget-independent.

§100 closes the boxed floor branch at `C = ◯r` on the one-γ-clause space `S1` by
supplying `prop s` — which the ambient and the boxed component yield (§98).  The
obvious generalisation is "atomic γ-head over a `∨`-free space", and the plan was an
induction on the defect, with `grownAmb_of_box` supplying the grown ambient at each
level and `itpA_atom_forces` doing the value conversion.

That plan is **not** available as stated.  On the two-γ-clause space `S2` — where the
grown context `s::Γ` still has a live γ-clause, so the analysis genuinely branches:

| sequent | verdict |
|---|---|
| `[snd, s] ⊢ ⋁ itpAoth "p" S2 3 1 G2 (◯r)` | **REFUTED** |
| `[snd] ⊢ same` | **REFUTED** |
| `[grownAmb, snd] ⊢ same` | `~` |
| `[grownAmb, snd] ⊢ its goal clause` | `~` |

So at `S1` the single atom `prop s` suffices and at `S2` it provably does not.  The
route of §100 uses the fact that at `S1` the grown context `s::Γ` is *saturated* —
every environment clause there is guard-dead — so `snd` collapses to something the
atom alone can drive.  With a second γ-clause alive that collapse does not happen.

### What this does and does not change

* §100 stands: `boxed_onpath` is a true, sorry-free theorem, and it is an on-path
  instance.  It is *one* instance.
* The **general** boxed row is open, and now known to be genuinely
  configuration-dependent rather than one uniform argument away.
* §98's `grownAmb_of_box`/`grownAmb_of_plain` are unaffected — they are general, and
  the `~` rows above say the search cannot decide the cell they feed, not that the
  cell is false.
* The proposed induction is not refuted either: it would supply the *grown ambient at
  each level*, which the `[snd, s]` row does not have.  What is refuted is the
  cheaper version of the route that uses only the atom.

### Standing summary, accurate

| branch, target budget `1` | status |
|---|---|
| floor, atom jump goal | **PROVED, general** (`∨`-free space) |
| floor, `⊃`-shaped jump goal | proved at two configurations |
| floor, boxed jump goal `◯A` | proved at one on-path configuration; general OPEN, route configuration-dependent |
| fresh-antecedent goal | proved at three configurations incl. the deciding one |

## §102 — the boxed goal clause remaps from a grown context (30 July)

`wip/atomForce.lean` §4.  PROVED sorry-free, general,
`[propext, Classical.choice, Quot.sound]`.

    boxGoal_remap :
      (∀ A B, A.or B ∉ S) → q ≠ p → (∀ Y ∈ Γ', Y ∈ S) →
      G4c Δ (itpE p S f (c+2) Γ')                                   -- grown ambient
      → G4c Δ ◯( E@c(Γ') ⇢ A@(c+1)(Γ', q) )                         -- clause at Γ'
      → G4c Δ ◯( E@c(Γ)  ⇢ A@(c+1)(Γ,  q) )                         -- clause at Γ

This is the heart of §100's route, extracted and proved for **arbitrary** `Γ`, `Γ'`.

`box_remap_free` reduces the remap to two conversions inside the box:

* the **guard** `E@c(Γ')`, which the grown ambient supplies by downward budget
  monotonicity — free, and the grown ambient itself comes from the ambient and the
  branch's own first component by §98;
* the **value** `A@(c+1)(Γ',q) ⊢ A@(c+1)(Γ,q)`, which is context *shrinking* and
  would be unsound in general — a table at a larger context has more disjuncts and
  is weaker.

The point is that at an **atom** goal it is not unsound: §91's `itpA_atom_forces`
turns the left side into `q` itself, and `q` is the goal clause of the right side at
*every* context.  So **the one step that appeared to need shrinking is exactly the
step the atom-forcing lemma licenses**, and there is no `Γ ⊆ Γ'` hypothesis at all —
the two contexts are unrelated.

### What is left for the boxed row

With `boxGoal_remap` and §98's `grownAmb_of_box`/`grownAmb_of_plain`, the boxed
branch reduces to: **reach the goal-clause disjunct of the second component at some
grown context.**  That is a traversal of the environment clause table one level down
— the same shape of work as §91's induction, and with the same two ingredients
available at every level (§98 supplies the grown ambient at each grown context, by
projection for ungated clauses and by firing for gated ones).

§101's refutation does not touch this: what it refutes is the cheaper route that uses
only the atom `prop s` and no grown ambient.

## §103 — the traversal must be shape by shape: a uniform "grown ambient" hypothesis is the ascent

An attempt at the §102 traversal was drafted and discarded, for a reason worth
recording.

The natural abstraction is to assume, once and for all,

    G4c Δ (itpE p S f (c+2) Γ')  →  Γ' ⊆ Γ''  →  G4c Δ (itpE p S f (c+2) Γ'')

— "the ambient at any larger context follows from the ambient".  That is **the
existential ascent**, in its pure context-growth form: `itpE` at a larger context has
strictly more conjuncts, so it is the *stronger* formula, and this is the hard
direction.  It is the statement `AmbGuardAscent` was about, and it must not be assumed
— using it would smuggle the refuted hypothesis back in under another name.

### What the structure actually gives, shape by shape

The grown ambient *is* available at each level, but differently per shape, and the
pattern is a structural match worth naming:

| context formula `F ∈ Γ'` | `itpA`'s disjunct grows to | how the ambient arrives |
|---|---|---|
| `A ∧ B` | `A::B::Γ'` | `itpE`'s clause for `F` **is** `E@(c+2)(A::B::Γ')` — project |
| `(prop q') ⊃ B` | `B::Γ'` | `itpE`'s clause is `E@(c+2)(B::Γ')`, or `prop q' ⇢ E@(c+2)(B::Γ')` — and in the latter case `itpA`'s own disjunct supplies `prop q'` as a conjunct |
| `(A ∧ B) ⊃ D`, `(A ∨ B) ⊃ D` | curried / split | project |
| `◯A ⊃ B` (gated) | `B::Γ'` | **fire** the ambient's γ-conjunct with the disjunct's first component — §98 |
| `(A⊃B) ⊃ D` (gated) | `D::Γ'` | same, with the jump conjunct |
| `◯χ` | `χ::Γ'` | `itpE`'s clause is `◯E@(c+2)(χ::Γ')` — **boxed**, and `itpA`'s disjunct for `◯χ` is boxed too, so the two pair up under `laxL` |

So in every shape the ambient arrives in exactly the form the disjunct can use —
unboxed where the disjunct is unboxed, boxed where it is boxed, and with the extra
antecedent supplied where `itpE` demands one.  That is not a coincidence: both tables
are generated from the same clause analysis of `F`, so their guards and their modal
depth agree by construction.

### The remaining obligation, stated exactly

> Traverse `itpAfull p S f (c+1) Γ' (◯q)` and, in each case, either apply
> `AtomForce.boxGoal_remap` (the goal clause) or obtain the grown ambient by the
> table above and recurse at strictly smaller defect.

Everything it needs is proved: `boxGoal_remap` (§102), `grownAmb_of_box` and
`grownAmb_of_plain` (§98), `itpA_atom_forces` (§91), `defect_lt_of_witness`.  What is
left is the case work — the same shape of task as §91's induction, which took ten
shapes and every guard branch.

## §104 — §103's table, proved: the grown ambient arrives shape by shape (30 July)

`wip/boxSnd.lean` (new).  Five lemmas, PROVED sorry-free, `[propext, Quot.sound]`.

§103 tabulated how the grown ambient arrives at each context shape, and warned that
the uniform version of that statement is the refuted ascent.  The table is now
theorems:

| lemma | shape | grows to | form |
|---|---|---|---|
| `grown_and` | `A ∧ B` | `A::B::Γ'` | the ambient's clause **is** the grown ambient |
| `grown_impAtom_pres` | `(prop q') ⊃ B`, `prop q' ∈ Γ'` | `B::Γ'` | ditto |
| `grown_impAnd` | `(A ∧ B) ⊃ D` | `A⊃(B⊃D) :: Γ'` | ditto (curried) |
| `grown_impOr` | `(A ∨ B) ⊃ D` | `A⊃D :: B⊃D :: Γ'` | ditto (split) |
| `grown_box` | `◯χ` | `χ::Γ'` | the grown ambient **under a `◯`** |

Each is a projection out of `itpEcls` — `itpE_succ`, then `andAll_elim` at the clause
for that context formula, with the guards discharged from the same hypotheses the
`itpA` disjunct carries.  Together with §98's two firing lemmas for the gated shapes,
every context shape now has its grown ambient available in the exact form the
corresponding `itpA` disjunct can use.

The last row is the one worth noticing: for `◯χ` the ambient arrives **boxed**, and
`itpA`'s disjunct for `◯χ` is boxed too, so the two pair under `laxL`.  That is not a
coincidence — both tables are generated from the same clause analysis of the context
formula, so their guards and their modal depth agree by construction.

### What is left

The assembly: the defect induction over `itpAfull p S f (c+1) Γ' (◯q)`, using
`boxGoal_remap` at the goal clause and these six lemmas (five here, plus §98) at the
environment clauses, with the truncation disjunct handled by `laxL`.  Every ingredient
is now a named, proved lemma; what remains is the case analysis that puts them
together, and the arithmetic of the fuel (the disjuncts sit one fuel down, so the
induction must quantify over the fuel inside the defect recursion, as §91's does).

## §105 — the boxed traversal assembled: four scoped obligations left (30 July)

`wip/boxSnd.lean`.  PROVED sorry-free, `[propext, Classical.choice, Quot.sound]`.

    boxSnd_reaches :
      (∨-free S) → q ≠ p → (S closed under ◯-subformula) →
      BoxCtxCase p S q → TruncCase p S q → ImpCase p S q → ZeroFuelCase p S q →
      ∀ d f c Γ Γ' Δ, defect S Γ' ≤ d → (Γ' ⊆ S) →
        ambient at Γ' → second component at Γ' → tgtClause p S f c Γ q

The recursion is on the **defect**, and what it proves outright is:

* **the goal clause** — by `boxGoal_remap` (§102), the mathematically substantive
  case, and the one that needed the atom-forcing lemma to license a context shrink;
* the **`∧`** environment family — by `grown_and` (§104) and the recursion;
* the vacuous families `prop q'`, `⊥`, and `∨` (the last excluded by `∨`-freeness).

The four hypotheses carry the remaining case work, each precisely scoped:

| obligation | what it is |
|---|---|
| `ImpCase` | the five `⊃`-headed environment families; their grown ambients are `grown_impAtom_pres`, `grown_impAnd`, `grown_impOr` and §98's two firing lemmas, so what is left is guard bookkeeping |
| `BoxCtxCase` | the `◯χ ∈ Γ'` family, where ambient and disjunct are *both* boxed and must be paired under `laxL` |
| `TruncCase` | the truncation disjunct, to be opened by `laxL` (legitimate — the conclusion is `◯`-shaped) and handled one level in |
| `ZeroFuelCase` | the fuel-`0` floor, where every component is `⊤` or `⊥` |

### One lemma worth noting on its own

    tgtClause_fuel_lift : tgtClause p S f c Γ q ⊢ tgtClause p S (f+1) c Γ q

The recursion returns the target one fuel down, so it has to be lifted — and both
conversions inside the box are **free, in opposite directions**: the guard converts
*down* in the fuel (`fuelE_le`, existential tables weaken as the fuel drops) and the
value converts *up* (`itp_fuel_mono`, universal tables weaken as the fuel rises).
That the two free directions are exactly the two needed is the same kind of structural
coincidence as §104's boxed/boxed pairing, and for the same reason.

### Where this leaves the boxed row

Before: one closed on-path instance and no general statement.  Now: a general theorem
whose hypotheses are four *case-analysis* obligations over a finite clause table, with
every mathematical ingredient already proved (`boxGoal_remap`, the six grown-ambient
lemmas, `itpA_atom_forces`, `defect_lt_of_witness`, `tgtClause_fuel_lift`).  None of
them is a statement that anything refutes — `ImpCase` in particular does *not* need the
ascent, because §98 fires the ambient instead.

### §105 addendum — `ZeroFuelCase` attempted and deferred

`ZeroFuelCase` is the easiest of the four obligations and is clearly true: at fuel `0`
every recursive component is `itpE p S 0 … = ⊤` or `itpA p S 0 … = ⊥`, so each
environment disjunct either *is* `⊥`, or is a conjunction with a `⊥` component, or is a
boxed guarded implication with value `⊥` and guard `⊤` — and that last shape yields any
`◯`-conclusion by `box_absurd`.

Two attempts at a uniform tactic for it were discarded.  The obstacles are both
mechanical and worth recording, since they will recur in the other three:

* the `.prop q'` environment clause is guarded by `q' = p ∧ ◯q = prop p`, and the
  second conjunct is false by constructor disjointness — but `split` treats it as an
  opaque decidable proposition and produces the impossible branch anyway, so it has to
  be killed by `simp` before the case split rather than after;
* `first | tac₁ | tac₂` does **not** reliably skip an alternative whose *elaboration*
  fails (as opposed to whose tactic fails), so `exact hin.elim` in a chain reports an
  error even when a later alternative would have applied.  Alternatives have to be
  ordered so the ones that can only succeed come first, and the catch-all has to be a
  tactic (`cases hin`) rather than a term.

Neither is mathematical.  `wip/boxSnd.lean` is left with the four obligations as
committed; `boxSnd_reaches` and the six grown-ambient lemmas are unaffected.

## §106 — `ZeroFuelCase` discharged; three obligations left (30 July)

`wip/boxSnd.lean`.  PROVED sorry-free, `[propext, Classical.choice, Quot.sound]`.

    zeroFuelCase : q ≠ p → ZeroFuelCase p S q

so `boxSnd_reaches` now needs three hypotheses, not four.

### The counting point that cost two attempts

§105's addendum recorded the tactic obstacles; the real one turned out to be arithmetic.
In `zeroFuelCase` the budget is `c + 1`, a **literal successor**, so `split` does *not*
branch on a gated clause's `match b with | 0 => … | b'+1 => …` — it reduces.  A gated
shape therefore has **one fewer `split`** than the same shape has when the budget is a
variable, which is the case in `AtomForce.atom_forces_aux`, where `b` is universally
quantified and the pattern that works there is `repeat' split`.

Getting that count wrong produces errors that read as type mismatches deep inside a
`rcases`, which is why two attempts at a "uniform" tactic went nowhere: the uniform
tactic was papering over a miscount.  Written shape by shape with the counts right, the
proof is routine — ten shapes, each three to eight lines, with four closers:

    byBot     ⊥ in hand closes anything
    byBotR    a conjunction with ⊥ on the right
    byImpBot  a conjunction whose left component is ⊤ ⇢ ⊥
    box_absurd  the boxed ◯(⊤ ⇢ ⊥)

This is worth recording as a general lesson for the three remaining obligations: **count
the splits from the clause table with the actual budget expression in hand**, not from
the shape of the table in the abstract.

### Remaining

| obligation | what it is |
|---|---|
| `ImpCase` | the five `⊃`-headed environment families; grown ambients proved (§§98, 104), guard bookkeeping left |
| `BoxCtxCase` | the `◯χ` family, ambient and disjunct both boxed, pair under `laxL` |
| `TruncCase` | the truncation disjunct, open by `laxL`, handle one level in |

## §107 — budget shift: the source's first components lift to what the ambient demands (30 July)

`wip/boxSnd.lean`.  Five lemmas, PROVED sorry-free, all first try.

A gated environment disjunct of `itpA p S f (c+1) Γ'` carries its first component at
budget **`c`**, while the matching conjunct of the ambient `E@(c+2)(Γ')` has its
antecedent at budget **`c+1`**.  So §98's move — firing the ambient with the disjunct's
own first component — needs a one-step budget shift, and the shift is **free**:

    shift_imp   : E@c(Γ) ⇢ A@c(Γ,X)      ⊢  E@(c+1)(Γ) ⇢ A@(c+1)(Γ,X)
    shift_box   : ◯(E@c(Γ) ⇢ A@c(Γ,X))   ⊢  ◯(E@(c+1)(Γ) ⇢ A@(c+1)(Γ,X))
    shift_plain : A@c(Γ,X)               ⊢  A@(c+1)(Γ,X)

free for the same reason `tgtClause_fuel_lift` is: the shift is *up* on the universal
side and *down* on the existential side, and both directions of `itp_budget_mono` point
that way.  This is the third time in the session that the two conversions a
`box_remap_free` needs turn out to be exactly the two free directions (§§104, 105, 107) —
the tables are built so that the guard and the value weaken oppositely, and every remap
of this kind rides that.

Composed with §98:

    grownAmb_of_box_shifted   : ambient + the disjunct's own boxed first component
    grownAmb_of_plain_shifted : ambient + the disjunct's own plain first component
                              ⊢  the grown ambient at `B::Γ`

so the gated shapes of `ImpCase` are now one recursion step away.

## §108 — correction: two of the three obligations were stated too strong (30 July)

`wip/boxSnd.lean`.  Still sorry-free; `boxSnd_reaches` unchanged in content.

`ImpCase` and `BoxCtxCase` as stated in §105 gave the prover the ambient, the disjunct
and the side conditions — and **no recursion**.  Both are steps of the defect recursion
(the `⊃`-headed families grow the context by `D`, the `◯χ` family by `χ`), so neither is
provable without it: they were unprovable as written, not merely hard.  Both now carry the
recursion hypothesis explicitly, at strictly smaller defect and one fuel down, exactly as
`boxSnd_reaches` supplies it.

That leaves the three obligations honest, and it isolates a structural difference worth
recording:

> `TruncCase` is **not** a step of the defect recursion.  The truncation disjunct's body
> is `⋁ others` at the *same* `Γ'`, so it is not smaller in defect and cannot be handed
> the recursion.

So the truncation needs either its own measure, or the **pairing** move `desc_of_oth`
uses for the truncation in the full-table descent — where the source truncation *commits*
the target truncation and the source box is opened against it, so the two truncations
cancel rather than one being consumed.  Which of the two applies here is open, and it is
the only one of the three obligations whose shape is not yet settled.

### Also from this pass

`set_option maxHeartbeats` had to go from 1 000 000 to 4 000 000 for `boxSnd_reaches`
once the obligations carried their recursion hypotheses — the statement's elaboration,
not the proof, is what costs.

## §109 — the grown-ambient table completed (30 July)

`wip/boxSnd.lean`: `grown_impAtom_fresh`, PROVED sorry-free, first try.

§103 tabulated six ways the grown ambient arrives; §104 proved five and §98 the two
gated ones.  The missing row was `(prop q') ⊃ B ∈ Γ'` with `prop q' ∉ Γ'` and `q' ≠ p`,
where the ambient's clause is not the grown ambient but an **implication**

    prop q'  ⇢  E@(c+2)(B::Γ')

— and the `itpA` disjunct for the same context formula is `prop q' ∧ A@b(B::Γ',C)`, so it
supplies the antecedent.  That is the one row of the table where the two tables' guards
genuinely differ (`itpE` demands the atom, `itpA` carries it), and it closes by firing.

So the table is complete: **every context shape now has its grown ambient available in
the form the corresponding `itpA` disjunct can use** —

| arrives as | shapes |
|---|---|
| the grown ambient outright | `A ∧ B`; `(prop q')⊃B` with the atom present; `(A∧B)⊃D`; `(A∨B)⊃D` |
| an implication the disjunct's own conjunct fires | `(prop q')⊃B` with the atom fresh |
| an implication the disjunct's own **first component** fires (after a free budget shift) | `◯A⊃B`, `(A⊃B)⊃D` |
| **boxed**, pairing with a boxed disjunct | `◯χ` |

and in each case what fires it is something the branch already has.  That is the whole
content of §98's observation, now checked at every shape.

## §110 — `ImpCase`'s six shapes, proved as lemmas (30 July)

`wip/boxSnd.lean`.  Six lemmas, PROVED sorry-free, all first try.

    impAnd_case, impOr_case, impAtom_pres_case, impAtom_fresh_case,
    gammaBox_case, gammaPlain_case

Each is three lines, because §§98, 104, 107 and 109 already did the work: take the grown
ambient from the table of §109, feed it and the disjunct to the recursion, lift the fuel
(§105).  `Step` abbreviates the recursion exactly as `boxSnd_reaches` passes it.

So `ImpCase` is now **pure membership bookkeeping** over proved lemmas — the clause
guards have to be unpacked and routed to the right one of the six, and nothing else.  With
§106's counting lesson (split from the clause table with the *actual* budget expression in
hand) that is a mechanical exercise.

### Where the boxed row stands

| piece | status |
|---|---|
| the traversal | **PROVED** (`boxSnd_reaches`) |
| its goal-clause case | **PROVED** (`boxGoal_remap`) |
| its `∧` case | **PROVED** (in the traversal) |
| its fuel-`0` floor | **PROVED** (`zeroFuelCase`) |
| the six `⊃`-headed shapes | **PROVED** as lemmas; `ImpCase` = routing them |
| `BoxCtxCase` (`◯χ`) | open; ambient available boxed (`grown_box`), pairs under `laxL` |
| `TruncCase` | open, and the one whose *shape* is unsettled (§108) |

Every mathematical ingredient of the boxed row is now proved.  What is left is one
routing exercise, one boxed pairing, and one question about the truncation's measure.

## §111 — a design point for `BoxCtxCase`: its recursion must be context-polymorphic

Attempting `BoxCtxCase` surfaced one more thing about its statement, recorded here rather
than half-implemented.

The `◯χ` case does its work **inside two boxes**: the grown ambient arrives boxed
(`grown_box`, §104) and the disjunct is boxed, so both are opened by `laxL` — legitimate,
since the conclusion `tgtClause` is itself `◯`-shaped — and the recursion is then applied
at a context *larger* than `Δ`.

So `BoxCtxCase`'s recursion hypothesis must quantify over the context:

    ∀ (Δ' : List PLLFormula) (Γ'' : List PLLFormula) (w : PLLFormula), …
      G4c Δ' (itpE …) → G4c Δ' (itpA …) → G4c Δ' (tgtClause …)

as `boxGoal_remap` and §98's lemmas already do.  `boxSnd_reaches` can supply that: its
`ihd` is context-polymorphic, and the fixed-`Δ` `step` it currently builds is a
specialisation of it.  `ImpCase` does *not* need this — its shapes never enter a box — so
the two obligations differ in this respect as well as in §108's.

The sketch of the proof, for whoever picks it up:

1. `G4c.cut` the boxed grown ambient in and `laxL` it, putting `E@(c+2)(χ::Γ')` in the
   context at the `⊳`-successor;
2. `box_open` the disjunct, firing its guard `E@(c+1)(χ::Γ')` from that by downward
   budget monotonicity (`ambE`);
3. apply the context-polymorphic recursion at `χ::Γ'`, whose defect is strictly smaller
   because `χ ∈ S ∖ Γ'`;
4. `tgtClause_fuel_lift`.

Every step is a lemma that exists.  What stopped this pass was the statement, not the
proof.

## §112 — `BoxCtxCase` discharged: two obligations left (30 July)

`wip/boxSnd.lean`.  PROVED sorry-free, first try once the statement was right.

    boxCtxCase : BoxCtxCase p S q

§111 diagnosed the statement: the `◯χ` family works inside two boxes, so its recursion
hypothesis has to be context-polymorphic.  With that corrected the proof is the four steps
sketched there, and it went through unchanged:

1. open the boxed grown ambient (`grown_box`, then `laxL` — legitimate, the conclusion is
   `◯`-shaped);
2. open the disjunct with `box_open`, firing its guard from the grown ambient by downward
   budget monotonicity;
3. recurse at `χ :: Γ'`, of strictly smaller defect because `χ ∈ S ∖ Γ'`;
4. `tgtClause_fuel_lift`.

**So `boxSnd_reaches` now needs two hypotheses**, and they are of very different kinds:

| obligation | kind |
|---|---|
| `ImpCase` | **routing**: unpack the clause guards and dispatch to one of the six lemmas of §110.  No mathematics left. |
| `TruncCase` | the one open *question*: the truncation's body is `⋁ others` at the same context, so it is not a step of the defect recursion and needs either its own measure or `desc_of_oth`'s pairing move (§108). |

### The pattern of the last few sections, worth naming

Three obligations in a row (§106 `ZeroFuelCase`, §111–112 `BoxCtxCase`, and §108's
correction to `ImpCase`) turned out to be **statement** problems, not proof problems: a
miscounted `split`, a missing context quantifier, a missing recursion hypothesis.  Each
looked like a hard proof until the statement was right, and then went through in a few
lines or first try.  That is worth remembering for `TruncCase`: before looking for a
measure, check that what is being asked for is what the traversal can supply.

---

## §34 (2026-08-03) — the RN classification is mechanised: im h = rungs ∪ {⊤}, and the complement is infinite with no caveat

`wip/rnClassify.lean` (with `wip/rnClass.lean` from yesterday) completes all five
stages of `docs/rn-classification-plan.md`.  The theorem, in full:

    image_classification : for every ◯-free formula A whose only variable is p,
        (∃ n, Interd (A[p := ◯⊥]) (rnSub n))  or  Interd (A[p := ◯⊥]) ⊤.

Method: classify semantically (`cls : PLLFormula → UpCode` computes the ladder
truth set of A by structural recursion through three fully-tabulated Heyting
operations on up-set codes), then *derive* each table row (`meet_interd`,
`join_interd`, `imp_interd`: 48 rows, each hard side a ≤ 4-step modus-ponens
composition through the Rieger–Nishimura recursion, each easy side rung order
through the decision procedure `rnSub_order`), then glue by the congruence
lemmas in the structural induction `rn_classification`.

Consequences, all now UNCONDITIONAL (the standing caveat of §33 is gone):
`q5 ∉ im h` (`q5_off_image`), `◯q11 ∉ im h` (`boxq11_off_image`),
`chainF k ∉ im h` for every k ≥ 2 (`chain_off_image`), and
`complement_infinite_final`: **RN(◯,{}) ∖ im h is infinite** — the boxed odd
rungs are pairwise distinct and all off the image.  Everything sorry-free,
audits pinned at `[propext, Classical.choice, Quot.sound]`.

Bonus: `Interd q11 (rnSub 7)` is now an *instance* of the classification
(`cls (¬¬p ∨ (¬¬p ⊃ p)) = odd 3` by `decide`), identifying `◯q11 ≡ chainF 3`
without a hand derivation — the classification doubles as a decision procedure
for interderivability on the whole ◯-free one-variable fragment.

---

## §35 (2026-08-03) — RN(◯,{}) has UNBOUNDED WIDTH: the collapse statements form an infinite antichain

`wip/gapWidth.lean`.  The family, generalising the dictionary class `q8`
level by level:

    gap k := ◯(rnSub (2k+1)) ⊃ rnSub (2k+1)          gap 1 ≡ q8 (gap_one_q8)

**width_infinite**: the `gap k` for `k ≥ 2` are pairwise non-interderivable
(indeed pairwise ⊬-incomparable, `gap_incomparable`) — an ℕ-indexed
antichain, so the width question is settled: INFINITE, not bounded.

One new semantic computation only: on the edged lift `cmE m` (the §34-era
model with the single extra constraint edge `(m+3) ⇝ 0`),

    T(chainF k) = [0,k] ∪ { m+3  if m+1 ≤ k }        (cmE_chainF)

so `gap k` fails in `cmE m` exactly when `k ∈ {m+1, m+2}` and holds at
every world otherwise; choosing the edge level per pair (m = k−2 when
j = k+1, else m = k−1) refutes `gap j ⊢ gap k` by soundness.

The new classes are genuinely new: off im h (`gap_off_image`, via the
mechanised classification), distinct from every chain class
(`gap_not_chain` — on the plain lift `gap k` is forced everywhere while
chains/rungs have bounded truth sets), and pairwise distinct.  Picture of
RN(◯,{}) so far: im h ≅ RN({p}) ∪ {⊤} (8 drawn classes + ⊤), an infinite
strictly ascending chain of boxed odd rungs sprouting at q5/q12/◯q11, and
an infinite antichain of their collapse statements sprouting at q8.  Open:
whether q9/q13/q14/w15 seed further families of the same kind.

Debug note: omega silently dropped equations at type `ladder.W` (defeq ℕ
but syntactically a projection) — same family of quirk as §34's `→ False`
finding; fix is a `∀ y : Nat` annotation in the statement.

---

## §36 (2026-08-03) — q9, q13, q14 each seed an infinite family; the gap antichain matches nothing known; the connectivity map; the t-notation

All PLL (`Deriv`/`Interd` = LaxND throughout; no PCLL notion appears in
§§34–36).  `wip/families.lean` + `wip/connect.lean`.

**New canonical notation** (Lean bridges pinned; old name in brackets):
t n = class of rung n [q0=t0, q2=t1, q3=t2, q4=t3, q6=t4, q7=t5, q10=t6,
q11=t7]; ⊤ [q1]; c k = ◯t(2k+1) [q5=c1, q12=c2, ◯q11=c3] — chain;
g k = c k ⊃ t(2k+1) [q8=g1] — antichain; s k = c k ∨ t(2k+2) [q9=s1] —
chain (sC_le/sC_strict); r k = t(2k+4) ⊃ c k [q14=r1] — antichain
(rC_incomparable, ALL j ≠ k ≥ 1); ◯g k [q13=◯g1] — antichain
(bg_incomparable).  w15 = g1 ∧ t6 (w15_form).

**The probes**: s-family strict chain, off-image, not a chain-class
(sC_off_image, sC_not_chain — the plain truth sets of sC k and
chainF (k+1) agree, so the edge separates); r-family and ◯g-family
antichains, off-image (rC_off_image, bg_off_image, bg_not_chain).

**The gap antichain is new**: gap_not_q9/q13/q14/w15 close the last
possible coincidences (with gap_not_rung/top/chain and gap 1 ≡ q8, no
known class matches any gap k).

**Connectivity** (connect.lean): t(2k+1) ⊢ g k (weakening) and
g k ⊢ ◯g k, c k ⊢ s k, s j ⊢ c k (j<k), t(2k+3) ⊢ s k — all en masse;
c k and g k incomparable at every level; and the dictionary's low-level
arrows are LEVEL-1 ACCIDENTS: q5 ⊢ q10, q7 ⊢ q8, q6 ⊢ q8 are true
(d_q7_q8, d_q6_q8 derived; q5⊢q10 pinned) but their schemas die from
level 2 (chain_not_le_even, odd_not_le_gap, even_not_le_gap,
chain_not_le_odd).  En-masse programme per Matthew's directive: strict
families replace piecemeal cells; covering (⋖) statements stay relative
to the known inventory.

---

## §37 (2026-08-03) — new seeds: two identities and a fourth family (all PLL)

`wip/seeds.lean`.  Three candidate seeds settled, one left open:

1. **◯(s k) ≡ c (k+1)** (`box_sC`): boxing the s-chain folds it into the
   c-chain one level up.  Consequence `boxq9_q12`: the PLL value of the
   OPEN table cell ◯q9 is **q12** — while PCLL collapses ◯q9 to q9
   (the harvested cell), so this is a sharp PLL/PCLL divergence point.
2. **c k ∧ g k ≡ t(2k+1)** (`chain_meet_gap`, axiom-free): chain and gap
   are complementary over the anchor rung — the comb closes.  Also
   c k ⊢ ◯g k (`chain_le_bg`).
3. **w15 seeds a family with the EVEN-RUNG order type**:
   wC k := g k ∧ t(2k+4) (wC 1 ≡ w15); pairwise distinct, off the image
   (`wC_off_image`), ordered exactly like the even rungs — wC j ⊢ wC k
   iff j = k or j+2 ≤ k (`wC_le`/`wC_strict`/`wC_succ_not_le`): a THIRD
   order type among the families (neither chain nor antichain).
4. OPEN: second-order gaps ◯g k ⊃ g k — same truth set as g k on every
   model in the edged-lift family; separating them needs a new model.

---

## §38 (2026-08-03) — the second-order gap COLLAPSES (en masse); the co-gaps are new; unit rows closed

`wip/gap2.lean`, all PLL.  The "new model construction" hunt for
◯g k ⊃ g k ended in a theorem instead: on ANY lift of the ladder
skeleton a world forcing ◯t(2k+1) automatically forces ◯g k (each
box-witness lands in [0,k] ∪ F, and both force g k) — and that
blindness syntactifies into the derivation:

    imp_gap_collapse : c k ⊢ X  →  (X ⊃ g k) ≡ g k        [propext only]
    gap2_collapse    : (◯g k ⊃ g k) ≡ g k
    c_imp_gap        : (c k ⊃ g k) ≡ g k

The DUAL does not collapse: dC k := g k ⊃ c k is strictly above c k
(dC_not_le_chain, via cmE (k−2) at world k+3 where every cone point
either fails g k or sits low enough to force c k), matches no rung,
is off the image (dC_off_image) — a NEW family, order structure open.
Also chain_le_rC (c k ⊢ r k).

Unit rows: Matthew's ⊤ ∧ φ ≡ φ observation implemented en masse —
eleven ∀φ unit-law lemmas (top_and_interd … bot_imp_interd) close
every ⊤/⊥-row cell of the operation tables for every present and
future class (negation cells φ ⊃ ⊥ deliberately excluded — genuine
content).  The v9 explorer fills these cells algebraically.

---

## §39 (2026-08-03) — the UI-obstruction hypothesis, tested (all PLL)

`wip/uiObstruct.lean`.  Matthew's hypothesis: the rich structure of
RN(◯,{}) (in particular an infinite antichain) may point at semantic
obstructions to uniform interpolation.  The bridge: ∃p.φ for
one-variable φ must be the LEAST variable-free consequence of φ — an
element of RN(◯,{}); the consequence set is a filter, so ∃p.φ exists
iff the filter is principal; dually for ∀p.φ and the antecedent ideal.
This is the Ghilardi–Zawadowski mechanism for UI failure in S4-like
logics.

STRUCTURALLY CONFIRMED — both engines exist:
* t3_below_gap: the gap antichain has common floor t3, so the antichain
  alone does NOT obstruct (finite meets exist); but
* Gmeet_strict / Gmeet_desc_strict: the partial meets g1 ∧ … ∧ g(n+1)
  descend STRICTLY FOREVER — the first infinite strictly descending
  chain proved in RN(◯,{});
* the c-chain provides the ascending engine, and chain_cofinal_not_rung
  plus the family lemmas show no known class but ⊤ bounds it.

REDUCTION: no_post_interp_schema / no_pre_interp_schema (axiom-free!):
UI fails iff a single witness exists — a one-variable φ entailed by
every chainF k (dually entailing every gap k) with no variable-free
formula interpolating between the family and φ.  That witness question
is exactly where the syntactic UI hunt stalled from the other side;
both outcomes are live, and the schemas record what each would need.

---

## §40 (2026-08-03) — the witness hunt: near-witness, collapse lever, im h closed (all PLL)

`wip/witness.lean`.  Toward constructing-or-refuting the UI witness:

* **L climbs and has width**: t5 ∈ L (t5_in_L, via the level-1 accident
  q7 ⊢ q8) and w15 ∈ L (w15_below_all_gaps — the k = 2 case descends
  inside the box through t6 = t5 ⊃ t3); t3 < w15 strictly
  (t3_le_w15, w15_not_le_t3); t5 and w15 incomparable, t6, t7 ∉ L.
* **phi1 := ◯p ⊃ ◯(p ∧ t3)** is a NEAR-witness: c 1 ⊢ phi1
  (c1_le_phi1) but c 2 ⊬ phi1 (c2_not_le_phi1, on the new model cmP =
  plain lift with all atoms true everywhere; cmP_agree transfers
  atom-free forcing).  Yet phi1 satisfies the OTHER schema hypothesis:
  bound_collapse (the substND lever at p ↦ ⊤): any variable-free
  χ ⊢ phi1 entails c 1, so no variable-free bound of the c-chain
  entails phi1 (phi1_hU) — else c 2 ⊢ c 1.
* **Within im h the ∀-side closes**: inimage_chain_bound_top — any
  image class bounding the whole c-chain is ⊤ (classification +
  rung_cofinal).  A witness-blocker must therefore be OFF-IMAGE
  variable-free; every known off-image family is already excluded.

Status: witness OPEN, reduced to (a) a one-variable bound of the
rung-chain beyond theorems (the bind mechanism's regress), vs (b) the
full off-image version of "only ⊤ bounds the chain".

---

## §41 (2026-08-03) — the rung chain has NO nontrivial bound: the ∀-side of the UI attack is CLOSED (delegated probe, verified, landed)

`wip/rungbound.lean`.  For EVERY φ: (∀k, rnSub(2k+1) ⊢ φ) → ⊢ φ
(chain_bound_is_theorem; likewise c_chain_bound_is_theorem), so
pre_interp_schema_vacuous: the ∀-side obstruction schema can never be
instantiated.  Ingredients: rank_bound (finite model ⇒ every world
forces an odd rung of rank ≤ 2·|up-set|; pure ∨/⊃ induction with the
vacuous-implication trick at clusters) + the repo's OWN finite model
property (PLLFiniteModel.lean) — which also proves C1 outright and
refutes the earlier claim that no semantic route to derivability
existed.  Corroborated by a kernel-checked 6-world rank computation
and a 690-model scan.  Audits pinned, sorry-free.  All weight now on
the ∃-side (Gmeet descent + landing ideal L).

---

## §42 (2026-08-04) — the ∃-side hunt opened: monad-escape reformulation, witness constraints, two probes launched

ui-attack.md new section.  hg unfolds to [φ, ◯t(2k+1)] ⊢ t(2k+1): the
witness is a uniform monad-escape along the odd rungs.  Derived
constraints (composites of pinned lemmas, being pinned): the witness
may entail NO rung (φ ⊢ t(2K+1) puts χ* = g1 ∧ … ∧ g(K−1) ∧ t(2K+1)
into F(φ) ∩ L; even rungs via the w15 mechanism, general version
conjectured) and must dodge every variable-free instance of itself
(Deriv.substP' puts each φ[p↦ψ] into L; hence p occurs
non-positively).  The ∀-side killer does NOT dualise: the mirror kill
needs the gap meet ATTAINED at a variable-free χ₀ forced at every
all-gaps world, but plain_forces_gap + bounded traces of t1..t5, w15
refute attainment at every known member of L; sole loophole = an
unknown ladder-valid member of L.  Probes (delegated, background):
(1) floor probe — edge-stability ⇒ every χ ∈ L has bounded ladder
trace ⇒ meet unattained (or the refuting floor); (2) witness sweep —
bounded one-variable enumeration under the constraint filters,
PLLSearch two-sided verdicts.

---

## §43 (2026-08-04) — the floor probe landed: THE GAP MEET DOES NOT EXIST (delegated, verified, landed)

wip/floor.lean.  Edge-stability machinery (cmE_agree_below: the edged
lift differs from plain only in the lax edges leaving m+3, so they
agree at all y ≤ m+2; plain_trace_dichotomy: every formula's ladder
trace is everything or bounded; edge_stability: past a
formula-dependent bound the two lifts agree AT the edge world — the
◯-clauses differ by one conjunct, killed by the dichotomy) gives
L_bounded: ANY χ entailing every gap has bounded plain trace — no
atomFree hypothesis, so it covers one-variable formulas too.
Corollaries: no_ladder_valid_lower_bound, gap_meet_not_attained,
no_lower_bound_above_odd_rungs — the FMP mirror of the ∀-side kill is
PROVED impossible.  New derivation lemmas: even_rung_gap (exact
threshold t(2a+2) ⊢ g k for k ≥ a+1), wC_gap_step (generalised w15
box-descent g(j+1) ∧ t(2j+6) ⊢ g(j+2)).  Headline: Wit b :=
Gmeet b ∧ t(2b+6) ∈ L with trace ∋ b+3, so a glb would have unbounded
trace: gap_no_glb / L_no_greatest — {g k} has NO greatest lower bound
among ALL formulas and L has no greatest element.  Gmeet provably has
no floor.  Not yet a UI refutation: the witness (F(φ) ∩ L = ∅) is
still OPEN, and L_bounded warns that hL countermodels cannot come from
the plain ladder (a witness also dies deep there) — edge models with
tuned valuations are the natural family.  Audits pinned, sorry-free,
all PLL.

---

## §44 (2026-08-04) — witness sweep EMPTY; the filters are now theorems; the collapse conjecture (delegated sweep, verified, landed)

wip/wlanding.lean + harnesses wip/wsweep.lean, wip/wscout.lean (exes
wsweep/wscout).  Zero survivors, zero certified near-misses.  Filters
as theorems: rung_kills/rung_blocks_schema (a gap-entailing φ that
entails ANY rung entails Ufam m = Gmeet m ∧ rnSub m ∈ L: hL dies —
the no-rung constraint exact at every index); inst_in_L /
no_theorem_instance / self_instance_kills (every variable-free
instance of a candidate lies in L; entailing one's own instance is
fatal — the filter that killed every hand design); Vf n = Gmeet n ∧
t(2n+4), a lower no-descent family in L.  Sweep: size ≤ 8 exhaustive
(26,032): all 2,653 g1-entailers entail a rung (◯⊥ 2070 / t2 503 /
t3 6 / t4 74); clause-pool (9,537 over 120 clauses): only gap2-carried
shapes reach g1∧g2, p contributing nothing; 34 hand designs all die at
the self-instance filter.  Frontier fact pinned by hand:
gap_two_le_one — g 2 ⊢ g 1 (so the antichain starts at k = 2; g1 < g2
strict via gap_one_not_le_two; g k ⊢ g 1 for k ≥ 3 OPEN).  NEXT
TARGET, the collapse conjecture (OPEN): with ρ(v) = min rung rank,
β(v) = min ◯-rung rank (β ≤ ρ), hg says ρ = β hereditarily above
φ-worlds; conjecture: one-variable φ enforcing this must entail a
rung — then rung_kills makes the ∃-side schema VACUOUS at 1 pv, both
sides of the UI attack close, and the strongest known obstruction is
neutralised (gap_no_glb still standing as pure structure).  Delegated
probe launched.

---

## §45 (2026-08-04) — the COLLAPSE THEOREM is PROVED: the ∃-side of the UI attack closes

wip/collapse.lean (new, sorry-free, `[propext, Classical.choice,
Quot.sound]` throughout).  The §44 target is now a theorem, and with no
one-variable hypothesis:

    collapse : (∀ k, 1 ≤ k → Deriv [φ] (gap k)) → ∃ m, Deriv [φ] (rnSub m)

Composed with the pinned rung filter this gives the headline

    post_interp_schema_vacuous :
      (∀ k, 1 ≤ k → Deriv [φ] (gap k)) →
      ¬ (∀ ψ, atomFree ψ = true →
           (∀ k, 1 ≤ k → Deriv [ψ] (gap k)) → ¬ Deriv [φ] ψ)

— the ∃-side obstruction schema `no_post_interp_schema` has jointly
contradictory hypotheses at the gap antichain, exactly as
`pre_interp_schema_vacuous` (wip/rungbound.lean) killed the ∀-side.
Also `L_eq_union_Ufam`: `φ ⊢ g k (k ≥ 1) ↔ ∃ m, φ ⊢ U m`, i.e. the
landing ideal is the union of the principal ideals of the variable-free
rung companions.  Both UI obstruction routes through this antichain are
now closed; `gap_no_glb` still stands as pure order structure.

The proof is semantic, in four moves.  RANK: in a finite model
`ρ w = min {k : w ⊩ t(2k+1)}` exists (`exists_rung_of_finite`), is
antitone, and `ρ w ≤ k ↔ w ⊩ t(2k+1)`.  RANK DESCENT (`rho_descent`):
`ρ u = n ≥ 2` gives `v ≥ᵢ u` with `ρ v = n−2` (read off
`t(2n−2) = t(2n−3) ⊃ t(2n−5)`).  EDGE SURGERY (`surgery`,
`surg_cotype`, `surg_force`, `surg_rung`): with the co-type
`S v = {B ∈ Φ : some Rₘ-successor of v forces B}` for a
subformula-closed `Φ ∋ ⊥, φ`, a *descent map* `x` (for all `v ≥ᵢ u`:
`v Rᵢ x v`, `S (x v) ⊆ S v`, `ρ (x v) < ρ u`) lets one add the
`Rₘ`-edges `{(z,y) : ∃ v ≥ᵢ u, z Rₘ v ∧ x v Rₘ y}` — the co-type
condition makes them invisible to every `Φ`-formula and (via `⊥ ∈ Φ`)
to `◯⊥`, hence to every rung — while `u` now `Rₘ`-sees rank
`< ρ u`, so `gap (ρu−1)` FAILS at `u` though `u ⊩ φ`: contradiction
with hg.  PIGEONHOLE: hence above every `φ`-world of rank ≥ 2 sits a
*rigid* world of the same rank (`exists_rigid`); iterating rank descent
and rigidity builds `T+1` rigid worlds `g 0 ≤ᵢ … ≤ᵢ g T` with
`ρ(g a) + 2a = ρ w` (`rigid_chain`), and with `T = 2^|Φ|` two share a
co-type — contradicting rigidity of the lower-indexed one.  So
`ρ w < 2·2^|Φ| + 2` at every `φ`-world (`rho_bounded`), and the FMP
plus deduction (`countermodel_of_not_deriv`) turns that into the
derivability.

The `cmE` edge model of wip/gapWidth.lean is exactly an instance of the
surgery (edge `(m+3) ⇝ 0`), which is why `gap_fails` reads like the
general mechanism.  Cross-check `collapse_bound_not_uniform`: the rung
index CANNOT be bounded uniformly in `φ` (else `Wit M`, forced at
plain-ladder world `M+3`, would entail a rung of index ≤ M), so the
exponential dependence on `|Sub φ|` is forced by `gap_no_glb`, not an
artefact.

---

## §46 (2026-08-04) — the GZ shape formalised family-generally; the analogy's exact verdict pinned

wip/gzSchema.lean.  no_post_interp_schema_family /
no_pre_interp_schema_family: the Ghilardi–Zawadowski obstruction
shape for an ARBITRARY ℕ-indexed variable-free family D (axiom-free;
the schema needs no order structure on D — chains/antichains only
make hL plausible, never run the argument).  gap_family_instance:
the campaign's schema is the D = gap (k+1) instance.
gz_gap_uninhabited / gz_chain_uninhabited: at the gap family and the
c-chain the schemas' hypotheses are jointly contradictory (collapse,
rungbound restated in family indexing).  Verdict on the 2026-08-03
"same conditions as GZ" observation: TRUE at the ambient level
(descent, floorlessness, width — all pinned), REFUTED at the filter
level (no instance can fire at these families).  Literature anchor
recorded in the docstring: the S4 witness B = p₁ ∧ □(p₁→◇p₂) ∧
□(p₂→◇p₁) ∧ □(p₁→q) ∧ □(p₂→¬q) (GZ 1995; Bílková thesis §3.1) lives
on a two-element cluster realising infinite q-alternation in a
finite model — the structural device intuitionistic heredity forbids,
which is why collapse holds in PLL and fails in S4.

---

## §47 (2026-08-04) — THE PIVOT: proving last-variable UI; substitution covers; ◯-free ∃p PROVED (delegated, verified, landed)

wip/postui.lean (1607 lines, sorry-free, pinned).  Method =
SUBSTITUTION COVERS: inst θ φ := φ[p := θ]; inst_below / inst_above
([propext, Quot.sound]) put every variable-free instance below F(φ)
and above I(φ), so ∃p exists whenever φ ⊢ ⋁ instances over a finite
variable-free pool S (HasCover; postInterp_of_cover), and ∀p whenever
⋀ instances ⊢ φ (HasMeetCover; preInterp_of_cover).  CoverConj :=
every 1-pv φ has a cover — THE remaining gap to last-variable ∃p.
PROVED subclasses: polarity-pure (subst_mono; UI_of_pure — both
quantifiers, θ ∈ {⊤,⊥}); THE ◯-FREE 1-pv FRAGMENT, ∃-side
(postInterp_of_boxFree — one-element cover; ingredients:
force_inst_congr (axiom-free, fully general: p ↔ θ interchange above
m transfers to A ↔ A[p:=θ], ◯-clause stays in the cone since
Rₘ ⊆ Rᵢ), evalCl two-valuedness, non-fallible-witness case split).
Calculus: post/preInterp_self/_unique/_congr, postInterp_or/andClosed,
preInterp_and/impClosed.  Pinned instances: ∃p.p = ⊤, ∀p.p = ⊥,
∃p.◯p = ⊤, **∀p.◯p = ◯⊥** (July's stabilisation probe now a theorem),
∃p.(◯p ⊃ p) = ⊤, **∃p.(p ∧ (p ⊃ t3)) = t3** (a genuine rung),
**∃p.((p ⊃ ◯⊥) ∧ ¬¬p) = ¬¬◯⊥** (mixed polarity, cover θ = ◯⊥).
REFUTED: the Boolean pool {⊤,⊥} does not suffice
(phiMix_no_boolean_cover, model M3); **MeetCoverConj FALSE**
(wemP_no_meetCover at p ∨ ¬p: two-world model N whose worlds the
variable-free fragment cannot separate, N_uniform) — yet
**∀p.(p ∨ ¬p) = ⊥ EXISTS** (preInterp_wemP) via the DOUBLING
construction dbl C (W × Fin 2; dbl_transfer: variable-free formulas
cannot see the second coordinate), so the ∀-side method is strictly
one-directional while UI itself stands untouched.  OPEN: CoverConj;
sticking point named exactly — the ◯-free proof upgrades "instance
forced at a non-fallible world ≥ᵢ w" to "provable" by two-valuedness,
unavailable in RN(◯,{}); the general cover needs the instance forced
AT w, where the collapse machinery (co-type pigeonhole, rho_bounded,
surgery) is the designated tool, with force_inst_congr as interface.


---

## §48 (2026-08-04) — REFUTED: CoverConj.  The substitution-cover method fails on the ∃-side too

wip/coverfail.lean (sorry-free, pinned) + wip/coverprobe.lean,
wip/interpprobe.lean (compiled probes).  §47's remaining gap is now
CLOSED — negatively.

    φ★ = ((◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)) ∧ ¬¬p     has NO variable-free
    substitution cover:  phiStar_no_cover,  hence  coverConj_false.

Countermodel M4 (four worlds): 0 ⊑ 1 ⊑ 2 ⊑ 3, Rₘ = id ∪ {(x,3) : x ≠ 0},
F = {3}, V(a) = {2,3}.  Here ‖◯⊥‖ = {1,2,3} and ‖p‖ = {2,3} is squeezed
STRICTLY between ‖⊥‖ and ‖◯⊥‖; the crux is M4_swap — worlds 1 and 2
satisfy the same VARIABLE-FREE formulas (1 sees 2 intuitionistically but
not modally, and above 1 the ◯-clause only reports the fallible top) —
so ‖p‖ is undefinable.  φ★ holds at the root and every instance
φ★[p := θ] fails there (M4_inst_fails): if θ reaches world 1 then
◯⊥ ⊃ θ holds at 0 and the first conjunct would force ◯⊥ at 0; if not,
θ lives only on the fallible world and ¬¬θ fails at 0.

So the method is incomplete on BOTH sides (∀: wemP_no_meetCover, §47).
UI itself is untouched: φ★ ⊢ ¬¬◯⊥ (phiStar_nnbox), φ★ ⊬ ◯⊥, φ★ ⊢ phiMix
(φ★ strengthens §47's phiMix, which HAS the cover [◯⊥]; the added clause
(◯⊥ ⊃ p) ⊃ ◯⊥ is exactly what kills θ = ◯⊥ and everything above it,
while ¬¬p kills everything below).

Also PROVED here: hasCover_iff_semCover — covers are a statement about
VALUATIONS (soundness + FMP); force_inst_top and force_inst_bot — the
two cases the method handles in FULL generality (w ⊩ p ⟹ w ⊩ φ[p:=⊤];
p only fallibly true above w ⟹ w ⊩ φ[p:=⊥]), so any counterexample must
live in the INTERMEDIATE case, and M4_intermediate pins that φ★'s does.

NEXT QUESTION, now the live one: does ∃p.φ★ exist, and is it ¬¬◯⊥?
postInterpPhiStarIsNNBox_iff reduces it to MINIMALITY alone (every
variable-free χ with φ★ ⊢ χ follows from ¬¬◯⊥).  Two findings point the
way.  (i) The cheap route is DEAD: M3v_root_nnbox + M3v_phiStar_fails —
the three-world M3 frame forces ¬¬◯⊥ at its root yet φ★ fails there
under EVERY valuation of p, so a proof must STRETCH the model (M4 is M3
with the ◯⊥-floor split in two), not re-value it; the dbl construction
of §47 is the template.  (ii) Probe evidence FOR the candidate: over all
rooted models with ≤ 5 worlds (28 639 models), the variable-free root
TYPES realised at ¬¬◯⊥-roots and at φ★-roots coincide exactly (2 types,
dictionary of 18 including rungs t1..t10), so no dictionary formula
separates φ★ from ¬¬◯⊥; 845 of the 8 750 ¬¬◯⊥-roots at n = 5 are
"deficient" (no valuation works there), all of the M3 shape.

Probe method (wip/coverprobe.lean, exhaustive and cap-free at n ≤ 5):
for each rooted model compute D(C) = truth sets of variable-free
formulas (closure of {F} under ∧,∨,⊃,◯), then for each undefinable
valuation U search the subalgebra of A_U × ∏_{d∈D} A_d generated by
p ↦ (U, d₁, …, d_k) for an element that is the whole model in
coordinate 0 and proper in every other — i.e. ALL formulas up to
semantic equivalence, not a sample.  Verdict: n ≤ 3 none; n = 4 four
hits (φ★ and one variant); n = 5, 2 548 hits over 69 834 (model, U)
pairs, max closure 164 (no cap hit).  The phenomenon is generic, not an
accident of one model.

---

## §49 (2026-08-04) — ∃p.φ★ = ¬¬◯⊥ PROVED; the STRETCH method; MixedCoverConj is the new live reduction (delegated, verified, landed)

wip/phistar.lean (737 lines, sorry-free, pinned).  VERDICT (A):
postInterp_phiStar : IsPostInterp phiStar (¬¬◯⊥) — F(φ★) is
PRINCIPAL; φ★ is NOT a UI counterexample; route (B) closed at φ★
with no family table needed.  Non-triviality pinned (value neither ⊥
nor ⊤).  THE CONSTRUCTION: `stretch C` = GUARDED doubling on
C.W ⊕ C.W — upper copy of x reachable from inl x exactly when
x ⊩ ◯⊥ (the guard is the entire content; unguarded dbl destroys
φ★'s first conjunct); V(p) = upper layer ∪ F, so on the ground
layer ¬p means ¬◯⊥.  Driving lemmas: stretch_transfer (variable-free
formulas cannot see the split, [propext]) and stretch_force_phiStar
(u ⊩ ¬¬◯⊥ ⇒ inl u ⊩ φ★); minimality by countermodel_of_not_deriv +
soundness through the stretch.  GENERALISATION: the stretch is a
TRANSLATION — tr : PLLFormula → PLLFormula × PLLFormula with
Lo p = ⊥, Up p = ⊤, Lo(A⊃B) = (Lo A ⊃ Lo B) ∧ (◯⊥ ⊃ (Up A ⊃ Up B)),
Lo ◯A = ◯(Lo A) ∧ (◯⊥ ⊃ ◯(Up A)); stretch_tr (axiom-free) computes
forcing on both layers; stretch_below: every variable-free
consequence of φ follows from Lo φ — a NON-SUBSTITUTIONAL lower
bound on F(φ), parallel to inst_below; postInterp_of_stretch (no
one-variable hypothesis needed).  stretch_beats_cover: φ★ has a
stretch cover but no substitution cover.  STATUS BOARD: CoverConj
REFUTED (φ★); MeetCoverConj REFUTED (p ∨ ¬p); StretchCoverConj
REFUTED (at p: Lo p = ⊥); **MixedCoverConj OPEN** — φ ⊢ Lo φ ∨
⋁ instances — survives all three refutations
(hasMixedCover_phiStar, hasMixedCover_pv) and is now the live
reduction of last-variable ∃p (postUI_of_mixedCoverConj).  Next
probes named: stretches along ‖◯χ‖ for arbitrary variable-free χ
(a family of lower bounds Lo_χ), n-fold stretches (an ascending
tower); a MixedCoverConj counterexample must defeat every member.
∀-side untouched (no co-stretch by symmetry: the guard uses ◯⊥
essentially).

## §50 (2026-08-04) — REFUTED: MixedCoverConj, and GuardedMixedConj with it — φ♦ in the DIAMOND (delegated, verified, landed)

wip/mixedprobe.lean (probe), wip/guardstretch.lean, wip/mixedfail.lean
(both sorry-free, pinned).  VERDICT: **mixedCoverConj_false** and
**guardedMixedConj_false**.  §49's live reduction is dead, and so is
its own weakening.

THE COUNTEREXAMPLE.  φ♦ = ((◯⊥ ⊃ p) ∨ ◯⊥ ∨ ¬p) ⊃ ((◯⊥ ∧ p) ∨ (◯⊥ ∧ ¬p))
in the DIAMOND model M♦: 0 ⊑ 1, 2 ⊑ 3 with 1, 2 incomparable,
Rₘ = id ∪ {(x,3) : x ≠ 0}, F = {3}, V(p) = {1,3}.  ‖◯⊥‖ = {1,2,3};
the transposition 1 ↔ 2 is a frame automorphism (Md_swap), so the
variable-free truth sets are exactly {⊥, ◯⊥, ⊤} and ‖p‖ = {1,3} is
undefinable.  Root ⊩ φ♦ (above the root the consequent is ◯⊥ ∧ (p ∨ ¬p),
true at 1 by p, at 2 by ¬p, at 3 by fallibility); the antecedent fails
at the root, which is what makes every substitution instance fail
there (Md_inst_fails): θ true at 1 iff true at 2, so either θ ⊇ ‖◯⊥‖
(then ◯⊥ ⊃ θ holds at the root) or θ lives on the fallible world alone
(then ¬θ holds at the root) — and the consequent always needs ◯⊥,
which fails at the root.  So φ♦ is the ∃-side twin of postui's
p ∨ ¬p, relativised to the ◯⊥-region.

WHY NO STRETCH RESCUES IT.  Md_gstretch_fails: for EVERY guard χ
(variable-free or not) φ♦ fails at inl(root) of gstretch M♦ χ — three
cases: 1 ⊩ χ (the attached upper copy inr 1 forces p and is not
fallible, so ¬p fails at inl 1 while p fails there too: the consequent
dies where ◯⊥ holds), 2 ⊩ χ (same at inl 2), and 1, 2 ⊮ χ (the upper
layer sits only over the fallible 3, so ¬p holds at inl 0 while ◯⊥
does not).  Through gstretch_tr this says: every guarded lower bound
LoG χ φ♦ fails at the root of M♦.

THE GENERALISED GUARDS (wip/guardstretch.lean, the §49 "next probe"
discharged).  gstretch C χ = the stretch with the upper layer attached
over ‖χ‖ — a constraint model for ANY χ (the only property used is
that a truth set is Rᵢ-upward closed).  trG χ = (LoG χ, UpG χ) is tr
with ◯⊥ replaced by χ; gstretch_transfer (axiom [propext]),
gstretch_tr (axiom-free), gstretch_below: LoG χ φ ⊢ ψ for every
variable-free ψ with φ ⊢ ψ — a FAMILY of non-substitutional lower
bounds on F(φ), one per guard.  gstretch C ◯⊥ = stretch C and
LoG ◯⊥ = Lo, so §49's bound is the ◯⊥ member; the guards are not
cosmetic (not_hasGuardedCover_top_phiStar: LoG ⊤ φ★ ⊢ ◯⊥, so the ⊤
guard overshoots at φ★, where the ◯⊥ guard succeeds).
postInterp_of_guardedMixed / postUI_of_guardedMixedConj give the
weaker reduction — refuted above.  Semantic tools added:
hasMixedCover_iff_semMixed, not_hasMixedCover_of_model,
not_hasGuardedMixedCover_of_model.

THE SEARCH (wip/mixedprobe.lean, coverprobe extended with (‖LoG χ‖,
‖UpG χ‖) coordinates per guard; every hit cross-checked against an
explicitly built stretch frame).  mode=mixed (guard ◯⊥): n = 2: 4
models / 2 undefinable pairs / 0 hits; n = 3: 37 / 40 / 0; n = 4:
726 / 1232 / 4 cover-hit pairs of which 2 are MIXED hits (the two
symmetric valuations of the diamond) — closure never capped, max 62.
mode=guarded (all three guards of D(M♦)): same 2 hits at n = 4, Lo
coordinates {1,2,3}, {3}, {3} for guards ⊥, ⊤, ◯⊥ — none containing
the root.  n = 5 (cap 40000, ran to completion in 712 s): 28639 models,
69834 undefinable (model,U) pairs, 0 capped, 2548 cover-hit pairs
(reproducing coverprobe's 2548 exactly) of which 2280 are MIXED hits —
the stretch bound rescues only 268 of the 2548 cover failures.  11
distinct minimal separating formulas; the commonest is
(¬◯⊥ ⊃ (¬p ∨ p)) ⊃ (¬◯⊥ ∨ ◯⊥) (564 pairs), then
((p ⊃ ◯⊥) ∨ ◯p) ⊃ (¬◯⊥ ∨ ◯⊥) (528).  The phenomenon is generic, as it
was for covers.

STATUS.  Both reductions of last-variable ∃p by cover-style methods
are now dead: CoverConj, StretchCoverConj, MixedCoverConj,
GuardedMixedConj all REFUTED, MeetCoverConj REFUTED on the ∀-side.
UI itself is untouched.  The new live question is the φ★-analogue for
φ♦: PostInterpPhiDiaExists — does ∃p.φ♦ exist at all?  In M♦ only ⊤
survives as a candidate (the variable-free truth sets containing the
root are just ⊤), and postInterpPhiDiaIsTop_iff reduces that to "every
variable-free consequence of φ♦ is a theorem".  A positive answer needs
a construction that is neither substitutional nor a guarded stretch.

Addendum (scheduler, same day): the §50 remark "⊤ is the only
candidate M♦ permits" was WRONG as an inference — M♦ only shows any
interpolant is ⊤-valued ON M♦, and ¬¬◯⊥ also has full truth set there.
Pinned in the mixedfail addendum: phiDia_nnbox (φ♦ ⊢ ¬¬◯⊥, axiom-free,
same two-line mechanism as phiStar_nnbox) and
postInterpPhiDiaIsTop_false (⊤ is EXCLUDED as ∃p.φ♦).  The successor
question is exactly the φ★-shape question one construction further
out: **∃p.φ♦ =? ¬¬◯⊥**, now beyond every guarded two-layer stretch —
the same conjectured VALUE as φ★, needing a construction the guarded
family provably cannot supply (Md_gstretch_fails quantifies over ALL
guards).  Note the escalation pattern: p ∨ ¬p killed meet covers; φ★
(its ◯⊥-relativisation) killed substitution covers; φ♦ (the ∨-form
relativisation on a branching frame) killed mixed + guarded.  Whether
this ladder of defeaters terminates in a construction or climbs
forever is now the sharpest form of the last-variable UI question.

---

## §51 (2026-08-04) — ∃p.φ♦ = ¬¬◯⊥ PROVED by the FORK; fork ⊥ stretch INCOMPARABLE; φ♣ moves the frontier to the PARAMETERISED fork (delegated, verified, landed)

wip/branchdia.lean (1034 lines, sorry-free, pinned) + branchprobe.
VERDICT (A): postInterp_phiDia : IsPostInterp phiDia (¬¬◯⊥) — UI does
NOT fail at φ♦; the escalation p∨¬p → φ★ → φ♦ refutes METHODS only.
The brief's 3-layer branching stretch was WRONG (any construction
leaving the ◯⊥-region on the ground layer with p-copies above fails
condition (α)); the right shape is the FORK bstretch C χ: TWO copies
of C glued below the guard region and separated ON it — cross edges
inl x ⇝ inr y guarded by ¬(x ⊩ χ), legitimate because the COMPLEMENT
of a truth set is down-closed (not_force_of_Ri), exactly what trans_i
needs; V(p) = ‖χ‖ on inl, F on inr.  At χ = ◯⊥, bstretch M3 IS M♦
(copy-swap = frame automorphism ⇒ undefinable valuation): the
defeater was the construction in disguise, again.  Forcing condition
read off φ♦: ◯⊥-worlds must DECIDE p (α); non-◯⊥-worlds must kill
the antecedent two-sidedly (β) — the two copies of one oBot_witness
world are exactly (β)'s two witnesses.  bstretch_transfer [propext];
bstretch_force_phiDia; phiDia_minimal; postInterp_phiDia.  General
method: translation pair BLo/BUp with the guard as a DISJUNCT
(BLo(A⊃B) = (BLo A ⊃ BLo B) ∧ (χ ∨ (BUp A ⊃ BUp B)), mutually
recursive symmetric; bstretch_tr carries Classical.choice — the χ ∨ …
step needs case analysis, unlike gstretch_tr); lower bounds
bstretch_below/_below_up; postInterp_of_branch; hasBranchCover_phiDia;
interd_BLo_phiDia.  INCOMPARABILITY (branch_stretch_incomparable):
φ★ has stretch-not-branch (the fork's ¬p-copy kills ¬¬p:
bstretch_M3_not_phiStar), φ♦ has branch-not-guardedMixed — the
successor conjecture must JOIN all three families (BranchMixedConj +
postUI_of_branchMixedConj + refutation tool landed).  Instance bound
pinned: both Boolean instances of φ♦ ⊣⊢ ◯⊥, strictly below ¬¬◯⊥.
PROBE (branchprobe, fork arithmetic verified 0 mismatches over all
n ≤ 4): branch coordinate kills every n ≤ 4 defeater of the guarded
family; n = 5 partial (1500 s) found ONE hit φ♣ = ((p ⊃ ◯⊥) ∨
(¬p ⊃ ◯⊥)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p)) in C♣ (5 worlds, D = 5 truth sets) —
defeats LoG AND BLo at every guard (independent from-scratch Python
re-check) BUT is rescued by the PARAMETERISED fork
fork C χ δ₁ δ₂ (free copy-valuations δᵢ ⊢ χ; bstretch = fork χ χ ⊥):
forced at χ = ¬¬◯⊥, {δ₁,δ₂} = {◯⊥, ¬¬◯⊥}; k = 3,4 copies add
NOTHING beyond free valuations at k = 2.  So BranchMixedConj as
stated is expected FALSE at φ♣ (unpinned; Python-verified), and the
corrected frontier = join of substitution + guarded stretch +
parameterised fork.  sorryAx-injection trap hit again and caught by
the pins (three missing .1s in an 8-case rintro).

## §52 (2026-08-04) — φ♣ PINNED and BranchMixedConj REFUTED; ∃p.φ♣ = ¬¬◯⊥ ⊃ ◯⊥ PROVED by the PARAMETERISED fork (the interpolant is NOT ¬¬◯⊥); then φ♠ REFUTES the corrected frontier too (delegated, verified, landed)

wip/paramfork.lean (2125 lines, sorry-free, 44 #guard_msgs pins) +
wip/pforkprobe.lean.  Branch probe/paramfork off ui-confluence.

(1) φ♣ PINNED.  C♣ : W = Fin 5, Rc x y := x = 0 ∨ x = y ∨ (x = 1 ∧
y = 2), Rmc x y := x = y ∨ (x = 1 ∧ y = 2), F = {2}, V(p) = {1,2,3}.
φ♣ = ((p ⊃ ◯⊥) ∨ (¬p ⊃ ◯⊥)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p)).  Root forces φ♣
(Cclub_force_phiClub): at 1, 2 the consequent's second disjunct, at
3, 4 the first, at the root the ANTECEDENT fails (3 is a p-world
outside ‖◯⊥‖, 4 a ¬p-world outside it).  UNDEFINABILITY: the
transposition 3 ↔ 4 is a frame automorphism (Cclub_swap), and that
alone is enough — no classification of D(C♣) is needed anywhere.
CORRECTION to §51: D(C♣)'s element {1,2,3,4} is ◯⊥ ∨ ¬◯⊥, NOT ¬¬◯⊥;
in C♣ one has ¬¬◯⊥ ≡ ◯⊥ ≡ {1,2} (Cclub_nnOBot_iff).  Every guarded
stretch fails UNIFORMLY in the guard, at inl 1 (there ◯⊥ holds, so
p ⊃ ◯⊥ is vacuous, while p on the ground layer means "fallible" and
1 ∉ F) — simpler than mixedfail's three-way split.  Every (χ,⊥)-fork
fails by a two-case split on the root: 0 ⊮ χ gives the cross edge
inl 0 ⇝ inr 1 and inr 1 refutes; 0 ⊩ χ makes χ universal, p ≡ ⊤ on
the inl copy, and inl 0 itself refutes.  Every variable-free instance
fails: if 3 ⊩ θ then 4 ⊩ θ and ‖¬θ‖ ⊆ ‖◯⊥‖, so ¬θ ⊃ ◯⊥ holds at the
root; if 3 ⊮ θ then ‖θ‖ ⊆ ‖◯⊥‖ and θ ⊃ ◯⊥ holds.  Fed to
not_hasBranchMixedCover_of_model: phiClub_no_branchMixedCover,
branchMixedConj_false.

(2) THE PARAMETERISED FORK.  fork C χ δ₁ δ₂ h₁ h₂ = the bstretch frame
(bRi C χ, stRm C, stF C) with V(a) = ‖δ₁‖ on inl, ‖δ₂‖ on inr.  The
ONLY condition is δ₁ ⊢ χ and δ₂ ⊢ χ (pointwise h₁, h₂), and it is used
exactly once: hered_V on a cross edge inl x ⇝ inr y needs x ⊩ δ₁ →
y ⊩ δ₂, and the edge exists only when x ⊮ χ, so x ⊩ δ₁ ⊢ χ is already
absurd — the obligation is VACUOUS, not discharged.  full_F is free
(fallible worlds force everything).  fork C χ χ ⊥ = bstretch C χ by
rfl (fork_eq_bstretch), and trF χ χ ⊥ = trB χ (trF_eq_trB).  Transfer
comes free: fork and bstretch share W, Rᵢ, Rₘ, F and differ only in V,
so they agree on every variable-free formula (fork_force_eq, [propext])
and fork_transfer follows from bstretch_transfer.  Translations
FLo/FUp = BLo/BUp with the atom clause freed (FLo p = δ₁, FUp p = δ₂);
fork_tr, fork_below/_below_up, postInterp_of_fork, FLo_iff_fork.

(3) ∃p.φ♣ = ¬¬◯⊥ ⊃ ◯⊥ PROVED.  UPPER BOUND: φ♣ ⊬ ¬¬◯⊥ (assume ¬◯⊥
and the consequent's FIRST disjunct fires — phiClub_not_nnbox), but
φ♣ ⊢ ¬¬◯⊥ ⊃ ◯⊥ (phiClub_psi): at v ⊩ ¬¬◯⊥ with v ⊮ ◯⊥ one gets
v ⊮ ¬◯⊥, so v is a GAP world, the consequent fails and the antecedent
must fail; its second disjunct gives z ⊒ v with z ⊩ ¬p and z ⊮ ◯⊥;
clause (α) (every ◯⊥-world of the cone forces p, phiClub_alpha) turns
z ⊩ ¬p into z ⊩ ¬◯⊥, and ¬¬◯⊥ at v then makes z fallible — hence
z ⊩ ◯⊥, contradiction.  MINIMALITY by the fork at
(χ, δ₁, δ₂) = (◯⊥ ∨ ¬◯⊥, ◯⊥ ∨ ¬◯⊥, ◯⊥): the guard's complement IS the
gap region, so the two copies are glued exactly where clause (β) has
work to do; at a gap world x the hypothesis produces a non-fallible
¬◯⊥-world y ⊒ x, and BOTH copies of y are above every copy of x (the
cross edges exist because x ⊮ χ) — inl y is a p-world outside ‖◯⊥‖
(y ⊩ ¬◯⊥ ⊢ δ₁) and inr y is a ¬p-world outside ‖◯⊥‖ (its only
successors are inr z, since y ⊩ χ kills its cross edges, and
inr z ⊩ p means z ⊩ ◯⊥ hence z fallible).  δᵢ ⊇ ‖◯⊥‖ is clause (α).
postInterp_phiClub : IsPostInterp phiClub ((¬¬◯⊥) ⊃ ◯⊥).  VERDICT: the
value found at φ★ and φ♦ is NOT a universal attractor.  Instance
bracket: φ♣[p := ⊤] ⊣⊢ ◯⊥ ∨ ¬◯⊥, φ♣[p := ⊥] ⊣⊢ ¬◯⊥, and
◯⊥ ∨ ¬◯⊥ ⊢ ¬¬◯⊥ ⊃ ◯⊥ STRICTLY (psiClub_not_gapGuard, at C♣'s root) —
so no substitution join can reach it.

(4) INCOMPARABILITY SURVIVES PARAMETERISATION.  not_hasForkCover_
phiStar: φ★ has NO parameterised fork cover at any admissible triple.
At M3's root (which forces ¬¬◯⊥ = ∃p.φ★), three cases on the copy
valuations at world 1: 1 ⊮ δ₁ makes inl 1 a non-fallible ¬p-world
(the cross edge that could supply a p-world above it exists only when
1 ⊮ χ, which δ₂ ⊢ χ forbids), killing ¬¬p; 1 ⊩ δ₁ with 0 ⊩ χ leaves
inl 0 with no cross edges, so ◯⊥ ⊃ p holds there and the first
conjunct forces ◯⊥; 1 ⊩ δ₁ with 0 ⊮ χ splits on 1 ⊩ δ₂ into the same
two shapes.  Hence paramFork_stretch_incomparable — the corrected join
genuinely needs LoG as well as FLo.

(5) THE CORRECTED FRONTIER.  ParamForkMixedConj = every 1-pv φ is
covered by finitely many LoG χ φ, finitely many FLo χ δ₁ δ₂ φ (over
variable-free triples with δᵢ ⊢ χ) and finitely many instances;
postInterp_of_paramForkMixed, postUI_of_paramForkMixedConj,
not_hasParamForkMixedCover_of_model, and the embedding
hasParamForkMixedCover_of_branchMixed (via (χ, χ, ⊥)).  p, φ★, φ♦, φ♣
are all covered, each by a different member.  §13 states the POINTWISE
form SemParamForkMixed (what the probe tests) with
semParamForkMixed_of_cover; §14 records that the bridge from pointwise
to a single finite cover sticks at UNIFORMITY ACROSS MODELS — D(C) is
finite per finite C but unbounded over all C, so what is needed is a
bound on the size of the required triples in terms of φ (all three
defeaters are covered by a SINGLE member built from ◯⊥ and ¬◯⊥, which
is evidence, not proof).  Both are Prop-valued statements only.

(6) PROBE (pforkprobe, two-phase: coverprobe subalgebra search on the
VALUATION coordinates only, then every guard tested in the explicitly
built stretch frame and every admissible triple in the explicitly built
fork frame — exact, no compositional arithmetic to trust; carrying even
one (LoG,UpG) pair per guard inside the subalgebra made the n = 5 sweep
intractable, which is why branchprobe's guarded mode never finished).
mode=verify, n ≤ 4: 5410 admissible triples, 0 constraint-model law
failures; 3474 inadmissible triples DO break a law (δᵢ ⊢ χ is not
decorative); 0 degenerate mismatches ((χ,χ,⊥) reproduces branchdia's
fork on the whole battery).  mode=run, EXHAUSTIVE n ≤ 5, 0 capped, 0
skipped at the phase-B budget:

  n=2:     4 models,     2 pairs,    0 cover-hit,   0 sep,   0 FULL-JOIN
  n=3:    37 models,    40 pairs,    0 cover-hit,   0 sep,   0 FULL-JOIN
  n=4:   726 models,  1232 pairs,    4 cover-hit,   6 sep,   0 FULL-JOIN
  n=5: 28639 models, 69834 pairs, 2548 cover-hit, 6294 sep, 564 FULL-JOIN
       (5604 of the 6294 separators killed by a stretch or a fork;
        max closure 185, max triples 119, 325 s)

The 2548 cover-hit pairs at n = 5 reproduce coverprobe's 2548 exactly.
n ≤ 4 is a CLEAN SWEEP; n = 5 is not.

(7) REFUTED: ParamForkMixedConj — the defeater φ♠.  Commonest of the
564 hits (235 of them, 3 distinct formulas in all):

  C♠ : W = {0,1,2,3,4}, 0 ⊑ all, 1 ⊑ 4, 2 ⊑ 3, 3 and 4 maximal,
       Rₘ = id ∪ {(1,4)}, F = {4}, V(p) = {1,3,4}
  φ♠ = (¬◯⊥ ⊃ (¬p ∨ p)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))

D(C♠) = {⊥={4}, ◯⊥={1,4}, ¬◯⊥={2,3,4}, ◯⊥∨¬◯⊥={1,2,3,4}, ⊤}; ‖p‖ is
undefinable because worlds 2 and 3 satisfy the same variable-free
formulas — and this time NOT by an automorphism (2 ⊑ 3, 3 ⋢ 2) but by
the D-classification itself, got by `decide` from a five-row table
(spTbl, sp_bot/sp_and/sp_or/sp_imp/sp_box, Cspade_defs, Cspade_agree23).
Root forces φ♠; every instance fails at the root (the ¬◯⊥-worlds are
2, 3 and the fallible 4, and a variable-free θ is DECIDED at 2, 3);
every guarded stretch fails UNIFORMLY at inl 1 (1 ⊩ ¬¬◯⊥ makes the
antecedent vacuous there, while the consequent needs ¬◯⊥ — false at 1 —
or p, which on the ground layer means "fallible"); every PARAMETERISED
fork fails UNIFORMLY at inl 0 (consequent fails outright; the antecedent
holds because p is decided at every copy of 2 and 3, both copy
valuations being variable-free and hence blind to 2 vs 3 — and a
p-world on the other copy above inl 2 would need 3 ⊩ δ₂ with 2 ⊮ χ,
which 3 ⊩ δ₂ ↔ 2 ⊩ δ₂ ⊢ χ forbids: the δᵢ ⊢ χ condition closes the
last gap).  phiSpade_no_paramForkMixedCover, paramForkMixedConj_false,
and semParamForkConj_false — even the POINTWISE form fails, so the §14
bridge question does not arise for this family.  Independently
re-verified from scratch in Python, including k = 3, 4 copies (0
k-forks rescue φ♠); with ARBITRARY up-set copy valuations, dropping
BOTH definability and δᵢ ⊢ χ, 43 choices do rescue it — the first being
guard ⊤ with δ₁ = ‖p‖ itself, which is exactly the undefinable
valuation one is trying to eliminate.  φ♠'s own ∃p is OPEN
(PostInterpPhiSpadeExists); as at φ★, φ♦, φ♣ the refutation is of the
METHOD, and uniform interpolation is untouched.

---

## §53 (2026-08-04) — ∃p.φ♠ = ¬¬◯⊥ ⊃ ◯⊥ PROVED by the SERIES gluing; THE GLUE SCHEME unifies every construction; the two endgames are formal (delegated, verified, landed)

wip/phispade.lean (1404 lines, 84 declarations, sorry-free, pinned).
∃p.φ♠ = ψ♣ = ¬¬◯⊥ ⊃ ◯⊥ (postInterp_phiSpade — same value as φ♣;
postInterp_phiSpade_eq_phiClub).  Forcing condition: (α) ◯⊥-worlds
force p (identical to φ♣); (β) above every GAP world, a ¬◯⊥-world
where p is UNDECIDED — p must CHANGE along an Rᵢ-edge inside the
guard region, which no parallel gluing with variable-free copy
valuations can reproduce.  THE SERIES GLUING sfork C χ δ₁ δ₂ =
guarded-stretch FRAME (up-polarity cross guard on the target, one
direction) + parameterised-fork FREE VALUATIONS; only side condition
δ₁ ⊢ δ₂ (hered_V on the cross edge); (⊥,⊤) recovers gstretch
exactly.  φ♠'s member: (χ,δ₁,δ₂) = (¬◯⊥, ◯⊥, ⊤) — the cross edge's
guard is exactly what the ψ♣-witness supplies, putting the p-world
directly ABOVE the ¬p-world in one chain.  series_needs_free_valuations
localises the advance (fixed-(⊥,⊤) series and all dn/dn forks fail at
C♠'s root for every parameter).  Substitution bracket: all four
instances ⊣⊢ gapGuard or ¬◯⊥, strictly below ψ♣.  THE META-OBJECT
glue C cl cr d₁ d₂: two copies, independent Cross condition per
direction (off | up χ = guard on TARGET, up-closed | dn χ = guard on
SOURCE, down-closed), layer-preserving Rₘ, free variable-free copy
valuations.  Frame legality FREE at all nine polarity pairs
(crossRel_le/right/left uniform in polarity); the ONLY condition is
CrossHered per direction, with the model-independent sufficient form
OkCross: up-edges need INCLUSION δ_s ⊢ δ_t, dn-edges need VACUITY
δ_s ⊢ χ — the uniform explanation of the fork's and series' seemingly
unrelated side conditions.  glue_transfer needs NO conditions
[propext].  Translation trGl/GLo/GUp: guard-as-implication (up),
guard-as-disjunct (dn), per direction (force_cross_forall/box,
force_guardImp; classicality enters only at dn).  glue_below +
postInterp_of_glue + HasGlueMixedCover + refutation tool.
IDENTIFICATIONS (rfl per node): GLo off off θ θ = inst θ (substitution
IS the glue!); GLo (up χ) off ⊥ ⊤ = LoG χ (guarded stretch);
GLo (dn χ) (dn χ) δ₁ δ₂ = FLo (fork); series = up/off free.
glue_strictly_beats_paramForkMixed.  ENDGAMES: GlueMixedConj;
GlueCompleteConj dict (parameters bounded by a φ-dictionary — the
uniformity question); GlueDiagonal; glueMixedConj_iff_no_diagonal;
postUI_of_glueMixedConj.  EVIDENCE reading: four defeaters, four
positive resolutions; every cover coordinate ever needed lies in the
◯-depth ≤ 1 dictionary {⊥, ◯⊥, ¬◯⊥, ◯⊥ ∨ ¬◯⊥, ⊤}; each ladder step
needed a new POLARITY SHAPE, never a new parameter — and the shapes
are now enumerated (nine, all legal).  OPEN: SeriesSuffices (is dn/dn
subsumed by series-with-free-valuations?); GlueCompleteConj for a
concrete dict; cross-Rₘ (translations worked out on paper, both
polarities expressible, deliberately not mechanised — φ♠ did not
need it).  sorryAx-injection fired again (implicit Prop args of a
reducible model) and was caught by the pins; fix = per-member
wrapper lemmas.

---

## §54 (2026-08-04) — TOWER vs LADDER: the syntactic scheme passes every test vector; ZERO disagreements (delegated, verified, landed)

wip/towerkit.lean + towertest (exe) + towerpin.lean + towerpack.lean
(unregistered: root-level tower imports, LEAN_PATH-built).  The July
tower's COMPUTABLE quantifier tables (itpE/itpA, PLLG4UITrunc.lean —
definitions verified sorry-free; sorryAx enters only via adequacy
through cascade_low_pos_box) were run on the ladder's pinned battery
and certified against the proved values.  RESULT: 12 rows, 8 fully
certified AGREES (∃p of p/◯p/◯p⊃p/exLadder/phiMix; ∀p of p/◯p/wemP),
φ★ AGREES on the nf-normalised output, 3 UNDECIDED-AT-BUDGET (positive
search truncations only — never refutations), ZERO DISAGREEMENTS.
The tower computes ⊤, rnSub 3, ¬¬◯⊥, ◯⊥, ⊥ ON THE NOSE at budgets
0–1; sub-threshold budgets err exactly as the budget-gating predicts
(∃-side too weak, ∀-side too strong) and itp_budget_mono_le
(axiom-clean) transfers certified verdicts UP to the prescribed
budget (eRow_settled/aRow_settled pinned) — essential because the
prescribed-budget output is astronomically large (~10^b nodes; the
prescribed budget for φ★ is 339).  BLIND PREDICTION: on φ♠ (open at
the agent's base commit) the tower's b=1 output certifies
¬¬◯⊥ ⊬ ∃p.φ♠ — CONSISTENT with ∃p.φ♠ = ψ♣ proved independently in
§53 (¬¬◯⊥ ⊬ ψ♣ ✓); the full Interd(nf T♠1, ψ♣) check is the natural
follow-up.  This is the July campaign's first test-vector evidence
ever, and it points the same way as the open lemma: THE TOWER'S
RECURSION COMPUTES THE RIGHT FUNCTION.  Named follow-ups: (b) nf
correctness lemma ∀φ, Interd φ (nf φ) (~100-line induction; congruence
lemmas exist) — hardens the nf-level verdicts to kernel grade; (c)
atoms(itpE …) ⊆ atoms S ∪ atoms Γ (easy induction the library lacks);
(d) kernel evaluation blocked by pieceClosure's WellFounded.fix —
route: pin pieceClosure = literal Finset by simp with the unfolding
equations; (e) postui's import closure reaches rnc_probe's root-level
main — battery re-declared in towerkit, all nine rfl-checked
(phiStar_eq etc., axiom-free).  RECOMMENDATION: redirect to the
assault on cascade_low_pos_box with the ladder as regression suite.

---

## §55 (2026-08-04) — Hardening the tower test: `nf_interd` PROVED, the `atomFree` gap reduced to one containment, the φ♠ circle UNDECIDED-AT-BUDGET

Branch `probe/towerharden` off `7f1fdc7`.  Three named §54 follow-ups
attacked; two closed, one reduced.

**(b) `nf_interd` — CLOSED.**  `wip/nfcorrect.lean`.
`PLLND.Search.nf` (`LaxLogic/PLLSearch.lean` §0) is what makes the
tower's outputs legible — on φ♠ at `b = 1` it takes 88 202 nodes to
391 — and every `nf`-level verdict of §54 was, until now, a claim about
a formula the library said nothing about.  Now:
`smash_interd : ∀ φ, Interd φ (smash φ)` (ten branches: the ⊥/⊤
absorptions, idempotence at ∧/∨, `A ⊃ A ≡ ⊤`, and the two lax laws
`◯⊤ ≡ ⊤`, `◯◯B ≡ ◯B`), then `nf_interd : ∀ φ, Interd φ (nf φ)` by the
four `Interd` congruence rules of `LaxLogic/PLLSemUIFrag.lean`, then
`nfIter_interd : ∀ n φ, Interd φ (nfIter n φ)` for the fixpoint
iteration consumers actually run.  All three `[propext]` — no choice, no
`Quot.sound`, no `sorryAx`.  The transfer rules
(`deriv_/interd_/g4c_of_nf`, `_to_nf`, and the `_nfIter` forms) cut an
`nf`-level certificate down to the original **without evaluating
anything**: the certificate is an object about the *term* `nf T`.
`wip/towercircle.lean` applies this to the tower's row lemmas —
`eRow_settled_nf` / `aRow_settled_nf` (+ `_nfIter`) are §54's
`eRow_settled` / `aRow_settled` with the certificate moved to the normal
form, `itp_budget_mono_le` transfer to the prescribed budget intact.  So
§54's nf-mediated rows (φ★'s agreement, the φ♠ prediction facts) are now
raw-table facts modulo their search certificates.

**(c) the atoms lemma — REDUCED, not closed.**  `wip/toweratoms.lean`.
The wanted statement is `atoms (itpE p S f b Γ) ⊆ atoms Γ`; its proof is
the ≈500-line induction mirroring `itp_pfree`
(`LaxLogic/PLLG4UITrunc.lean`:1961) clause for clause, which did not fit
this session's budget.  What is closed instead is everything on either
side of it: `atomFree_iff` (the bridge between the `Bool` predicate
`atomFree` and the `Finset String` `atoms`, which the library also
lacked — PROVED), the containment named `ItpAtomsBounded` in the
pointwise form the induction will produce (**stated, OPEN, never
claimed — no sorry**), and the reduction
`atomFree_eTower_of_bounded` / `atomFree_aTower_of_bounded`: with
`itp_pfree` killing `p` and `ItpAtomsBounded` killing everything else,
`atomFree (eTower φ b) = true` for every subject whose only atom is `p`
— i.e. every row of the battery.  `phiSpade_atoms` PROVED;
`spade_circle_of_bounded` then closes the φ♠ circle at every budget
above `b` from `ItpAtomsBounded` plus the FORWARD certificate alone.
Useful structural observation, and the reason `S` does not appear in
`ItpAtomsBounded`'s hypothesis: `itpE`/`itpA` use the space `S` only in
membership *tests* — it never contributes a formula to the output — and
the recursive calls only ever extend `Γ` by *subformulas* of its own
members.  That is exactly the invariant the induction needs.

**(the φ♠ circle) — UNDECIDED AT BUDGET 2·10⁷ per direction.**
`wip/towertest.lean` gained a `circle` mode: `nf` iterated with the pass
count reported, and the two directions of `Interd (nf^k T♠b) ψ♣` run
separately so a generous `findBudget` can go to one at a time.
Measured: `nf` reaches its fixpoint in **one pass** (`k = 1`), and
`T♠1` is 88 202 nodes against `nf T♠1`'s 391.  `nf T♠1` is visibly
variable-free, of `◯`-depth 1, built entirely from `◯⊥` and `¬◯⊥` —
consistent with `ψ♣`, and its outermost antecedent
`((¬◯⊥ ∨ ◯⊥) ⊃ (¬¬◯⊥ ∧ ¬◯⊥)) ⊃ (¬◯⊥ ∨ ◯⊥)` is `⊣⊢ ⊤`.  Both
directions REMAIN UNDECIDED, and the two runs failed differently.  At
`findBudget` 2·10⁵ both returned a verdict — UNDECIDED with the
**positive stage truncated** (node budget exhausted: 27.8 s forward,
9.1 s backward).  At `findBudget` 2·10⁷ neither returned at all: both
were killed by `scripts/probe`'s 1000 s wall-clock cap (rc = 143) with
no verdict line emitted.  In no run was a countermodel produced —
`settle` is countermodel-first, so the refutation stage completed and
found nothing, twice — so there is **no evidence against the circle**;
what there is, is a search-capacity wall.  Recorded as
UNDECIDED-AT-BUDGET, with the two Lean-side composites already in place
so a later certificate closes it in one line: `spade_circle`
(both certificates, no side condition at all) and `spade_circle_up`
(forward certificate + atom-freeness, transferred to every budget above
`b`, the prescribed `579` included).

**Reading.**  The `nf` gap was the load-bearing one and it is gone.  The
φ♠ circle is now purely a *search-capacity* question about one
391-node variable-free sequent — a much better shaped problem than
before, and one the RN(◯,{}) dictionary machinery (§§43–47) may settle
without search at all: classify `nf T♠1` in the 15-class dictionary and
compare with `ψ♣`'s class.  That is the recommended next move on this
thread, ahead of re-running the search wider.

---

## §57 (2026-08-04) — PROVE prong: TruncCase DISCHARGED, ImpCase retired and replaced, and the budget miscalibration FOUND — in the apparatus, not the kernel (delegated, verified, landed)

wip/boxSnd.lean (rebuilt, sorry-free), wip/boxSndTight.lean (new),
wip/floorGoals.lean (new).  The crown was NOT reached; the reasons
are now exact and every one is a STATEMENT matter.

DISCHARGED: TruncCase — needed NO measure and NO pairing: the
truncation body is ⋁ others, so box_open against the ◯-target with
the guard fired from the ambient (fuel and budget both free) lands on
the traversal's own disjunct analysis once that analysis is HOISTED
(othersOne/othersAll); three lines after the restatement.  RETIRED:
ImpCase — unprovable as stated (whole-table membership loses which
F ∈ Γ' produced φ); routing moved into the traversal; §110's
six-shape count corrected to NINE (jump family contributes 2, γ
family 2 + one continuation per boxed member; impOr's fresh witness
needed the symmetric branch); nine new lemmas, all first try.
boxSnd_reaches now sorry-free, signature pinned.

THE DECISIVE FINDING (Matthew's predicted failure mode, located):
boxSnd_reaches ran at ambient budget = source + 1, but its consumer
GammaPairFloorBox supplies ambient = source — §§92-112 were built at
budgets the interface never supplies.  The FIX IS LOCAL AND SIMPLER:
boxSndTight decouples the budgets (ambient and source at e+2, target
arbitrary c) and compiled FIRST TRY — at matched budgets the §107
shifts are not needed at all, and the target budget rides free
because the only target-producing clause is the goal clause, where
itpA_atom_forces holds at every budget.  First instances of all
three floor interfaces landed (gammaPairFloorBox/A_boxedAtom,
jumpPairFloor_boxedAtom, floorBox_of_grownAmb, floorAny_atom —
budgets independent); over ∨-free spaces the residue of ALL THREE
floor interfaces is exactly SIX goal shapes (p, ⊥, ∧, ⊃, ◯p, ◯D
non-atom; ∨ vacuous by g ∈ S).

TWO BLOCKERS TO THE CROWN, both named: (a) cascade_low_pos_box's
statement carries hbox over ARBITRARY S while the entire cascade
apparatus needs piece-closure + coverage — the non-closed bands have
no route; required: a cascade_main re-parameterisation threading
closure/coverage exactly as cascade_main_bf already does box-free.
STATEMENT CHANGE FLAGGED, NOT MADE.  (b) the floor-interface residue
(six shapes × three interfaces) + AmbGuardAscent (untouched, no
partial).  NO suspicion the lemma is false — every branch attacked
closed, several first try.  Regression: tables byte-identical
(nothing imports the changed files); towertest sizes reproduced
exactly.  Method: SIX consecutive obligations were statement
problems; check statements against the CONSUMER, not only the
traversal.  New traps recorded: `split at h` silently resolving
guards from context (use by_cases + simp only if_pos/if_neg);
Option.noConfusion vs cases.

COMBINED VERDICT WITH §56: the two prongs AGREE — the kernel lemma
survives its first room-satisfying gate-live attack (all failures at
c = 0, below the guard; structural defect-1 argument matches the
measured constant boundary), and the one real miscalibration was in
the apparatus one level up, with a local, simplifying fix.  The wall
is now a finite list.

---

## §58 (2026-08-04) — Round 2: the re-parameterisation LANDED, and the §57 apparatus REFUTED — the ◯-band target was the room-free descent

wip/absorb_base.lean (re-parameterised), wip/adequacy.lean,
wip/packaging.lean (consumers adjusted), wip/reparamRefute.lean (new),
wip/cascadeBox.lean (stub section re-headed).  The crown was NOT
reached, and the reason is now a machine-checked negative.

**(a) THE RE-PARAMETERISATION — DONE (Matthew-authorised statement
change).**  `cascade_low_pos_box`'s old `hbox` disjunction over an
ARBITRARY space is gone.  It now carries piece-closure
(`hand`/`hor`/`himp`/`hsome`) and coverage (`g ∈ S`, `∀ X ∈ Γ, X ∈ S`)
**in addition to** the room hypotheses `1 ≤ defect S Γ` and
`defect S Γ · (|jumpGoals S| + 2) ≤ c`, which are KEPT.

Old statement:

    private theorem cascade_low_pos_box (p) (S) (fh Γ fuel c g Δ)
        (hbox : ¬ ((∀ F ∈ S, boxFree F) ∧ and/or/imp-closure ∧
                   g ∈ S ∧ (∀ F ∈ Γ, F ∈ S)))
        (hd1 : 1 ≤ defect S Γ)
        (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ c)
        (hamb : G4c Δ (itpE p S fuel (c+1) Γ))
        (hhead : G4c Δ (itpA p S fh (c+1) Γ g)) (hfh : fh ≤ fuel) :
        G4c Δ (itpA p S fuel c Γ g)

New statement:

    private theorem cascade_low_pos_box (p) (S)
        (hand) (hor) (himp) (hsome)          -- piece-closure of S
        (fh Γ fuel c g Δ)
        (hgS : g ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S) (hc : 1 ≤ c)
        (hd1 : 1 ≤ defect S Γ)
        (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ c)
        (hamb) (hhead) (hfh) : G4c Δ (itpA p S fuel c Γ g)

Determined from the CALL SITES, not from guesswork: the single consumer
is `cascade_low_pos`, and the chain up is `cascade_low` → `cascade_main`
→ `cascade_entry` → `cascade_impLImp`/`_jump`/`_gamma` →
`cascade_impLImp_ant`/`cascade_gamma_box` → `itp_stab_aux` → `itp_stab`
→ `itp_stab_le` → `existsP_adequate`/`forallP_adequate`.  At the two
final consumers the space is `pieceClosure φ` resp. `pieceClosure C`,
which is `PieceClosed` and covers its own context and goal — exactly the
arguments the box-free mirror `itp_stab_le_bf` already receives at the
same two sites.  Closure went in as four top-level parameters (`S` never
changes inside, so it is free); coverage was threaded through every
recursion of `cascade_main` and `itp_stab_aux`, mirroring the sorry-free
box-free spine `cascade_main_bf` clause for clause.  `stab_lower` in
adequacy and its four sites took `hPC`/`hΓS`/`hCS` the way
`stab_lower_bf` already did.

BONUS, and it is structural: the FOURTH sealed position — the fresh goal
antecedent outside `S` — is now DEAD CODE (`(himp hgS).1` puts it in
`S`), exactly as the "Two structural leads" note predicted in July.
`cascade_main`'s sealed sites drop from four to THREE (the goal-γ
disjunct, the clause-γ-head component, the truncation disjunct).

Also simplified: `itp_stab_aux`/`itp_stab`/`itp_stab_le` need only
`hand`/`hor`/`himp`/`hsome`, not the `himpAnd`/`himpOr`/`himpImp` the
box-free mirror carries.

**(b) THE DECISIVE FINDING — the §57 apparatus is aimed at a REFUTED
statement.**  The obvious next step was to make the holdout verbatim
`cascade_box` (`wip/cascadeBox.lean`:1532), i.e. to drop `hd1`/`hroom`
and keep only `1 ≤ c`.  That was drafted, compiled, and then caught:
**the room-free form is FALSE**, and the repo already contained the
refutation.  `AscRefute.not_roomFreeDescent` (`wip/ascRefute.lean`,
axioms `[propext, Quot.sound]`) kills it at

    Sk = {◯p⊃r, ◯p, p, r, (◯r⊃s)⊃t, ◯r⊃s, ◯r, s, t}
    Γ = [◯p⊃r],  g = (◯r⊃s)⊃t,  fuel = 4,  c = 1

`wip/reparamRefute.lean` (new, sorry-free, pinned) closes the remaining
gap in that argument.  `AscRefute`'s statement is *bare* — no closure or
coverage side conditions — so one could have hoped closure and coverage
excluded the counterexample.  They do not:

* `sk_and`, `sk_or`, `sk_imp`, `sk_some`, `sk_cover`, `sk_goal` —
  `Sk` satisfies EVERY closure and coverage condition, checked in Lean;
* `not_reparamKernelRoomFree` — the kernel stated in absorb_base's own
  idiom (inner head fuel `fh`, both premises, `fh ≤ fuel`) with closure
  and coverage but WITHOUT the room is FALSE
  [propext, Classical.choice, Quot.sound];
* `defect_Sk_Gk : defect Sk Gk = 8`, `room_fails` — only `hroom`
  excludes the counterexample;
* `room_ge_jump` / `room_two` — `hd1` + `hroom` force
  `|jumpGoals S| + 2 ≤ c`, hence **`2 ≤ c`**.

**Consequences, and they are sharp.**

1. `cascade_box` derives the room-free conclusion from its four open
   interfaces at a space satisfying all its side conditions, and that
   conclusion is false there.  So `AmbGuardAscent`, `GammaPairFloorA`,
   `GammaPairFloorBox`, `JumpPairFloor` are **jointly unsatisfiable at
   `Sk`**.  One is already refuted outright
   (`AscRefute.not_ambGuardAscent`).
2. Therefore NO repair of `oth_descent`'s ascent sites — however clever,
   and whatever `wip/freshAnt.lean` finds at particular cells — can
   yield the room-free descent.  `AmbGuardAscent` is not merely "off the
   critical path": the whole path is refuted.
3. The §57 residue — "six goal shapes × three floor interfaces over
   ∨-free spaces" — is a residue of a refuted statement.  **Do not grind
   it.**  The three pair-floor interfaces are stated at target budget
   `1`; the kernel's own band never reaches `c = 1` (`room_two`).  They
   arise only from a budget-descending recursion that pays no ledger,
   which is exactly what `oth_descent` runs.
4. `wip/floorRefute.lean` reached the same conclusion from the other
   side in July: the descent to budget `0` is false too, so the budget
   tier has no base case at any floor, and the recursion must terminate
   on the pigeonhole, not on the budget.  §58 and floorRefute now agree.

**What survives and is reusable.**  Everything above `cascadeBox`'s stub
section; `wip/boxSndTight.lean`'s `boxSnd_tight`, `boxGoal_remap_free`,
`floorBox_of_grownAmb`, `floorAny_atom` and the three `*_boxedAtom`
instances — all unconditional theorems about the tables, not about the
refuted descent; and the whole re-parameterised spine, which now hands a
◯-band build exactly the closure and coverage it needs, at the room.

**THE ROUTE, restated.**  The only viable ◯-band build is
**ledger-carrying**: `cascade_main`'s pigeonhole over jump goals,
extended to the ◯-clauses, so that every recursive call stays inside
`defect S Γ · (|jumpGoals S| + 2) ≤ c`.  That is `cascade_main`-scale
work (the July docstring said as much) and it was not attempted here.
`cascade_main_bf` remains the template; the re-parameterisation has now
made the non-bf spine carry the same invariants, so the two spines
differ only in the ◯-clauses.

**Build state.**  Full standalone stack rebuilds
(absorb_base → adequacy → packaging → indiff → spaceindiff → final),
`wip/absorb_base.lean` has exactly ONE `sorry` (the holdout), every
`#guard_msgs` pin passes, and the crown is unchanged:

    'PLLND.uniform_interpolation_PLL' depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

Regression: `lake exe towertest sizes 2` reproduces the twelve-row table;
no table definition changed (zero files touched under `LaxLogic/`,
`wip/towerkit.lean`, `wip/towertest.lean`).

**Method note for the next round.**  §57's lesson was "check the
statement against the CONSUMER, not only the traversal".  §58 adds:
**check the statement against the repo's own refutations before
adopting it.**  The room-free re-parameterisation was drafted, compiled
cleanly, and passed the whole stack — a false statement can do all
three, because it is a `sorry`.  What caught it was reading
`wip/ascRefute.lean` while recomputing the obligation set, which the
round's brief explicitly asked for.

---

## §59 (2026-08-04) — Round 3: the ledger route is REFUTED at the seam, and the `◯`-goal positions turn out to need no ledger at all

`wip/sealLedger.lean` (new, sorry-free, pinned), `wip/seal2Free.lean`
(new, sorry-free, pinned).  `wip/absorb_base.lean` and everything below
it are **untouched**; the standalone stack rebuilds and the crown is
unchanged.  The round's brief was "extend `cascade_main`'s pigeonhole
over jump goals through the `◯`-clauses, so that every budget-consuming
recursive call is financed by the ledger".  That route is now a
machine-checked dead end, and the reason points at the replacement.

**(a) The MEASURE was never the obstruction — settled.**  With the
goal-size measure `gsize` and the lex triple
`(c, defect S Γ, gsize g)`, two of `cascade_main`'s three surviving
sealed sites strictly decrease it:

* the **goal-γ disjunct** (`absorb_base`:2748) descends from goal `◯D`
  to goal `D` at the *same* budget and the *same* context —
  `seal1_lexLt`;
* the **clause-γ-head component** (:3261) descends from budget `c'+1` to
  `c'` — `seal2_lexLt`.

The **truncation disjunct** (:3513) moves nothing at all: it restarts at
the caller's own budget, context, goal *and* fuel (`fh = F+1`,
`fuel = fl+1`) — `seal3_not_lexLt`.  So a
`(budget, defect, goal-size)`-lex induction over the holdout would
discharge two of the three sites outright.  That question has been open
since the July docstring asked for "a `(defect, budget)`-lex landing
map"; it is answered, and it is not what blocks the build.

**(b) THE ROUND'S RESULT — no ledger can cross the γ-head seal.**  The
holdout hands `cascade_main` nothing but its own room
`defect S Γ · (|jumpGoals S| + 2) ≤ c`, so any ledger must be
*derivable* from the room at the entry budget.  The clause-γ-head seal
hands the holdout back its own room **one budget lower**, so any ledger
must *imply* the room at `c` from itself at `c + 1`.  Composed, the two
demands lift a budget hypothesis across a budget drop:

    theorem no_ledger_survives_gamma_seal
        {Room' : Finset PLLFormula → List PLLFormula → Nat → Prop}
        {L : Finset PLLFormula → List PLLFormula → Finset PLLFormula → Nat → Prop}
        {S Γ g c}
        (hhi : Room' S Γ (c + 1)) (hlo : ¬ Room' S Γ c)
        (hentry : ∀ S' Γ' g' c', Room' S' Γ' c' → L S' Γ' {g'} c')
        (hseal  : ∀ S' Γ' seen' c', L S' Γ' seen' (c' + 1) → Room' S' Γ' c') :
        False :=
      hlo (hseal S Γ {g} c (hentry S Γ g (c + 1) hhi))

No arithmetic, no assumption on the shape of either predicate, axioms
`[propext, Quot.sound]`.  It applies as soon as the room is
budget-sensitive at **one** instance, and §5 of the file exhibits one
inside the re-parameterised kernel's own band: `Sγ` = the piece-closure
of a single γ-clause `◯a ⊃ b`, `Γγ` everything but its consequent, so
`defect = 1` (`hd1` holds), `|jumpGoals Sγ| = 2`, room `4 ≤ c` — true at
`4`, false at `3`.  A budget-*insensitive* room is no escape either: it
is a `c`-free side condition, and the `c`-free kernel is already refuted
(`ReparamRefute.not_reparamKernelRoomFree`).

**Corollaries that diagnose the existing file exactly.**  The two
ledgers actually in `absorb_base` sit on opposite horns, each provably:

* `cascade_main`'s unshifted ledger meets **both** seal demands
  (`ledger0_seal1`, `ledger0_seal2`, proved in general) and **fails** the
  entry demand (`ledger0_entry_fails`) — which is why `cascade_main` is
  entered from `kcap_room`'s full allotment at the top and never from the
  holdout;
* `cascade_main_bf`'s shifted ledger meets the **entry** demand
  (`ledgerS_entry`, proved in general) and **fails** both seal demands
  (`ledgerS_seal1_fails`, `ledgerS_seal2_fails`) — which costs it
  nothing, because over a box-free space every sealed site is dead code.

And no constant in between exists: `shift_dilemma` bounds any shift below
by `|jumpGoals S| + 1` (entry) and above by `0` (γ-head seal) at one and
the same instance.  This is the precise, general form of the July
docstring's "short by `J+1` for every `X`".

**(c) THE ESCAPE, and it is already half-built.**  All three sealed
sites are `◯`-goal positions — site 1 and site 3 have enclosing goal
`◯D`, site 2's sealed obligation has goal `◯A₁`.  And PROGRESS §57's
`boxSnd_tight` (`wip/boxSndTight.lean`:147) says the `◯`-goal pair
descent is **budget-free**: it reaches the boxed goal clause at an
*arbitrary* target budget from a matched-budget source.
`wip/seal2Free.lean` carries that the last step, from the clause to the
target **value**:

    theorem gammaHead_budget_free (p) (S)
        (hOr : ∀ A B, A.or B ∉ S) {q} (hq : q ≠ p)
        (hsome : ∀ {A}, A.somehow ∈ S → A ∈ S)
        (f e c : Nat) (Γ Δ) (hΓS : ∀ Y ∈ Γ, Y ∈ S)
        (hamb : G4c Δ (itpE p S (f + 1) (e + 2) Γ))
        (hsrc : G4c Δ (itpA p S (f + 1) (e + 2) Γ ((prop q).somehow))) :
        G4c Δ (itpA p S (f + 2) (c + 1) Γ ((prop q).somehow))

`c` is universally quantified; **no room, no ledger, no defect bound**
appears (pinned by `#guard_msgs` on the `#check`).  The proof is
`boxSnd_tight` plus one free fuel conversion of the guard
(`fuelE_le`) and one `orAll` introduction — three lines.

So the ledger route was trying to finance something that does not need
financing.  **The design for round 4**: route every `◯`-goal position
through the boxSnd traversal, whose target budget is free, and keep the
seen-set ledger only for the non-`◯` goals, where it already works.

**Calibration to check first (the §57 lesson, applied in advance).**
`boxSnd_tight` consumes both premises at fuel `f+1` and concludes at
`f+2`, while `cascade_main`'s sealed sites hold the source at fuel `F`
and want the target at `fl` with only `F ≤ fl` — so at `F = fl` the
traversal lands one fuel level above the consumer.  Either the holdout's
`fh ≤ fuel` must be tightened to `fh < fuel` at its call sites, or the
traversal must be re-run one level down.  Check this against the
CONSUMER before building, exactly as §57 had to.

**Scope of (c).**  `∨`-free `S`, `◯`-subformula-closed `S`, `q ≠ p`, and
the goal body atomic.  Generalising the body from `prop q` to an
arbitrary `D ∈ S` is `boxGoal_remap`'s own case, not a new ledger, and it
is round 4's first target.

**Build state.**  `wip/absorb_base.lean` still has exactly ONE `sorry`
(the holdout, :2379); the standalone stack rebuilds
(absorb_base → adequacy → packaging → indiff → spaceindiff → final);
every `#guard_msgs` pin passes; the crown is unchanged:

    'PLLND.uniform_interpolation_PLL' depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

Regression: `lake exe towertest sizes 2` reproduces the twelve-row table
byte-identical; no table definition changed (zero files touched under
`LaxLogic/`, `wip/towerkit.lean`, `wip/towertest.lean`).

**Method note.**  §57 said "check the statement against the CONSUMER";
§58 added "check it against the repo's own refutations".  §59 adds the
cheapest of the three: **check the FINANCING before the proof.**  The
entry/seal dilemma is four lines of Lean and it rules out the whole
1500-line build the round was scoped for.

**Amendment (same session) — the atom restriction in (c) is NOT plumbing.**
`boxSnd_tight`'s substantive case is `boxGoal_remap`
(`wip/atomForce.lean`:382), and its value step is
`A@(c+1)(Γ', D) ⊢ A@(c+1)(Γ, D)` with `Γ ⊆ Γ'` — context *shrinking*,
which is unsound in general.  At `D = prop q` it is licensed by
`itpA_atom_forces` (the grown table forces the atom, and the atom is the
goal clause of the target table at *every* context); at a general body
there is no such licence.  So generalising the body is a genuine
mathematical step, not a re-statement.  Two ways round it are visible
and neither has been tried:

1. keep the traversal's target context in step with its source context
   (the shrinking step is only needed because the boxSnd recursion grows
   `Γ'` while the target `Γ` stays fixed) — at all three sealed sites the
   context does *not* grow, so a same-context traversal may suffice;
2. replace the goal-clause case by the holdout at the lex-smaller state
   `(c, defect S Γ, gsize D)`, which §59(a) shows is available for sites
   1 and 2 — but not for the truncation, which is why 1. is the one to
   try first.

## §60 (2026-08-05) — Round 4: the seals reduce to ONE room-free lemma, the fuel warning dissolves, and the `◯` is machine-screened load-bearing

`wip/round4Comp.lean`, `wip/round4Free.lean`, `wip/round4probe2.lean`,
`wip/round4probe3.lean` (all new, all sorry-free, all pinned).
`wip/absorb_base.lean` and everything below it are **untouched**; the
standalone stack rebuilds and the crown is unchanged.  The round's
four tasks were: financing analysis first, then semantic pre-check,
then the same-context traversal, then assembly.  Three landed; the
fourth is blocked on one identified mathematical step, reported below
with the exact reduction rather than a partial build.

**(a) TASK 0 — the positive twin of `no_ledger_survives_gamma_seal`,
type-checked.**  `cascade_low_pos_box` is consumed from exactly three
places in the whole development: the `cascade_low` calls at
`absorb_base`:2764, :3291 and :3516 (`grep -n "cascade_low "` finds no
others; `cascade_low_pos` is called only from `cascade_low`:2428 and
`cascade_low_pos_box` only from `cascade_low_pos`:2407).  So the
holdout is not a lemma the tower needs — it is a lemma **those three
sites** need, and killing the sites makes the `sorry` unreachable
whether or not it is ever proved.

All three reduce to **one** obligation:

    def BoxDesc (p : String) (S : Finset PLLFormula) : Prop :=
      ∀ (fs ft b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
        D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → fs ≤ ft → 1 ≤ b →
        G4c Δ (itpE p S ft (b + 1) Γ) →
        G4c Δ (itpA p S fs (b + 1) Γ D.somehow) →
        G4c Δ (itpA p S ft b Γ D.somehow)

— the holdout **restricted to `◯`-goals**, with `hroom`, `hd1` and
every ledger deleted.  `boxDesc_seal2` and `boxDesc_seal3` are
instances; `boxDesc_kills_site1` **eliminates** site 1 rather than
discharging it (site 1's own goal is the body `D`, but site 1 is only
reached inside the `g = ◯D` arm, and `BoxDesc` closes that arm before
the head is unfolded, using the caller's own continuation).
`boxDesc_discharges_the_seals` bundles all three,
`[propext, Quot.sound]`.

**Why this dodges round 3.**  Every use of `BoxDesc` is at the
*caller's own* budget, so `no_ledger_survives_gamma_seal`'s `hseal`
premise is never instantiated.  The dilemma needed both demands; the
architecture makes only `hentry` — which `LedgerS`, the shifted ledger
`cascade_main_bf` already runs on, satisfies in general
(`ledgerS_entry`, proved in round 3).  `shifted_ledger_is_entered`
re-exports it.  A room-carrying fallback `BoxDescR` is also
type-checked (`boxDescR_discharges_the_seals`): all three sites supply
the room **at the target budget** (`hroomW` at `c'+1` for sites 1 and
3, `hroomW0` at `c'` for site 2), so if the general body turns out to
need financing the composition does not change.

Two transcription discrepancies recorded: `sealLedger`'s `Seal2` omits
the `1 ≤ c'` that `cascade_low` demands and the site proves
(`seal2_room_gives_no_positivity` shows `Room` alone does not give it);
`Seal3` quantifies over `g ∈ S` while the site is inside
`cases g with | somehow D`.  Both are in the safe direction.

**(b) TASK 2 — the §59 fuel warning DISSOLVES.**  §59 warned that
`boxSnd_tight` lands one fuel level above the consumer and that either
`fh ≤ fuel` must be tightened to `fh < fuel` or the traversal re-run a
level down.  Neither is needed: the `+1` is an artefact of how
`tgtClause` is *written*, not of what the traversal proves.  The
target is produced in exactly one place, and there the guard slot is
never used (the source's guard is discharged against the grown
ambient) and the value slot is the forced atom.  So all four target
parameters are free:

    theorem tgtClause_relax (p) (S) (hOr) {q} (hq)
        {f c fg cg fv cv} {Γ Δ}
        (hΓS : ∀ Y ∈ Γ, Y ∈ S) (hf : f ≤ fg) (hc : c ≤ cg)
        (h : G4c Δ (tgtClause p S f c Γ q)) :
        G4c Δ (((itpE p S fg cg Γ).ifThen
          (itpA p S (fv + 1) cv Γ (prop q))).somehow)

and `boxDesc_atom_all` is `BoxDesc` at an **atomic** body with exactly
the sites' own calibration `fs ≤ ft` — no fuel tightening, no re-run.
The `ft ≤ 1` corner is absorbed by `itpA_one_budget_blind` (`by rfl`:
at fuel `1` every recursion sits at fuel `0`, where `itpE = ⊤` and
`itpA = ⊥`, so the table cannot read the budget).

**(c) TASK 1 — the `◯` is load-bearing, machine-screened.**  The
sharpest available test: `AscRefute.not_roomFreeDescent` refutes the
room-free descent at `gk = (◯r ⊃ s) ⊃ t` over `Sk` in the model `Mk`
at budget `1`.  Open `BoxDesc`'s target box and the obligation inside
looks like exactly that descent — so if the `◯` changed nothing, `Mk`
would refute `BoxDesc` too.  Add `◯gk` to `Sk` and ask the same model
at the same budget and fuels (`wip/round4probe3.lean`,
`decide +kernel`, `[propext, Quot.sound]`):

    unboxed_refuted   : checkB Mk 0 [srcU, ambB] tgtU = true
    boxed_survives    : checkB Mk 0 [srcB, ambB] tgtB = false
    boxed_survives_Mr : checkB Mr 0 [srcB, ambB] tgtB = false

The control fires and the boxed form survives — in both inventory
models, and (scratch, unpinned) also when the source is replaced by its
goal-clause disjunct alone, the strongest form of the instance.
`wip/round4probe2.lean` screens compound bodies at the `◯`-band room
floor countermodel-first over the ladder + default battery: 18 rows,
**zero** refutations, with the atomic control rows (theorems) coming
back `proved` as they must and the compound rows `proved` at the
gapped and higher-fuel calibrations.  No `Seal_i` obligation is false
at any admissible instance the repository can exhibit.

**(d) TASK 3 — NOT reached, and the reason is one identified step.**
`BoxDesc` at a general body is not `boxSnd_tight` with `prop q`
replaced.  §59's amendment named the context-shrinking value move; the
round's analysis sharpens it.  In the traversal the target is a fixed
formula because its value is the forced atom; at a general body the
value must instead be injected into the target's table **at the
context the traversal has grown to**, and the target's own `itpAenv`
supplies exactly the matching nested disjunct at each growth step — so
the shrink is avoidable.  What is *not* avoidable is the jump clause:
the target's env disjunct for `(A⊃B)⊃D` carries its first component one
budget below the source's, so injecting it needs a same-context descent
at the jump goal — the pigeonhole the ledger exists for.  So the
general-body `BoxDesc` is a **direct-form (value-concluding) clone of
`cascade_main`'s A-half**, which is the ~1500-line build §58 scoped.
It is available to be entered with the full ledger (`hroom` is in scope
at all three sites), and the entry demand is the only one it faces —
which is the round's contribution to it.

**(e) THE ASSEMBLY LANDED — the three sites are CLOSED in the file,
and the holdout is DELETED.**  (e) was written after (d): the analysis
in (d) says the *remaining mathematics* is a direct-form clone, but it
does not stop the restructuring, and the restructuring is what the
composition was for.  `wip/absorb_base.lean` now reads:

* `cascade_main`'s A-half splits on the **goal shape at its head** —
  `by_cases hbox : ∃ D, g = D.somehow`, inserted after the two
  `obtain`s and *before* `rw [itpA_succ] at hhead`.  A `◯`-goal is
  discharged outright by `cascade_boxgoal` and consumed by the
  caller's own continuation `hcls`.  No target disjunct is committed,
  so no seal is crossed and nothing is handed back one budget lower —
  `no_ledger_survives_gamma_seal`'s `hseal` is never instantiated;
* **old sealed site 1** (goal-γ disjunct, :2764) and **old sealed site
  3** (truncation disjunct, :3516) are now DEAD CODE — both sit inside
  a `cases g with | somehow D` arm and are closed by
  `exact absurd ⟨D, rfl⟩ hbox`.  Site 3 is the one §59(a) proved *no*
  `(budget, defect, goal-size)`-lex induction can discharge; it is
  gone, not financed;
* **old sealed site 2** (clause-γ-head, :3291) is a `cascade_boxgoal`
  instance outright, with `hroomW0` — the room **at the target
  budget** — passed straight through;
* `cascade_low_pos_box`, `cascade_low_pos` and `cascade_low` are
  **deleted**.  They had no other consumer anywhere in the
  development.  The chain is now
  `cascade_boxgoal → cascade_main → cascade_entry`.

`wip/absorb_base.lean` has **exactly one** `sorry` and it is now

    cascade_boxgoal_pos :
      ◯D ∈ S → Γ ⊆ S → fs ≤ ft → 1 ≤ b → 1 ≤ defect S Γ →
      defect S Γ · (|jumpGoals S| + 2) ≤ b →
      Δ ⊢ E@(ft, b+1)(Γ) → Δ ⊢ A@(fs, b+1)(Γ, ◯D) →
      Δ ⊢ A@(ft, b)(Γ, ◯D)

`cascade_boxgoal` dispatches `defect S Γ = 0` to the sorry-free
`cascade_zero`, which is why the obligation may be *stated* without
`hd1` while the `sorry` keeps it.

**STATEMENT CHANGE, FLAGGED.**  The file's open obligation is no
longer the general-goal pair descent.  It is a **weakening**, and the
weakening is certified rather than asserted:
`Round4.boxDescR_pos_of_holdout` (`wip/round4Comp.lean`) derives the
new obligation from `Holdout`, the deleted statement transcribed
verbatim.  Nothing stronger has been assumed, so no falsity can have
been introduced by the replacement.  Consumers adjusted: **none**
outside `cascade_main`; `cascade_low_pos_boxfree`, `cascade_main_bf`,
`cascade_zero` and the whole box-free tier are untouched.

**Build state.**  `wip/absorb_base.lean` has exactly ONE `sorry`
(`cascade_boxgoal_pos`); the standalone stack rebuilds
(absorb_base → adequacy → packaging → indiff → spaceindiff → final);
every `#guard_msgs` pin passes; the crown is unchanged:

    'PLLND.uniform_interpolation_PLL' depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

and it will stay that way until `cascade_boxgoal_pos` lands — but the
statement it is waiting on is now the `◯`-goal descent, not the
general-goal one, and two of the three positions that used to consume
it no longer exist.

Regression: `lake exe towertest sizes 2` reproduces the twelve-row
table byte-identical; zero files touched under `LaxLogic/`,
`wip/towerkit.lean`, `wip/towertest.lean`.

**Method note.**  §57 "check the statement against the CONSUMER"; §58
"check it against the repo's own refutations"; §59 "check the FINANCING
before the proof".  §60 adds the cheapest structural check of all:
**count the consumers.**  The holdout had been treated as a lemma the
tower needs; it is consumed from three places, all of one shape, and
that fact — three lines of `grep` — is what turns a 1500-line ledger
rebuild into a single room-free statement.

## §61 (2026-08-05) — Round 5: the `◯`-goal descent's own γ-row is the residue, no budget-sensitive hypothesis can finance it, and the statement's own regime probes clean

`wip/round5probe.lean`, `wip/round5probe2.lean`, `wip/round5core.lean`
(all new, all sorry-free, all pinned).  `wip/absorb_base.lean` and
everything below it are **untouched**: the one `sorry` is still
`cascade_boxgoal_pos`, exactly as round 4 left it.  The round's brief
was to prove it — the direct-form clone of `cascade_main`'s A-half —
and carried a hard constraint: STOP if the build ever needs a
seal-style demand (a hypothesis handed back one budget lower), because
`no_ledger_survives_gamma_seal` refutes that route.  The build reaches
that demand, from every design, at one and the same place; this round
pins the place, refutes every financing of it, finances everything
else, and screens the statement's own regime for the first time.

**(a) WHERE THE DEMAND ARISES — the γ-row self-recursion.**  Unfold
`cascade_boxgoal_pos`'s source `A@(fs, b+1)(Γ, ◯D)` one level.  For a
live γ-clause `◯A₁ ⊃ B₀ ∈ Γ` (`B₀ ∈ S ∖ Γ`) the γ-row contributes

    ( ◯( E@(b)(Γ) ⊃ A@(b)(Γ, ◯A₁) ) ) ∧ A@(b+1)(B₀::Γ, ◯D)

and, at a context with no bare `◯`-member (the general case: the
γ-context and `somehow`-χ rows need some `◯x ∈ Γ`), every disjunct of
the target `A@(ft, b)(Γ, ◯D)` that can absorb it pairs the grown
second component with a first component one budget down:

    ( ◯( E@(b-1)(Γ) ⊃ A@(b-1)(Γ, ◯A₁) ) ) ∧ A@(b)(B₀::Γ, ◯D)

(the truncation disjunct only re-enters the same analysis one box in).
Producing that component from the held one is the `◯`-goal descent
`b → b-1` at the SAME context and defect — an instance of
`cascade_boxgoal_pos` itself, one budget below its own room.  The
recursion is self-similar: the `◯`-goal table's γ-rows are the
recursion, each step dropping the budget by one, capped only by fuel.

**(b) WHY NO DESIGN ESCAPES — the two horns, and the repeat
asymmetry.**  The two workable traversal designs sit on opposite horns:

* **fire** (`boxSnd_tight`'s fixed-target design): every gated row is
  absorbed by firing the ambient's matching conjunct — at the tight
  budgets (`cascade_boxgoal_pos`'s ambient IS at the source's budget)
  the match is exact, room-free, defect-recursive.  Nothing lands
  except the source's goal row, and its landing is the context-SHRINK
  `A@(b+1)(Γ', D) ⊢ A@(b)(Γ, D)`, `Γ ⊆ Γ'` — licensed only by
  `itpA_atom_forces` at atomic bodies (§59's amendment), unsound in
  general.
* **map** (`cascade_zero`/`cascade_main`-style per-disjunct mapping):
  every row lands same-context; the jump rows are financed (see (d));
  the γ-row lands only through the boxed head one budget down — the
  demand of (a).

And the pigeonhole cannot rescue the map horn in direct form: a
continuation-form repeat lifts a deep low-budget value UP into a
pending high-budget slot (`itp_budget_mono_le`, the easy direction);
a direct-form repeat would need a value DOWN at a budget below
everything held, and there is no downward monotonicity.  This is the
precise content of July's "the target chain above a splice cannot be
rebuilt after the fact", and it is design-independent — which is also
why no statement renegotiation within the ledger family (seen-sets,
shifts) helps, and why no statement change is flagged this round.

**(c) THE REFUTATION — no side-condition family finances the
self-recursion** (`wip/round5core.lean`, pinned):

    theorem no_self_financed_crossing
        {Φ : Finset PLLFormula → List PLLFormula → Nat → Prop}
        (hsupply : ∀ S Γ c, 1 ≤ defect S Γ → Room S Γ c → Φ S Γ c)
        (hcross  : ∀ S Γ c, Φ S Γ (c + 1) → Φ S Γ c)
        (hneed   : ∀ S Γ c, Φ S Γ c → Room S Γ c) : False

with `room_not_descending` the `Φ := Room` instance, both at round 3's
`Sγ` (piece-closed, `◯a ∈ Sγ`, `defect = 1` — every hypothesis of the
statement is satisfiable there).  Round 3 refuted ledgers threaded
through `cascade_main`'s seals; this refutes every financing of the
round-4 architecture's OWN self-recursion: §60(e)'s "the architecture
makes only the entry demand" is true of the three call SITES and false
of the proof obligation inside `cascade_boxgoal_pos`.  Consequently
any proof must either

1. close the γ-row self-recursion with NO budget-sensitive hypothesis
   on the recursion path — i.e. prove the room-free descent
   (`Round4.BoxDesc`) there, as the atomic proof does by forcing; or
2. not recurse at the γ-row at all (a forcing-style direct production
   of the boxed component).

**(d) THE POSITIVE — the entry band is exactly two deep, so the jump
rows are NOT the obstruction** (`wip/round5core.lean`, pinned):

    theorem ledgerS_entry_two_below :
        x ∈ jumpGoals S → Room S Γ (c + 2) → LedgerS S Γ {x} c

and at `Sγ` the entry at `c = 1` — three below the room — fails
(`ledgerS_entry_dies_at_sγ`).  So the same-context CPS descents the
jump-row landings need can be ENTERED from the statement's bare room
down to two budget levels below it.  §60(d) flagged the jump clause as
the one case needing the pigeonhole; it is financed.  The residue is
the γ-row, not the jump row.

**(e) THE PROBES — the statement's own regime, screened for the first
time.**  Round 4's screens ran the `gam` family at budgets `1..3`;
that family's room is `4`, so every screened cell sat BELOW the floor,
in the room-free regime.  `wip/round5probe.lean` screens the floor
`b = 4` and slack-one `b = 5` at fuels `3` and `4` (deep enough for
two/three nested γ-row unfoldings), plus the γ-head crossing itself
(source component and ambient to the component one budget down, no
room in the sequent); `wip/round5probe2.lean` adds the
fresh-`⊃`-antecedent corner (body `x ⊃ y`, `x ∉ Γ`, `defect = 2`,
floor `b = 8`) — the one configuration where the guard-ascent step
inside the landing is room-priced.  Verdicts, verbatim:

    MAIN  ATOM/IMP/AND/BOX (gam, d=1, room=4):  P at (3,3,4) (4,4,4) (3,3,5) (4,4,5)
    GHEAD ATOM/IMP/AND/BOX (gam):               P at (3,3,4) (4,4,4) (3,3,5)
    MAIN  fresh-x (d=2, room=8):                P at (3,3,8) (4,4,8) (3,3,9) (3,3,4)
    GHEAD fresh-x:                              P at (3,3,8) (4,4,8) (3,3,4) (3,3,2)
    MAIN/GHEAD pres-x control (d=1, room=4):    P at (3,3,4) (4,4,4)

Zero refutations anywhere — including the crossing rows with no room
at all, and including cells well BELOW the floor.  Together with
`boxDesc_atom_all` (atomic case, room-free, PROVED) and
`Round4Probe3.box_is_load_bearing`, the machine evidence now points at
alternative 1 of (c): the room-free `◯`-goal descent is the true
statement, and `cascade_boxgoal_pos`'s room is dead weight its own
proof cannot even use.  (The small probe spaces close through
saturation-adjacent accidents — one growth step saturates, atoms
force — so the probes support but cannot decide the general case:
`AscRefute`'s `Sk` needed defect `8` to refute the unboxed form.)

**(f) ROUTE FOR ROUND 6 (OPEN, design sketch, not attempted).**  The
truncation-tower: conclude the target through its truncation row
(`laxR`, `impR` are free), so the budget descent becomes GUARD
accumulation — and under the accumulated guard the source's goal row
remaps with the guard budgets matching on the nose, turning the γ-row
self-recursion `◯A₁ at b-1` into the goal-size recursion `A₁ at the
landing` (alternative 1 of (c), room-free on the recursion path).  Its
residues, in order: (i) the fresh-`⊃`-antecedent guard ascent — 
financed from the bare room iff the E-half's room constant tightens
from `|jumpGoals S| + 3` to `|jumpGoals S| + 2`; the E-half's internal
arithmetic has slack `1` at its entry demand (`hroomA`), so the
tightening looks mechanical, but this is hand-checked only — OPEN;
(ii) ambient-carrying atom forcing over `∨`-spaces
(`itpA_atom_forces` assumes `∨`-freeness; the or-rows should split
against the ambient's or-conjunct, defect-recursively).

**Build state.**  `wip/absorb_base.lean` untouched, exactly ONE
`sorry` (`cascade_boxgoal_pos`); the standalone stack rebuilds
(absorb_base → adequacy → packaging → indiff → spaceindiff → final and
sealLedger → round4Comp → round4Free → round4probe → round4probe2 →
round4probe3, plus round5probe, round5probe2, round5core); every
`#guard_msgs` pin passes; the crown is unchanged:

    'PLLND.uniform_interpolation_PLL' depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

Regression: `lake exe towertest sizes 2` reproduces the twelve-row
table byte-identical; zero files touched under `LaxLogic/`,
`wip/towerkit.lean`, `wip/towertest.lean`.

**Method note.**  §57 "check the statement against the CONSUMER"; §58
"against the repo's refutations"; §59 "check the FINANCING before the
proof"; §60 "count the consumers".  §61 closes the circle: **check the
financing of the RECURSION, not only of the entry.**  An architecture
can make only the entry demand at its call sites and still make a seal
demand inside its own proof — the round-4 composition was sound about
the sites and silent about the self-call, and the four-line
`no_self_financed_crossing` would have caught it before any build was
scoped.

## §62 (2026-08-05) — Round 5, refute prong: the box-goal descent is SCREEN-CLEAN at and above its own room floor; every decide-feasible budget-active cell PROVED except three named ones

`wip/round5refute.lean` (kernel-pin schema + harness + families),
`wip/round5refute_bdefs.lean` (tower instance defs), stage/battery
runners `wip/round5refute_s1`–`_s4`, `_b`–`_g`, and the durable
cell-by-cell transcript `wip/round5refute_out.txt`.  Run concurrently
with §61's prove prong, in a separate detached worktree at `ea3a755`;
no existing file touched.

**Headline.**  `cascade_boxgoal_pos` is NOT refuted.  ~210 distinct
admissible cells were run — every cell machine-checked for
admissibility before counting: `S` piece-closed including `◯`,
`◯D ∈ S`, `Γ ⊆ S`, `defect ≥ 1`, `fs ≤ ft`, and the room
`defect·(J+2) ≤ b`; sub-room cells were never counted, since every
certified July failure sat ~30× below the room and refutes nothing
about this statement.  Aggregate: 176 `P` (searcher-proved), 68 `~`
(undecided at node budget), 128 size-SKIPs, **0 refutations**.  The
screen is live-fire calibrated: the harness reproduces round 4's
unboxed control (`CALIB(unboxed r4p3): R! as expected`), so a silent
screen is not a broken screen.  The pin schema
(`Round5Refute.BoxGoalPos`, `not_boxGoalPos_of_check`, pattern of
`RoomPin.not_roomDescent_of_check`) compiled ready for immediate use
had anything fired; nothing did.

**Structural finding A — the `J = 0` room band is budget-blind.**
With no jump-shaped member of `S`, no clause of the tables reads the
budget: `A@(ft, b+1) = A@(ft, b)` syntactically (`act = false` on
every such cell).  There the statement's budget-descent content is an
identity and only its fuel-gap content is live; every `act = false`
cell with `fs = ft` is true outright, so their `~`s are searcher
weakness, not open mathematics.

**Structural finding B — the active band, affirmatively proved.**
Budget-activity requires a live gate and fuel above the budget, which
confines decide-feasible active cells to defect 1, room 3–5.  All 42
active cells that fit were `P` except three:

* room 3, jump body `D = (a⊃b)⊃c` (four `S`-variants): 19 active
  cells, budgets 3–4, fuels 1..7 including gaps (1,6), (2,7) — all
  `P` (deepest: (7,7) at b=4, 50k nodes);
* room 4, `J = 2` `⊃◯`-gate band at the consuming sites' own shape
  (`D = a` and `D = a⊃b`): 9 active cells — all `P` (up to 424k
  nodes);
* room 3, nested-box jump body `D = ◯((a⊃b)⊃c)`: 11 active cells —
  8 `P`, **3 residual `~`**: `(fs,ft) = (5,5), (4,5), (1,5)` at
  `b = 3`.  No countermodel over the widened battery (5-world chains,
  rigid chains, forks + defaults); unproved at 30000 search nodes
  ((5,5): 403 s).  OPEN-at-budget.  Their `b = 4` neighbours and both
  fuel-gapped `b = 3` siblings are all `P`.

The fuel-gap dimension (`fs = 1, 2` against `ft` up to 7) screened
clean throughout.  The July family was screened **at its own room for
the first time** (`Skb = insert ◯gk Sk`, `D = gk`): `P` at `b = 7/8`
saturated variants; the remaining July cells are budget-blind at
truncating fuels.  The configuration that generated every July
refutation does not touch the box-goal statement in its own band.

**What the clean screen does NOT rule out.**  It is not a proof; the
three residual nested-box cells are genuinely undecided; and the
size-infeasible regions — dense gate towers at active fuels (0.9–17M
nodes), all defect ≥ 2 active bands (room ≥ 6 forces fuel ≥ 7), July
rows at `ft ≥ 5` — were screened not at all or only at truncating
fuels.  Any refutation living only there is invisible to this method
(and would also be beyond `decide +kernel` to pin).  Mitigation, not
proof: every refutation in the repository's history appeared at the
smallest instances of its family, and the cascade's own recursion
drives defect down toward the screened defect-1 floor.  Battery
limits: frames ≤ 5 worlds, closure emitter off.

**Caveats for the record.**  `_d`/`_e` originally used a leading-comma
field layout inside a `with`-update, which Lean rejects at parse and
recovers by dropping the field; their recorded runs therefore used the
default adaptive fuel grid (a superset of the intended cells; headers
and admissibility all correct).  Sources since corrected to match what
ran.  Lean trap worth keeping: leading-comma field layout is fine in
plain structure literals, invalid in `with`-updates.  Battery B (dense
towers) and the `i53` tail were deliberately killed after every cell
proved size-infeasible; `i15`/`i53` fuel bounds in `round5refute.lean`
post-date the recorded run.  The stage runners are committed as
recorded artifacts with `round5refute_out.txt` as the durable
transcript; re-executing them re-runs multi-minute batteries.

**Round-5 verdict, both prongs.**  The refute prong finds nothing
false and affirmatively proves every feasible budget-active cell
except three named ones; the prove prong (§61) locates the precise
obstruction (the γ-row self-recursion's seal-style demand,
`no_self_financed_crossing`) and certifies the way forward
(`boxgoal_pos_of_boxDesc`: the room-free `BoxDesc` suffices).
`cascade_boxgoal_pos` remains OPEN — supported by the strongest
positive screen this family has had, blocked by a machine-checked
financing obstruction, with the truncation-tower design of §61(f) as
the concrete round-6 attack and the three `JB2` cells at `b = 3` as
the sharpest place to aim any further doubt.

## §63 (2026-08-05) — Round 6: both named residues of the truncation-tower LANDED (the E-half tightens to `J+2`; atom forcing over `∨`-spaces), and the tower's financing is BANDED — dead at the second same-context γ-crossing

`wip/round6core.lean`, `wip/round6force.lean` (both new, both sorry-free,
all pinned).  `wip/absorb_base.lean` and everything below it are
**untouched**: the one `sorry` is still `cascade_boxgoal_pos`, exactly as
round 4 left it.  The round's brief was to prove the room-free
`Round4.BoxDesc` at general bodies via the truncation-tower design of
§61(f), attacking its two named residues first.  Both residues fell —
and are now theorems available to any future build — but assembling the
tower exposed a THIRD gate §61(f) did not name, and that gate is
machine-refuted at its exact boundary.  Per the round's fallback rules
the obstruction is delivered pinned, with the reduction it leaves.

**(a) RESIDUE (i) LANDED — the E-half room constant tightens,
`J+3 → J+2`** (`Round6.easc_tight`).  The one-step budget ascent
`E@(f,c)(Γ) → E@(f,c+1)(Γ)` holds under

    (jumpGoals S).card + 2 + defect S Γ · ((jumpGoals S).card + 2) ≤ c

— `cascade_main`'s E-half transcribed with the constant lowered and every
internal `omega` re-closed.  §61(f)(i)'s hand-check was right: the entry
demand `hroomA` closes with ZERO slack from `+2` (so `+2` is exact), and
the two grown-context demands (`hEg`, `hAg`) have a whole defect level of
slack each.  The statement is parametric in `EntryDesc` — the
entry-shaped same-context descent at a singleton seen-set, the ONE
interface through which the E-half consumes the A-half (`hAd`/`hAg`),
which `cascade_main`'s own `ihfA` supplies verbatim inside
`wip/absorb_base.lean`; `cascade_main` being `private`, the parametric
form is what a standalone file can certify, and it is also exactly the
shape a transplant would consume.  Why it matters:
`tight_ascent_from_room` shows the tightened demand at any defect-paying
grown context follows from the BARE room `defect·(J+2) ≤ b` —
`cascade_boxgoal_pos`'s only budget hypothesis — and `tight_exact_at_sγ`
pins that the `+3` form FAILS at the same instance (`Sγ` floor, grown
context saturated).  So the defect-paying guard ascents of the tower
(fresh `⊃`-antecedent, `somehow`-χ, γ-context rows) are financed by the
statement's own room if and only if the tightening holds.  It holds.

**(b) RESIDUE (ii) LANDED — ambient-carrying atom forcing over
`∨`-spaces** (`Round6Force.itpA_atom_forces_amb`).

    q ≠ p → Γ ⊆ S → Δ ⊢ E@(f,e+2)(Γ) → Δ ⊢ A@(f,e+2)(Γ, q) → Δ ⊢ q

**No `∨`-freeness hypothesis.**  The or-rows split against the ambient's
or-conjunct `E(A::Γ) ∨ E(B::Γ)`, defect-recursively, exactly as §61(f)(ii)
prescribed; every other growth row fires the ambient's matching conjunct
(the `grown_*`/`tGrownAmb_*` apparatus at matched budgets).  The ambient
and source sit at matched fuel and budget — the configuration
`boxSnd_tight`'s traversal holds at every step — so the lift is
consumable wherever `AtomForce.itpA_atom_forces` was, by any caller that
carries the ambient (all of them do).  What is PROVED is the forcing
lemma itself; extending the lift to the whole atomic tier
(`boxDesc_atom_all`, `gammaHead_budget_free`) needs two adjustments to
`boxSnd_tight`'s traversal — the same or-split at its or-case, and the
goal-clause value switched from the bare to the ambient-carrying
forcing (available there: the traversal holds the grown ambient at the
matched budget) — both by the moves of this file, but NOT re-run this
round, so the tier-wide statements keep their `∨`-free hypothesis for
now.

**(c) THE THIRD GATE — the tower's financing is BANDED, and the band is
too shallow.**  Assembling §61(f)'s tower: conclude the target through
its truncation row, accumulating a guard per budget level; the source's
γ-head rows land goal-size (the accumulated guard fires the held value's
goal row with the guard budgets matching on the nose), so each
same-context γ-crossing turns into (1) a same-context CPS entry
(`LedgerS`, the shifted spine) for the landing body one budget further
down, and (2), when the γ-clause body is itself `◯`-shaped, a further
tower level at the same context and defect.  The entries are financed by
the bare room in a BAND, pinned at both ends
(`tower_entry_depth0/1/2`, round 5's `ledgerS_entry_two_below` and
`ledgerS_entry_dies_at_sγ`, and the new `S3` pins):

* landing body a JUMP GOAL of the space (the γ-clause bodies): financed
  at `c ∈ [b−2, b]`, dead at `b−3`;
* landing body GENERIC (the goal-row body of a nested tower level):
  financed at `c ∈ [b−1, b]` — `depth1_entry_exact_at_s3` holds with
  zero slack — dead at `b−2`: `no_depth2_entry_at_s3`.

The witness `S3` = piece-closure of `◯◯(a⊃b) ⊃ c` (defect 1, `J = 2`,
room floor 4, `s3_nested_gamma`): its γ-clause has a BOXED body, so the
first γ-crossing's landing is again a `◯`-goal, the tower recurses a
second budget down at the same context, and the second crossing's
goal-row body `a⊃b` — not a jump goal of `S3` — needs the entry at
`c = b−2 = 2`, where `LedgerS` demands `7 ≤ 6`.  One clause, one nest,
one budget short.

**(d) No family escapes the band** (`Round6.no_self_financed_nest`).
Round 5's `no_self_financed_crossing` refuted side-condition families
that must re-supply the room at their own level.  The tower's entries
demand strictly less — only `Room` two levels up (`hneed : Φ c →
Room (c+2)`, the two-below entry).  Even that dies: supplied from the
bare room, surviving one budget drop per crossing, and paying the
two-below entry at each level, the family contradicts `sγ_room_lo` after
THREE crossings.  Four hypotheses, no arithmetic beyond the `Sγ`
instance.  So the band of (c) is not an artefact of `LedgerS`: no ledger
family extends it by a single level, and §61(c)'s dichotomy sharpens —
on the recursion path below depth two there can be no budget-sensitive
hypothesis AT ALL, not even a two-below one.

**(e) What remains, exactly.**  The tower closes every case of the
`◯`-goal descent EXCEPT: a same-context γ-nest of depth ≥ 2 whose
landing bodies are compound — which requires a γ-clause with a boxed
body (`◯◯E ⊃ B ∈ S`, the `S3` shape).  Everything else is financed:
defect-paying steps regenerate the room; guard ascents fit exactly by
(a); atomic landings are free at any depth by (b) plus the ambient the
tower always holds (over `∨`-spaces once the traversal repeats (b)'s
or-split); jump-row and goal-row landings enter the spine within the
band.  The unfinanced configuration is precisely the
nested-box shape of the refute prong's three residual `JB2` cells
(§62, `b = 3`, `D = ◯((a⊃b)⊃c)`, still OPEN-at-budget) — the machine
evidence thus concentrates prove-side and refute-side residue on the
SAME shape.  Round-7 forks: (1) alternative 2 of §61(c) at depth ≥ 2
only — a forcing-style direct production of the boxed γ-component from
the accumulated guard stack (the guards `E@(b−1)…E@(b−k)` are held
there, and they are the one resource the financing analysis does not
price); or (2) aim the deepened battery at the three `JB2` cells: a
refutation there would kill `cascade_boxgoal_pos` as stated and
re-open the statement, not the proof.

**Build state.**  `wip/absorb_base.lean` untouched, exactly ONE `sorry`
(`cascade_boxgoal_pos`); the standalone stack rebuilds from a fresh
`.dep` in the pinned order (absorb_base → adequacy → packaging → indiff
→ spaceindiff → final → sealLedger → round4Comp → round4Free →
round4probe → round4probe2 → round4probe3 → round5core → round5probe →
round5probe2 → round5refute → round5refute_bdefs → round6core →
round6force); every `#guard_msgs` pin passes; the crown is unchanged:

    'PLLND.uniform_interpolation_PLL' depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

Regression: `lake exe towertest sizes 2` reproduces the twelve-row table
byte-identical; zero files touched under `LaxLogic/`, `wip/towerkit.lean`,
`wip/towertest.lean`.

**Method note.**  §59 "check the FINANCING before the proof"; §61 "check
the financing of the RECURSION".  §63 closes the sequence: **check the
financing at every DEPTH of the recursion.**  A design can be financed at
its call sites (§60), financed at its first self-call (§61(d)'s entry
band), and still die at a fixed finite depth — the band must be computed
before the build is scoped, and here it is two levels wide against a
recursion of unbounded depth.

## §64 (2026-08-05) — Round 6, refute prong: the room-free `BoxDesc` is SCREEN-CLEAN across the sub-room band, including the July family at budgets 1–3

`wip/round6refute.lean` (pin schema + room-gate-free harness + families),
stage runners `wip/round6refute_s1`–`_s9`, durable transcripts
`wip/round6refute_out.txt` / `_out2.txt`.  Run concurrently with the
round-6 prove prong (§63), in the round-5 detached worktree at `762fc23`;
no existing file touched.

**Headline.**  `Round4.BoxDesc` is NOT refuted.  The statement's
room-freeness opened a band no round had swept: every certified July
refutation of the unboxed descent sat ~30× below its room, and the
room-carrying round-5 screen (§62) was barred from that band by its own
admissibility floor.  This round swept it: 863 two-sided verdicts over
693 admissible cells (`◯D ∈ S`, `Γ ⊆ S`, `fs ≤ ft`, `1 ≤ b`, `S`
piece-closed), 695 sub-room, **zero refutations**.  The refutation
schema `not_boxDesc_of_check` (`[propext, Quot.sound]`, pinned) needs no
closure hypotheses — `BoxDesc` as stated has none, so ANY firing cell
would have killed it; none fired.  Calibration fired in the refuting
direction (`R!` on round 4's unboxed control, 16 ms) and, new, the boxed
July cell survived the FULL 22-frame battery, extending
`boxed_survives` from two fixed models to all 22 frames.

**The July family sub-room, first sweep.**  `Skb`/`Sk` at `ctx = Gk`
(defect 8–9, room 56–63), bodies `gk`, `r`, `p`, budgets 1–3, six fuel
calibrations: no battery frame refutes any cell — and no cell proves
either, at up to 20000 nodes and 1843 s/cell.  The band is two-sidedly
undecided; the saturated defect-1 variants prove (33/36), `miss-t` and
the defect 2–3 contexts stay open or size-out.  The configuration that
generated every July refutation does not touch the boxed statement even
in its own budget range.

**The ∨-band, screened hard** (the prove prong's sub-task (ii)
surface): ∨-bodies boxed once/twice, ∨ under and inside jump gates, ∨
as gate consequent — 129/135 cells PROVED at depth, 2 residual `~`,
zero countermodels.  The least-exercised apparatus is the
best-behaved.

**The §62 residual JB2 cells at 10×.**  `(1,5)`, `(4,5)`, `(5,5)` at
`b = 3` re-run at 300000 nodes (19–64 min each): still `~`, still no
countermodel.  OPEN-at-budget, now at 10× the round-5 budget.

**Method caveats, recorded.**  The closure emitter never ran anywhere:
measured closures (30–158, stage-9 instrumentation) exceed every
feasible cap, so the negative side of the whole screen is the ≤5-world
battery alone.  A refutation needing a larger or off-battery model is
invisible to this method — and would also be beyond `decide +kernel` to
pin.  The mitigation stands as in §62: every historical refutation in
this repository appeared at the smallest instances of its family, and
those instances are now swept clean both above (§62) and below (this
section) the room.  Runner provenance: `_s5`/`_s6` were killed
externally mid-run; `_s7`/`_s8` are their recorded re-runs (documented
in their docstrings); `_s5`/`_s6` have no oleans and are committed as
recorded artifacts only.  Unswept: budgets 4–7 under rooms ≥ 8;
defect-0 contexts (admitted by `BoxDesc`, excluded by every family);
fuels beyond 6; 91 size-SKIPs.

**Verdict for round 6, both prongs.**  The room hypothesis of
`cascade_boxgoal_pos` is not certified necessary: no sub-room
countermodel exists within the screen's reach.  §63's financing
frontier (the depth ≥ 2 same-context γ-nest at compound landing bodies)
therefore stands unrefuted on BOTH sides of the room floor — the
statement looks true everywhere any instrument can reach, while every
self-financed proof design provably dies at depth 3.  The sharpest
remaining doubt sits in the two-sidedly undecided July defect ≥ 8
sub-room band and the three JB2 cells, none of which any instrument in
the repository can currently settle in either direction.  Round-7 forks
as recorded in §63(e), now to be entered through the frontier sampler
(§65) per the reach-over-completeness rule.

## §65 (2026-08-05) — The frontier sampler: 948 admissible cells over 19 strata, zero refutations, and the room-carrying statement's live regime measured and pinned unreachable wherever a γ-clause is present

`wip/frontierCore.lean`, `wip/frontier.lean`, `wip/frontier_pin.lean`
(all new, all sorry-free, all pinned), runners `wip/frontier_show` /
`_run` / `_run2` / `_replay` / `_row`, the calibration
`wip/frontier_calib.lean`, the wall-clock wrapper
`wip/_probe_elab.sh`, the cumulative corpus `wip/frontier_corpus.txt`
(1072 records) and `wip/frontier_replay.txt`.  A standalone skeleton of
the generic layer sits at `tools/FrontierSampler/`, unreferenced by the
main lakefile.  `wip/absorb_base.lean` and everything below it are
**untouched**; the one `sorry` is still `cascade_boxgoal_pos`.  Built
by a delegated agent in a separate detached worktree at `33548e4`,
commissioned on Matthew's completeness-vs-reach critique (2026-08-05).

**The brief.**  §§59–63 screened by exhaustive sweeps over small
bounded regions, re-scoped per formula as each arose.  The shape that
mattered in round 6 — a space with a doubly-boxed γ-clause `◯◯E ⊃ B`,
witness `S3` — sat one `◯`-nesting level beyond the swept region and
was found proof-side two rounds later.  This section is the other
method: sample sparsely and broadly along the axes the tables branch
on, one structural level beyond current use, and never re-derive the
region per formula.

**(a) THE HARNESS.**  Nineteen strata: γ-clause `◯`-nesting depth 1
(the swept region), 2 (the §63 frontier), **3** (one beyond);
goal-body shape atom / jump / nested-box / ∨-carrying; ∨-density
0/1/2; jump count `J`; defect 1/2; the eliminated variable inside `S`.
Generation is constructive — a seeded formula, its piece-closure, `◯D`
re-closed in, `Γ = S ∖ drop` with the drop biased toward
clause-completing members — so cells are admissible by construction,
and six machine gates transcribed from the statement's hypotheses
confirm it (`gated-out = 0` over 1072 records).  Triage is
**countermodel-only**: `refute?` with `emitClosureCap := 0`, i.e. the
certified battery and nothing else — no proof search, no exponential
emitter.  Every cell appends and flushes one corpus line before the
next begins.  Generation uses `Plausible.Gen` — the repo already
carries it via mathlib — through `runRandWith` with a splitmix step
(`Gen.run` is unseeded, and `mkStdGen` gave seeds 1000/1009/1017 the
same formula).

**(b) THE RESULT — nothing false, at 948 cells.**  Campaign 1 (15
strata) 692 counted, campaign 2 (4 strata) 256, **0 refutations**, 124
size-skips at the 40 000-node cap, live-fire calibrated against round
4's unboxed control at every run.  `Round4.BoxDesc` was screened at
sub-room budgets throughout, so its room-free content is included; a
hit there would have killed the round-7 prove route, and there was
none.

**(c) THE MEASUREMENT, AND ITS LEMMA.**  Of campaign 1's 692 cells,
only **12** were simultaneously room-admissible, budget-active and
non-trivial — all in the one stratum with no γ-clause.  The arithmetic
explains it and `wip/frontier_pin.lean` pins it:
`two_le_jumpGoals_of_gamma` (a γ-clause `◯X ⊃ B ∈ S` puts **both** `X`
and `◯X` in `jumpGoals`, and they are distinct), hence
`four_le_budget_of_gamma` (room + `1 ≤ defect` forces `4 ≤ b`), hence
fuel `≥ 5`, hence tables of 10⁵–10⁶ nodes — past `checkB`.  **The
room-carrying statement's own live regime is not decide-feasible
wherever a γ-clause is present.**  `three_le_budget_of_j1` gives the
escape: at `J = 1` the room is 3 and the band is reachable.  This is
the sampling-side counterpart of §62's structural finding A, and it is
now a theorem rather than an observation.

**(d) CAMPAIGN 2, AIMED BY (c).**  Four `J = 1` strata in the
reachable band: `jb1-imp` (`D = (x⊃y)⊃z`, round 5's JB family),
**`jb1-nbox` (`D = ◯((x⊃y)⊃z)` — a randomised generalisation of §62's
three residual JB2 cells)**, `jb1-nbox2` (one `◯` beyond them),
`jb1-atom2`.  27 live cells against campaign 1's 12; 0 refutations.
The JB2 residue shape and the level beyond it both screen clean under
randomisation — weak positive evidence for the statement, and against
§63(e)'s fork (2).

**(e) WHAT THE SCREEN DOES NOT RULE OUT.**  It is not a proof.  Cells
above 40 000 nodes were not run (124 of them); defect ≥ 2 contributes
sub-room cells only (room ≥ 6 forces fuel ≥ 7); the battery is ≤ 5
worlds with the closure emitter off; and 265 of the 948 counted cells
are syntactically vacuous (`src = tgt`, which happens exactly when
`fs = ft` and the budget is inactive) and are excluded from the live
counts above.  Two replay passes aimed at *different* statements — the
unboxed room-free descent, and the statement with the ambient premise
dropped — returned **no hits over 683 non-trivial cells**, which
measures the battery's reach at these sizes at least as much as it
measures the statements.

**(f) REPLAY, ASSESSED PLAINLY.**  The corpus is replayable: 1072 of
1072 records regenerate with identical shape columns from
`(stratum, seed, size)` alone, including campaign 1's records after
campaign 2's generator refactor.  That determinism audit is replay's
only demonstrated yield so far; the two re-aim passes found nothing.
Its designed value is at statement-change time — when round 7 revises
`cascade_boxgoal_pos`, 948 admissible instances are available for a
certificate-check pass at zero generation cost.  **If that pass is
also empty, the replay layer should be pruned rather than carried**
(explore first, prune later — Matthew's stated principle).

**Sharing stance.**  `tools/FrontierSampler/SHARING.md` leads with
Matthew's named prerequisites (the mechanisms must be proved against
tasks beyond proof/model theory before any generalisation or
publication) and records that the default is NOT to publish;
recommendation as written there: leave it in-tree.  One ungated piece:
a small upstream note to Plausible that `Gen.run` is unseeded and
`mkStdGen` diffuses consecutive seeds poorly, with a pure
`Gen.runWithSeed` — a Plausible observation, not a publication of this
tool.  Ecosystem picture (verified by web search, URLs in the README):
Plausible is the Lean 4 QuickCheck descendant (ex-SlimCheck, split out
2024-11); constrained *generation* exists outside it
(Chamelean/Specimen, Palamedes); stratification with per-region sample
budgets, certificate-carrying persistent corpora, and cross-property
replay were found in no Lean tool, and mostly in no tool anywhere.

**Build state.**  `wip/absorb_base.lean` untouched, exactly ONE
`sorry`; nothing under `LaxLogic/` modified; the new files build in
order `frontierCore → frontier → frontier_pin` from the pinned `.dep`;
all four `#guard_msgs` pins pass, transcribed from actual output.
`wip/round5refute.lean`'s admissibility instruments are imported, not
reimplemented.

**Method note (standing rule, adopted).**  §59 "check the FINANCING
before the proof"; §61 "the financing of the RECURSION"; §63 "the
financing at every DEPTH".  §65 adds the cheap prior step: **each
round's residue shape defines the next sampler stratum, and the
sampler runs before any proof build is scoped.**  A stratum costs
minutes of countermodel checking; a mis-scoped proof build costs a
round.  Corollary, from (c): when a sampler cannot reach a statement's
live regime, that unreachability is itself a result — compute it, pin
it, and re-aim the next campaign at the band where the regime *is*
reachable.

## §66 (2026-08-05) — Round 7, prove prong: fork (1) enters through the replay layer — the boxed-component production (`CompProd`) stated and screened two-sidedly, its band pinned at both ends, the γ-head case certified to factor through it room-free, and the goal-row landing refuted at EVERY ambient elevation: the two §61(c) horns meet at one machine-checked wall

`wip/round7core.lean`, `wip/round7pin.lean` (both new, both sorry-free,
all pinned); replay drivers `wip/frontier_g7.lean` / `_g7b` / `_g7c`
(recorded artifacts; durable transcript `wip/frontier_g7.txt`).
`wip/absorb_base.lean` and everything below it are **untouched**: the one
`sorry` is still `cascade_boxgoal_pos`.  The round's brief was §63(e)'s
fork (1) — produce the boxed γ-component directly from the accumulated
guard stack — under the §65 standing rule: candidates STATED and REPLAYED
over the corpus before any build is scoped.  The rule earned its keep:
the replay verdicts re-scoped the build twice before a line of proof was
written, and the one build-shaped step that was attempted anyway
(the direct walk's goal-row landing) turned out to be kernel-refutable —
found by a 10-second targeted probe, pinned the same hour.

**(a) THE GUARD STACK IS FREE — AND THAT CUTS BOTH WAYS.**  The design
observation that reframes fork (1): every guard the truncation tower
accumulates (`E@(b−1)(Γ) … E@(b−k)(Γ)`, same context) is derivable from
the statement's own ambient `E@(ft, b+1)(Γ)` by downward budget
monotonicity (`ambE`).  So the "unpriced resource" of §63(e) costs
nothing — and supplies nothing beyond the ambient.  What it DOES license:
every boxed row of the source can be OPENED (`laxL` under a boxed goal,
guard fired by the lowered ambient), so the γ-head self-recursion becomes
a gap-preserving pair recursion `(b, c) → (b−1, c−1)` on the held
components, with NO budget-sensitive hypothesis per level — the demand
profile that escapes `no_self_financed_nest` (which kills per-level
`Room (c+2)` demands, not demand-free descents).

**(b) THE CANDIDATE** (stated first, per the standing rule) — the
production of the boxed γ-head component, ROOM-FREE
(`Round7.CompProd`):

    for all fs ≤ ft, 1 ≤ c ≤ b, Γ ⊆ S, ◯D ∈ S:
      Δ ⊢ E@(ft, b+1)(Γ)                          (the ambient)
      Δ ⊢ ◯( E@(fs, b)(Γ) ⊃ A@(fs, b)(Γ, ◯D) )   (the held component)
      ────────────────────────────────────────────
      Δ ⊢ ◯( E@(ft, c)(Γ) ⊃ A@(ft, c)(Γ, ◯D) )

This is the exact shape of the γ-row landing: the first conjunct of the
target's γ-head disjunct is a `CompProd` conclusion
(`Round7.gammaComp_lands`), and the source's γ-head row hands exactly the
premise component.

**(c) THE REPLAY VERDICTS — the corpus's first decisive value test.**
Ten passes over the 1072-record corpus (683 non-trivially run cells),
zero generation cost, countermodel-only, live-fire calibrated per pass:

    Z  control: production at c=0            344 HITS (calibration)
    A  from the table, c=b−1                 0 hits over 1072
    B  from the table, c=1 (the deep end)    0 hits
    C  committed goal clause, c=b−1          0 hits
    D  committed goal clause, c=1            0 hits
    G  from the component, c=b−1 (γ-cells)   0 hits
    H  from the component, c=1  (γ-cells)    0 hits
    T  gap-recursion bottom, γ-body          0 hits
    U  gap-recursion bottom, goal body       0 hits
    V  bottom + grown conjunct               0 hits

Pass C's cleanness is a surprise worth recording: committing the target
to its own goal disjunct — the "fire"-horn extension §61(b) argued
unsound as a LEMMA — is nowhere refuted as a STATEMENT, compound bodies
included.  The control matters as much as the clean rows: 344 kernel-
checkable certificates at `c = 0` prove the pass machinery can fire on
exactly this sequent shape, so the nine silent rows are calibrated
silence.

**(d) THE BAND, PINNED AT BOTH ENDS.**  `Round7Pin.comp0_refuted`
(+ `comp0_not_derivable`, both `[propext, Quot.sound]`): at `c = 0` the
production fails — corpus cell `d1-atom/1021`, a one-world model; at
budget 0 the component's value table degenerates to a boxed negation of
the live atoms.  `Round7.compProd_gap0`: at `c = b` the production is
unconditional (open, fire with the lowered ambient, lift the fuel,
re-box).  The open content of `CompProd` is exactly the band
`1 ≤ c < b`.

**(e) THE REDUCTIONS** (`wip/round7core.lean`, sorry-free):
`compProd_of_boxDesc` — the production follows from the room-free
`Round4.BoxDesc` by opening the component and iterating the descent with
the ambient re-lowered at every step (no room anywhere); hence
`not_boxDesc_of_not_compProd`: any countermodel to `CompProd` at
admissible parameters refutes `BoxDesc` itself.  Passes G/H are thereby
two-sided instruments for the room-free route as a whole — and they came
back clean.

**(f) THE NEW NEGATIVE — the goal-row landing dies at EVERY ambient
elevation** (`Round7Pin.goalrow_landing_refuted_elev1/_elev2`,
`goalrow_landing_not_derivable`, all `[propext, Quot.sound]`).  Inside
any value-concluding walk (of `CompProd` or of `cascade_boxgoal_pos`
itself), the source's goal row opens to the UNBOXED value
`A@(b)(Γ, D)` and the target's goal row needs `A@(c)(Γ, D)`, `c < b`,
same context.  July's `Mk` refuted that descent at MATCHED budgets
(ambient = source); the walk's inner positions are better off by one
budget of ambient (top ambient `b+1` against a fired value at `b`), so
the matched refutation left a gap.  Closed: `Mk` refutes the landing
with the ambient elevated by one AND by two.  The elevation is not
load-bearing.  Consequently the goal rows of any direct walk MUST be
treated in continuation form (the pigeonhole), which is room-priced
through the spine — against `CompProd`'s room-free statement.

**(g) THE S3 INSTANCE — the bottom is not only clean, it is PROVED.**
The gap-preserving recursion bottoms at `c = 1` (the source's γ-head row
hands a budget-1 component against a budget-1 table).  At the round-6
witness (`S3`/`Γ3`, the space that killed the tower), at the room floor
`b = 4` and the budget-active reference fuel `fs = ft = 5`:

    [ comp@1 , grown@2 , amb@5 ] ⊢ A@(5,1)(Γ3, ◯◯(a⊃b))   P (40000)
    [ comp@1 , amb@5 ]           ⊢ A@(5,1)(Γ3, ◯◯(a⊃b))   P (40000)

— searcher-PROVED, certificate-carrying, even WITHOUT the grown
conjunct (the `fs = ft = 2` truncating-fuel variants stay `~`, searcher
weakness at a nearly-degenerate component).  The bottom of the fork-1
recursion is affirmatively derivable at the exact configuration that
was the round-6 residue.

**(h) WHERE THE RESIDUE NOW STANDS — one wall, seen from every side.**
Fork (1) delimits as follows.  (i) The γ-head rows of the `◯`-goal
descent factor through `CompProd` room-free — and IF `CompProd` were
proved, the walk's spine would enter once, at depth 0 (`tower_entry_depth0`
from the bare room): §63(c)'s per-crossing entry band evaporates, because
the crossings live inside `CompProd`'s recursion, not on the spine.
(ii) `CompProd`'s own direct proof closes room-free at boxed bodies
(size recursion), atomic bodies (ambient-carrying forcing, §63(b)) and
its bottom (screened clean; PROVED at the witness) — and is obstructed
at exactly one place: its goal rows at compound UNBOXED cores
(jump-shaped `D`), where the pointwise landing is kernel-refuted at
every elevation (f) and the continuation-form alternative re-imports the
room-priced pigeonhole against a room-free statement.  The prove-side
residue of the entire campaign is now a single named lemma shape:

    RESIDUE (round 8): `CompProd` restricted to the goal-row case at
    jump-shaped unboxed bodies — equivalently, absorb the source's goal
    row `◯(E@(b−1) ⊃ A@(b)(Γ, D))` into the target's table at `c < b`
    from the ambient alone, `D` compound unboxed, WITHOUT the pointwise
    descent (refuted) and WITHOUT a budget-priced side condition
    (`no_self_financed_nest`).

Everything else — both horns of §61(c), the §63(c) band, the bottom,
the atomic tier, the ∨-tier — is either proved, financed, or reduced to
this.

**(i) REPLAY VALUE VERDICT: KEEP.**  §65(f) set the test: if the
round-7 pass answers nothing fresh screening wouldn't, prune the layer.
It answered: ten statement-variants screened at zero generation cost in
one afternoon, one boundary (c = 0) certified refuted at 344 known-
admissible instances, two candidate re-scopings before any build, and
the S3 bottom aimed by the recursion analysis the passes made possible.
This is the designed statement-change-time use, delivered.

**Build state.**  `wip/absorb_base.lean` untouched, exactly ONE `sorry`
(`cascade_boxgoal_pos`, :2269); full stack rebuilt from fresh `.dep` in
the pinned order (absorb_base → adequacy → packaging → indiff →
spaceindiff → final → sealLedger → round4Comp → round4Free → round4probe
→ round4probe2 → round4probe3 → round5core → round5probe → round5probe2
→ round5refute → round5refute_bdefs → round6refute → round6core →
round6force → frontierCore → frontier → frontier_pin → round7core →
round7pin), RC=0, one `sorry` warning; every `#guard_msgs` pin passes;
the crown is unchanged:

    'PLLND.uniform_interpolation_PLL' depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

Regression: `lake exe towertest sizes 2` byte-identical; zero files
touched under `LaxLogic/`.

**Method note.**  §59 financing before the proof; §61 the recursion; §63
every depth; §65 the sampler before the build.  §66 adds the
counterpart for POSITIVE design steps: **when a design names a rescuing
resource, first check what the resource is derivable from** — the guard
stack was ambient-derivable, so the design's real content was the
demand-free recursion it licensed, and the real obstruction was wherever
the ambient alone provably does not suffice: findable by one targeted
countermodel probe at the inherited witness, before any build.

## §67 (2026-08-05) — Round 8: the goal-row absorption stated and screened two-sidedly (clean over 1152 cells, two new residue strata included), the env route kernel-refuted, the atomic tier and the band top PROVED room-free, and the open shape delimited to the fresh-antecedent inner goal row

`wip/round8core.lean`, `wip/round8pin.lean` (both new, both sorry-free,
all pinned); replay drivers `wip/frontier_g8.lean` / `_g8b` / `_g8c` /
`_g8d` / `_g8e` (recorded artifacts; durable transcripts
`wip/frontier_g8.txt`, `wip/frontier_g8e.txt`); two new strata in
`wip/frontier.lean` (`g8-d1jump` seeds 20000, `g8-d2jump` seeds 21000 —
existing strata byte-identical, `campaign1Strata`/`campaign2Strata`
value-preserved).  `wip/absorb_base.lean` and everything below it are
**untouched**: the one `sorry` is still `cascade_boxgoal_pos`.  The
round's brief was §66(h)'s residue — `Round7.CompProd`'s goal-row case at
compound unboxed bodies — attacked two-sidedly under the §65 standing
rule: candidates STATED, REPLAYED, the residue shape given its own
sampler stratum, and the witness instances run with derivation terms,
before any build was scoped.

**(a) THE CANDIDATES** (stated first).  With `Gsrc` the source table's
goal row at the reference fuel (`f = ft − 1`; the walk lifts the fired
value to `ft`, so its rows sit at inner fuel `f`):

    Gsrc = ◯( E@(f, b−1)(Γ) ⊃ A@(f, b)(Γ, D) )

* GR-W (the residue verbatim, `Round8.GoalRowAbsorb`, room-free):
      Δ ⊢ E@(f+1, b+1)(Γ) → Δ ⊢ Gsrc → Δ ⊢ A@(f+1, c)(Γ, ◯D),  1 ≤ c ≤ b
* GR-X (the committed-goal-clause route, exact inner slots):
      … → Δ ⊢ ◯( E@(f, c−1)(Γ) ⊃ A@(f, c)(Γ, D) )
* CP-P (`CompProd` proper at the cell's OWN body — round 7's G/H screened
  only the γ-antecedent body):
      Δ ⊢ E@(ft, b+1)(Γ) → Δ ⊢ ◯(E@(fs,b)(Γ) ⊃ A@(fs,b)(Γ,◯D)) →
      Δ ⊢ ◯(E@(ft,c)(Γ) ⊃ A@(ft,c)(Γ,◯D))
* GR-E (the γ-env route: land `Gsrc` in the target's γ-head env disjunct):
      … → Δ ⊢ (◯(E@(f,c−1)(Γ) ⊃ A@(f,c−1)(Γ,◯A₁))) ∧ A@(f,c)(B₀::Γ,◯D)

**(b) THE REDUCTION — the W passes are two-sided instruments**
(`Round8.goalRowAbsorb_of_boxDesc`, `not_boxDesc_of_not_goalRowAbsorb`,
`[propext, Classical.choice, Quot.sound]`).  GR-W follows from the
room-free `Round4.BoxDesc`: the goal row IS a disjunct of the source
table at budget `b`, and the band is walked by iterating the descent with
the ambient re-lowered per step (`Round7.compProd_of_boxDesc`'s move).
Hence any GR-W countermodel at admissible parameters kills `BoxDesc` and
the whole room-free route — the same upgrade round 7 gave the G/H passes.

**(c) THE REPLAY VERDICTS.**  Nine passes over the corpus (1072 records;
then re-driven over the enlarged 1152 after (d)), countermodel-only,
live-fire calibrated:

    Z0 control (Gsrc → component@0):      608 HITS (+35 on the g8 strata)
    Z1 control (Gsrc → table@0):          745 HITS (+49 on the g8 strata)
    P1  CP-P, c=b−1:                      0 hits          (0 on g8 strata)
    P2  CP-P, c=1:                        0 hits          (0)
    W1  GR-W, c=b−1:                      0 hits          (0)
    W2  GR-W, c=1:                        0 hits          (0)
    X1  GR-X, c=b−1:                      0 hits          (0)
    X2  GR-X, c=1:                        0 hits          (0)
    E1  GR-E, c=b−1 (γ-cells):            8 HITS          (0)

The eight E1 hits (`d2-imp/4000-4001`, `d3-atomgoal/8032-8033`,
`or2/12064-12065`, `pvar/15016-15017`, all one-world models) refute the
env route across four strata.  Everything else is calibrated silence: the
goal-row absorption, its committed form, and `CompProd` at the cells' own
bodies are NOWHERE refuted — compound unboxed bodies included.

**(d) THE RESIDUE STRATUM** (the §65 standing rule).  Jump-shaped UNBOXED
goal bodies over a γ-carrying space need `jumpExtra` (the γ-seed's own
closure has no jump-shaped member — recorded: `d1-jump`'s `D` is the
γ-clause itself).  Two new strata (`g8-d1jump`, `g8-d2jump` — the latter
the S3 nest shape behind a jump goal, THE residue configuration), 67
admissible run cells appended to the corpus: the standard screen
(`[src, amb] ⊢ tgt`, a hit kills `BoxDesc` outright) and all six
candidate passes came back CLEAN; both controls fire on the same cells.

**(e) THE NEW NEGATIVE — the env route is CLOSED**
(`Round8Pin.genv_absorption_refuted` / `genv_absorption_not_derivable`,
`[propext, Quot.sound]`).  At July's jump witness (`Skb`/`Gk`,
`D = gk = (◯r⊃s)⊃t` — the residue's compound unboxed shape; `ft = 4`,
`b = 2`, `c = 1`), from the FULL walk position — goal row, introduced
guard `E@(4,1)(Gk)`, ambient `E@(4,3)(Gk)` — `Mk` refutes the target's
γ-head env disjunct, kernel-checked.  In the same model the same
premises SATISFY the committed goal clause, the full target table and
the `CompProd` conclusion (scratch-probed, recorded in the transcript).
With round 7's pointwise pins: if the goal-row absorption is derivable
at all, it goes through the target's own goal clause or truncation row.

**(f) THE DELIMITED POSITIVES** (`wip/round8core.lean`):

* `goalRowAbsorb_top` (`[propext, Quot.sound]`): at `c = b` the
  absorption is disjunct introduction — ANY body, no descent, no room;
* `goalRowAbsorb_atom` (`[propext, Classical.choice, Quot.sound]`): at
  ATOMIC bodies `D = q ≠ p` the full band `1 ≤ c ≤ b` closes room-free —
  commit the target's goal clause, fire the goal row with the lowered
  ambient, and the fired value is consumed whole by the ambient-carrying
  atom forcing (`Round6Force.itpA_atom_forces_amb`, no `∨`-freeness);
  the fuel-0 corner closes by explosion under the box.

**(g) THE WITNESS INSTANCES** (the `_g7c` pattern, `refute?` full battery
first, then `prove?Bounded 40000` with the found derivation printed).
At the jump witness `Skb`/`Gk` (defect 8, fresh goal antecedent
`◯r⊃s ∉ Gk`):

    Skb-CTRL (the round-7 pinned landing)      R!  (Mk — live fire)
    Skb-W  gap 1   [Gsrc, amb] ⊢ table@1       ~ (quiet, unproved 40000)
    Skb-P  gap 1   CompProd instance           ~ (quiet, unproved 40000)
    Skb-F  [freshRow@2, amb@3] ⊢ freshRow@1    ~ (quiet, unproved 40000)
    Skb-F3 [freshRow@3, amb@4] ⊢ freshRow@1    ~ (quiet, unproved 40000)
    Skb-U  grown-context descent (r::Gk)       P (PROVED, budget 40000)
    Skb-U0 = U + extra ambient premise         ~ (searcher noise: U's
                                                  derivation weakens in)

`freshRow(β) = E@(2,β)((◯r⊃s)::Gk) ⊃ A@(2,β)((◯r⊃s)::Gk, t)` is the
DELIMITED INNER OBLIGATION of the committed route at the fresh inner
goal row — the step whose only known financing is the room-priced guard
ascent (`cascade_main_bf`'s `hroomE`; `Round6.easc_tight`'s demand
`J+2+defect′·(J+2) ≤ budget` fails at `c < J+2`), which a room-free walk
does not have.  `Skb-U` is the counter-signal on the OTHER inner family:
the unboxed same-context descent at the GROWN context `r::Gk` (defect 7,
one below July's refuted instance) is searcher-PROVED — July's
refutation does NOT propagate one growth step in; the γ-row-inner
landing is affirmatively financed at the witness.
At the same witness the committed clause itself:

    Skb-X  gap 1   [Gsrc, amb] ⊢ gclause@1    ~ (quiet, unproved 40000)

(first derived in the ordered `_g8c` run, whose verdict line was lost to
a concurrent-writer race on the ledger — two processes appending to one
file can clobber a line in the open-to-write window; re-derived on a
separate ledger, `wip/frontier_g8e.txt`, and recorded there.)

At the nest witness `S3`/`Γ3` (defect 1, PRESENT goal antecedent
`a ∈ Γ3`, room floor `b = 4`, `fs = ft = 5`):

    S3-X  c=3   [Gsrc, amb] ⊢ gclause@3       P (PROVED, budget 40000)
    S3-X  c=1   [Gsrc, amb] ⊢ gclause@1       P (PROVED, budget 40000)

with the `c = 3` derivation printed IN FULL — eight rules:

    ◯R (→R (∨R₁ (→R (∨R₁ (∧L (∧L (∧L init)))))))

box, guard in, commit the present-antecedent inner goal disjunct, guard
in, commit the atom disjunct, and the atom `b` is a CONJUNCT of the
introduced grown guard `E(a::Γ3)` (`b ∈ Γ3`): guard-absorption.  The
source goal row is never touched — the §61(e) caveat in sharpest form:
atom-rich contexts close the committed route through the guard alone,
which is why the S3 positives support but cannot decide the bare-context
case, and why `Skb`/`Gk` (no atoms in the context) is the witness that
matters.  (The remaining `S3-W`/`S3-P` and gap-2 `Skb` rows of the
re-ordered driver are recorded in `wip/frontier_g8e.txt` as they land;
none of them is load-bearing for (h).)

**(h) WHERE THE RESIDUE NOW STANDS.**  The goal-row case delimits row
family by row family, each with machine evidence:

* target env family: CLOSED (kernel-refuted, (e) + the eight E1 hits);
* atomic bodies: PROVED ((f), any `c`);
* band top `c = b`: PROVED ((f), any body);
* γ-row-inner (grown second components): financed — grown-context
  descent searcher-PROVED at the witness ((g) `Skb-U`), defect strictly
  drops per growth;
* fresh-antecedent inner goal row (`D = C₁ ⊃ C₂`, `C₁ ∉ Γ`): THE OPEN
  SHAPE.  Pointwise it needs the guard ascent `c → b` at the grown
  context `C₁::Γ`, room-priced with zero room in the statement; the
  delimited sequent is two-sidedly undecided at the witness (battery
  quiet, searcher exhausted at 40000 over the defect-8 space).

    RESIDUE (round 9): `Round8.GoalRowAbsorb` restricted to compound
    unboxed `D` whose decomposition reaches a FRESH implication
    antecedent — equivalently, close (or refute) the fresh-row descent

        E@(f,b)(C₁::Γ) ⊃ A@(f,b)(C₁::Γ, C₂) , E@(ft, b+1)(Γ)
          ⟹ E@(f,c)(C₁::Γ) ⊃ A@(f,c)(C₁::Γ, C₂)      (C₁ ∉ Γ, c < b)

    from the ambient alone.  Nothing else of the goal-row case is open.

**(i) REPLAY VALUE VERDICT: KEEP.**  Third statement-change use, third
yield: two controls calibrated 608/745-hot on the exact premise pair,
one route (env) refuted at eight instances the round-7 passes never
touched, and the two-sided W upgrade ((b)) turned 4 × 1152 silent cells
into implied evidence for the room-free route.  The residue-shape
stratum (67 cells) ran BEFORE the build was scoped, per §65.

**Build state.**  `wip/absorb_base.lean` untouched, exactly ONE `sorry`
(`cascade_boxgoal_pos`); full 27-file stack in the pinned order
(absorb_base → … → round7pin → round8core → round8pin) RC=0, every
`#guard_msgs` pin passes; the crown is unchanged:

    'PLLND.uniform_interpolation_PLL' depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

Regression: `lake exe towertest sizes 2` byte-identical; zero files
touched under `LaxLogic/`.

**Method note.**  §66 checked what a rescuing resource is derivable
from; §67 adds the mate: **when a route is refuted, ask which DISJUNCT
FAMILY of the target it used, and refute per family** — the env family
died by one countermodel probe and eight replay hits, which is what
narrowed the open shape to a single row family with a single financing
question.  And a search-engine note, recorded for future rounds: the
searcher is not premise-monotone (`Skb-U0` quiet with `Skb-U` proved —
the extra premise only enlarged the space past the budget); a quiet
verdict on a STRONGER premise list proves nothing about the weaker one.

## §68 (2026-08-05) — Round 9: the ROOM-FREE ROUTE IS REFUTED.  The §67(h) residue is false, `BoxDesc` / `CompProd` / `GoalRowAbsorb` fall with it, and three independent blind spots in the screen are identified and closed

`wip/round9pin.lean` (new, sorry-free, all pins from actual output);
`wip/frontier.lean` extended by ten strata and two axis knobs (every
campaign-1/2/g8 stratum byte-identical — the 1152-record regression replay
agrees 1152/1152); probe artifacts `wip/frontier_g9a/b/c/v/w/x/y/z.lean`
with durable transcripts.  `wip/absorb_base.lean` and everything below it
are **untouched**: the one `sorry` is still `cascade_boxgoal_pos`, and the
crown is unchanged.  The round's brief was §67(h)'s residue attacked
two-sidedly under the §65 standing rule.  It came back NEGATIVE.

**(a) THE RESIDUE IS FALSE.**  §67(h) left exactly one shape open — the
goal-row absorption at a compound unboxed body `D = C₁ ⊃ C₂` whose
antecedent is FRESH (`C₁ ∉ Γ`), equivalently the **fresh-row descent**

    E@(f,b)(C₁::Γ) ⊃ A@(f,b)(C₁::Γ, C₂) ,  E@(ft,b+1)(Γ)
      ⟹  E@(f,c)(C₁::Γ) ⊃ A@(f,c)(C₁::Γ, C₂)            (C₁ ∉ Γ, c < b)

`Round9Pin.not_freshRowDescent` refutes it (`[propext, Classical.choice,
Quot.sound]`), from the kernel-checked countermodel
`Round9Pin.freshRow_refuted` (`[propext, Quot.sound]`).  The instance:
`vS` = the piece-closure of `◯((◯x ⊃ y) ⊃ z)` (seven formulas), `Γ = []`,
inner fuel `3`, `b = 2`, `c = 1`; the model `M2` = July's `Mk` with the
atoms renamed (two worlds `0 ⊑ 1`, `0 ⊳ 1`, infallible, `x`, `y`, `z`
exactly at world `1`).  At `Γ = []` the ambient premise is literally `⊤`,
so the refutation holds with every resource the walk has.

**(b) …AND IT LIFTS TO THE THREE ROOM-FREE STATEMENTS.**  `M2` alone does
NOT refute the `◯`-goal statements: its modal successor is its top world,
where `z` holds, so the target's boxed disjuncts are satisfied there —
`Round4Probe3.box_is_load_bearing`'s rescue, at this instance.  Pushing the
modal step one world UP removes the rescue.  With
`P3c = ⟨3, ri = 0⊑1⊑2, rm = [(1,2)], fall = [], x,y,z at 2⟩`:

    Round9Pin.not_boxDesc        ¬ Round4.BoxDesc "p" vS
                                   (fs = ft = 5, b = 1, Γ = [])
    Round9Pin.not_compProd       ¬ Round7.CompProd "p" vS
                                   (fs = ft = 5, b = 2, c = 1, Γ = [])
    Round9Pin.not_goalRowAbsorb  ¬ Round8.GoalRowAbsorb "p" vS
                                   (f = 4, b = 2, c = 1, Γ = [])

each `[propext, Classical.choice, Quot.sound]` over a `decide +kernel`
`FinCM.checkB` certificate.  Rounds 7 and 8's own upgrade theorems
re-derive the first from the other two
(`Round9Pin.not_boxDesc_via_compProd`, `…_via_goalRowAbsorb`), so the three
refutations are mutually consistent by machine.  The `◯` is load-bearing
but not decisive: it buys exactly one modal step, and a chain longer than
the one the battery carried spends it.

**(c) WHERE THE SCREEN WAS BLIND — three independent axes.**  Rounds 4–8
screened ~1150 cells and nine candidate passes, all clean, for statements
that were false the whole time.  The corpus missed the refutation three
times over, and each miss is a fixed assumption in the harness:

* **defect.**  `genDrop cfg.defectTarget` removes one or two members, so
  every cell's context is nearly all of `S`.  The refutation lives at the
  other end: `Γ = []`.  (July's `Gk` — the inventory's one high-defect
  instance — is also the one place the unboxed room-free descent was
  already known to fail.)
* **fuel.**  `fuelGrid` ties `ft = b + 1`, so a `b = 1` cell is screened at
  `ft = 2`.  At `Γ = []` the `BoxDesc` cell is PROVABLE at `ft ≤ 4` and
  REFUTED from `ft = 5` — the tie made the refuting fuel unreachable at
  every budget inside `ftCap`.
* **frame.**  `P3c` is in NEITHER frame list: `Round5Refute.xFrames` has
  the three-chain with `rm` EMPTY, `defaultFrames` has it with
  `rm = [(1,2)]` but a FALLIBLE top, which forces every atom at world `2`
  and destroys the configuration.  The infallible single-modal-step
  three-chain — the frame that refutes — was never in the battery.

**(d) THE SAMPLER, CORRECTED.**  `wip/frontier.lean` gains, all
value-preserving at their defaults (`gimp := false`, `bgridOverride := []`,
`fuelBump := 0`): a fresh-antecedent generator (`genBaseGimp`, `D =
(◯x ⊃ y) ⊃ z` with `C₁ = ◯x ⊃ y` dropped from the context — July's `Sk` at
rotation 0), a stratum-fixed budget grid, and a fuel bump that unties `ft`
from `b + 1`.  Ten new strata: `g9-gimp/gimpX/gimp0` (fresh antecedent),
`g9-gimpP` (the PRESENT-antecedent control), `g9-bare/bareG/bareJ`
(context emptied), `g9-bareF/bareFG/bareFJ` (context emptied, fuels lifted
by three — the refuting region).  Regression: 1152/1152 shape agreement,
so every stored verdict still stands for the statement it was recorded
against.

**(e) THE REPLAY VERDICT — the corrected screen fires.**  Over the enlarged
corpus (1382 records) with `P3c` and its four-world analogue prepended to
the frame list:

    Z0 control (goal row to component@0):        825 HITS (calibration)
    F2  fresh-row descent, c = 1:                 19 HITS
    F1  fresh-row descent, c = b−1:               10 HITS
    Fp  PRESENT-antecedent row descent, c = 1:     0 hits  (control)
    BD  Round4.BoxDesc, [src, amb] ⊢ tgt:          4 HITS
    W2  Round8.GoalRowAbsorb, c = 1:              10 HITS

Every F1/F2 hit is on a round-9 stratum and every certificate is `P3c` (up
to atom renaming); the matched present-antecedent control is silent, so the
discriminator is exactly the `C₁ ∉ Γ` branch of `itpAgoal` — the branch
that does NOT lower the target's guard, and therefore demands the guard
ascent `c → b` at the grown context that `AscRefute.not_ambGuardAscent`
already refuted room-free.  The three fixes are jointly necessary: with the
round-8 frame list, or the round-8 defect range, or the tied fuel grid, the
same passes are silent.

**(f) WHAT IS UNTOUCHED.**  The refuted cell has
`defect vS [] · (|jumpGoals vS| + 2) = 35` and `b = 1`
(`Round9Pin.vS_room`, `not_room_at_one`, `not_room_at_two`): it is
STRICTLY SUB-ROOM by a factor of 35.  `Round4.BoxDescR` — the room-carrying
obligation, `Room S Γ b` at the target budget — and
`wip/absorb_base.lean`'s `cascade_boxgoal_pos` are therefore untouched, and
nothing in this round bears on them.  The crown is unchanged:

    'PLLND.uniform_interpolation_PLL' depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

**(g) THE REDIRECT.**  §61(c) alternative 1, §63(e) fork (1), and the whole
of rounds 6, 7 and 8 were assembled on `Round4.BoxDesc` being true.  It is
not.  What survives is the room-carrying fallback the `sorry` already
states — `BoxDescR` plus `1 ≤ defect S Γ` — and the campaign's question
becomes the one §65 measured and set aside: the room-carrying statement's
live regime is not decide-feasible wherever a γ-clause is present
(`two_le_jumpGoals_of_gamma`, `four_le_budget_of_gamma`), so the next round
cannot screen its way in and must build.  The positive results of rounds 6
and 8 survive intact and are reusable there: `Round6.easc_tight` (the E-half
at `J+2`), `Round6Force.itpA_atom_forces_amb`, `Round8.goalRowAbsorb_top`
and `goalRowAbsorb_atom` are theorems about the tables, not about the
room-free route.

**(h) METHOD NOTES.**

* **A clean screen is a statement about the screen.**  Nine passes over
  1152 cells, three rounds, all clean — and false.  Every "quiet" verdict
  in the corpus was produced by a battery blind to one frame, a generator
  blind to one end of one axis, and a grid that tied two axes together.
  A negative result from a fixed battery bounds the countermodel, not the
  statement; the bound must be recorded with the verdict.
* **Sample the DEGENERATE end of every axis, not just the interesting
  end.**  `Γ = []` is where the tables collapse and the ambient becomes
  `⊤` — the cheapest instances in the whole space, and the ones no
  stratum drew.  Cheap degenerate cells should be screened FIRST, before
  the expensive interesting ones.
* **Never tie two axes in a grid.**  `ft = b + 1` was a convenience; it
  made a whole region unreachable at every budget, silently.
* **Widen the frame list when a `◯`-goal statement survives a screen its
  unboxed form fails.**  §60 recorded that contrast
  (`box_is_load_bearing`) as evidence FOR the `◯`-goal form.  It was
  really a signal that the battery's modal depth was the binding
  constraint: the `◯` buys one modal step, so the refuting frame is one
  step longer than the one that refutes the unboxed form.
