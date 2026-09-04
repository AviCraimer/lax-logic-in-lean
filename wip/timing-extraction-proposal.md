# Reanimating constraint extraction: a chunky timing example for PLL-in-Lean

*Proposal. Research agent, 2026-07-11. Companion to `LaxLogic/PLLConstraints.lean`.*

The repo already contains a working, `rfl`-checked constraint extractor
(`PLLConstraints.lean`): `◯` is read as a writer monad `M × ⟦φ⟧`, `Tm.eval`
evaluates a proof term to its constraint, and a two-gate *series* circuit
extracts delay `d₁+d₂`. This note proposes the chunky, concrete example that
turns that toy into a reproduction of Mendler's original "proofs-as-delays"
programme, with the reconvergent-fanout / false-path punchline that a
*series* chain cannot show.

---

## 1. The original programme (two paragraphs)

`◯` was born as a hardware modality. Mendler's Edinburgh PhD — *A Modal Logic
for Handling Behavioural Constraints in Formal Hardware Verification* (Univ.
Edinburgh, tech. report [ECS-LFCS-93-255](https://publish.lfcs.inf.ed.ac.uk/reports/93/ECS-LFCS-93-255/),
1993) — proposed reading "correctness **up to a constraint**" as an
intuitionistic modality, so that a proof of an *abstract* combinational
specification collects its timing side-conditions instead of discharging
them. Fairtlough & Mendler crystallised this as PLL: first *An Intuitionistic
Modal Logic with Applications to the Formal Verification of Hardware* (CSL
1994, [LNCS 933](https://link.springer.com/chapter/10.1007/BFb0022268)), then
*Propositional Lax Logic* (*Information and Computation* 137(1):1–33, 1997,
[ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540197926274)).
The three axioms carry the delay reading the repo already cites: `◯R` (`M⊃◯M`,
unit) = a wire, delay `0`; `◯M` (`◯◯M⊃◯M`, multiplication) = sequential
composition, delay `+`; `◯S` (`◯M∧◯N ⊃ ◯(M∧N)`, strength) = parallel
composition, delay `max`. The discipline is "prove the function now, collect
the delay as a constraint on `◯`, evaluate on concrete numbers later."

The extraction mechanism is worked out in full in Mendler's *Timing Analysis
of Combinational Circuits in Intuitionistic Propositional Logic* (*Formal
Methods in System Design* 17(1):5–37, 2000,
[Springer](https://link.springer.com/article/10.1023/A:1008780817617) /
[PDF](https://www.uni-bamberg.de/fileadmin/uni/fakultaeten/wiai_professuren/grundlagen_informatik/papersMM/fmsd00.pdf)).
Circuits are timed Kripke models; `⊃` means "**boundedly gives rise to**";
realisers `⟦φ⟧` are *stabilisation bounds*, with `⟦φ⊃ψ⟧ = ⟦φ⟧ → ℕ×⟦ψ⟧` — a
function returning a **delay** paired with the consequent's realiser. §6
("Extracting Stabilisation Bounds") translates an `LJ` proof to a typed
λ-term with delay germs `del(n)` and evaluates it in the strong monad
`T A = ℕ×A` with `η(a)=(0,a)`, multiplication `μ(n₁,n₂,a)=(n₁+n₂,a)` and
tensorial strength `σ = max` — the delay algebra `(ℕ,0,+,max)`, "both `+` and
`max` essential." §7 evaluates it on a concrete circuit and observes the
bound "may be smaller than the topological delay, i.e. the longest path."
The bridge to PLL is explicit (p. 8): every circuit induces a PLL constraint
model `C*`, and `C ⊨ φ` iff `C* ⊨ φ*`, where `φ*` inserts `◯` on each `⊃`'s
consequent. Page 29 names the principle **"proofs-as-delays."** Related
threads: *Characterising Combinational Timing Analyses in Intuitionistic
Modal Logic* (LJIGPL 8(6):821–853, 2000) links it to ternary simulation;
Fairtlough–Mendler–Walton's QLL (*First-order Lax Logic as a Framework for
Constraint Logic Programming*, Passau MIP-9714, 1997) and *On the Logical
Content of Computational Type Theory* (TYPES 2000, LNCS 2277) extend the
constraint reading beyond circuits.

---

## 2. Survey of candidate case studies

**(A) Mendler's `CIRC`, FMSD 2000 §7 — the canonical seed.**
`c = (a∨b) ∧ ¬b`, built from `OR(a,b)=d`, `INV(b)=e`, `AND(d,e)=c`. Timing
question: what is the stabilisation delay of `c`, per transition and per
input? It abstracts to PLL by construction — it *is* the paper's example.
`◯` marks each gate output's ready-time; the constraint is the extracted
delay table. Signal `b` **fans out** to `OR` and `INV` and **reconverges** at
`AND`, so the rising bound `δ_CIRC↑ = max(δ_OR↑, δ_INV↑) + δ_AND↑` genuinely
uses `max` — unlike the repo's series toy. Data: any gate library. Size:
small (3 gates; ~15-constructor `Tm` terms per transition), the right first
target. Bonus: a real hazard — classically `a=0 ⟹ c=0`, but a `1→0` glitch on
`b` can spike `c`; the intuitionistic proof needs `b=1 ∨ b=0` explicitly.

**(B) Carry-skip (carry-bypass) adder — the chunky false-path scale-up.**
The 2-bit carry-skip adder is *the* textbook false-path example: the longest
*topological* path (ripple through a block **and** take the skip multiplexer)
is never sensitisable, so topological STA over-estimates
([carry-skip adder, Wikipedia](https://en.wikipedia.org/wiki/Carry-skip_adder);
Kuehlmann, EECS 219B timing-analysis lectures). Timing question: the true
critical carry delay. In PLL: each carry/propagate/generate signal is a `◯`'d
stability; the correctness sequent is `carry-out correct up to timing`; the
extracted constraint set contains exactly the paths a proof traverses, so the
false ripple-and-skip path is **absent by construction**. Data: standard-cell
delays (below). Size: medium (tens of gates; a 2–4-bit slice). Recent hook:
approximate computing deliberately *fabricates* false paths — Alioto et al.,
*Design of Approximate Circuits by Fabrication of False Timing Paths: The
Carry Cut-Back Adder* (IEEE JETCAS, 2018,
[ResearchGate](https://www.researchgate.net/publication/326075904)).

**(C) Carry-lookahead vs ripple-carry adder — critical-path contrast.**
Chunky, classic, reconvergent: the CLA group-generate/propagate logic has
each carry depending on all lower `g`/`p`, and its critical path is much
shorter than the ripple carry chain. In PLL: two derivations of the same
`◯`-annotated `cout` spec, one per adder, whose extracted bounds differ —
extraction *reproduces the known asymptotic win*. `◯` = carry-ready. Data:
sky130. Size: medium–large (a 4-bit CLA block is ~tens of gates).

**(D) Mendler–Shiple–Berry 2012 — the recent theoretical anchor.**
*Constructive Boolean Circuits and the Exactness of Timed Ternary
Simulation* (*FMSD* 40(3):283–329, 2012,
[Springer](https://link.springer.com/article/10.1007/s10703-012-0144-6)).
Defines *constructive* circuits (signals settle to a unique value in bounded
time under the up-bounded non-inertial "UN" delay) and proves three-valued
(Brzozowski–Seger) ternary simulation both *decides* constructivity and
computes *exact* stabilisation bounds. This is `◯`-as-bounded-stabilisation
made rigorous and modern; it is the natural semantic yardstick. Size: large
if mechanised (ternary simulation is its own development) — cite as the
correctness anchor and a stretch direction, not the first target.

**(E) Ferrari–Fiorentini–Ornaghi — a parallel "bounds from proofs" line.**
*Extracting Exact Time Bounds from Logical Proofs* (LOPSTR 2001, LNCS 2372,
pp. 245–265). Independent of lax logic: constructive proofs annotated to
yield *program* execution-time bounds. Useful as related work — it confirms
the proofs-as-bounds idea has legs outside PLL — but the domain is program
complexity, not circuit delay, and the modality is absent. Not the target.

**(F) Concrete delay data — SkyWater sky130 + OpenSTA.**
The [SkyWater SKY130 PDK](https://skywater-pdk.readthedocs.io) ships
open-source Liberty (`.lib`) files with NLDM (SPICE-characterised) delay
tables for every `sky130_fd_sc_hd` cell (`inv`, `nand2`, `and2`, `xor2`, …);
[OpenSTA](https://github.com/parallaxsw/OpenSTA)/OpenROAD read them. Per-gate
delays are on the order of tens–low-hundreds of ps (load/slew-dependent 2-D
tables). This is the freely-citable substrate for the "evaluate on concrete
data" step; fix a nominal load/slew operating point to get the single scalar
per gate/transition that Mendler's model assumes.

---

## 3. Recommendation

**Primary: mechanise Mendler's `CIRC` natively in PLL/`Tm`, upgrade the
extractor to the real `(ℕ,0,+,max)` algebra, then scale to a carry-skip
adder slice — landing the false-path punchline on sky130 numbers.**

*The PLL sequents.* Model each gate as a context hypothesis over ready-time
signals (`◯`-typed inputs, `◯`-typed output):

- `gOR  : ◯a ⊃ ◯b ⊃ ◯d`   `gINV : ◯b ⊃ ◯e`   `gAND : ◯d ⊃ ◯e ⊃ ◯c`

and derive, as a `Tm` proof term over `Γ = [gOR, gINV, gAND]`, the
circuit-correctness sequents Mendler proves for `CIRC↑` and the two `CIRC↓`
input-classes (F&M/Mendler eqs. 15–16). Curry–Howard (`Tm.toND`,
`curry_howard`, both in-repo) certifies these are genuine PLL derivations.

*The extracted constraint set.* Evaluate each proof term with `Tm.eval`. Give
the gate hypotheses **delay-carrying denotations**: `gAND ↦ λ(δd,_)(δe,_).
(max δd δe + δ_AND, ⟨⟩)`, etc. — a multi-input generalisation of the existing
`gate d f = λx.(d, x)`. Then `Tm.eval CIRC↑` computes
`δ_CIRC↑ = max(δ_OR, δ_INV) + δ_AND` **by `rfl`**, and the two falling cases
compute `δ_OR↓ + δ¹_AND↓` and `δ_INV↓ + δ²_AND↓` — each traversing **one**
reconvergent branch. Keeping the gate delays as free `ℕ` variables yields the
symbolic delay *table* (Mendler's `T_OR, T_INV, T_AND` and their
composition); substituting concrete numbers is the evaluation.

*The evaluation & punchline.* Discharge on sky130 scalars at a fixed
operating point. Define the topological bound `max(δ_OR,δ_INV)+δ_AND`
independently, and show — by `decide`/`rfl` on the numbers — that the
data-dependent falling bounds are **strictly smaller**: the proof term for
the `a=0,b=0` case never mentions `INV`, so the false path is absent from its
constraint set. Expected headline: *extraction reproduces the true
per-transition critical path and beats the topological longest path by
recognising a non-sensitisable path — for free, because a proof only
traverses real logical dependencies.* Scaling `Γ` to a 2-bit carry-skip
adder's netlist reproduces the classic false-path result at "tens of gates."

**Fallback:** if the adder derivation term proves heavy to build by hand,
stop at `CIRC` plus a single ripple-vs-skip 2-bit comparison — that already
demonstrates `max`, data-dependence, and the false-path win. The verified
decider (`decidablePLL`/`search`, `PLLG4Dec.lean`) can *synthesise* the
proof term via `curry_howard`, but may not return the path-specific
derivation the punchline needs; hand-write the two or three key terms.

---

## 4. Repo fit (what exists, what to add — honest)

*Exists and is directly reusable* (`LaxLogic/PLLConstraints.lean`):
- `sem : PLLFormula → Type` with `sem (somehow φ) = M × sem φ` — the writer
  reading of `◯`. `Env`, `Var.look`, and `Tm.eval` (parametric in `op,e`) are
  the extractor; it already evaluates proof terms to constraints.
- `gate d f`, `twoGates`, `joinTm`, and `rfl`-checked delay examples under
  both `(ℕ,+,0)` and `(ℕ,max,0)`.
- The whole `Tm` calculus (`PLLTerms.lean`): `val`=`laxIntro`,
  `bind`=`laxElim`, plus `pair/fst/snd`, `app/lam`. `Tm.toND`/`curry_howard`
  (`PLLNDCore.lean`) certify extracted terms are PLL proofs. `Tm.pretty`
  (`PLLRun.lean`) prints them.

*Must be added (all small and well-scoped):*
- **The two-operation delay algebra.** The current file takes a *single* `op`
  and instantiates it as `+` *or* `max` — fine for a series chain, but a
  reconvergent circuit needs `+` for sequential `bind`/`◯M` **and** `max`
  where two `◯`-branches merge (`◯S`) in the *same* evaluation. Cleanest
  route: keep `op = +` for `bind` and put the `max` inside the multi-input
  gate denotations (least invasive; matches "gates emit constraints"). This
  is the one genuine design step; it is exactly Mendler's `μ=+, σ=max` strong
  monad and resolves why the current example is degenerate.
- Multi-input gate denotations (`gateAND` above) and the `CIRC` proof terms
  for `↑` and the two `↓` classes — a handful of `Tm` constructors each, in
  the style of `twoGates`.
- A tiny concrete-delay table (sky130 scalars) and the topological-bound
  definition, with `#guard_msgs`-pinned `#eval`s for the strict-inequality
  punchline — matching the repo's existing audit discipline.

No frozen file is touched; this is a new self-contained section (or a
`PLLTiming.lean`) built on `PLLConstraints`/`PLLTerms`.

---

## 5. Risks and scope

- **The `+`/`max` split is load-bearing.** Conflating them into one `op` is
  precisely why the current toy is degenerate; the fix is bounded but must be
  done deliberately (don't "optimise" it back to one operation). Low risk,
  named above.
- **Derivation terms are the real labour.** `Tm` proof terms for a gate
  netlist are written by hand; the decider can synthesise *a* term but not
  necessarily the path-minimal one the false-path story needs. A full CLA or
  wide carry-skip adder multiplies this by rising/falling × input-class ×
  bit — keep the first deliverable to `CIRC` + a 2-bit slice, or scope creep
  is real.
- **"Beats topological" is per-transition/per-input**, exactly as in Mendler
  — state it that way; it is not a single global inequality.
- **sky130 delays are 2-D (load/slew) tables, not scalars.** Honest
  simplification: pin a nominal operating point. This matches Mendler's
  single-scalar-per-gate-transition model; note the simplification explicitly.
- **Concrete numbers are illustrative, not sign-off STA.** The contribution
  is *the extraction mechanism and the false-path observation*, mechanised
  and kernel-checked — not a competitive timing engine. Frame it so.
- **Ternary-simulation exactness (candidate D) is a separate development.**
  Cite Mendler–Shiple–Berry 2012 as the semantic anchor; do not fold its
  mechanisation into this task.

---

## Phase 2 results

*Delivered 2026-07-11. Two new files, both sorry-free and axiom-audited, built
via `lake build`; `PLLConstraints.lean` and every other existing file
untouched. Namespace `PLLND`.*

### What was mechanised

**`LaxLogic/PLLTiming.lean` — the two-operation algebra + Mendler's `CIRC`.**
The extractor of `PLLConstraints.lean` is *imported unchanged* and instantiated
at the delay algebra `(ℕ, 0, +, max)`: `Tm.eval (· + ·) 0` supplies Mendler's
`η = (0,·)` and `μ = +` on the object-level `bind`, while the `max` (his
tensorial strength `σ`) lives inside the multi-input gate denotations
`gate2 δ = λ p q ↦ (max p.1 q.1 + δ, ⟨⟩)` — exactly the least-invasive split
proposed in §4. Both operations now occur in one evaluation, which the single
`op` of the old toy could not do.

- `circUp : Tm ΓCIRC (◯a ⊃ ◯b ⊃ ◯c)` over `Γ = [gOR, gINV, gAND]` — the
  netlist `OR(a,b)=d, INV(b)=e, AND(d,e)=c`, with `b` fanning out and
  reconverging at `AND`. Certified a genuine PLL derivation via `circUp.toND`
  (`Nonempty (LaxND …)`).
- **Extraction (`rfl`):** `circUp_extract` reads the composite delay straight
  off the proof term:
  `max (max δa δb + δ_OR) (δb + δ_INV) + δ_AND` — Mendler's symbolic delay
  table `T_OR, T_INV, T_AND` composed, kept fully symbolic.
- **Rising bound:** at inputs ready `0`, `circUp_rising` gives
  `δ_CIRC↑ = max(δ_OR, δ_INV) + δ_AND` — a genuine `max`. Concrete nominal
  sky130: **210 ps**.
- **Both operations, one evaluation:** `gateThenBuf_extract` (`rfl`) exhibits
  the object-level `bind` paying `μ = +` *on top of* a 2-input gate's
  `σ = max`: `max δd δe + δ_G + δ_BUF`.

**The false path in `CIRC` (miniature punchline).** On the input class `a = 1`,
`d = a ∨ b = 1` is stable, so `◯d` is available at time `0` and the correct
per-class proof `circUp_a1 : Tm [gINV, gAND, ◯d, ◯b] ◯c` **never mentions
`gOR`** — the reconvergent `OR → AND` branch is literally absent from the term
(and certified via `.toND`).
- `circUp_a1_extract` (`rfl`): `max δd (δb + δ_INV) + δ_AND`;
  `circUp_a1_bound` (at ready `0`): `δ_INV + δ_AND` = **130 ps**.
- `falsePath_beats_topological` (`decide`): **130 < 210**, i.e. the extracted
  data-dependent bound is strictly below the topological longest path
  `dTopo = max(δ_OR, δ_INV) + δ_AND = 210`. The saving is exactly the
  non-sensitised `δ_OR − δ_INV = 80 ps`.

**`LaxLogic/PLLTimingAdder.lean` — the carry-skip false path at scale.** An
explicit 4-bit block (proposal candidate B), *not* descoped:
- `rippleTm : Tm Γripple ◯c₄` — four ripple carry stages
  (`csᵢ : ◯cᵢ ⊃ ◯pᵢ ⊃ ◯cᵢ₊₁`, each `max + δ_carry`). `ripple_extract` (`rfl`)
  and `ripple_bound` (`= 4·δ_carry`): the long ripple sub-path, **480 ps**.
- `coutSkip : Tm Γskip ◯cout` — the all-propagate (`P = 1`) skip derivation:
  balanced `P`-tree `(p₀∧p₁)∧(p₂∧p₃)` then `muxSkip : ◯cin ⊃ ◯P ⊃ ◯cout`.
  It bypasses the ripple entirely, so the carry chain `c₁…c₄` is **absent from
  the term**. `coutSkip_bound` (`= 2·δ_and + δ_mux`): **280 ps**.
- `skip_beats_topological` (`decide`): **280 < 580**, where the topological
  longest path `dTopoAdder = 4·δ_carry + δ_mux = 580` is the classic
  ripple-**and**-skip false path (needs `P = 1` to ripple and `P = 0` to select
  ripple — contradictory). Extraction beats topological STA by **300 ps
  (> 2×)**, because a correct proof only ever traverses a sensitisable path.
- Both terms certified genuine PLL derivations via `.toND`.

### Extracted numbers (nominal sky130 `sky130_fd_sc_hd`, single scalars, ps)

| gate | delay | cell |
|------|-------|------|
| INV   | 40  | `inv_1` |
| OR2   | 120 | `or2_1` |
| AND2  | 90  | `and2_1` |
| carry | 120 | `maj3_1` / full-adder carry |
| MUX2  | 100 | `mux2_1` |

| quantity | value | provenance |
|----------|-------|-----------|
| `CIRC↑` rising bound | 210 ps | `max(δ_OR,δ_INV)+δ_AND`, `= dTopo` |
| `CIRC↑` on `a=1` class | **130 ps** | `δ_INV+δ_AND` (OR path absent) |
| carry-skip topological longest | 580 ps | `4·δ_carry+δ_mux` (false path) |
| carry-skip ripple sub-path | 480 ps | `4·δ_carry` |
| carry-skip `P=1` skip bound | **280 ps** | `2·δ_and+δ_mux` (ripple absent) |

### The false-path verdict

Confirmed twice, kernel-checked by `decide`: the delay **extracted from a
proof** is strictly below the topological longest path whenever that longest
path is non-sensitisable — `130 < 210` in `CIRC` (the `a=1` class drops the
`OR→AND` reconvergent branch) and `280 < 580` in the carry-skip adder (the
`P=1` class drops the whole ripple chain). "A proof only traverses real logical
dependencies, so a non-sensitisable path is absent from its constraint set —
for free," exactly as forecast. Per-transition/per-input, as Mendler frames it.

### Axiom audit (honest report)

`#guard_msgs`-pinned `#print axioms` on the extraction and punchline theorems.
The results are **stronger** than the expected
`[propext, Classical.choice, Quot.sound]`: no theorem here touches
`Classical.choice`, and `decide`/`rfl` results are entirely **axiom-free**.

- `circUp_extract`, `circUp_a1_extract`, `falsePath_beats_topological`,
  `ripple_extract`, `coutSkip_extract`, `skip_beats_topological` —
  *"does not depend on any axioms."*
- `circUp_rising` — `[propext, Quot.sound]` (the only appeal is `omega`'s use
  of propositional extensionality; the `_bound` lemmas are the same shape).
- No `native_decide` anywhere, so no `Lean.ofReduceBool`: every number is
  kernel-reduced, not compiled.

### Deviations from the proposal

1. **`rfl` vs. arithmetic normalisation.** The proposal expected
   `Tm.eval CIRC↑ = max(δ_OR,δ_INV)+δ_AND` *by `rfl`*. The honest split is: the
   **raw** extraction (`circUp_extract`) — the constraint the kernel reads off
   the term — *is* `rfl`; collapsing it to Mendler's table entry needs one line
   of `omega`, because Lean's `Nat` makes neither `0 + n` nor `max 0 0`
   definitional. Concrete numbers are `decide`. No fidelity lost — arguably
   gained: the `rfl` witnesses the *symbolic table*, `omega` its evaluation.
2. **`gateThenBuf` added.** With gates modelled as `◯`-consuming hypotheses
   (the proposal's own `gAND ↦ λ(δd,_)(δe,_).(max δd δe+δ_AND,⟨⟩)`), the `CIRC↑`
   term is pure application and never fires an object-level `bind`. To
   demonstrate the "`+` on `bind`" half of the split *explicitly* — not merely
   as the `+δ` inside gate denotations — `gateThenBuf` routes a 2-input gate
   into a buffer via `bind`. Over-delivers on §4's "both operations in the same
   evaluation."
3. **`a = 1` rather than `a = 0, b = 0`.** The proposal named the `a=0,b=0`
   case in passing; the `a = 1` class gives the cleaner "`OR → AND` branch
   absent" story (`δ_INV+δ_AND` vs. `max(δ_OR,δ_INV)+δ_AND`). Both are
   sanctioned by §3 ("the two falling cases … each traversing one reconvergent
   branch").
4. **4-bit adder block, fully mechanised** (the fallback in §3 — "stop at
   `CIRC` plus a single 2-bit comparison" — was not needed). The topological
   bound is defined independently and the ripple sub-chain is extracted from a
   real term, so the `280 < 580` inequality compares two kernel-checked
   quantities.
5. **`gate1`/`gate2` denotations** are a mild `◯`-consuming generalisation of
   `PLLConstraints.gate` (which consumes an *unlifted* input); the buffer in
   `gateThenBuf` reuses the original `gate`. `PLLConstraints.lean` is imported,
   not modified.

### What remains (future work, not descoped from this task)

- A generic `n`-fold ripple builder (the chain here is unrolled to 4 stages);
  the carry-lookahead vs. ripple contrast (candidate C) on the same netlist
  substrate; the ternary-simulation exactness anchor (candidate D) as a
  separate development, per §5.
