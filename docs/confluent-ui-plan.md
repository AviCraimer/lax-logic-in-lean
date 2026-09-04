# UI for confluent PLL — the plan, and the calculus

*Branch `ui-confluence`, 2026-07-21. Standing order (Matthew): prove UI
for **confluent PLL** = PLL + the distribution scheme
`distF A B := ◯(A∨B) ⊃ (◯A∨◯B)`, starting from a new sequent calculus
adapted from G4c, porting the development, deferring probes, delegating
only if stuck. Every term is defined before use.*

---

## 0. The setting, and why it should help

**Confluent PLL** is the extension whose models are the **mutually
confluent** constraint models: for all worlds `x, w, v`,
`Rₘ x w → Rᵢ x v → ∃ u, Rᵢ w u ∧ Rₘ v u` (`PLLFrames.lean:224`,
"F&M Theorem 4.5"). It is **sound and complete** for `distF`
(`force_somehow_or_dist_of_confluent`; `derivU_iff_confluent_valid` in
`PLLConfluentComplete.lean`, via the natural-deduction system `DerivU`).

The one structural fact that drives everything: on confluent models the
∀∃-clause for ◯ **collapses to bare possibility**
(`force_somehow_iff_of_confluent`):

> **`w ⊩ ◯φ  ⟺  ∃u, Rₘ w u ∧ u ⊩ φ`.**

So on this class ◯ is an ordinary **diamond** over the
reflexive-transitive `Rₘ` — the ∀-over-`Rᵢ` layer disappears.

---

## 1. The new calculus G4cf

**G4c** (`PLLG4H.lean:97`) is `G4c Γ C := ∃ n, G4h n Γ C`, the
height-indexed contraction-free calculus (the repaired complete
"G4iLL″"). Its ◯-machinery is `laxR`, `laxL` (restricted to
◯-conclusions), and the two implication-left rules `impLLax`,
`impLLaxLax` — the second (double-◯ financing) is exactly the ∀∃
complication.

**G4cf** := G4c **plus one left rule** for the distribution:

> **`distL`**:  if `Γ` is `◯(A∨B), Δ` (up to permutation), then from
> `◯A, Δ ⊢ C` and `◯B, Δ ⊢ C` conclude `Γ ⊢ C`.

This is the additive, analytic (subformula-property-preserving) form of
`◯(A∨B) ⊢ ◯A∨◯B`: a `◯`-disjunction in the antecedent may be
case-split. Adding it as a *primitive* keeps the calculus cut-free. All
17 G4h rules are inherited verbatim.

**Why `distL` and not new ◯-right rules.** The user's "some proofs port
verbatim with only name changes" is maximised by an *additive* rule:
every existing structural theorem gets exactly one new case (the
`distL` case), everything else is a mechanical `G4h → G4hf` rename. A
more radical redesign (replacing `laxL`/`impLLaxLax` by diamond rules)
would be cleaner as a final artifact but would not port; it is a later
optional simplification, not the starting point.

---

## 2. Metatheory: what is provable, what is assumed

| Theorem | Status / route |
|---|---|
| **Soundness** `G4cf Γ C → confluent-valid` | PROVABLE. Induction on `G4hf`; the 17 shared cases mirror the existing G4c soundness, the `distL` case is `force_dist_elim` (a two-line corollary of `force_somehow_or_dist_of_confluent`, PROVED in the scaffold). |
| **Completeness** `confluent-valid → G4cf Γ C` | PROVABLE via `DerivU`: `G4cf ⊇ G4c` and `G4cf` derives every `distF` instance (from `◯A ⊢ ◯A∨◯B`, `◯B ⊢ ◯A∨◯B` by `distL`), so `G4cf ≡ DerivU`, and `derivU_iff_confluent_valid` closes it. Matthew's "already proven" holds *modulo* this equivalence. |
| **Cut admissibility** | ASSUME initially (Matthew's licence). Later: port `PLLG4HCut` — 17 cases verbatim + the `distL`/cut interaction (a genuine but standard new case). Only needed where the interpolation development uses cut. |
| **Termination / inversion** | Port `PLLG4HInv`, `PLLG4Space` — `distL` decreases the same multiset measure (`◯(A∨B)` ≻ `◯A`, `◯B`), so it fits the existing well-founded order. |

The whole G4 tower (`PLLG4H*.lean`, ~24 files) ports the same way:
**verbatim + one `distL` case each**. That is bulk, not difficulty.

---

## 3. The payoff: does bare possibility dissolve THE WALL?

This is the crux, and the reason the restriction is worth proving. Recall
the wall (`docs/semantic-ui-route.md` §0(hh)): in the amalgamation's
truth lemma / bisimulation, the **forward ◯-case** at a **same-val-trace
promising successor** cannot be financed — the promise pair keeps Henkin
depth `d`, needs a layered link at level `2d`, and every spend yields
`2d−1`. The repair (same-trace no-descent) is machine-refuted, and the
confluence refilter confirms the refutation *survives* on the confluent
class (gap-row failures 12/12).

**Claim: under bare possibility the wall does not arise.** The argument:

1. In the ∀∃ semantics, refuting `◯χ` at a world `k` is a **non-local**
   condition — *some* `Rᵢ`-successor `v` must have its row miss `χ`, and
   that `v` (the "promising successor") is the thing whose financing
   fails. Under **bare possibility**, `k ⊮ ◯χ` iff **`k`'s own row
   misses `χ`** — a *local* condition. **There is no promising
   `Rᵢ`-successor `v`, hence no same-val-trace promise pair, hence no
   `2d`/`2d−1` bookkeeping.**
2. The forward ◯-case of the truth lemma becomes the **standard diamond
   case**: `⟨Δ,m⟩ ⊩ ◯χ` iff some `Rₘ`-successor forces `χ` iff (canonical
   `Rₘ`, `obInv`) `χ ∈ Δ'.val` for an `Rₘ`-successor `Δ'` iff `◯χ ∈
   Δ.val`. `PLLConfluentComplete.lean` proves precisely this with **no
   promise component** ("no third theory component is needed anywhere").
3. In the recalibrated budget, ◯ costs **1**, not 2 (`crankC`): the
   ◯-case spends one `Rₘ`-zigzag, no preceding `Rᵢ`-zigzag. The parity
   mismatch that *was* the wall (need `2d`, have `2d−1`) is a `crank`-2
   artifact.

**Why the surviving samval failures do not reinstate the wall.** The
samval failures are about **`Rᵢ`-move rank descent at dead-ends** — the
`⊃`-case / `iforth`. Under confluence the `⊃`-case is unchanged and its
descent (`n → n−1`, `agree_iforth`, PROVED) is the *standard* budget,
which is fine. The dead-end failures only ever mattered to the
*promise-financing repair*, which is now unnecessary. So they become
**moot**, not fatal.

**The ONE new obligation this creates** (the honest sticking point): the
amalgamated model `N` must itself be **mutually confluent**, or the
bare-possibility ◯-clause cannot be used throughout the induction. This
`amalgam_confluent` obligation replaces the promise bookkeeping as the
thing to discharge. It is plausibly routine — `K` (canonical, confluent
by `PLLConfluentComplete`) and `M` (confluent by hypothesis) with an
amalgam whose `Rᵢ`/`Rₘ` are built componentwise — but it is genuinely
new, and it is where the next real proof effort goes. **If it fails,
that is the confluent analogue of the wall, and — per Matthew's rubric —
evidence against UI even in the restricted logic.**

---

## 4. Roadmap (multi-turn; this is a research port, not a one-turn task)

1. **[this turn]** `wip/G4conf.lean`: define `G4hf`/`G4cf` with `distL`;
   prove `force_dist_elim`; state soundness / completeness / cut with
   precise port-comments. Compile green.
2. `crankC` (◯ cost 1) + `LayeredBisimC` (bare-possibility zigzags) +
   `force_iff_of_layeredC`; redo the `WitTriple` arithmetic and CONFIRM
   the parity gap dissolves (this is the decisive mechanised step).
3. `witAmalgamC` + `amalgam_confluent` (the new obligation) + the
   confluent `wit_forceC`/`wit_pbisimC` — the ◯-case via `obInv`, no
   promises.
4. Port the interpolant construction (`itpA`/`itpE`) to `G4cf` and check
   whether the descent (H1/H2) simplifies under `distL`.
5. Only if stuck at (2)/(3): spin probe agents to hunt a confluent
   counterexample to the dissolved-wall claim.

Testing is deferred until (2)–(3) are attempted, per standing order.
