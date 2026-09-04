# Where the uniform-interpolation proof for PLL stands

*A status report for the supervisor, 2026-07-21. Written to be read by
someone who is not a specialist in uniform interpolation. Every
project-specific term is defined in §2, the glossary. Claims are marked
**PROVED** (machine-checked, `sorry`-free, axiom-audited), **REFUTED**
(machine-checked counterexample), or **OPEN**. Where I rely on a
background agent's report rather than my own check, I say so.*

---

## 0. The one-paragraph headline

We are trying to prove **Propositional Lax Logic (PLL) has uniform
interpolation (UI)**. We have a complete proof *skeleton* by the
"semantic route": UI reduces to three lemmas ("pillars"), and the final
assembly is machine-checked **modulo two named holes**, `wit_pbisim`
and `wit_force`. Pillar 1 is fully PROVED. Pillar 2 is PROVED except for
two "modal zigzag" clauses backed by 746,108 machine-checked examples
but not yet proved. Pillar 3 — the amalgamation — is assembled and
PROVED down to those two holes, and inside them *one single sub-case* is
the genuine obstruction: the forward ◯-case at a "same-value-trace"
successor. The natural repair for that sub-case was **REFUTED** by a
machine probe, which also *decoded the exact shape* of the obstruction
(a "rigid dead-end" world). A design pass (a background agent, report
below in §6, **not yet independently verified by me**) has since turned
that decoding into a candidate **dead-end clause** that appears to
**close** the truth-lemma half of the obstruction and **relocate** the
bisimulation half to a smaller, better-understood problem. So UI for PLL
is, honestly, still **OPEN** — but the wall has moved. Every individual
uniform interpolant we have ever tried to compute, we *have* computed
and machine-checked; what is missing is the general theorem that the
construction always works.

---

## 1. What we are trying to prove

### 1.1 PLL and the ◯ modality

**PLL** is intuitionistic propositional logic extended by one modality,
written **◯** ("lax"; in the belief reading of the companion paper,
"◯A = A holds under some idealised constraint"). It is a *nucleus* /
strong-monad modality: `A ⊢ ◯A`, `◯◯A ⊣⊢ ◯A`, and `A ⊢ B` gives
`◯A ⊢ ◯B`. The load-bearing fact for us is that ◯ is **reflexive**
(`A ⊢ ◯A`) — this is exactly what breaks the standard proof technique
(§5).

**Semantics (constraint models).** A model is a set of "worlds" with

* a preorder **Rᵢ** (the intuitionistic accessibility — "more
  information"),
* a sub-relation **Rₘ ⊆ Rᵢ**, reflexive and transitive (the
  *constraint* relation), and
* a set **F** of **fallible worlds** — worlds that force *every*
  formula, `⊥` included (collapsed/inconsistent evidence states; the
  genuinely new ingredient PLL adds over ordinary Kripke semantics).

Forcing (`⊩`) is intuitionistic on the connectives, and on ◯ it is the
**∀∃-clause** (`PLLKripke.lean:58`):

> **w ⊩ ◯φ  ⟺  for every Rᵢ-successor `v` of `w`, there is an
> Rₘ-successor `u` of `v` with `u ⊩ φ`**
> i.e.  `w ⊩ ◯φ  :=  ∀v, Rᵢ w v → ∃u, Rₘ v u ∧ u ⊩ φ`.

Read it as: no matter how much more information you gather (`v`), a
constraint can still deliver `φ`. This ∀-then-∃ shape is the source of
every difficulty below.

### 1.2 From interpolation to *uniform* interpolation

Ordinary **interpolation**: if `A ⊢ B`, there is an "interpolant" `I` in
the *shared* vocabulary of `A` and `B` with `A ⊢ I ⊢ B`.

**Uniform** interpolation makes the interpolant depend on only *one*
side. For every formula `M` and variable `p` there are **`p`-free**
formulas `∀p.M` and `∃p.M` (the *propositional quantifiers*, a.k.a. the
uniform interpolants) such that for every `p`-free `N`:

> `N ⊢ ∀p.M  ⟺  N ⊢ M`   and   `∃p.M ⊢ N  ⟺  M ⊢ N`.

Equivalently, in the Lindenbaum algebra (`⊢` is `≤`),

> **∀p.M  :=  ⋁ { D `p`-free | D ⊢ M }**   and
> **∃p.M  :=  ⋀ { D `p`-free | M ⊢ D }**.

The content of UI is that these **infinite** joins/meets are always
*attained by a single formula*. (Machine-checked sanity checks:
`∀p.(ξ ∨ p) = ξ`, `∃p.(ξ ∧ p) = ξ`.) Pitts proved UI for intuitionistic
logic (1992). Whether **PLL** has UI is **open in the literature**; the
algebraic form (amalgamation / model-completion for *nuclear Heyting
algebras*) is likewise recorded as open — a proof would settle it. The
nearest positive result is Litak–Visser's 2024 semantic UI for **iSL**
(intuitionistic strong Löb); adapting their argument is the "semantic
route" of §3.2.

### 1.3 What we already know (this is not starting from zero)

Machine-checked, `sorry`-free:

* **The essential-fibre theorem (an iff):** for `p`-free `ξ`, some `M`
  with `p` essential has `∀p.M = ξ` **iff** `⊬ ξ` (dually `∃p` iff
  `ξ ⊬ ⊥`). On the closed fragment this pins the essential ∀p-image to
  `RN(◯,{}) ∖ {⊤}` — the conjectured structure theorem, proved.
* **The entire one-variable value table is certified** (25 classes;
  attained values `{⊥, ◯⊥, ⊤, ¬◯⊥, ◯¬◯⊥}`).
* **Individual interpolants proved outright:** `∀p.p = ⊥`,
  `∀p.◯p = ◯⊥`, `∀p.(p∨¬p) = ⊥`, `∀p.(◯p⊃p) = ⊥`, `∀p.◯(◯p⊃p) = ◯⊥`,
  `∀p.(((p⊃◯⊥)⊃p)⊃p) = ◯⊥`, and the whole ◯-free one-variable fragment
  (Pitts's values, unconditionally).

So we can compute the interpolant for every concrete formula we try.
**What is open is uniformity** — a *single construction* that provably
works for *all* `M`.

---

## 2. A working glossary (the terms this report leans on)

You asked me to pin down several terms as if they were real
definitions. They are, so here they are. Two of the three diagrams in
the accompanying chat message illustrate the last two entries.

**Constraint model.** As in §1.1: worlds `W`; a preorder `Rᵢ`; a
reflexive-transitive `Rₘ ⊆ Rᵢ`; a fallible set `F`; and a valuation
saying which atoms hold at which worlds (up-closed along `Rᵢ`).

**The constraint-row of a world.** For a world `w`, its **row** is the
set of its `Rₘ`-successors,

> **Row(w) := { u ∈ W | w Rₘ u }.**

The name is literal: if you write `Rₘ` as a 0/1 matrix indexed by
`W × W`, then `Row(w)` is exactly the `w`-th **row** of that matrix; the
`w`-th **column** would be the `Rₘ`-*predecessors* `{ u | u Rₘ w }`. The
∀∃-clause for ◯ *reads rows*: `w ⊩ ◯φ` demands that every `Rᵢ`-successor
`v` has *some* member of `Row(v)` forcing `φ`. A **row-witness** for
`◯φ` at `v` is such a member; a **row-member** of `v` is any element of
`Row(v)`. (Because `Rₘ` is reflexive, `v ∈ Row(v)` always — a world is
in its own row. That reflexivity is one of the few things that finances
the ◯-case; see `canon_box_dichotomy` in §4.3.)

*This is a notion in a model, not in an algebra.* You asked whether "row"
is about `RN`. **No.** `RN(◯,{})` (next entry) is a lattice of *formula
classes*; a *row* is a set of *worlds*. They meet only in that the
formulas in `RN` are what *describe* worlds (via the description triple,
below).

**`RN(◯,{})`.** The Lindenbaum algebra of the **closed** (variable-free)
fragment of PLL: variable-free formulas up to provable equivalence, with
`⊢` as the order. It is the lax analogue of the **Rieger–Nishimura
ladder** (the free Heyting algebra on one generator), here generated by
`◯` and `⊃` over *no* variables. It is an **infinite** ladder
`⊥ < ◯⊥ < ¬◯⊥ < ◯¬◯⊥ < …`; its exact lattice height is itself open in
the literature. Every value we have computed for a closed uniform
interpolant lives in this ladder.

**Hereditary / up-closed.** A set of worlds `X` is **hereditary** (an
`Rᵢ`-up-set) if `w ∈ X` and `Rᵢ w w'` imply `w' ∈ X`. The truth-set
`{ w | w ⊩ φ }` of *every* formula is hereditary — that is intuitionistic
monotonicity. This is why the m-clause is hard (see below and §4.2):

> "**No PLL formula quantifies over one world's row (row-membership is
> not hereditary).**" Precisely: fix a target world `u₀`. The property
> `P(w) := "u₀ ∈ Row(w)"` (i.e. `w Rₘ u₀`) is **not** the truth-set of
> any formula, because (i) formulas cannot name a specific world `u₀`,
> and (ii) `P` is not even hereditary — moving to a more-informed
> `w' ≽ᵢ w` need not preserve which specific `u₀` are `Rₘ`-reachable.
> The only thing a formula *can* say about rows is existential and
> hereditary — "`◯φ`: every future's row has *some* `φ`-witness". So
> there is no formula whose *failure* hands you a *particular*
> row-member to use as a bisimulation partner. That missing handle is
> exactly the open modal clause.

**Fallible world.** A world in `F`; it forces every formula. In the
`Rₘ`-zigzag a fallible target can be matched "for free" (it constrains
nothing) — the "escape" clauses of the bisimulation.

**The description triple (`trace c`).** Fix the finite subformula-closure
`cl` of the formula `M` under study. A world `c`'s **description** is the
triple

> **trace `c` = ⟨val, fal, mfal⟩**, all subsets of `cl`:
> `val` = closure formulas `c` forces; `fal` = closure formulas `c`
> refutes; **`mfal` = the "promises"** — the ◯-formulas that `c` refutes
> but which are *delivered along some `Rᵢ`-successor's row* (promised,
> not delivered at `c` itself).

The **val-trace** of `c` is just the `val` component. Two worlds have
"the same val-trace" when they force exactly the same closure formulas.

**`crank`** (`PLLSemUILayered.lean:87`). A complexity measure: atoms and
`⊥` cost 0; `∧`/`∨` take the max; `⊃` adds 1; and **◯ adds 2**. ◯ costs
two because its ∀∃-clause spends one `Rᵢ`-move *then* one `Rₘ`-move (see
the middle diagram). Rank bounds throughout are stated in `crank`.

**`ν(M)`, the budget count.** The number of subformulas of `M` that are a
variable, an implication, or a ◯-formula (Litak–Visser's `n_X`). The
rank bound for the fragment join is `2ν+1`.

**Budget, and "finances".** This has real technical content; it is not a
figure of speech. Both routes carry a **numeric budget** that proof
steps spend:

* in the syntactic route (§3.1) it is the integer `b` in `itpA…b…`;
* in the semantic route it is the **level** of a layered bisimulation
  link, `2d ± 1`, where `d` is the Henkin depth (below).

A proof step **costs** budget (a zigzag move drops the level by one). A
few steps **release** budget: when the theory strictly grows, the Henkin
depth `d` drops, and a lower depth *needs a lower link level*, freeing
slack. To say "**step X is financed**" is the precise statement that,
after X, the invariant's numeric inequality can be re-established — the
link level you are left holding is `≥` the link level the next witnessing
triple requires. **The wall (§4) is an unfinanced step**: it requires a
link at level `2d` but leaves you holding only `2d−1`. So "finances" =
"the budget arithmetic closes", nothing looser.

**Zigzag; modal zigzag; layered bisimulation.** A **bisimulation** `Z`
between models `M`, `N` is a relation satisfying the **back-and-forth**
("zigzag") conditions (first diagram):

* **forth (zig):** if `w Z w'` and `w R v` in `M`, there is `v'` with
  `w' R v'` in `N` and `v Z v'`;
* **back (zag):** if `w Z w'` and `w' R u'` in `N`, there is `u` with
  `w R u` in `M` and `u Z u'`.

The name pictures the path: go forth in one model, come back matched in
the other. PLL has **two** relations, so a bisimulation needs **four**
clauses — the **intuitionistic zigzag** `iforth`/`iback` (for `Rᵢ`) and
the **modal zigzag** `mforth`/`mback` (for `Rₘ`). A **layered (bounded)
bisimulation** `Z_n` (`LayeredBisim`, `PLLSemUILayered.lean:111`) is
level-indexed: **each single zigzag move drops the level `n+1 → n`**
(middle diagram, right panel). A `Z_n`-link guarantees agreement on all
formulas of `crank ≲ 2n`; because ◯ costs 2, checking one ◯-formula
spends one `iforth`/`iback` *and* one `mforth`/`mback` — two levels.

**Henkin depth `d(Δ) := |cl| − |val(Δ)|`.** The number of closure
formulas the theory `Δ` has *not* validated. It **strictly drops** when
the theory grows, and it is the well-founded measure that makes the
truth-lemma recursion terminate and pays for fresh witnessing triples.

**Witnessing triple (`WitTriple`).** The Litak–Visser Lemma-5.4
bookkeeping. A pair `⟨Δ, m⟩` (a canonical theory `Δ`, a model world `m`)
is **admissible** when there is a triple `(k, k′, m′)` with
`Δ = Th(k) = Th(k′)`, `k′ ≼ k`, `m′ ≼ m`, and two layered links
`k′ Z_{2d+1} m′` and `k Z_{2d} m`. The links are the *budget* the
zigzag moves spend.

**Dead-end.** A world with no proper successors (only itself under `Rᵢ`
and `Rₘ`) — a "rigid postponement point". In the refuted repair (§4.2)
every failure is caused by a dead-end successor forcing `q ∧ ¬◯⊥`.

**A note on the word "LEGO".** In earlier notes I called the collection
of small proved auxiliary lemmas in `PLLSemUIHenkin.lean` "the canonical
LEGO". **That is not an acronym and not a technical term** — it was a
throwaway metaphor (small reusable *bricks* you assemble into the
amalgamation). It should not appear in the thesis. From here I call them
**the proved auxiliary lemmas** or **the canonical toolkit**; the
mathematics is in §4.3 and each lemma carries an in-file `#print axioms`
guard.

---

## 3. The strategy: two routes, one live

### 3.1 The syntactic route (task #9) — the side thread, and the X9 worked example

Build the interpolant as an explicit term `itpA`/`itpE` carrying a
numeric **budget** `b` (`itpA 0 = ⊥`, `itpE 0 = ⊤`). UI reduces to a
**budget-descent** lemma: past a threshold, `itpA(b+1) ⊢ itpA(b)`, i.e.
the ascending budget sequence has stabilised.

You asked to see **configuration X9** concretely. Here it is, verbatim
from the probe harness (`wip/onevar_probe.lean:129`):

```lean
  -- eliminate p from the interpolation problem  Γ ⊢ g  over space S:
  let S : Finset PLLFormula := {fp, bb, nbb, op, bx op}   -- {⊥, ◯⊥, ¬◯⊥, p, ◯p}
  let Γ : List PLLFormula := [nbb]                        -- [¬◯⊥]
  let g := bx op                                          -- ◯p
```

So X9 asks for the ∀p-interpolant of the sequent **`¬◯⊥ ⊢ ◯p`**,
eliminating `p`, with the subformula space `S = {⊥, ◯⊥, ¬◯⊥, p, ◯p}`.
`itpA p S b Γ g` is the ∀p-interpolant at budget `b`.

**Why X9 looked dangerous.** Printing the *raw* interpolant sizes at
`b = 0,1,2,3,4` gave normal-form weights **1, 2, 39, 143, 566** —
apparently exploding, the signature of a genuine counterexample where the
interpolant never stabilises. The interpolants obey a clean recursion
(writing `g := ◯⊥`, `n := ¬◯⊥`):

> `A₁ = ◯⊥`, `E₁ = ¬◯⊥`,
> `E_{b+1} = ¬◯(E_b ⊃ A_b)`,
> `A_{b+1} = P_b ∨ ◯(E_b ⊃ P_b)`  where  `P_b = ◯¬E_b ∨ ◯(E_b ⊃ A_b)`.

**Why it is actually harmless.** Under a sound simplifier the apparent
climb collapses to a **five-element** equivalence class,

> `{ ⊥, ⊤, ◯⊥, ¬◯⊥, ◯(¬◯⊥ ⊃ ◯¬¬◯⊥) }`,

and the interpolant **stabilises at `b = 2`**:

| `b` | 0 | 1 | 2 | 3 … 9 (checked) |
|-----|---|---|---|-----------------|
| ∀-interpolant `itpA` | ⊥ | ◯⊥ | ◯(¬◯⊥ ⊃ ◯¬¬◯⊥) | **same class** |
| ∃-interpolant `itpE` | ⊤ | ¬◯⊥ | ¬◯⊥ | **same class** |

Now the **threshold arithmetic**, which is the whole point. The library
threshold is `defect(S,Γ) · (|jGoals S| + 2)`, where
`defect(S,Γ) = |S ∖ Γ|` (`PLLG4UITrunc.lean:114`) and `jGoals` collects
the "jump goals" of `S`. For X9:

* `defect = |{⊥,◯⊥,¬◯⊥,p,◯p} ∖ {¬◯⊥}| = 4`;
* `jGoals(S) = {⊥, ◯⊥}` (only `¬◯⊥ = ◯⊥⊃⊥` contributes), so
  `|jGoals| = 2`;
* threshold `= 4 · (2 + 2) = **16**`.

So the interpolant stabilises at `b = 2` against a threshold of **16** —
**fourteen levels of slack**. The "climb" was pure syntactic bloat of one
constant equivalence class. **No counterexample survives.**

The Lean development (`wip/onevar_descent_dev.lean`) reduces the descent
to two named holes, of which the second is the real one:

```lean
/-- (H2) The distilled core — ∃-side stabilisation at threshold. -/
theorem itpE_stab (p : String) (S : Finset PLLFormula)
    (fuel b : Nat) (Γ : List PLLFormula)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jGoals S).card + 2) ≤ b + 1)
    (hSv : ∀ F ∈ S, F.atoms ⊆ {p}) (hΓv : ∀ F ∈ Γ, F.atoms ⊆ {p}) :
    G4c [itpE p S fuel b Γ] (itpE p S fuel (b + 1) Γ) := by
  sorry
```

This route is currently the **side thread**; the frontier is the
semantic route.

### 3.2 The semantic route (task #33) — the live thread

Take the **rank-bounded join** as the *definition* of the interpolant:

> **`∀p.M := ⋁ { D p-free, crank D ≤ 2ν+1 | D ⊢ M }`**  (dually for ∃p).

For this to *be* UI we need the **three pillars**:

| Pillar | Statement (informal) | Buys us |
|---|---|---|
| **1. Fragment finiteness** | Finitely many `p`-free formulas of `crank ≤ r`, up to ≡. | The join is a **finite** disjunction — an actual formula. |
| **2. Agreement ⇒ layered bisimulation** | Agreeing on all `p`-free formulas of `crank ≤ 2α+2` ⟹ linked by a rank-α layered bisimulation off `p`. | "Same fragment-value" ⟹ "behaves the same". |
| **3. Amalgamation** | A layered link between fragment-world `k₀` and model-world `m₀` ⟹ a `p`-variant `N` of `M` agreeing with `k₀` on the whole closure. | "Forgets `p`": the join's models = the `p`-projections of `M`'s models. |

With all three, the Litak–Visser Theorem 5.1 argument gives that the
rank-bounded join **is** `∀p.M`.

---

## 4. Pillar-by-pillar status, and the exact `sorry`-ledger

**Import is not dependency.** In Lean a `sorry` only matters to a result
if that result's proof *term* names the sorried lemma — which shows up as
`sorryAx` in its `#print axioms`. The root module imports all fifteen
`PLLSemUI*` files, and that chain has **five** live `sorry`s, but they
are *not* all on any critical path. Verified by name-reference:

| # | Location | What it is | Consumed by a proof term? |
|---|---|---|---|
| 1 | `PLLSemUILayered.lean:827` | `amalgamation` (old `LayeredBisim`-form interface) | **No** — every reference is a comment. Dead. |
| 2 | `PLLSemUIChar.lean:322` | pillar-2 **mforth** m-clause | **No** — `layered_of_frag_agree_W` named by no proof term yet. |
| 3 | `PLLSemUIChar.lean:327` | pillar-2 **mback** m-clause | **No** — same. |
| 4 | `PLLSemUIHenkin.lean:341` | **`wit_pbisim`** (pillar-3 Claim 1) | **Yes** — by `amalgamation_assembled`. |
| 5 | `PLLSemUIHenkin.lean:352` | **`wit_force`** (pillar-3 Claim 2) | **Yes** — by `amalgamation_assembled`. |

The **three pillars are not yet chained into a single UI theorem**: the
would-be capstone (`SemAllDefinable`/`SemExDefinable`) is deliberately
left as an unproved `Prop`. So *no proved result today depends on any of
these five sorries* — the artifact that would is not written. The one
assembled result, `amalgamation_assembled`, has a remaining footprint of
**exactly** `wit_pbisim` + `wit_force`.

### 4.1 Pillar 1 — Fragment finiteness — PROVED

`frag_reps_exist'` (`PLLSemUIFrag.lean`, `sorry`-free): a
DNF-over-components construction gives, per rank `r` and finite alphabet,
a finite list of representatives for the `p`-free formulas of
`crank ≤ r`. This makes `∀p.M` a *definable object*. Nothing open.

### 4.2 Pillar 2 — Agreement ⇒ layered bisimulation — i-clauses PROVED, two m-clauses OPEN

`layered_of_frag_agree_W` builds a rank-`n` weak layered bisimulation
from fragment agreement at `crank ≤ 2n+2`. Six of eight clauses proved;
the intuitionistic zigzags via the **character argument** (a non-fallible
successor `v` refutes its own negative character `θ⁻`, so `θ⁺ ⊃ θ⁻` fails
at `v`, agreement transfers the failure, and the witness *is* the
partner). The two **modal** clauses are open. The proof state at `mforth`
(`PLLSemUIChar.lean:318`):

```lean
  · -- mforth: THE open clause (probe-backed)
    intro α w₁ w₁' hZ u hu
    by_cases huF : u ∈ M.F
    · exact .inr huF                 -- u fallible: land on a fallible escape
    · exact .inl (by sorry)          -- u NON-fallible: need a genuine partner
```

At the `sorry`: given rank-agreement `hZ` of `(w₁,w₁')` at level `α+1`,
and a **non-fallible** `Rₘ`-successor `u` of `w₁`, produce a non-fallible
`Rₘ`-successor `u'` of `w₁'` with rank-α agreement between `u` and `u'`.
In words, **"forth-m from agreement"**: a non-fallible row-member must
have an agreeing row-partner. This is exactly the clause the glossary's
heredity remark says has no character-derivation handle: no formula
isolates a single row-member. Evidence: `mforth_probe.lean` over **504
frames / 746,108 agreeing pairs** finds **zero** non-fallible forth-m
violations. Very probably true — but not proved. The default endgame
**bypasses** it: route the amalgamation's ◯-case through the canonical
promises (which `wit_force` does anyway).

### 4.3 Pillar 3 — Amalgamation — assembled, PROVED modulo two claims

The whole amalgamation is machine-checked down to two named holes:

```lean
theorem amalgamation_assembled (hcl : SubClosed cl)
    (k₀ : K.W) (m₀ : M.W) (hB : B.Z (2 * cl.card + 1) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) := by
  … obtain ⟨C, hC⟩ := wit_pbisim cl B      -- Claim 1
  … rw [wit_force cl B hcl _ φ hφ]          -- Claim 2  (fully proved otherwise)

theorem wit_pbisim :   -- Claim 1: projection ⟨Δ,m⟩ ↦ m is a p-bisimulation
    ∃ C : PBisim p M (witAmalgam cl B),
      ∀ (q : (witAmalgam cl B).W), C.Z q.1.2 q := by sorry

theorem wit_force (hcl : SubClosed cl) :   -- Claim 2: the truth lemma
    ∀ (q : (witAmalgam cl B).W) (φ : PLLFormula), φ ∈ cl →
      ((witAmalgam cl B).force q φ ↔ φ ∈ q.1.1.1.val) := by sorry
```

The **proved auxiliary lemmas** (the "canonical toolkit", each
axiom-guarded in-file) finance *most* of the ◯-case, replacing the iSL
trick that does not port:

* `canon_box_dichotomy` (backward ◯, *reflexivity rescue*): if
  `◯χ ∈ val(Δ)` then either `χ ∈ val` and `Δ` is its own row-witness by
  `Rₘ`-reflexivity (no move), or the witness strictly grows the theory
  (depth drop pays).
* `trace_box_refuter` + `promise_blocks_row` (forward ◯, *promise
  rescue*): a world refuting `◯χ` has an `Rᵢ`-successor whose description
  **promises** `χ` (in `mfal`), and a promised formula is validated by
  **no** canonical `Rₘ`-successor — so the amalgam refutes `◯χ` through
  the promise alone, with no `Rₘ`-move in `M`.
* `imp_unval_cases` + `traceT_val_ssubset`: the `⊃`-case with strict
  theory growth (the one iSL "ψ-trick" that ports).
* `traceT_mfal_empty_of_fallible`, `canonTop`, `rm_canonTop_iff`:
  fallible row-members erase promises; the canonical top `⟨cl,∅,∅⟩` is
  consistent and fallible; the m-zigzag's fallible escapes land there.

All strict cases and the backward direction are fully financed. One
sub-case is not. That is the wall.

---

## 5. The wall — the goal I believe is true but cannot yet close

### 5.1 The exact obstruction (third diagram)

Inside `wit_pbisim`/`wit_force`'s ◯-case, take a world `k` with a
**promising** `Rᵢ`-successor `v ≽ᵢ k`. Normally `v` grows the theory,
the Henkin depth drops, and the drop finances a fresh triple. **The
unfinanced case: `v` has the *same val-trace* as `k`.** Then:

* the promise pair `⟨trace v, m₂⟩` keeps the **same depth `d`**;
* admissibility wants an unprimed link at level **`2d`**;
* every spend of the reservoir yields only **`2d − 1`** — **one level
  short** (the middle box of the third diagram).

In iSL, Litak–Visser pay for this by choosing the refuting world
**`⊏`-maximal**, which needs **converse well-foundedness (Löb
structure)** of the modal relation. **PLL has none:** `Rₘ` is
reflexive-transitive, so a world refuting `◯χ` can *never* force `◯χ`,
and the maximality trick is unavailable. This is *the* one combination —
**same-theory + K-side-first** — their bookkeeping cannot pay for, and it
is exactly PLL's reflexive ◯-case.

### 5.2 The repair we tried, and why it failed

The natural fix is a **same-trace no-descent clause**: if the i-move
keeps the closure-trace, let the partner keep the rank (`n` in, `n` out,
not `n → n−1`). If sound, it plugs the gap directly. **It is
machine-REFUTED** (`samval_probe.lean`, two passes):

* Variable-free (264 models, 746,108 pairs): **clean** — and the awkward
  same-trace moves *vanish* as the closure grows (109 / 5 / 0 needed over
  `cl = [⊥] / [⊥,◯⊥] / [⊥,◯⊥,¬◯⊥]`).
* One-atom (650 models, **2,377,307** pairs): **REFUTED** — 499 / 44 / 12
  failures over `cl = [⊥,q] / [⊥,q,◯q] / Sub(◯q⊃q)∪{⊥}`.

**The decoded failure shape** (checked by hand on `◯(◯q⊃q)`):

> the moved world is a **rigid dead-end** forcing `q ∧ ¬◯⊥` (**crank 3**),
> no proper successors; the partner model has **no** dead-end above the
> matched world; the roots still agree up to rank 3 because the *absence*
> of such a dead-end only becomes visible at `¬¬◯⊥` (**crank 4**).

So the one-level rank descent is **semantically sharp** even under
closure-trace-equality, and every decoded failure involves a **dead-end
successor**. This is what the dead-end clause (§6) must handle.

---

## 6. Update: the design agent's dead-end clause (kernel-verified 2026-07-21 13:41)

*The design agent's scaffold and doc are committed on its worktree
branch (not merged, not pushed). **Independently verified by me**: I
elaborated a copy of `wip/promise_pair_dev.lean` against the built
dependency chain and ran `#print axioms` on every declaration. Result:
the file compiles; exactly two `sorry` warnings (`wit_force'` at 343,
`wit_pbisim'` at 356); the six substantive lemmas are `sorryAx`-free —
the dead-end core (`IsDeadEnd`, `box_val_of_val`, `deadend_box_in_val`)
pins `[propext, Quot.sound]` (choice-free, as claimed), the financing
lemmas (`nondeadend_passup`, `deadend_wit_of_move`,
`strict_wit_of_passup`, `deadend_pair_refutes_box`) pin the standard
three; the three deep claims (`wit_force'`, `wit_pbisim'`,
`amalgamation_assembled'`) carry `sorryAx` exactly as expected.*

**The invariant (a hybrid).** Admissibility becomes a disjunction

> `Adm ⟨Δ,m⟩ := Nonempty (WitTriple …) ∨ Nonempty (DeadEndWit …)`,

where the new `DeadEndWit` certificate carries: `isDeadEnd`
(`Δ.fal ⊆ Δ.mfal` — `Δ` promises everything it refutes), a describing
non-fallible K-world `kd`, and a **degraded** link `B.Z (2d−1) kd m`
(one below the full `2d`). Option (a)'s degraded link is used, but *only
at dead-end pairs*, where option (b)'s structural rigidity makes the
missing level irrelevant.

**Discharge of the ◯-forward same-trace case — a dichotomy on the
promiser `v`** (all four sub-lemmas reported PROVED):

* **Non-dead-end** (`nondeadend_passup`, `strict_wit_of_passup`): a
  `ψ ∈ fal ∖ mfal` exhibits an `Rₘ`-successor that still promises `χ` but
  *strictly grows the val-trace* — so it is not a same-trace move at all,
  but an ordinary strict move, financed by the unprimed link into a
  **full** `WitTriple`.
* **Dead-end** (`deadend_box_in_val`, `deadend_pair_refutes_box`,
  `deadend_wit_of_move`, choice-free): `◯χ ∈ fal ⇒ χ ∈ mfal` (from
  strength + totality + `fal ⊆ mfal`), so the pair refutes `◯χ` **in
  place** through `promise_blocks_row` — no move, no link spend, so the
  `2d−1` certificate suffices.

Neither branch asks for `2d` where only `2d−1` exists; the refuted
no-descent step never reappears. "Is a dead-end" is a **decidable
`Finset` inclusion** (no normalisation needed); a genuine promise forbids
fallibility, cleanly separating rigid dead-ends from the fallible
`canonTop`.

**Honest assessment (the agent's, which I find plausible): closes one
horn, relocates the other.**

* **Closes** the truth-lemma horn (`wit_force`): the ◯-forward same-trace
  obstruction is dissolved; its new mathematical content is proved.
  (`wit_force'` itself stays sorried pending a mechanical port of the
  existing induction that calls the four lemmas at the ◯-branch.)
* **Relocates** the bisimulation horn (`wit_pbisim`): `DeadEndWit` pairs
  carry no primed reservoir, so `wit_pbisim`'s same-theory zag at a
  dead-end world facing an atom-growing `M`-move cannot be financed (the
  level decays `2d−1, 2d−2, …`). This is *localised* to rigid-row-shadow
  worlds, has a named tool (`lobTowerBase`, a proved `p`-variant, with
  `resid_probe` discharging the live gap row through it), and converts a
  *financing* problem into a *frame-assembly* problem where the existing
  `adjoin` framework has traction.

Net: a faithful reduction of the open problem to its rigid core — real
progress, not a full solution. **My next verification step** is to
rebuild the scaffold and `#print axioms` the five sub-lemmas before I let
any of this count as PROVED.

---

## 7. The honest ledger — and: is UI even true?

* **PROVED:** pillar 1; pillar 2's intuitionistic zigzags; the canonical
  toolkit; the amalgamation assembly modulo the two claims; the
  essential-fibre theorem; the full one-variable value table; many
  individual interpolant values; the ◯-free fragment unconditionally.
* **REFUTED:** the naive Litak–Visser Thm 4.7 form of pillar 2; the
  same-trace no-descent repair (§5.2); the "3-chain confinement"; and the
  X9 counterexample candidate itself (stabilises at `b=2 ≪ 16`).
* **OPEN:** `wit_pbisim`, `wit_force` — now reduced, per §6
  (kernel-verified), to `wit_pbisim`'s dead-end zag.

**Is UI for PLL true? Probably yes — a judgement, not a theorem.** *For:*
every counterexample search dies (24 configs, deep X9, 746k pairs with
zero violations, the whole one-variable table certified; nothing climbs
past its budget). *Against:* the obstruction is real and specific, the
standard financing trick provably does not port (reflexive ◯), and the
first repair was refuted before the dead-end clause rescued the truth-lemma
half. Under the machine-checked mandate, "probably yes" means **OPEN**.

---

## 8. Background agents + where I could use your help

* **Agent A — rerun `v2quant`** (still running at the time of writing):
  computes the semantic rank-bounded `∀p`/`∃p` in the old one-variable
  harness with a lowered budget and the F-free frames added, and reads
  the **X9 verdict** — is the syntactic wall the same wall as the
  semantic one? Interim: dictionary 15 classes as expected; `∀p.◯p` and
  `∀p.◯(◯p⊃p)` both stabilise at `◯⊥` from rank 2, countermodel-certified.
  The decisive X9 row and the match tests are still pending.
* **Agent B — the dead-end clause** (done; §6): design + scaffold on a
  branch, pending my verification.

**Where your supervision helps most:**

1. **The dead-end clause is a modelling choice.** Are you content to
   treat a "rigid dead-end forcing `q ∧ ¬◯⊥`" as a *primitive* canonical
   world (repair 2), or must it arise from the promise mechanism (repair
   1)? The agent chose a hybrid; the residual `wit_pbisim` gap is a
   frame-assembly problem where your nuclei/assembly intuition is exactly
   the relevant expertise.
2. **Is the reflexive-◯ obstruction telling us UI might *fail*?** If
   `wit_pbisim`'s dead-end zag genuinely cannot be assembled, the honest
   next experiment is to *hunt* a two-variable formula whose interpolant
   climbs — I can aim the probe at the dead-end family directly.
3. **Sign-off on the machine-checked reading.** I treat "746k pairs, 0
   violations" as *evidence*, never proof; and I have flagged §6 as
   agent-reported-pending-my-verification. If you want the pillar-2
   m-clause (or the §6 sub-lemmas) proved-or-refuted rather than
   probe-backed / agent-reported, that sets the priority order.

*Files: `docs/semantic-ui-route.md` §0(ff)/(gg)/(hh); `PLLSemUIHenkin.lean`
(toolkit + the two claims); `PLLSemUIChar.lean` (pillar 2);
`PLLSemUIFrag.lean` (pillar 1); `wip/onevar_probe.lean` + `…descent_dev.lean`
(X9); `wip/samval_probe.lean` (the refutation); `wip/v2quant_probe.lean`
(cross-route); and the design agent's branch (§6).*

---

# Addendum, 2026-07-21 afternoon (supervisor session, Fable)

## 9. The confluence route (Matthew's proposal (b)) — the correspondence is already machine-checked

**Definition (mutual confluence; verbatim from `PLLFrames.lean:224`,
docstring "F&M Theorem 4.5").** A constraint model `C` is **mutually
confluent** when

> for all worlds `x, w, v`:  if `x Rₘ w` and `x Rᵢ v`, then there is a
> world `u` with `w Rᵢ u` and `v Rₘ u`.

A commuting square: a constraint step and an information step from a
common source can always be reconciled at a common world; opposite
sides of the square carry the same relation. (Diagram delivered in
chat, 2026-07-21.)

**Status of the claimed equivalence: CONFIRMED, both halves formalised.**

* *Soundness* (`PLLFrames.lean:240`,
  `force_somehow_or_dist_of_confluent`): on mutually confluent models
  every instance of the distribution scheme
  `distF A B := ◯(A∨B) ⊃ (◯A ∨ ◯B)` is valid.
* *Completeness* (`LaxLogic/PLLConfluentComplete.lean`):
  `derivU_iff_confluent_valid` — `DerivU Γ φ ↔ Γ ⊨ φ` over all mutually
  confluent models, where **`DerivU`** is natural deduction (`LaxND`)
  with finitely many instances of the scheme as extra hypotheses
  (equivalent to the Hilbert extension). Canonical model: worlds =
  deductively closed prime sets (the improper set allowed — it is the
  fallible world); `Rᵢ` = inclusion; `T Rₘ U` iff `T ⊆ U` and every
  member of `U` is ◯-ed in `T`. The engine is `obInv T := {ψ | ◯ψ ∈ T}`,
  which **because of the scheme** carries prime sets to prime sets and
  yields both the modal truth-lemma case and canonical confluence.
  The file's header notes it is deliberately classical (Zorn) with
  audit `clean`; I have not independently re-run its `#print axioms`
  (flagged for the audit pass).

**The structural bonus** (`force_somehow_iff_of_confluent`,
`PLLFrames.lean:229`): on mutually confluent models the ∀∃-clause for
◯ **collapses to bare possibility**:

> `w ⊩ ◯φ  ⟺  ∃u, w Rₘ u ∧ u ⊩ φ`.

("Bare possibility" = the clause of an ordinary diamond modality over
`Rₘ`; the ∀-over-`Rᵢ` layer disappears.) Four consequences aimed
squarely at the open sorries:

1. **The §0(gg) ∀∃-divergence dissolves.** The reason the pillar-2
   m-clause had no character-argument handle was that no PLL formula
   speaks about a single world's row. Under bare possibility, `◯χ` at
   `w` says exactly "Row(w) meets ⟦χ⟧", and `w ⊮ ◯χ` says exactly
   "Row(w) ∩ ⟦χ⟧ = ∅" — ◯-formulas now speak directly about the
   world's own row, in both polarities.
2. **The promise machinery becomes dispensable on this class.** The
   completeness file states it in as many words: no promise component
   is needed anywhere, because refuting `◯χ` at a canonical world is
   definitional (`χ ∈ U` for a row-member `U` forces `◯χ ∈ T`).
   `mfal`, `trace_box_refuter`, `promise_blocks_row` — the forward-◯
   apparatus — may all simplify drastically.
3. **The budget calibration changes.** `crank` charged ◯ **2** because
   the clause spends an `Rᵢ`-move then an `Rₘ`-move. Under bare
   possibility ◯ should cost **1**. THE WALL was a parity mismatch
   (a same-val-trace promise pair needs a link at level `2d`, every
   spend yields `2d−1`); whether that mismatch survives the ◯-cost-1
   recalibration is precisely the first thing to check. A hope with a
   concrete check, not a result.
4. **The countermodel geography shifts.** The or-split fork
   (`modelOrSplit`, F&M Fig. 3 middle) is *not* mutually confluent
   (hand-check: `r Rₘ a`, `r Rᵢ b`, and no `u` with `a Rᵢ u ∧ b Rₘ u`)
   — consistent with it refuting the scheme. Whether the **555
   samval failure models** (the refutation of the same-trace
   no-descent repair) are confluent is the **decisive refilter
   experiment**: if all failures are non-confluent, the *original
   simple repair* returns to play over the confluent class.

**Honest costs.** (i) This proves a *different* theorem — UI for
PLL + distF ("confluent PLL"), not for PLL; Matthew has ruled the
restricted result still excellent, and its failure evidence against
the UI hypothesis. (ii) Interpolant *values* can shift in the stronger
logic; every value whose proof used a non-confluent construction must
be re-derived (audit item: `lobModel` for `∀p.◯(◯p⊃p) = ◯⊥`).
(iii) Every REFUTED-verdict resting on a non-confluent countermodel is
void in the restricted class and reverts to OPEN there. (iv) NOT
everything reopens: `chainF` (two-point chain, fallible top, trivial
rows — `Rₘ` reflexive-only) **is** mutually confluent (with `Rₘ` ⊆ the
identity the square closes trivially), so the §27 refutation of the
naive Litak–Visser Thm 4.7 form **survives** on the confluent class —
the fall-zigzag obstruction was about fallibility, not rows; the
escape-form redesign stays. (v) The belief-axis connection is real and
already in the draft (`strategy_dist_refuted`; the twenty-world
promise-machinery countermodel of the scheme, `belief-paper-draft.md`
≈338, ≈723).

**Oracle discipline for the extension.** Extension-derivability =
existing G4c search with the relevant `distF` instances added to `Γ`
(that is `DerivU` verbatim); countermodel certificates count only if
the emitted model passes the (decidable, O(n³)) `MutuallyConfluent`
check.

**Agent outcome (branch `ui-confluence`): died at the Fable credit
limit after producing the refilter/audit infrastructure but before the
theory recalibration.** Its committed refilter drivers had a
`main`-collision bug (imported the probe modules, which each declare
`main`) and never ran as committed; I salvaged them via its own
`main`-free `confl_core`, fixed the build globs, and ran everything
myself (2026-07-21 ≈14:00). Sanity passes reproduce the pinned numbers
EXACTLY (mforth 746,108 / 0 / 22,506; samval one-atom 2,377,307 /
499·44·12), validating the harness.

**RESULTS (my run; the theory task, ◯-cost-1 recalibration, remains
UNWRITTEN):**

* **Confluence ELIMINATES pillar 2's escape obstruction.** On the
  mutually confluent sub-battery the mforth sweep gives **0 forth-m
  candidates and 0 fallible-pair failures** (unrestricted: 22,506
  fallible-pair failures). The §30 witness `forkF` is NOT confluent —
  so `pair_escape_not_from_agreement` is **void in the extension**. The
  escape geography is a *fork* pathology, and confluence forbids forks.
* **Confluence does NOT dissolve the pillar-3 wall.** The same-trace
  no-descent failures, restricted to pairs of confluent models, are
  **324 / 44 / 12** (unrestricted 499 / 44 / 12) — the two deeper
  closures, including the **gap row `Sub(◯q⊃q)`, are 44/44 and 12/12
  preserved**. The decoded dead-end counterexample (`q ∧ ¬◯⊥`, a
  *chain*) is itself confluent. Chains are confluent; the wall is a
  chain phenomenon.
* **The known closed-fragment values TRANSFER.** Every fails-half
  certificate for `∀p.(p∨¬p)=⊥`, `∀p.(◯p⊃p)=⊥`, `∀p.◯(◯p⊃p)=◯⊥`, and
  the frontier `=◯⊥` is realised by a **confluent** countermodel
  (including a one-world model for the Löb fails-half); holds-halves
  derive in the extension. No value reopens.
* **Backward audit — only the forks are void.** Of the 11 default
  battery frames exactly one is non-confluent (`defaultFrames[8]`, the
  fork); of the named gadgets, only `modelOrSplit`, `forkF`, and the
  battery fork are non-confluent. `chainF` (the §27 naive-pillar-2
  refuter) and `chainFM` (the §30 weak-escape refuter) are **both
  confluent**, so those refutations SURVIVE — the escape-form redesign
  stays necessary even on the class.

**The clean diagnostic.** Confluence *separates* the two obstructions:
it removes the ∀∃/fork/row pathology (pillar 2's escape — gone) and
leaves the chain/dead-end pathology (pillar 3's wall — intact). The
wall was never about confluence. **Caveat that keeps this from being
evidence against UI:** the refilter tests the *old* same-trace repair;
the actual confluence lever — bare possibility, under which a world
refutes `◯χ` iff its *own row* misses `χ`, so promising-i-successors
(hence same-val-trace promise pairs) may not arise at all — was never
mechanised (task 3). Whether the wall's problematic *case* survives the
recalibration is a different question from whether the *old repair*
survives confluence, and only the latter is answered. **Next
concrete step (I can do this directly): write `crankC`/`LayeredBisimC`
and redo the `WitTriple` parity arithmetic under ◯-cost-1.** Salvaged
Lean (`wip/confl_core.lean`, `wip/confl_run.lean`, `wip/confl_audit.lean`,
lakefile globs) is staged, uncommitted, on `ui-confluence`.

## 10. Cross-route probe (v2quant): death and relaunch

The first run died at ≈08:00 when its host agent session ended (log
frozen at 62 lines, 4 of 10 battery formulas; no process). What it
established before dying, with the two-line fix demonstrably working:
dictionary = 15 classes (crank ≤ 9, 6 rounds); `∀p.◯p` and
`∀p.◯(◯p⊃p)` climb `⊥ → ◯⊥` at r = 2 with the climbs
**countermodel-certified** (the added F-free frames doing their job),
then frozen; `∃`-side `⊤` throughout for those rows. Relaunched
detached at 13:25 (same binary, fresh log `wip/v2quant_run2.txt`);
at 13:25 it was mid-dictionary (round 5). Still pending: the X9 row
(`¬◯⊥ ⊃ ◯p`), the match tests against the frozen dictionary, the
skip-count.

## 11. Matthew's question (d): must the proof ignore the derivation?

Two distinct layers, and the policy applies to only one of them.

* **The interpolant-as-object cannot be computed from a single
  derivation.** Uniformity means one `p`-free formula must serve
  *every* `p`-free partner `N` with `N ⊢ M` — infinitely many sequents
  with unrelated derivations. Maehara-style ordinary interpolation
  (Girard's "proof mutilation": transform the one given derivation,
  rule by rule, splitting the sequent) reads one derivation and serves
  one sequent. A uniform interpolant must exist before `N` is chosen.
* **But derivations are not banished — they move.** In Pitts's IPC
  proof (JSL 57, 1992) the quantifiers are defined by recursion over
  the *terminating backward proof-search space* of Dyckhoff's
  contraction-free calculus (G4ip/LJT), well-founded by a multiset
  order on sequents — morally, Maehara performed simultaneously over
  the whole search tree, which contains every derivation. And the
  correctness half (`N ⊢ M ⟹ N ⊢ ∀p.M`) **is** an induction on
  derivations in that calculus. Construction = recursion on the search
  space; verification = induction on derivations.
* **Our development mirrors this exactly.** Syntactic route:
  `itpA`/`itpE` recurse on (fuel, budget, context) over the G4c
  backward search — the PLL analogue of Pitts, with the budget as the
  termination finance. Inductions on derivations are everywhere they
  belong: `soundness_valid` (on `LaxND` derivations — the engine of
  every countermodel refutation), the G4 structural/cut files
  (`PLLG4HCut`/`HComp`), `search_sound`, the strong-normalisation
  development (`PLLTopTop`, on typing derivations). Semantic route:
  derivation-free by design — `IsSemAll`/`IsSemEx` are universal
  properties, the pillars quantify over models, and derivability
  enters only through the completeness bridge.
* **Where a derivation-sensitive idea could genuinely help:** the
  H1/H2 same-context budget regress is exactly a question of threading
  a well-founded measure through the search tree (the seen-set
  refinement — tracking which jump clauses a derivation actually
  uses). Matthew's instinct is not misguided; it is half-realised in
  the syntactic route already, and that regress is where the other
  half would land.
* **The underivable-input datum (why the object cannot see a
  derivation).** An interpolation problem's sequent need not be
  derivable: X9's `¬◯⊥ ⊢ ◯p` is *underivable* (one non-fallible world
  with `p` false refutes it), yet its ∀-interpolant is the contentful
  `◯(¬◯⊥ ⊃ ◯¬¬◯⊥)`. There is literally no derivation to mutilate, and
  the object exists anyway — derivation-independence of the *object* is
  forced by its type, not by policy.
* **The terminating-calculus corollary.** Pitts's method needs a
  terminating complete calculus; PLL currently has none (Iemhoff's
  G4iLL is machine-refuted incomplete in this repo). The budget `b` in
  `itpA`/`itpE` is a *surrogate* termination measure, and H1/H2 are
  the price of the surrogate. A repaired Dyckhoff-style terminating
  calculus for PLL would let Pitts's proof run essentially verbatim
  and dissolve H2 — the strongest sense in which "use derivations
  directly" could be decisive (this is the existing Thm 2.8 route).
* **A new candidate task from the question: H2 as derivation
  normalisation.** Stated proof-theoretically, H2 says every G4c
  derivation of `[itpE b] ⊢ itpE (b+1)` can be *mutilated* into one
  re-entering each budget-gated clause at most once per context (the
  seen-set bound as a normal-form theorem) — Girard-style mutilation
  aimed at exactly the open lemma, in the role cut-elimination plays
  for SN. Unexplored; speccable as a task on request.

## 12. Agent B's scaffold: verification status

**VERIFIED (2026-07-21 13:41), with Matthew's go-ahead.** Method: copy
of `wip/promise_pair_dev.lean` (commit `2e2b002`) elaborated in my own
worktree against the design agent's built cache (`lake --dir` — no
writes to their tree), with `#print axioms` appended for every
declaration. Verbatim results:

    'IsDeadEnd'                depends on: [propext, Quot.sound]
    'box_val_of_val'           depends on: [propext, Quot.sound]
    'deadend_box_in_val'       depends on: [propext, Quot.sound]
    'nondeadend_passup'        depends on: [propext, Classical.choice, Quot.sound]
    'deadend_wit_of_move'      depends on: [propext, Classical.choice, Quot.sound]
    'strict_wit_of_passup'     depends on: [propext, Classical.choice, Quot.sound]
    'deadend_pair_refutes_box' depends on: [propext, Classical.choice, Quot.sound]
    'wit_force''               depends on: [propext, sorryAx, Classical.choice, Quot.sound]
    'wit_pbisim''              depends on: [propext, sorryAx, Classical.choice, Quot.sound]
    'amalgamation_assembled''  depends on: [propext, sorryAx, Classical.choice, Quot.sound]

Exactly two `sorry` warnings (the theorem declarations at 343/356).
Conclusion: the agent's report was accurate — the six sub-lemmas are
PROVED with clean footprints (dead-end core choice-free), and the open
content is exactly the two deep claims. §6 of this report is upgraded
from "agent-reported" to "kernel-verified".
