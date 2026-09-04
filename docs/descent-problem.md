# The descent problem

*A self-contained statement of the single open lemma between this repository
and uniform interpolation for propositional lax logic, with every claim cited
to a machine-checked Lean name.  Written 30 July 2026 on branch
`ui-confluence`.*

Nothing below is asserted unless it is either (i) a definition, (ii) a
sorry-free Lean theorem, named, or (iii) explicitly labelled OPEN or a
measurement.  Measurements are labelled as such and are evidence, not proof.

---

## 1. What is being proved, and what the descent is for

Uniform interpolation for a logic `L` says: for every formula `φ` and variable
`p` there are `p`-free formulas `∃p.φ` and `∀p.φ` satisfying Pitts'
conditions — in particular

    φ ⊢ ∃p.φ ,       and     φ ⊢ ψ  ⟹  ∃p.φ ⊢ ψ   for `p`-free ψ,

and dually for `∀p`.  The decisive word is *uniform*: the interpolant must
depend on `φ` and `p` alone, not on the `ψ` it is later compared with, nor on
any ambient context.

The construction in this repository (`LaxLogic/PLLG4UITrunc.lean`) builds the
interpolants as explicit formulas by recursion on a **context** `Γ` inside a
finite **space** `S` of formulas closed under immediate subformulas:

    itpE p S fuel b Γ        the ∃-side table, a conjunction (`andAll`)
    itpA p S fuel b Γ C      the ∀-side table, a disjunction (`orAll`)

Two natural-number parameters bound the recursion.

* **fuel** bounds *context growth*.  Every clause that grows `Γ` recurses at
  `fuel − 1`.
* **budget** `b` bounds *same-context* recursion.  Exactly two context-formula
  shapes generate clauses that recurse at the same `Γ`, and those clauses are
  the only place `b` is read:

      (A ⊃ B) ⊃ D   with `B ⊃ D ∈ Γ`     the **jump** clause
      ◯A ⊃ B                             the **γ** clause

  Each is deleted when `b = 0` and otherwise produces one component at `b − 1`.
  Call these the **budget-gated** clauses.  Three goal-side clauses are gated
  in the same way (a `⊃`-goal with its antecedent already in `Γ`, a `◯`-goal,
  and the truncation disjunct).

Because the interpolant must not depend on the ambient context, the budget at
which it is *defined* is fixed by `φ` alone, while the budget at which
adequacy is *proved* depends on the whole surrounding sequent, and the latter
is unboundedly larger. Bridging that gap is exactly the descent.

> **The descent.**  For `fh ≤ fuel`,
>
>     Δ ⊢ itpE p S fuel (c+1) Γ        Δ ⊢ itpA p S fh (c+1) Γ g
>     ─────────────────────────────────────────────────────────────
>     Δ ⊢ itpA p S fuel c Γ g

Lowering the budget by one is harmless, financed by the ∃-side table at the
higher budget (the **ambient**).  Since `itpA` is a disjunction and lowering
`b` deletes disjuncts, the lower-budget table is the *stronger* formula; the
descent says it is no stronger, i.e. that the family has stabilised.

The *converse* direction is free and unconditional: `itp_budget_mono` and
`itp_budget_mono_le` in `LaxLogic/PLLG4UITrunc.lean`, sorry-free.

**Where the descent is consumed.**  `itp_stab` / `itp_stab_le`
(`wip/absorb_base.lean`) → `itp_adequate` (`wip/adequacy.lean`) →
`existsP_adequate` / `forallP_adequate` (`wip/packaging.lean`) →
`uniform_interpolation_PLL` (`wip/final.lean`).  The consumers quantify over
`b` above the threshold `kcap S < b`, and `itp_stab_le` walks the whole gap
one budget at a time, so no single fixed budget suffices.

**Current status of the crown theorems.**

| theorem | file | status |
|---|---|---|
| `uniform_interpolation_IPC` | `wip/final.lean` | **PROVED**, `[propext, Classical.choice, Quot.sound]` |
| `uniform_interpolation_PLL` | `wip/final.lean` | carries `sorryAx`, through one lemma |

The one lemma is `cascade_low_pos_box` (`wip/absorb_base.lean`), the descent
in the band where the space contains `◯`-formulas.  The `◯`-free case is
proved (`cascade_main_bf`), which is why the IPC specialisation is complete.

---

## 2. The two termination measures, and why the budget has no base case

`defect S Γ = |S ∖ Γ|` measures how much of the space is still outside the
context; context growth strictly decreases it (`defect_cons_lt`).

An exhaustive transcription of the clause tables gives:

> **Every budget-decrementing recursive reference sits at the same context,
> and every context-growing reference sits at the same budget.**

(The single apparent exception is the `⊃`-goal clause when its antecedent is
already in `Γ`; the context grows by a formula already present, so the defect
is unchanged — `defect_cons_eq`.)

Two consequences.

**The recursion terminates for free.**  Every recursive call drops the defect
at fixed budget or drops the budget at fixed defect, so the lexicographic pair
`(defect, budget)` strictly decreases.  No pigeonhole argument is needed for
*termination*.

**But the budget's base case is false.**  Two refutations, both sorry-free and
both in models that are mutually confluent *and* infallible — so they refute
PCLL, PILL and PICLL as well as plain PLL, and the obstruction is not an
artefact of fallible worlds or of the missing distribution scheme:

| statement | Lean name | file |
|---|---|---|
| the descent at target budget `1` is false | `not_roomFreeDescent` | `wip/ascRefute.lean` |
| the descent at target budget `0` is false | `not_floorDescent` | `wip/floorRefute.lean` |
| the ambient-relative ∃-ascent at budget `1` is false | `not_ambGuardAscent` | `wip/ascRefute.lean` |

The budget-`0` refutation needs no countermodel search: at the empty context
the environment table is empty, so at budget `0` a `◯`-goal's table is
*literally* `⊥` — both its goal clause and its truncation disjunct are gated
away (`itpA_starve_floor`, `wip/starve.lean`) — while the source table at
budget `1` is satisfiable.  The only semantic input is consistency.

So **raising the floor does not help**: a proof with a floor at `n` needs the
descent at `n − 1`, and `n − 1 ∈ {0, 1}` are both refuted.  A proof must
instead show that the low-budget instances *actually reached* are harmless.

---

## 3. Where the budget tier is entered

From the clause tables again: the only universal components at budget `b − 1`
anywhere are

    A@b'(Γ, A) ,     A@b'(Γ, A⊃B) ,     A@b'(Γ, ◯A)

from the two gated **environment** clauses.  Every other `b'`-reference is
existential.  The three goals occurring there are the **jump goals**

    jumpGoals S  =  { A⊃B : (A⊃B)⊃D ∈ S } ∪ { A, ◯A : ◯A⊃B ∈ S }.

So the budget tier is entered only at jump goals, and only one step at a time.

---

## 4. The goal side is settled

`wip/goalDesc.lean`, sorry-free.  Of the seven goal families, six close, and
none of them ever reaches budget `0`:

| goal `g` | gated | mechanism | Lean name |
|---|---|---|---|
| `prop q` | no | the source disjunct *is* the target disjunct | `desc_goal_atom` |
| `⊥` | no | no goal clause exists | — |
| `C₁ ∧ C₂` | no | descent at `C₁`, `C₂` | `desc_goal_and` |
| `C₁ ∨ C₂` | no | descent at `C₁` or `C₂` | `desc_goal_or` |
| `C₁ ⊃ C₂`, `C₁ ∈ Γ` | yes | ambient ⇒ guard, then descent at `C₂` | `desc_goal_imp_pres` |
| `◯D` | yes | `box_open`, ambient ⇒ guard, descent at `D` | `desc_goal_box` |
| `C₁ ⊃ C₂`, `C₁ ∉ Γ` | no | the ∃-ascent at a fresh antecedent | `desc_goal_imp_fresh`, on `FreshAntAscent` |

The reason the two gated rows cost nothing is worth isolating: **a gated
*goal* clause demotes only its existential component**, keeping the universal
one at `b`.  The demoted existential then comes from the ambient at budget
`c+1` by downward monotonicity, which is free (`ambE`, composing
`itp_fuel_mono`, `itp_budget_mono_le` and `itp_congr`).

Attribution: these six are already discharged inline inside `oth_descent`
(`wip/cascadeBox.lean`), and none of them consumes that file's four
interfaces.  What `wip/goalDesc.lean` adds is the public per-branch form, with
the bookkeeping exposed, which is what makes this table checkable.

**Consequence.**  The whole low-budget difficulty of the descent lives in the
*environment* clauses.

---

## 5. The environment side, above the floor

`wip/envDesc.lean`, sorry-free.  The two gated environment clauses contribute
disjuncts of the form (first component) ∧ (second component).  The second
component sits at the *grown* context and the same budget, so the defect tier
supplies it.  The three first components are:

| clause | target first component at budget `c+1` | Lean name |
|---|---|---|
| jump | `E@c(Γ) ⇢ A@c(Γ, A⊃B)` | `jump_of_desc` |
| γ, plain | `A@c(Γ, A)` | `gamma_plain_of_desc` |
| γ, boxed | `◯( E@c(Γ) ⇢ A@c(Γ, ◯A) )` | `gamma_boxed_of_desc` |

All three close, at every target budget `c + 1`, from the descent at the
corresponding jump goal at target budget `c` — bundled as `gated_env_first`.
The mechanism is again the ambient's slack:

> the ambient sits at budget `c + 2`, **two** above the component's budget, so
> downward existential monotonicity alone supplies the guard `E@(c+1)(Γ)`
> needed to fire the source.

In particular the ∃-*ascent* is consumed by none of the three, and the boxed
γ-component — the "γ-seal" that the residue analysis in
`wip/absorb_base.lean` lists as unreachable by the continuation machinery —
is reachable at every target budget `≥ 2`, via `box_remap_free` with the guard
from the ambient and the value from the descent one budget down.

---

## 6. What is left

Exactly one branch, at exactly one budget.

> **OPEN.**  The **boxed γ first component at target budget `1`**: derive
>
>     ◯( E@0(Γ) ⇢ A@0(Γ, ◯A) )
>
> from the ambient `E@2(Γ)`, the source's boxed component
> `◯( E@1(Γ) ⇢ A@1(Γ, ◯A) )`, and the grown value `A@1(B::Γ, C)`.

The matching route needs the descent to budget `0` at a boxed goal, which is
certified false.  So the branch must reach a *different* disjunct of the
target table, and the target table at budget `1` offers exactly three:

    (a)  A@0(Γ, A)  ∧  A@1(B::Γ, C)          the plain γ-disjunct
    (b)  ◯( E@0(Γ) ⇢ A@0(Γ, ◯A) )  ∧  A@1(B::Γ, C)
    (c)  the goal clause of `C`

and the second conjunct of (a) and (b) is a hypothesis.  So the branch closes
iff one of `A@0(Γ,A)`, the boxed component, or `C`'s goal clause is derivable
from the three hypotheses.

Two partial results.

* **When the boxed target starves** — `A@0(Γ,◯A) = ⊥`, which holds whenever
  the environment table starves at the floor (`itpA_starve_floor`) — route (b)
  reduces to deriving `◯⊥`, with no descent and no ascent:
  `boxed_target_of_starved`, `boxed_target_of_env_nil` (`wip/envDesc.lean`,
  sorry-free).
* On the chain family of `wip/budgetfit.lean` that demand is met:
  `A@1(Γ,◯p) ⊢ ◯⊥` is **PROVED** by search (`wip/sealprobe2.lean`), together
  with `A@0(Γ,◯p) = ⊥`, `A@0(Γ,p) = ⊥`, `E@0(Γ) = ⊤`.

  But this is **family-specific and must not be oversold**: it works because
  that family's γ-clause is `◯p ⊃ r`, whose head is the *eliminated variable*,
  and the goal clause of `p` is empty at every budget.  With a head `A ≠ p`,
  `A@0(Γ,A)` contains the disjunct `A` and is not starved
  (`wip/sealprobe3.lean` prints `A@0(Γ,r) = r ∨ ⊥`).  A general
  `A@b(Γ,◯D) ⊢ ◯⊥` is false outright: take `Γ = []`, `D = ⊤`.

**Measurements bearing on whether the branch is true.**  Countermodel-first,
`checkB`-certified failures only:

* the descent's failure boundary does **not** move with the size of the space:
  every certified failure is at budget `0` or `1`, across `◯`-gated chains of
  length 2, 3, 4, up to four live gates and defect 15 (`wip/ascprobe.lean`).
  The product law assumed by the tower would predict boundaries 63, 108, 165
  for those chains; the measurement is flat.
* the descent at atom jump goals is **proved by search at budget `0`**, at
  `findBudget` up to 200 000 (`wip/jumpprobe.lean`).  At boxed jump goals it is
  certified false at budget `0` and undecided at budget `1`.
* the whole boxed obligation is undecided by search at `findBudget` 200 000,
  while the plain one (`GammaPairFloorA`) comes out **PROVED** at atom and
  boxed goals `C` (`wip/sealprobe.lean`).  No countermodel has been found for
  the boxed obligation in any probed configuration, including with
  infallibility and mutual-confluence filters (`wip/sealprobe3.lean`).

So the branch is plausibly **true** and the obstruction is proof-theoretic.

---

## 6a. Update (later the same session): the floor, branch by branch

§6 above describes the position as of the middle of the session.  What followed
changed it, and this section supersedes §6's "exactly one branch" framing.

**The case analysis.**  No *uniform* route closes a floor branch — each of the
three target disjuncts it could aim at is individually underivable
(`wip/sealRefute.lean`, `not_uniformRouteA/B`, in infallible mutually confluent
models).  The replacement is a case analysis that costs nothing: the branch's
**second** hypothesis is itself a disjunction, so `orAll_elim` on it gives one case
per disjunct of the grown-context table, and different cases may reach different
target disjuncts.

    EnvDesc.branch_of_cases        -- sorry-free
    EnvDesc.branch_of_cases_nonbox

The earlier survey missed this because it looked at the source's *first*
component and at the target's disjuncts, never at the second.

**Atom goals, in general.**  At an atom goal `q ≠ p` over a `∨`-free space the
universal table *forces the atom*:

    AtomForce.itpA_atom_forces :
      (∀ A B, A.or B ∉ S) → q ≠ p → (∀ Y ∈ Γ, Y ∈ S) →
      G4c [itpA p S f b Γ (prop q)] (prop q)

at every fuel and every budget, by strong induction on the defect over all ten
environment clause shapes.  Every clause either produces nothing or produces a
disjunct with a conjunct `itpA p S f b Γ' (prop q)` at strictly smaller defect —
the sole exception being the `∨`-clause, whose disjunct is a conjunction of
*implications*.  Hence `AtomForce.floor_branch_atom`: **all three floor branches
close at an atom goal**, using neither the ambient nor the first component.

Atoms are special, not merely easier: `prop q` is a disjunct of the target at
*every* context, so a fact proved at the grown context lands where it is needed.
Every other goal shape's goal clause mentions the context.

**Instances closed.**  `BoxedBranchS1.boxed_branch` — the boxed floor branch at a
configuration whose γ-head is an ordinary atom, so the refutations bite and the
`◯⊥` collapse is unavailable.  `FloorImp.floor_branch_imp_S1/S2` — the
`⊃`-shaped floor branch.  `FreshAnt.*` — the fresh-antecedent goal branch,
including at a cell with the goal's consequent unrelated to the context, under
**exhaustive** search, and **without the existential ascent** that route was
thought to require.  All sorry-free, all `#pinsrc`-generated and re-checked.

**A methodological correction.**  An intermediate claim that no case reaches any
target disjunct at a boxed goal rested on cells run at `findBudget` 20 000 — and a
`~` at a bounded budget asserts nothing.  The fresh-antecedent branch needed
200 000 nodes to yield a 56-node derivation, so that comparison was invalid;
`wip/sealprobe12.lean` re-runs the boxed cells at 200 000 and 2 000 000.  A `~`
may only be compared with another `~`.

**Status of the two branches at budget `1`.**

| branch | status |
|---|---|
| floor, atom jump goal | **proved in general** (`∨`-free space) |
| floor, `⊃`-shaped jump goal | proved at two configurations |
| floor, boxed jump goal | OPEN; being re-measured at adequate budget |
| fresh-antecedent goal | proved at three configurations, without the ascent; general lemma OPEN |

## 6b. Update (§§97–105): the residue is no longer blocked anywhere

**The substantive discovery.**  The ambient `E@(c+2)(Γ)` is a *conjunction*, and for a
γ-clause `◯A ⊃ B ∈ Γ ∩ S` two of its conjuncts are

    A@(c+1)(Γ,A)                      ⇢  E@(c+2)(B::Γ)
    ◯( E@(c+1)(Γ) ⇢ A@(c+1)(Γ,◯A) )   ⇢  E@(c+2)(B::Γ)

whose antecedents are **exactly the two first components of the source's γ-disjuncts**.
So the branch can *fire* the ambient and obtain the **grown ambient** — precisely what
`AmbGuardAscent` was introduced to produce, with no ascent and nothing refuted
(`EnvDesc.grownAmb_of_box`, `grownAmb_of_plain`, sorry-free, general).  §5 above uses
the ambient only for weaker tables by downward monotonicity; this is the stronger use,
and the July survey missed it by asking what the branch could aim *at* and never what
the ambient could be fired *with*.

**The remap.**  `AtomForce.boxGoal_remap` (general): given the grown ambient, the boxed
goal clause at *any* `Γ'` remaps to the one at *any* `Γ`.  The value conversion is
context shrinking — unsound in general — and at an atom goal `itpA_atom_forces`
licenses it, because `prop q` is a disjunct of the target at every context.

**The grown ambient, shape by shape** (`wip/boxSnd.lean`, five lemmas, sorry-free):
`grown_and`, `grown_impAtom_pres`, `grown_impAnd`, `grown_impOr`, `grown_box`.  With
the two firing lemmas this covers every context shape, and the form always matches what
the corresponding `itpA` disjunct can use — unboxed where it is unboxed, **boxed** for
`◯χ` where the disjunct is boxed too.  Both tables come from the same clause analysis
of the context formula, so their guards and modal depth agree by construction.

*Do not* replace these by a uniform "ambient at any larger context follows from the
ambient": that is the existential ascent in pure context-growth form, and it is
refuted.

**The assembly.**  `BoxSnd.boxSnd_reaches` (sorry-free): the defect recursion over
`itpAfull p S f (c+1) Γ' (◯q)`, proving outright the goal clause (via `boxGoal_remap`),
the `∧` family, and the vacuous families, with four named obligations left —
`ImpCase` (the five `⊃`-headed families; grown ambients proved, guard bookkeeping
left), `BoxCtxCase` (`◯χ`, both sides boxed, pair under `laxL`), `TruncCase`
(open by `laxL`, legitimate since the conclusion is `◯`-shaped), `ZeroFuelCase`
(the fuel-`0` floor).  Also `tgtClause_fuel_lift`, whose two conversions are free in
opposite directions.

**Closed on-path instances**, sorry-free: `FloorImp.*` (`⊃`-shaped floor branch),
`FreshAnt.*` (fresh-antecedent branch, including the deciding cell, **without** the
ascent), `BoxedOnPath.boxed_onpath` (boxed floor branch at `C = ◯A`, the goal the
recursion reaches).

**Status.**

| branch, target budget `1` | status |
|---|---|
| floor, atom jump goal | **PROVED, general** (`∨`-free space) |
| floor, `⊃`-shaped jump goal | proved at two configurations |
| floor, boxed jump goal `◯A` | general theorem modulo four scoped case obligations; one closed on-path instance |
| fresh-antecedent goal | proved at three configurations incl. the deciding one |

Nothing in the descent is now known to be blocked.  What remains is generality and case
work, not an obstruction with refutations across it.

## 7. The budget law, as a parameter

Three fixed budget laws were assumed and refuted in July.  The statement now
carries the requirement as an unknown function

    Need := Finset PLLFormula → List PLLFormula → PLLFormula → Nat
    Descends p need  :=  the descent, with `need S Γ g ≤ c` as its hypothesis

(`wip/descent2.lean`), and every branch deposits a *law* that `need` must
satisfy, while every countermodel deposits a *lower bound*.  What is settled:

| fact | Lean name |
|---|---|
| every workable `need` asks `≥ 2` at the `ascRefute` configuration | `refutation_lower_bound` |
| every workable `need` asks `≥ 1` at a configuration with **no** gated pieces | `gate_free_lower_bound` |
| the truncation-pairing branch needs a floor of one at boxed goals | `NeedBoxFloor1`, `descends_of_othDescends_shape` |
| the gate-count law is dead, by the proof obligation and by data | `needGate_not_floor1`, `needGate_excluded` |
| the bare product law fails the floor at saturated contexts | `needProduct_not_floor1` |
| the **ledger** law is exactly what the tower's entry condition pays | `needKcap`, `needKcap_funded` |
| proving the parametric descent with the ledger law closes the tower's holdout | `ledgerDescent_of_othDescends` |

The last line is the reduction that matters: **the tower's remaining content is
the single proposition `OthDescends p needKcap`.**

The measured law is `needShape` — `0` at atoms and `⊥`, `1` at boxed goals, `2`
elsewhere — which satisfies the refined floor exactly (`needShape_boxFloor1`)
and survives both certified lower bounds with nothing to spare.

---

## 8. Vocabulary index

| term used here | standard reading |
|---|---|
| space `S` | a finite set of formulas closed under immediate subformulas |
| context `Γ` | the list of formulas the table recurses over |
| fuel | recursion bound on context growth |
| budget `b` | recursion bound on same-context recursion |
| budget-gated clause | a clause deleted at `b = 0`, recursing at `b − 1` |
| defect `defect S Γ` | `|S ∖ Γ|` |
| jump goal | a goal a budget-gated clause puts in first-component position |
| starved state | one whose clause list is empty, so the table is literally `⊥` |
| the ambient | the ∃-side table at the higher budget, financing the descent |
| the descent | budget stabilisation of the ∀-side table (§1) |
| the ∃-ascent | `E@c(Γ) ⊢ E@(c+1)(Γ)`, the hard direction for the ∃-side |
| room requirement `need` | the budget the descent needs at a configuration |
| the ledger | `\|jumpGoals S\| + 1 + defect S Γ · (\|jumpGoals S\| + 2)` |
