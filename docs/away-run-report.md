# Away-run report — 29 July to 2 August 2026

Matthew is away until Sunday 2 August, 12:00 BST, and asked for continuous
work with no check-ins.  This file is the running record: **plan, running
results, and the resume pointer** if the run is cut short.  It is written to
be read by someone who was not present.

Latest revision: see the dated sections; newest last.

**A note on the timestamps below.**  The section headings carry wall-clock
guesses made while working, and the early ones drifted: the run began at
**22:11 BST on 29 July** and the sections labelled "30 July, ~00:00" through
"~09:00" were in fact all written between 22:30 on 29 July and 00:00 on 30 July.
The *order* is right and the content is unaffected; only the clock times are
approximate.  The same caveat applies to the "(30 July)" dates on PROGRESS
§§83-91.

---

## 0. Where the work is

Two live threads, in two worktrees of `lax-logic-in-lean`:

| thread | worktree | branch | subject |
|---|---|---|---|
| **syntactic** | `.claude/worktrees/agent-a6d28ed6d9d9b868d` | `ui-confluence` | uniform interpolation for **plain PLL** via the truncated quantifier tables |
| **semantic** | `LaxLogic/.claude/worktrees/agitated-nobel-443fbd` | `claude/ui-proof-status-8a40d5` | the layered-bisimulation / amalgamation route |

The syntactic thread is the main line.  It is about **plain PLL** (`G4c`),
not PCLL.  PCLL, PILL and PICLL enter only as *scope*: refuting models that
are mutually confluent and infallible refute those systems too, so an
obstruction exhibited by such a model is not an artefact of plain PLL.

## 1. Vocabulary

Every term used below, in standard language.

* **quantifier tables.**  `itpE p S fuel b Γ` and `itpA p S fuel b Γ C`
  (`LaxLogic/PLLG4UITrunc.lean`) are formulas built by recursion on `Γ`;
  they are the candidate uniform interpolants.  `itpE` is a conjunction of
  clauses (`andAll`), `itpA` a disjunction (`orAll`).  `p` is the variable
  being eliminated, `S` a finite set of formulas closed under immediate
  subformulas ("piece-closed"), `Γ` the context.
* **fuel** `fuel` — the recursion bound on context growth.
* **budget** `b` — a *second* recursion bound, read at exactly two clause
  shapes: a context formula `(A⊃B)⊃D` and a context formula `◯A⊃B`.  Each
  of those clauses is deleted when `b = 0` and otherwise produces a
  component at `b−1`.  These are the **budget-gated** clauses.
* **starved.**  A state `(Γ, C, b)` is starved when the clause list of
  `itpA` is empty, so the table is *literally* `⊥` (`orAll [] = ⊥`).
* **defect** `defect S Γ = |S ∖ Γ|` — how much of the space is not yet in
  the context.  Context growth strictly decreases it.
* **jump goals** `jumpGoals S` — the goals a budget-gated clause can put in
  first-component position: `A⊃B` from `(A⊃B)⊃D ∈ S`, and `A`, `◯A` from
  `◯A⊃B ∈ S`.
* **the descent.**  The statement

      Δ ⊢ itpE p S fuel (c+1) Γ ,  Δ ⊢ itpA p S fh (c+1) Γ g
      ──────────────────────────────────────────────────────
      Δ ⊢ itpA p S fuel c Γ g                    (fh ≤ fuel)

  i.e. lowering the budget by one is harmless, financed by the existential
  table at the higher budget.  Lower budget means fewer disjuncts, hence a
  *stronger* formula, so the descent is a stabilisation statement.
* **room requirement** `need : Finset PLLFormula → List PLLFormula →
  PLLFormula → Nat` — the budget the descent needs at a configuration.
  `Descends p need` (`wip/descent2.lean`) is the descent with `need S Γ g ≤ c`
  as its budget hypothesis.  It is a *parameter*: three fixed budget laws
  were refuted in July, so the law is now solved for rather than guessed.

## 2. Status at the start of the run (29 July, 22:00 BST)

PROVED, sorry-free and axiom-pinned:

* `descends_of_othDescends` — the descent follows from the others-descent
  for any `need` with a floor of one (`wip/descent2.lean`).
* `not_ambGuardAscent`, `not_roomFreeDescent` — two of the four interfaces
  `wip/cascadeBox.lean` reduces to are false; both refuting models are
  mutually confluent and infallible, so the refutations reach PCLL, PILL
  and PICLL (`wip/ascRefute.lean`).
* `refutation_lower_bound` — every workable `need` asks ≥ 2 at the
  refuting configuration.

OPEN: `cascade_low_pos_box` (`wip/absorb_base.lean`) — the tower's only
`sorry`, and the last thing between the repo and `uniform_interpolation_PLL`.

## 3. Plan as of 29 July 22:00

**Phase A** — bracket the budget law from above, and settle whether the
`cascadeBox` architecture can be repaired at all.
**Phase B** — the branch-by-branch rebuild, countermodel search *before*
every proof attempt.
**Phase C** — solve the accumulated laws, wire into the tower.
**Phase D** — audit, scope transfer to PCLL/PILL/PICLL, then the semantic
thread.

Stall rule: no branch gets more than about four hours without movement.

---

## 4. Result 1 (30 July, ~00:00) — the budget tier has no base case

`wip/floorRefute.lean`, PROVED sorry-free, `[propext, Quot.sound]`.

**`not_floorDescent`: the descent at target budget `0` is FALSE.**  At

    S = {◯(⊥⊃⊥), ⊥⊃⊥, ⊥},   Γ = [],   g = ◯(⊥⊃⊥) ∈ S

the target table is *literally* `⊥` — at the empty context the environment
table is empty, and at budget `0` both the `◯`-goal clause and the
truncation disjunct are budget-gated away (`itpA_starve_floor`, already in
`wip/starve.lean`).  The source table at budget `1` is satisfiable.  So the
descent would derive `⊥` from consistent hypotheses.  **No countermodel
search was needed**: the only semantic input is that the two hypotheses are
jointly consistent, checked in the one-world model.

**Why this reshapes the plan.**  `wip/cascadeBox.lean`'s `oth_descent` is a
three-tier induction: strong induction on the defect, then strong induction
on the budget `c` (carrying `1 ≤ c`), then structural induction on the
source fuel.  Its three "floor" interfaces exist because the middle tier has
no recursive call at `c = 1`: a budget-gated clause of the *target* table at
budget `c` puts its first component at `c−1`, so that branch needs the
descent at `(c → c−1)`, and at `c = 1` that is the descent to budget `0`.

Now both of the bottom two rungs are refuted:

* target budget `0` — false (this result);
* target budget `1` — false (`wip/ascRefute.lean` §2).

So **raising the floor does not give the budget tier a base case.**  A floor
at `n` needs the descent at `n−1`; `n = 1` and `n = 2` are both closed off
by countermodel, and there is no reason to expect `n = 3` to behave
differently, because the obstruction is the *shape* of the gated clause and
not the numeral.  The recursion has to terminate on some other measure:
context growth (defect), or the pigeonhole over `jumpGoals S` that
`wip/absorb_base.lean`'s `cascade_main` already implements.

**Consequence for the rebuild.**  `oth_descent`'s architecture is not
repairable by choosing a better constant.  The parametrised `Descends need`
statement stands (it is the target either way), but the *proof* must come
from the defect/pigeonhole side, not the budget side.

**A second lower bound on `need`, and candidate B dead twice over.**  The
same configuration is an instance of `Descends` at target budget `0`, so it
forces `1 ≤ need S [] g` at a space whose **gated-piece count is zero**.
The gate-count candidate `needGate` asks for `0` there, so it is refuted by
data (`needGate_excluded`), not only by the proof obligation
`NeedFloor1` (`needGate_not_floor1`).  The earlier elimination used the
empty space and could be dismissed as degenerate; this space is piece-closed
with a genuine `◯`-goal.

**Resume here:** the next step is *not* to continue rebuilding
`wip/cascadeBox.lean`.  It is to build the starvation classification that
`cascade_low_pos_box`'s own failure analysis names as step one — which
`(Γ, g, b)` starve — and from it a `(defect, budget)`-lexicographic landing
map for the residue.  `wip/starve.lean` has the first four bricks.

---

## 5. Result 2 (30 July, ~01:00) — completeness is available, and does not shortcut this

Worth recording so a later session does not spend days on it.

`LaxLogic/PLLCompleteness.lean` proves `consequence_iff_derivable : Γ ⊨- φ ↔
Nonempty (LaxND Γ φ)` — full soundness **and** completeness for the
Fairtlough–Mendler constraint semantics, sorry-free, over `Γ` a list.  With
`G4c.equiv_nd` this means *any* sequent about the quantifier tables could in
principle be proved semantically instead of by building a derivation.  That
is attractive because the descent's known obstruction is a proof-engineering
one (continuations cannot cross a `◯`-introduction), and semantics has no
continuations.

It does not work, for a reason worth stating.  Semantically, the descent says
a monotone iteration has reached its fixed point by step `c`.  The iteration
is over *hereditary* sets of worlds, and the recursive references in the
tables sit under `⊃` and `◯`, so they are evaluated at other worlds: the
state is a function on worlds, not a finite vector, and a monotone iteration
in that lattice has no finite bound.  The syntactic pigeonhole works because
it counts *goals* visited in a derivation, and goals live in the finite set
`jumpGoals S`.  So completeness is a genuine escape hatch for individual
sequents but not for the general statement.

## 6. Result 3 (30 July, ~02:00) — the boundary does not climb; one statement left

Full detail in PROGRESS §84.  Headline: `wip/ascprobe.lean` measures the
*ambient-relative existential ascent* (never probed before) at every position
along `◯`-gated chains of length 2, 3, 4, and the descent at *jump goals*.
Every `checkB`-certified failure is at budget `0` or `1`; there is not one
certified failure at budget `≥ 2` anywhere, up to four live gates and defect
15.  The assumed product law would predict boundaries 63, 108, 165 for those
three chains; the measurement is flat.  So the room requirement is not a size
measure.

Also landed: `needKcap`, the **ledger law** — exactly what the tower's entry
condition `kcap S < c + 2` pays, with `kcap_room` reproved locally — and

    ledgerDescent_of_othDescends : OthDescends p needKcap → LedgerDescent p S

where `LedgerDescent` is `cascade_low_pos_box`'s statement.  The tower's
holdout is now **one named proposition**.

## 7. Result 4 (30 July, ~03:00) — the goal side closes; the residue is two branches

Full detail in PROGRESS §85.

An exhaustive transcription of the clause tables gives a structural fact:
**every budget-decrementing reference sits at the same context, and every
context-growing reference sits at the same budget.**  So the recursion is
well-founded on the lexicographic pair `(defect, budget)` with no pigeonhole
at all — the seen-set machinery of `cascade_main` is there to avoid the
*false* budget-`0` base case, not to make the recursion stop.  And the budget
tier is entered only at **jump goals**, one step at a time.

`wip/goalDesc.lean` then settles the goal side: six of the seven goal
families close, because a budget-gated *goal* clause demotes only its
existential component, and the ambient supplies that free by downward
monotonicity.  No goal branch ever touches budget `0`.  The seventh — the
fresh antecedent — needs the ascent, isolated as `FreshAntAscent`.

Consequently the entire low-budget difficulty lives in the **environment**
clauses, and precisely two branches remain, both at target budget `1`:

1. the γ-clause's **boxed** disjunct, which would need the descent to budget
   `0` at a boxed goal — certified false as a plain statement, so it must be
   routed through a different target disjunct;
2. the **fresh-antecedent ascent at budget `1`** — refuted, so that branch
   needs its own floor treatment.

The other two of `oth_descent`'s four interfaces now look reachable: the atom
jump goal at budget `0` is *proved by search* (`wip/jumpprobe.lean`, at
`findBudget` up to 200 000, for chain2 and chain3), and the `⊃` case is open
but unrefuted.

Also: the floor law `NeedFloor1` was too strong.  It is used only for the
truncation disjunct, which exists only at `◯`-goals, so
`GoalDesc.desc_of_oth_nonbox` weakens it to `NeedBoxFloor1` — a floor at
boxed goals only.  That is what admits `needShape`, the goal-shape law the
measurement points to (`0` at atoms, `1` at boxed goals, `2` elsewhere),
which survives both certified lower bounds exactly.

**Resume here:** `wip/sealprobe.lean` hands the two blocked branch
obligations to the two-sided oracle as ordinary sequents (with the defect
tier's contribution pre-applied), for chain2 and chain3 and four goal shapes.
A `PROVED` there is a blueprint for the Lean proof; a `REFUTED!` says the
interface is individually false and the branch needs the full recursive
hypothesis rather than the pre-applied form.  Output goes to
`wip/sealprobe_out.txt`.

## 8. Result 5 (30 July, ~06:00) — no uniform route closes the last branch

Full detail in PROGRESS §87; the standing technical statement is
`docs/descent-problem.md`.

§86 reduced the descent to one branch at one budget: the **boxed γ-disjunct of
the environment table at target budget 1**.  At that point the target table
offers exactly three kinds of disjunct, and the branch's third hypothesis is
already the second conjunct of two of them, so the branch closes iff one of

    (a)  A@0(Γ, A)                      (b)  ◯( E@0(Γ) ⇢ A@0(Γ, ◯A) )
    (c)  the goal clause of C

is derivable from the three hypotheses.  That is a finite question about three
*small* sequents rather than one large one — and the oracle answers it.

**All three are individually false** (`wip/sealRefute.lean`, sorry-free), at a
configuration whose γ-head is an ordinary atom rather than the eliminated
variable, with both refuting models **infallible and mutually confluent** — so
the refutations reach PCLL, PILL and PICLL:

    not_route_a ,  not_route_b ,  not_route_bot
    not_uniformRouteA ,  not_uniformRouteB

So the branch **cannot be closed by a uniform route; it needs a case analysis
over the target's disjuncts.**  This is the explanation of the July record:
every mechanism surveyed there — remap, seal-crossing, collapse — is a uniform
route, and each therefore had to fail.  It also explains why no countermodel to
the branch obligation *itself* has been found in any probed configuration: in
each of the three refuting models a **different** route succeeds, so the
obligation is plausibly true while every one-move proof of it is impossible.

One caveat, stated because it bounds the result: the three hypotheses used are
the ambient, the source's boxed component, and the defect tier's contribution
*pre-applied* as `A@1(B::Γ,C)`.  The real interface hands over the recursive
hypothesis rather than one instance of it.  The enumeration of *which target
disjunct* is complete either way (it is read off the clause table); what the
pre-applied form bounds is the *material* available to reach it.

## 9. Where the whole problem now stands

Combining the run's measurements, the financing of the descent's recursion is
complete except at one point:

| what the recursion needs | budget | status |
|---|---|---|
| goal-side branches | any | **proved** (`wip/goalDesc.lean`), never reach budget 0 |
| the three gated environment first components | target ≥ 2 | **proved** (`wip/envDesc.lean`) |
| descent at **atom** jump goals | 0 | **proved by search** (`wip/jumpprobe.lean`) |
| descent at **`⊃`-shaped** jump goals | 0 | **proved by search** (chainII1) |
| descent at **boxed** jump goals | 0 | **certified false** |
| the ∃-ascent at a fresh antecedent | ≥ 2 | no certified failure in any probed configuration |
| the ∃-ascent at a fresh antecedent | 1 | **certified false** |

So **everything reduces to budget-1 phenomena**, and exactly two branches
remain there: the boxed γ-disjunct (uniform routes all refuted, obligation
plausibly true) and the fresh-antecedent ascent (refuted in its uniform form).

That is a considerably sharper position than the run began in, where the
statement of record was "four jointly unsatisfiable interfaces" with no
localisation and a budget law that had been guessed three times and refuted
three times.

**Resume here:** two options, in order of expected value.
1. Prove the ∃-ascent at budget `≥ 2`, conditional on the jump-goal descents.
   That would let the descent be assembled above budget 1, making "budget 1 is
   the entire residue" a theorem rather than an analysis.  Mechanical but
   large: the existential clause table has eleven shapes, of which nine are
   ungated and reduce to the defect tier.
2. Build the case analysis for the boxed γ-branch at budget 1.  The three
   refuting models of `wip/sealRefute.lean` say what the cases must
   distinguish; turning that into a *decidable syntactic* case split is the
   open problem.

## 10. Result 6 (30 July, ~09:00) — the residual branch, closed at one configuration

Full detail in PROGRESS §§89–90.

Two things landed.

**`#pinsrc`** (`LaxLogic/PLLSearchPin.lean`, documented as `docs/search-manual.md`
§10).  The oracle's refutations were always theorems; its *proofs* were only
probe output, because `Verdict.proved` carries a typed `G4cTm` that had no way
into a source file.  `#pinsrc` prints it as Lean source, emitting **no
formulas** — every index is recovered by unification, each side formula from a
membership chain at a computed position in `Γ` — so the output is proportional to
the derivation, not to the tables.  Five facts are now theorems instead of
evidence, including the descent to budget `0` at both non-boxed jump-goal shapes.
That makes the localisation of §§86–87 rest on theorems rather than on how hard a
search was pushed.

**The residual branch closed at one configuration.**  §87 refuted every uniform
route.  The case analysis that must replace one was available for nothing, and
the earlier survey missed it because it looked at the source's *first* component
and at the target's disjuncts: the branch's **second** hypothesis is itself a
disjunction, so `orAll_elim` on it is a case analysis with one case per disjunct
of the grown-context table, and different cases may reach different target
disjuncts. `EnvDesc.branch_of_cases` is that reduction, and

    BoxedBranchS1.boxed_branch : G4c [amb, box, snd] (orAll (itpAoth …))

closes the branch at `S = {◯r ⊃ s, ◯r, r, s, z}`, `Γ = [◯r ⊃ s]`, `A = r`,
`B = s`, `C = z` — γ-head an ordinary atom, so §87's refutations bite and §86's
`◯⊥` collapse is unavailable.  **The branch that was the residue closes in the
case its refutations single out.**

And the split is not a formality: on that configuration the whole obligation is
search-truncated at 40 000 nodes, every uniform route is refuted, and the single
case is proved in **two**.

**What remains for the general lemma.**  A route per disjunct shape of the
grown-context table.  On a configuration whose *grown* context still has a live
clause there are three cases; the first (the goal clause) is proved, the second
is undecided at 40 000 nodes.  The natural continuation is that the analysis
**recurses**: each case either forces `C`'s goal clause or hands back a second
component at a strictly larger context, so the recursion is on the defect and
bottoms out when the context saturates and the environment table empties.  That
works cleanly for atom goals over `∨`-free contexts; the `∨` environment clause
produces a conjunction of *implications*, whose consequents cannot be extracted
without their guards, and is the next thing to settle.

**Resume here:** push the undecided second case of the two-γ-clause
configuration (`wip/sealprobe6.lean`, `S2`, case 1, weight 8) at a much larger
`findBudget`, and if it is provable, pin it and read off the route.  Then
enumerate the disjunct shapes of `itpAfull p S F 1 (B::Γ) C` and assign a route
to each, which is a finite obligation of the same kind as the goal-side table of
§85.

---

# CONSOLIDATED STATE — read this section first

*Rewritten after §99.  Supersedes everything above, including an earlier version
of this section.  Every claim below is either a sorry-free Lean theorem, named, or
explicitly labelled REFUTED, OPEN or a measurement.*

## 1. The one open lemma

`uniform_interpolation_IPC` is **proved**, sorry-free.
`uniform_interpolation_PLL` carries `sorryAx` through exactly one lemma:
`cascade_low_pos_box` (`wip/absorb_base.lean:2273`), the **descent** —

    Δ ⊢ itpE p S fuel (c+1) Γ ,  Δ ⊢ itpA p S fh (c+1) Γ g
    ─────────────────────────────────────────────────────────
    Δ ⊢ itpA p S fuel c Γ g                        (fh ≤ fuel)

"lowering the budget by one is harmless, financed by the existential table at the
higher budget".  It is what makes the interpolant independent of the ambient
context, so it cannot be dodged.

## 2. What is settled

**Refuted** (all in infallible, mutually confluent models, so they reach PCLL,
PILL and PICLL too):

| statement | name |
|---|---|
| the descent at target budget `0` | `not_floorDescent` |
| the descent at target budget `1`, general goal | `not_roomFreeDescent` |
| the ∃-ascent at budget `1` | `not_ambGuardAscent` |
| each of the three *uniform* routes for a floor branch | `not_uniformRouteA/B`, `not_route_bot` |

**Proved** (sorry-free):

| result | name |
|---|---|
| goal side, six of seven families; none reaches budget `0` | `wip/goalDesc.lean` |
| the truncation wrapper needs no budget floor at non-boxed goals | `desc_of_oth_nonbox` |
| the three gated environment components at target budget ≥ 2 | `gated_env_first` |
| the case analysis on the second component | `branch_of_cases` |
| **the table at an atom goal forces the atom** (`∨`-free space) | `itpA_atom_forces` |
| hence all three floor branches close at an atom goal, in general | `floor_branch_atom` |
| **the ambient plus either γ first component yields the grown ambient** | `grownAmb_of_box`, `grownAmb_of_plain` |
| the reduction of the tower's holdout to one proposition | `ledgerDescent_of_othDescends` |
| instances: `⊃`-shaped floor branch; fresh-antecedent branch (incl. the deciding cell, without the ascent); boxed branch at `C = ◯B` | `wip/floorImp.lean`, `wip/freshAnt.lean`, `wip/boxedS1b.lean` |

## 3. What is open

The budget tier of the descent is entered only at **jump goals**, one step at a
time, and jump goals have three shapes: `A`, `◯A`, `A ⊃ B`.  So the descent
reduces to the floor branches at those, plus the goal-side fresh-antecedent
family.  Status:

| branch, at target budget `1` | status |
|---|---|
| floor, **atom** jump goal | **PROVED, general** (`∨`-free space) |
| floor, **`⊃`-shaped** jump goal | proved at two configurations; general lemma OPEN |
| floor, **boxed** jump goal `◯A` | **OPEN**; goal clause is the only surviving target disjunct (the other two are refuted) |
| fresh-antecedent goal clause | proved at three configurations incl. the deciding one, without the ascent; general lemma OPEN |

Above budget `1` none of these arises: the gated components have the ambient two
budgets up, and the ∃-ascent has no certified failure at `c ≥ 2` in any probed
configuration.

## 4. The two substantive discoveries

**(a) At an atom goal the table forces the atom.**  For `q ≠ p` over a `∨`-free
space, `itpA p S f b Γ (prop q) ⊢ prop q`, at every fuel and budget, by strong
induction on the defect over all ten environment clause shapes.  Atoms are special
rather than merely easier: `prop q` is a disjunct of the target at *every* context,
so a fact proved at a grown context lands where it is needed.  Every other goal
shape's goal clause mentions the context.

**(b) The ambient supplies implications whose antecedents the branch already has.**
The ambient `E@(c+2)(Γ)` is a conjunction, and for a γ-clause `◯A ⊃ B ∈ Γ ∩ S` two
of its conjuncts are `A@(c+1)(Γ,A) ⇢ E@(c+2)(B::Γ)` and
`◯(E@(c+1)(Γ) ⇢ A@(c+1)(Γ,◯A)) ⇢ E@(c+2)(B::Γ)` — whose antecedents are exactly the
two first components of the source's γ-disjuncts.  So the branch can *fire* the
ambient and obtain the **grown ambient**, which is precisely what
`AmbGuardAscent` was introduced to produce, with no ascent and nothing refuted.
The July survey missed this because it asked what the branch could aim **at**, never
what the ambient could be fired **with**.

## 5. Two mistakes made and corrected in this session

Recorded because they bear on how the evidence should be read.

* **§96.**  §§92–93 concluded that at a boxed goal no case reaches any target
  disjunct, from cells run at `findBudget` 20 000.  A `~` at a bounded budget
  asserts nothing, and the fresh-antecedent branch later needed 200 000 nodes to
  yield a 56-node proof.  Rule: a `~` may be compared only with another `~`.
* **§99.**  §97 closed the boxed branch at `C = ◯s`, i.e. `◯B` where `B` is the
  γ-clause's consequent.  The recursion only ever reaches `A` and `◯A`, so that
  instance is off the path.  The theorem is true and was the worked example that
  produced discovery (b); it is not an instance of the residue.

## 6. New tooling

`#pinsrc` (`LaxLogic/PLLSearchPin.lean`, manual §10) turns a search-found proof
into a kernel-checked theorem, printing the derivation with **no formulas** in it,
so the output is proportional to the derivation and not to the tables.  Seven facts
in this session moved from probe output to theorem.  This completes the
discover-then-pin pipeline: probe → `#pinsrc` → generated source → kernel, with
nothing about the search trusted at the end.

## 7. Dead ends, so they are not retried

* **Completeness for the constraint semantics** is available and sorry-free but does
  not shortcut the descent: the semantic iteration is over hereditary sets of
  *worlds* and has no finite bound, whereas the syntactic pigeonhole counts goals in
  the finite `jumpGoals S`.
* **Raising the budget floor** cannot give the budget tier a base case; both bottom
  rungs are refuted and the obstruction is the clause shape, not the numeral.
* **`itpE` budget-independence for gate-free spaces** is false: `itpE`'s ungated
  clauses reference `itpA`, whose goal-side gating carries no `∈ S` condition.
* **The `◯⊥` collapse** closes a floor branch only when the γ-head is the eliminated
  variable.

---

# SESSION LEDGER

39 commits, 48 files, ~6 500 lines added.  `lake build LaxLogic wipshared` is clean and
reports `sorry` only in files that carried one before the session.  Every new file is
sorry-free and every `#guard_msgs` axiom audit passes as written.

## New Lean, by file

| file | contents |
|---|---|
| `LaxLogic/PLLSearchPin.lean` | `#pinsrc` — turns a search-found proof into a kernel-checked theorem |
| `wip/floorRefute.lean` | the descent at budget `0` is **false**; a second lower bound on the budget law |
| `wip/goalDesc.lean` | the goal side of the descent, six of seven families; `desc_of_oth_nonbox` |
| `wip/envDesc.lean` | the three gated environment components above the floor; `branch_of_cases`; **`grownAmb_of_box` / `grownAmb_of_plain`** |
| `wip/sealRefute.lean` | all three *uniform* routes for a floor branch are **false**, in infallible mutually confluent models |
| `wip/atomForce.lean` | **`itpA_atom_forces`**, `floor_branch_atom`, **`boxGoal_remap`** |
| `wip/boxSnd.lean` | the five shape-by-shape grown-ambient lemmas; `tgtClause_fuel_lift`; **`boxSnd_reaches`** |
| `wip/jumpPinned.lean`, `wip/pinnedFacts.lean` | five facts promoted from probe output to theorem |
| `wip/boxedS1b.lean`, `wip/boxedOnPath.lean`, `wip/floorImp.lean`, `wip/freshAnt.lean` | closed instances of all four branch shapes |
| `wip/descent2.lean` (extended) | `needKcap` + `needKcap_funded`; `NeedBoxFloor1`; **`ledgerDescent_of_othDescends`** |

Probe executables added: `ascprobe`, `jumpprobe`, `sealprobe`…`sealprobe13` — thirteen
in all, with their outputs committed next to them.

## Documentation

* `docs/descent-problem.md` — the standing technical statement, every claim cited to a
  Lean name (§§6a, 6b bring it to the end of the session).
* `docs/search-manual.md` §10 — `#pinsrc`.
* `PROGRESS.md` §§83–105 — the narrative, including §96 and §99, the two corrections.
* `docs/away-run-report.md` — this file; read **CONSOLIDATED STATE** first.

## Where to pick up

In order of expected value:

1. **Discharge `boxSnd_reaches`'s four obligations** (`ImpCase`, `BoxCtxCase`,
   `TruncCase`, `ZeroFuelCase`).  All four are case analyses over a finite clause table
   with every mathematical ingredient already proved; none is refuted.  Two attempts at
   `ZeroFuelCase` failed on *tactic* mechanics, and PROGRESS §105's addendum records
   exactly how — the `.prop` guard must be killed by `simp` before the case split, and
   `first` alternatives must be ordered so only-succeed-if-applicable ones come first
   with a *tactic* catch-all.  Writing one small lemma per shape (as `wip/boxSnd.lean`'s
   `grown_*` do — those compiled first try) is the pattern that works.
2. **Generalise the `⊃`-shaped floor branch and the fresh-antecedent branch**, each
   currently a finite set of closed instances.  For the latter, note the pinned 56-node
   derivation takes the introduced guard *apart* by cases rather than strengthening it —
   that is what to generalise.
3. **The `∨`-free restriction** on `itpA_atom_forces`.  The `∨` environment clause is
   the one shape whose disjunct is a conjunction of *implications*, so the induction
   cannot project through it.  Whether the ambient can fire those implications the way
   §98 fires the γ-conjunct is the natural question, and it has not been looked at.

## One methodological note worth carrying forward

Three of this session's results were obtained by the same move: **find the smallest
hypothesis set that makes a cell searchable, pin that with `#pinsrc`, and compose the
rest in Lean.**  Adding *derivable* hypotheses cannot change derivability but does widen
the search — `[amb, box, snd, s] ⊢ target` is not found at 200 000 nodes while
`[snd, s] ⊢ target` is found in 36.  So the searcher is best used on minimal cells, not
on the obligation as stated.

---

# LEDGER UPDATE (§§106–109)

Four more results after the ledger above was written, all in `wip/boxSnd.lean`, all
sorry-free.

* **`zeroFuelCase` discharged** — `boxSnd_reaches` needs **three** hypotheses, not four.
* **`shift_imp` / `shift_box` / `shift_plain`** — a gated disjunct carries its first
  component one budget below what the ambient's conjunct demands, and the shift is free
  (up on the universal side, down on the existential).  Composed with §98:
  `grownAmb_of_box_shifted`, `grownAmb_of_plain_shifted`.
* **`grown_impAtom_fresh`** — the last row of the grown-ambient table.  Every context
  shape now has its grown ambient in the form its own `itpA` disjunct can use, and in
  every case what fires it is something the branch already has.
* **A correction (§108).**  `ImpCase` and `BoxCtxCase` were stated in §105 with no
  recursion and were therefore *unprovable*, not merely hard — both are steps of the
  defect recursion.  Both now carry it.  And this isolated a real structural difference:
  `TruncCase` is **not** a step of the defect recursion (its body is `⋁ others` at the
  *same* context), so it needs either its own measure or the pairing move `desc_of_oth`
  uses for the truncation.  That is the only remaining obligation whose *shape* is
  unsettled.

## Two tactic lessons, recorded because they cost real time

* **Count the splits with the actual budget expression in hand.**  When the budget is a
  literal successor (`c+1`), `split` does *not* branch on a gated clause's
  `match b with | 0 | b'+1` — it reduces.  So a gated shape has **one fewer** `split`
  than the same shape has when the budget is a variable.  A miscount surfaces as a type
  mismatch deep inside a `rcases`, which is what made two attempts look like tactic
  problems when they were arithmetic.
* `first | t₁ | t₂` does not reliably skip an alternative whose *elaboration* fails.
  Order alternatives so the only-succeed-if-applicable ones come first, and make the
  catch-all a tactic (`cases h`) rather than a term (`h.elim`).

## Standing status

| branch, target budget `1` | status |
|---|---|
| floor, atom jump goal | **PROVED, general** (`∨`-free space) |
| floor, `⊃`-shaped jump goal | proved at two configurations |
| floor, boxed jump goal `◯A` | general theorem modulo **three** obligations, two of them ordinary case analyses with every ingredient proved, one (`TruncCase`) needing a measure or a pairing move; one closed on-path instance |
| fresh-antecedent goal | proved at three configurations incl. the deciding one |

---

# FINAL STATUS (§§110–112)

`zeroFuelCase` and `boxCtxCase` are **discharged**, and `ImpCase`'s six shapes are proved
as lemmas.  So `BoxSnd.boxSnd_reaches` — the general boxed-goal traversal — now rests on
**two** hypotheses:

* **`ImpCase`** — pure *routing*: unpack the clause guards and dispatch to one of the six
  lemmas (`impAnd_case`, `impOr_case`, `impAtom_pres_case`, `impAtom_fresh_case`,
  `gammaBox_case`, `gammaPlain_case`).  No mathematics left.
* **`TruncCase`** — the one open *question*.  The truncation disjunct's body is
  `⋁ others` at the **same** context, so it is not a step of the defect recursion and
  needs either its own measure or the pairing move `desc_of_oth` uses for the truncation
  in the full-table descent.

Everything else in the boxed row is proved: the traversal, its goal-clause case
(`boxGoal_remap`), its `∧` case, its fuel-`0` floor, the complete grown-ambient table
(seven shapes), the three free budget shifts, and `tgtClause_fuel_lift`.

## The most useful thing this session learned about *how* to work on this

Three obligations in a row turned out to be **statement** problems, not proof problems: a
miscounted `split` (§106), a missing context quantifier (§111), a missing recursion
hypothesis (§108).  Each looked like a hard proof until the statement was right, and then
went through in a few lines or first try.  Before hunting for a measure for `TruncCase`,
check that what is being asked for is what the traversal can supply.

The same lesson in the measurement register: a `~` from the oracle at a bounded budget
asserts nothing, and comparing one against a `PROVED` found at the same budget produced
§92's wrong conclusion (§96 retracts it).  And `[amb, box, snd, s] ⊢ target` is not found
at 200 000 nodes while `[snd, s] ⊢ target` is found in 36 — so pin the *minimal* searchable
cell and compose the rest in Lean.

## State of the tree

`lake build LaxLogic wipshared` clean; **zero** `sorry` in all fourteen files this session
created or extended; every `#guard_msgs` axiom audit passes as written; working tree clean;
everything pushed to `origin/ui-confluence`.
