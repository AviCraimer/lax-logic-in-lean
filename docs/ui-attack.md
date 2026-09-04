# The UI attack: goal, method, objects, status

*2026-08-03.  Fixes the names and the architecture of the campaign to
prove that uniform interpolation fails for PLL.  Everything cited as
PROVED is sorry-free Lean on `origin/ui-confluence`; all derivability
is PLL (`Deriv` = `LaxND`).*

## Goal

Prove that **PLL does not have uniform interpolation** (or discover
that this attack cannot work, which would be evidence the other way).
It suffices to refute the LAST-variable case: interpolants that
eliminate the only variable of a one-variable formula, which must be
**variable-free** — elements of RN(◯,{}), the algebra this whole
campaign has been charting.

## The four named objects

For a one-variable formula φ (atoms ⊆ {p}):

| name | definition | order structure |
|---|---|---|
| **consequence filter** `F(φ)` | `{χ variable-free : φ ⊢ χ}` | up-closed, ∧-closed |
| **antecedent ideal** `I(φ)` | `{χ variable-free : χ ⊢ φ}` | down-closed, ∨-closed |
| **post-interpolant** `∃p.φ` | the MINIMUM of `F(φ)`, if it exists | Lean: `IsPostInterp` |
| **pre-interpolant** `∀p.φ` | the MAXIMUM of `I(φ)`, if it exists | Lean: `IsPreInterp` |

UI for this fragment = both exist for EVERY φ.  To refute UI we need
ONE φ for which one of them fails to exist.

A fifth, fixed landmark of the algebra (not attached to any φ):

* **the landing ideal `L`** `:= {χ variable-free : ∀k ≥ 1, χ ⊢ g k}`
  — the common lower bounds of the gap antichain.  Down-closed and
  ∨-closed (an ideal).  Any post-interpolant of any gap-entailing φ
  must lie in `F(φ) ∩ L`.  PROVED about `L`: it contains `t3`, `t4`,
  `t5` and `w15`, with `t3 < w15` strictly and `t5, w15`
  incomparable (so `L` has width ≥ 2); `t6, t7 ∉ L`.

## Method: the S4 mechanism, transplanted

For S4-like modal logics UI fails (Ghilardi–Zawadowski).  The
semantic mechanism: some φ's consequence filter is **non-principal**
— it contains a strictly descending meet-chain with no floor inside
the filter, so no single formula can be the least consequence.  Our
plan is the same mechanism with RN(◯,{}) as the target fragment,
powered by the proved families:

* **descending engine** (∃-side): the partial meets of the gap
  antichain, `Gmeet n = g 1 ∧ … ∧ g (n+1)`, descend strictly forever
  (`Gmeet_strict`, `Gmeet_desc_strict`).
* **ascending engine** (∀-side): the chain `c 1 < c 2 < …`
  (`chain_lt_strict`), with no known upper bound but `⊤`.

## The architecture is TWO-step — the engine does not build φ

Step 1 (DONE): the engines exist.  Step 2 (OPEN): the **witness** — a
specific one-variable φ whose filter/ideal the engine breaks.  The
descending chain lives in the ambient algebra; a UI failure needs it
to be cofinal (downward) inside `F(φ)` for a single φ, with nothing of
`F(φ)` below it.  There is no general recipe that extracts φ from the
chain — in the S4 literature the witness is constructed by hand and
its filter computed.  The Lean reduction theorems make the two-step
shape exact (`no_post_interp_schema`, `no_pre_interp_schema`):

* ∀-side witness conditions: `hc : ∀ k, c k ⊢ φ` and
  `hU`: no variable-free bound of the whole c-chain entails φ.
* ∃-side witness conditions: `hg : ∀ k, φ ⊢ g k` and
  `hL`: no member of `L` is a consequence of φ.

## On ∃p vs ∀p (clearing a confusion)

Nothing has ever been PROVED about the existence of either quantifier
for all φ.  What happened earlier (July's rank-bounded probes) was the
computation of candidate VALUES for specific instances — e.g. the
approximants of `∀p.◯p` stabilising at `◯⊥` — which are consistent
with those particular interpolants existing.  Some certainly exist
(`∃p.p = ⊤`).  The attack needs one φ WITHOUT one; both sides are
live, and currently the ∀-side is further along:

* `phi1 := ◯p ⊃ ◯(p ∧ t3)` is a NEAR-witness: `c 1 ⊢ phi1` but
  `c 2 ⊬ phi1` (so `hc` fails), while its `hU` is PROVED outright via
  the substitution lever (`bound_collapse`: any variable-free
  `χ ⊢ phi1` entails `c 1` by the `p ↦ ⊤` instance, so a chain-bound
  entailing φ₁ would collapse `c 2 ⊢ c 1`).
* Within the image of `p ↦ ◯⊥` the ∀-side is CLOSED:
  `inimage_chain_bound_top` — only `⊤` bounds the c-chain there; and
  every known off-image family is separately excluded.

## The current fork, and what is running

(a) Find a one-variable bound of the RUNG chain
(`∀k, rnSub (2k+1) ⊢ φ`, φ not a theorem): the bind mechanism turns
any such φ into `◯φ`-material above the c-chain — the missing `hc`.
This is being probed now (enumeration + certificate search +
countermodel filtering, delegated).  The regress observation — bind
reduces c-chain bounds to rung-chain bounds, one ◯ down — suggests
the answer may be NO.

(b) If (a) is refuted: prove the off-image version of "only ⊤ bounds
the c-chain", completing `hU`-side impossibility — which would DEFEAT
the c-chain attack on UI and shift all weight to the ∃-side (where
`L`'s structure — does it have maximal elements? — becomes the
question).

Either outcome of (a) is progress: a witness kills UI; a refutation
redirects the attack with the search space halved.

---

## Postscript, same day: the fork is RESOLVED — the ∀-side is dead

`wip/rungbound.lean` (delegated probe, verified and landed).  Branch
(a) is refuted in maximal generality: **any φ whatsoever** (any
variables, any ◯-depth) entailed by every substituted odd rung is a
PLL theorem (`chain_bound_is_theorem`), hence likewise for the c-chain
(`c_chain_bound_is_theorem`), hence `no_pre_interp_schema` has
CONTRADICTORY hypotheses (`pre_interp_schema_vacuous`): **no formula
can ever instantiate the ∀-side obstruction.**  The mechanism: in a
FINITE constraint model every world forces a substituted odd rung of
rank ≤ twice its Rᵢ-depth (`rank_bound` — a pure ∨/⊃ induction, ◯⊥
treated as an opaque hereditary atom), and PLL's finite model property
(`LaxLogic/PLLFiniteModel.lean`, already in the repo) converts
finite-model validity into derivability.  A countermodel to a
chain-bound would need a world of infinite Rᵢ-depth — the limit point
of the Rieger–Nishimura Esakia space — which FMP says a non-theorem
never requires.

Consequences: C1 is proved (only ⊤ bounds the c-chain — for ALL of
RN(◯,{}) and beyond); the earlier "no completeness → no semantic
route" reasoning was WRONG (FMP is completeness enough, and was
already mechanised); `phi1` and the whole `◯p ⊃ ◯(p ∧ Y)` family are
dead as ∀-witnesses.  **The entire UI attack now lives on the ∃-side**:
the descending engine `Gmeet`, the landing ideal `L`, and the question
whether some φ's consequence filter meets the descent floorlessly.
Note the asymmetry that saves the ∃-side: the rank argument bounds
worlds FROM BELOW by rungs (joins upward); it says nothing about
common lower bounds of the gap antichain, where the descent lives.

---

## The ∃-side hunt (2026-08-04): reformulation, constraints, probes

All PLL.  Witness conditions (`no_post_interp_schema`):

* `hg`: ∀ k ≥ 1, φ ⊢ g k.  Unfolding g k = c k ⊃ t(2k+1):
  `[φ, ◯t(2k+1)] ⊢ t(2k+1)` — the witness is a UNIFORM MONAD-ESCAPE
  along the odd rungs.
* `hL`: no variable-free χ ∈ L is a consequence of φ.

**Why the ∀-side killer does not dualise.**  The mirror of
`chain_bound_is_theorem` would be ATTAINMENT of the gap meet: a fixed
variable-free χ₀ ∈ L forced at every finite-model world that forces
all the gaps.  Given attainment, FMP would turn hg into φ ⊢ χ₀,
contradicting hL — the exact mirror of `pre_interp_schema_vacuous`.
But on the plain ladder EVERY world forces EVERY gap
(`plain_forces_gap`, pinned), while every known member of L
(t1 = ◯⊥, t2, t3, t4, t5, w15) fails at all sufficiently deep plain
worlds (bounded trace, rung machinery).  So attainment already fails
at every known candidate χ₀; the sole loophole is an unknown
LADDER-VALID member of L.  Root cause of the asymmetry: every finite
world has finite rank and so sits ABOVE some rung (⊔ c k = ⊤ is a
formula), but the deep ladder worlds approximate ⊓ g k from above
forever without any formula landing on it — conjecturally ⊓ g k
exists only as the limit point of the completed (Esakia/assembly)
algebra, not as a formula.  UI for the right φ would manufacture that
formula; that is the shape of the refutation.

**Constraints on any witness** (compositions of pinned lemmas; the
composites are being pinned by the delegated probes):

1. *No rung may be entailed.*  If φ ⊢ t(2K+1) then
   χ* := g 1 ∧ … ∧ g (K−1) ∧ t(2K+1) is a variable-free consequence
   of φ lying in L (odd rungs ascend from t3 by `rungD`;
   `rung_le_gap`; hg supplies the low gaps) — hL dies.  Even rungs:
   same via the w15 mechanism (t6 = t5 ⊃ t3 descends inside the box;
   general even-rung version CONJECTURED, proved for t6).  Since
   t1 = ◯⊥ and t2 are rungs, φ ⊬ ◯⊥ and φ ⊬ t2 as well.
2. *The witness must dodge its own instances.*  If hg holds then
   every variable-free instance φ[p↦ψ] lands in L
   (`Deriv.substP'`; gaps are variable-free), so hL forces
   φ ⊬ φ[p↦ψ] for EVERY variable-free ψ.  In particular p cannot
   occur only positively (else φ ⊢ φ[p↦⊤]).

**Probes launched** (both delegated, background):

* *Floor probe*: prove every χ ∈ L has bounded plain-ladder trace,
  via an edge-stability lemma — a fixed variable-free formula's value
  at world m+3 agrees between `ladder.cm` and `cmE m` once m exceeds
  a bound depending on the formula (the models differ only in the lax
  edges (m+3)⇝0, (m+3)⇝none; the gap g k flips exactly in the window
  m ∈ {k−2, k−1}).  Corollary: the gap meet is attained at NO
  variable-free formula, so the ∃-side cannot be closed the way the
  ∀-side was.  A refutation (a ladder-valid floor) would be equally
  decisive the other way.
* *Witness sweep*: bounded enumeration of one-variable φ with the
  filters above (p non-positive; countermodels against rnSub 1..9,
  w15 and its family, own ⊤/◯⊥/t3-instances; certificates for
  g 1..g 3), PLLSearch two-sided verdicts.  An EMPTY sweep at depth
  is evidence for a collapse theorem ("every one-variable formula
  below all gaps entails a rung") — a positive-UI signal at this
  antichain.

---

## Postscript, same day: the floor probe landed — **the gap meet does not exist**

`wip/floor.lean` (delegated probe, verified, landed).  The conjecture
is PROVED and strengthened.  Mechanism: *below-edge agreement*
(`cmE_agree_below`: the edged lift differs from the plain lift only in
the lax edges leaving world m+3, so the two models agree at every world
y ≤ m+2), *trace dichotomy* (`plain_trace_dichotomy`: by heredity every
formula's plain-ladder truth set is everything or bounded), and *edge
stability* (`edge_stability`: for m past a formula-dependent bound, the
edged and plain lifts agree on the formula AT the edge world m+3 — the
◯-clauses differ by exactly one conjunct, killed by the dichotomy).
Hence:

* `L_bounded` — any χ entailing every gap has bounded plain trace.
  **No `atomFree` hypothesis**: both lifts read atoms as the fallible
  singleton, so this covers one-variable formulas too.
* `no_ladder_valid_lower_bound`, `gap_meet_not_attained`,
  `no_lower_bound_above_odd_rungs` — the meet is attained nowhere; the
  mirror of the ∀-side kill is now PROVED impossible, not merely
  evidenced.
* `even_rung_gap` — the exact rung-order threshold t(2a+2) ⊢ g k for
  k ≥ a+1; `wC_gap_step` — the generalised w15 box-descent
  g (j+1) ∧ t(2j+6) ⊢ g (j+2) at every level.
* `Wit b := (g 1 ∧ … ∧ g (b+1)) ∧ t(2b+6)` ∈ L with plain trace
  containing b+3 (`Wit_below_all_gaps`, `Wit_force_high`) — members of
  L with unboundedly large traces.  A glb would sit above every Wit b,
  forcing an unbounded trace, contradicting `L_bounded`:

**`gap_no_glb` / `L_no_greatest`: the family {g k : k ≥ 1} has NO
greatest lower bound in PLL — among ALL formulas, one-variable
included — and the landing ideal L has no greatest element.**  The
descending chain `Gmeet` provably has no floor; the infinite meet
⋀ g k exists only in the completed algebra, exactly the
Ghilardi–Zawadowski-shaped structure the ∃-side needs.

What this does and does not settle.  It settles: the ∃-side door
cannot be slammed the way the ∀-side was; the non-existence of the
meet — the structural fact a witness would exploit — is a theorem.  It
does NOT yet refute UI: `no_post_interp_schema` still needs one φ with
F(φ) ∩ L = ∅.  And `L_bounded`'s generality cuts both ways: a
candidate witness φ (entailing all gaps) ALSO has bounded plain trace,
so the plain ladder can never separate φ from members of L — the hL
countermodels must come from other model families (the edge models
with tuned valuations of p are the natural candidates).  The witness
sweep is running.

---

## Postscript 3, same day: the witness sweep is EMPTY — and the filters are now theorems

`wip/wlanding.lean` + probe harnesses `wip/wsweep.lean`/`wip/wscout.lean`
(delegated sweep, verified, landed).  All PLL.

**Filters promoted to theorems** (sorry-free, pinned):

* `rung_kills` / `rung_blocks_schema`: if φ entails every gap AND any
  single rung `rnSub m` (odd or even), then φ entails the variable-free
  `Ufam m := Gmeet m ∧ rnSub m ∈ L` — hL dies.  The no-rung constraint
  is exact, for every rung index.
* `inst_in_L` / `no_theorem_instance` / `self_instance_kills`: every
  variable-free instance φ[p↦χ] of a gap-entailing φ lies in L; none
  can be a theorem; entailing one's own instance kills hL.
* New low family in L: `Vf n := Gmeet n ∧ rnSub (2n+4)` (no
  box-descent needed; `Vf 0 = g1 ∧ t4` is lower than w15 where it
  matters).

**Sweep results.**  Exhaustive size ≤ 8 over {⊥, p, ∧, ∨, ⊃, ◯}:
26,032 formulas — 15,584 killed by polarity, 7,795 by `φ ⊬ g 1`
(search-space exhausted), and ALL 2,653 remaining entail a rung
(least entailed: ◯⊥ 2070, t2 503, t3 6, t4 74).  Zero survivors, zero
near-misses.  Structured clause-pool sweep (9,537 candidates over 120
rung/gap/collapse/link clauses): zero certified survivors; the only
shapes proving g 1 AND g 2 while dodging rungs and self-instances are
`X ∧ g 2` where the p-clause contributes nothing.  34 hand designs:
every one that survives g 1 + the rung dodge is killed by the
SELF-INSTANCE filter (φ ⊢ φ[p↦t3] or φ ⊢ φ[p↦◯⊥]).  Unswept: 2,573
pool candidates undecided at budget 8000; sizes ≥ 9.

**Frontier fact, pinned by hand** (`gap_two_le_one`): `g 2 ⊢ g 1` —
discovered by the sweep.  So the gap family is an antichain only from
k = 2, with g 1 < g 2 strictly (`gap_one_not_le_two`).  `g k ⊢ g 1`
for k ≥ 3 is OPEN.

**The collapse conjecture** (UNPROVED at the time of writing;
PROVED the same day — see Postscript 4).
For a world v of a finite model let ρ(v) = min{k : v ⊩ t(2k+1)}
(finite, by `rank_bound`) and β(v) = min{k : v ⊩ ◯t(2k+1)}; always
β ≤ ρ.  Then hg (φ ⊢ every gap) says exactly: hereditarily above every
φ-world, ρ = β — the ◯-escape never lowers the rung rank.  CONJECTURE:
any one-variable φ enforcing ρ = β hereditarily must bound ρ, i.e.
must entail some rung — whereupon `rung_kills` finishes it and NO
one-variable φ can instantiate `no_post_interp_schema` at the gap
antichain: the ∃-side would join the ∀-side as vacuous.  The sweep
data points this way.  Note the tension this would resolve AGAINST
refutation: `gap_no_glb` stands (the meet does not exist), but the
schema needs a φ pressed against the non-existent meet, and rung-free
gap-entailment may be unreachable for one-variable formulas.  Being
probed by delegation (prove: edge-surgery/limit transport of
`rank_bound` + `edge_stability` to arbitrary finite models; refute:
candidates beyond the sweep's bound).

---

## Postscript 4, same day: the COLLAPSE THEOREM — the ∃-side closes; the attack at the gap antichain is over

`wip/collapse.lean` (delegated probe, verified, landed).  All PLL,
sorry-free, `[propext, Classical.choice, Quot.sound]`.

    collapse : (∀ k ≥ 1, φ ⊢ g k) → ∃ m, φ ⊢ t m          -- ANY φ
    post_interp_schema_vacuous : hg → ¬ hL
    L_eq_union_Ufam : (∀ k ≥ 1, φ ⊢ g k) ↔ ∃ m, φ ⊢ U m

Every gap-entailing formula — one variable, many, arbitrary — entails
a rung, hence (rung_kills) a variable-free member of L: the two
hypotheses of `no_post_interp_schema` are jointly contradictory,
exactly as `pre_interp_schema_vacuous` closed the ∀-side.  The third
theorem is a structure result worth keeping: **the landing ideal is
the union of the principal ideals of the rung companions U m** — below
all the gaps ⟺ below some single U m.

Proof in four moves (details in the file and PROGRESS §45): rank
ρ w = min{k : w ⊩ t(2k+1)} in finite models; rank descent (ρ drops by
2 along Rᵢ, read off the even-rung recursion); EDGE SURGERY — the
general form of the cmE construction: adding lax edges toward lower
rank along a co-type-respecting descent map is invisible to a fixed
subformula-closed set (hence to the rungs, via ⊥) but makes
gap (ρu−1) FAIL at a φ-world, contradicting hg; so above every
φ-world sits a RIGID world of the same rank, and a pigeonhole on
co-types (2^|Sub φ| of them) bounds ρ at φ-worlds by 2·2^|Sub φ| + 2;
FMP converts the bound into φ ⊢ t m with m explicit.  Cross-check
`collapse_bound_not_uniform`: no uniform rung index can work (Wit M
forces the index above M) — the exponential dependence on |Sub φ| is
FORCED by gap_no_glb, a genuine consistency check between the two
results.

**Where this leaves the campaign.**  The UI-failure attack via the gap
antichain is closed BOTH ways, by parallel mechanisms: the ∀-side by
rank_bound + FMP (nothing sits strictly between the c-chain and ⊤),
the ∃-side by collapse + rung_kills (nothing sits between the gaps
and L without falling into L).  What stands as pure structure:
infinite width (gap_incomparable), the floorless descent
(Gmeet_desc_strict + gap_no_glb), L = ⋃ ↓U m, g1 < g2.  UI for PLL
itself remains OPEN — neither refuted (this attack is dead) nor
proved — but the strongest known obstruction is neutralised, and the
collapse machinery (surgery + rigidity + co-type pigeonhole) reads
like the germ of a POSITIVE method: it computes, for gap-entailing φ,
a variable-free consequence below all gaps — a step toward
constructing ∃p.φ outright.  Whether to pivot the campaign from
refuting UI to proving it (reconnecting with the dormant syntactic
tower) is the next strategic decision.
