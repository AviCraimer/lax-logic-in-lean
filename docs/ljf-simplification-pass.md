# LJF uniform interpolation: the simplification pass

*2026-08-09. Written immediately after the mega-mutual landed (all four
characteristic properties plus the saturated case proved, zero errors,
sorry-free). Three parts: what should be simplified, the proof read
side-by-side with its inspirations, and the tool lessons — the last being,
as agreed, at least as valuable an output as the theorem.*

## 1. What the development proves

For the focused calculus `LJF` (canonical-polarity Liang–Miller, built
from zero imports in `LaxLogic/LJF.lean`), one recursion

$$\mathrm{interp}\;p\;\mathit{todo}\;\mathit{done}\;g$$

computes both uniform interpolants (`g = none`: the strongest p-free
consequence ∃p; `g = some G`: the weakest p-free hypothesis ∀p), and the
four characteristic properties are machine-checked, unconditionally:

| | statement | status |
|---|---|---|
| E1 | `eSound` — the context proves its ∃p | PROVED |
| A1 | `aSound` — ∀p beside the context proves the goal | PROVED |
| E2 | `eMinF` — any p-free consequence follows from ∃p | PROVED |
| A2 | `aMinF` — any route from p-free material to the goal factors through ∀p | PROVED |
| — | `satE2`, `satA2`, `dykAnt` — the saturated cases and the Dyckhoff dispatch | PROVED |

Axioms: `[propext, Classical.choice, Quot.sound]` throughout. What is NOT
yet proved: focalization completeness (`Deriv Γ φ → LJF`), so the honest
label is **uniform interpolation for LJF**; the bridge to IPC-as-`Deriv`
is standard-but-unwritten, and `circL` remains the single new rule for the
PLL extension.

## 2. Simplifications the next pass should make

Ordered by value.

1. **Unify the p-fire eliminators.** `TpElim/TpLF/TpInv` (E-mode) and
   `UpElim/UpLF/UpInvG` (A-mode) differ only in what they *emit* at the
   dispatch points (conjunct fire vs attack disjunct). One family
   parametrised by an emission continuation halves ~700 lines. The same
   holds one level up for `TStab`-vs-`UStab`.
2. **Delete the superseded layer.** `eMin`/`aMin` (the `SatE2`/`SatA2`-
   parametrised versions) are strictly subsumed by `eMinF`/`aMinF`; keep
   the `SatE2`/`SatA2` *statements* (they name the saturated case) and
   `satE2_of_dyk`-era history only in git. Likewise `qAssemble`/
   `dykAssemble` are the `.up`-instances of `qAssembleN`/`dykAssembleN`.
3. **Shrink the decreasing farm.** The ~50-alternative combinator is
   archaeology, not design. With the lessons of §4 known up front it
   reduces to about ten entries: the exact `dec_*` lemmas stated in
   post-`simp` normal form, the slack variants (`+9` uniformly), and one
   `Prod.Lex.left`-wrapped block of term-chains. Every `Nat.lt_of_lt_of_le
   … (by omega)` glue entry that never fires should go.
4. **Drop dead machinery.** The `ΩOk` invariant's done-atom alternative
   became unreachable once the deep forced patterns
   (`.rel (.atomL (.stable s'))`) handled shifted atoms; revert to plain
   `PFreeΩ`. `atomConjMem`'s phantom `rest` is gone but similar phantoms
   should be audited.
5. **Fold the six fire-blobs.** `aSound` and `aMinF` repeat the aggregate
   fire-branch per goal shape only because `rw [interp]` needs a
   constructor-headed goal. The `eq1`-equation trick (prove
   `interp p [] done g = interp p [N] rest g` once, `G`-generically, via
   the `split`/`cases heq` dance) makes one shared branch possible.
6. **Name the attack map.** The A-aggregate's inlined per-shape attack
   lists forced the `interpA_*_eq` equation family and the oracle
   parameters. If `interp` named its attack-map through a top-level
   definition taking the recursive calls as data, the memberships would be
   direct. This is the deepest refactor and touches termination; do it
   only with the equations kept as a safety net.

What should NOT be simplified: the E-guards and the E-res conjunct (all
three were forced by the minimality induction — they are the mathematical
content); the parkedness hypothesis; the lexicographic offset pattern.

## 3. Side by side with the inspirations

**Pitts 1992 over Dyckhoff's G4ip.** The clause correspondence is exact
and worth recording:

| G4ip / Pitts | here |
|---|---|
| left rules on ∧,∨,⊥ | the `todo`-processing clauses |
| implication left-rules split by antecedent | the `imp`-clauses incl. currying |
| atom-implication rule (fire when atom present) | `findFire` + the fire clause |
| the `(A⊃B)⊃C` rule with residual `B⊃C` | the Dyckhoff park + `dykCommute` |
| Pitts' E/A simultaneous recursion | one `interp` with an `Option` goal |
| Pitts' A-clauses referencing E of extended contexts | the E-guards `↓E(Γ+b) ⊃ …` |
| his D-pair for the Dyckhoff hypothesis | the conjunct pair `(↓A([res],rest⇒M′) ⊃ E([N],rest)) ∧ E([res],rest)` |

The third component of the last row — `E([res],rest)` carried inside the
∃p conjunct — appears to be *forced by the well-founded mechanisation*:
on paper one silently uses minimality at the same station (E(done) ⊢
E([res],rest)); in a measure-carrying proof that call climbs, so the
definition must carry the fact instead. That is a genuinely new datum
about the proof's structure, not a workaround.

**Dyckhoff's weight.** His multiset ordering with a heavier ∧ becomes the
single number $2\sum_{todo}3^{w} + \sum_{done}3^{w} (+\,3^{w(G)})$, with
∧ costing 3 — forced by exactly the currying clause. Parking moves weight
from the doubled to the single side, which is what lets one Nat replace a
lexicographic pair for `interp` itself.

**The focusing dividend versus the repo's G4c route.** In G4c the earlier
campaign fought goal-entangled retention rules; in LJF, inversion is
head-only, so every "invertibility lemma" is a three-line total function
(`extract`, `unStable`, `lfocImp`, …) and the derivation-analysis in the
saturated case is by forced patterns instead of case bashing. The price
was paid once, in `routeStab` — cut's work done by a CPS traversal — and
in the eventual focalization-completeness debt.

**The candidates method.** As established: not load-bearing in the
artifact (the target is predicative), but it found the clause set, and
three times the failing (ii)-induction step dictated a definition change
(two E-guards, one E-res pair). That discipline — run the minimality
induction on paper before mechanising the clause — is the method's real
content here.

## 4. Tool lessons (the collection system's first deposits)

Term-level tools, all reusable for any focused calculus: `routeStab`
(CPS re-targeting; shift release, ∨-routing, ex falso as instances),
`simStab/simHyp` (hypothesis simulation; atomic `init`-uses reduce via
`idPos`), `invBranches`/`extract`, `stableFire`/`upMerge`,
`negOfDownStab`/`relStab` (shift release into a derivation), `fireClean`,
the assemblers, `memMapWitness`/`splitAt` (choice-free witnesses),
`dykCommute`.

Mechanisation lessons, several bought dearly today:

1. **`Prod.Lex` display deception.** The termination-error printer shows
   the *reduced first-component inequality* even when the tactic faces the
   raw `Prod.Lex` pair (when `simp_wf` fails to split it). Hours were
   lost proving the displayed goal. Diagnosis: make a suspect entry the
   *last* alternative — `first` reports the last error — or read the
   Type-mismatch of an `exact` against the goal.
2. **Omega and goal-only pow atoms.** `omega` can drop the positivity
   fact for a power atom that occurs only in the goal, making manifestly
   unsat constraint systems "satisfiable". Fix: term-level monotone
   chains — `Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 …) _) h`
   — where *defeq unification*, not atom sharing, does the matching.
3. **WF-compiled matchers never `rfl` against restatements.** The
   equation compiler fuses hypothesis discriminants into aggregate
   matchers during well-founded translation; a syntactically identical
   literal elsewhere compiles to a different matcher constant. State the
   aggregate equations *outside* the mutual (`interpE_eq`,
   `interpA_*_eq`) via `rw [interp]; split; · rw [h] at heq; cases heq`.
4. **`have w := e` is transparent for data.** Termination obligations see
   through it and unfold, desynchronising the goal's atoms from your
   lemma instance. `obtain ⟨rest, hXr⟩ := …` produces opaque fvars.
5. **Goal-determined implicits die in `have`.** `have h := lemma (by tac)`
   runs the tactic block before unification fixes the lemma's implicits;
   instantiate them (`(N := N)`) or pin literals (`show (5:Nat) ≤ 9`).
6. **Structural beats clever.** Deep forced patterns in equations
   (`.rel (.atomL (.stable s'))`) keep recursion structural where
   analyser functions would demand `sizeOf` lemma chains; decidable tests
   (`if h : x ∈ l`) replace `Or`/`∃`-elimination into `Type`; column
   patterns (`.or P₁ Q₁ :: _` in the Ω-slot) fix match motives that
   `@`-constructor patterns leave stuck.
7. **Lexicographic hygiene** (the §12 triad, confirmed repeatedly): align
   first components *syntactically* (`0 + n` is not defeq `n`); never
   `cases` an atom equality inside a dispatch (cast-twins sever size
   relations) — carry `a = p` hypotheses; prefer offset first components
   `(μ + k, 0)` to cross-definition `sizeOf` ties.

## 5. The state of the campaign

UI for **LJF**: done, machine-checked, first proof by any route that
survives this repo's scrutiny (Iemhoff's G4iLL being refuted-incomplete
here). Remaining for UI-for-**IPC**: focalization completeness. Remaining
for UI-for-**PLL** (the open prize): add `circL` and the `lax` judgment
to every layer — the calculus and toolkit were designed so that this is
one rule in one phase — then the PLL-side completeness bridge. The PLL2
programme (docs/pll2-plan.md) sits on top of exactly this engine.
