# Formalisation notes: PLL in Lean 4 vs. Fairtlough–Mendler 1997

A referee-style reading of the `lax-logic-in-lean` development against
Fairtlough & Mendler, *Propositional Lax Logic*, Information and Computation
137(1), 1997 (henceforth **F&M**).  The audience is an author of the paper; the
emphasis is on *where the formal statements say exactly what their names claim*,
*where the Lean proofs take a different route than the paper*, and *what is
constructive*.

**Method and scope.**  This is a static reading of the source in
`LaxLogic/*.lean`.  Statement shapes are quoted from the declarations
themselves, so claims about *what a theorem asserts* are marked **verified**.
Claims about *proof correctness* are marked **inspected**: I traced each proof
but did not re-run the Lean kernel (the checkout carries no `.lake/build`
oleans; a clean `lake build` is recommended to confirm kernel acceptance).  I
did confirm there is **no `sorry`, `admit`, or `native_decide`** anywhere in the
nine files the library root imports (`LaxLogic.lean` imports `PLLProof`,
`PLLNDCore`, `PLLKripke`, `PLLConsequence`, `PLLCompleteness`, `PLLTheorems`,
`PLLFrames`, `PLLHilbert`).  All headline theorems are stated over the single
slime-free system `PLLND.LaxND` of `PLLNDCore.lean`; the legacy systems
(`PLLNDProof.lean`, `PLLNDProofPostZoom.lean`, `PLLNDexperiment.lean`,
`olderMF.lean`, `Learning.lean`) are not reachable from the theorems below.

---

## 1. Statement fidelity

### `Nonempty (LaxND Γ φ)` as derivability

`LaxND : List PLLFormula → PLLFormula → Type` (`PLLNDCore.lean:72`) is
proof-*relevant*: an inhabitant is a specific derivation.  Provability is then
`Nonempty (LaxND Γ φ)` — "the type of derivations is inhabited" — which is
exactly F&M's `Γ ⊢ φ` with the individual derivation forgotten.  This is the
right notion for metatheorems, which must not depend on *which* derivation is
chosen.  **Verified faithful.**  Note the asymmetry that soundness consumes a
raw `LaxND Γ φ` (usable on a concrete derivation) while completeness produces
`Nonempty (LaxND Γ φ)`; `consequence_iff_derivable` (`PLLCompleteness.lean:634`)
reconciles them, its reverse direction being `fun ⟨p⟩ => soundness p`.

### The `orElim` rule matches F&M ∨-elimination

`LaxND.orElim` (`PLLNDCore.lean:90–92`) carries its **major premise**:

```lean
| orElim (p₀ : LaxND Γ (.or φ ψ))
    (p₁ : LaxND (φ :: Γ) χ) (p₂ : LaxND (ψ :: Γ) χ) : LaxND Γ χ
```

This is F&M's ∨-E.  **Verified.**  For contrast, the legacy
`PLLNDProof.lean:21–23` had `orElim : LaxND (Γ++φ::Δ) χ → LaxND (Γ++ψ::Δ) χ →
LaxND (Γ++Δ) χ` — **no** major premise — so with `φ=ψ=χ` and two `iden` leaves
it derives every sequent.  The companion paper's "every ND system in the repo
was inconsistent" (§7) is accurate; the fix is exactly the `p₀` argument, and it
is genuinely load-bearing downstream (primeness `or_mem`, disjunction congruence
`iff_congr_or`, the set-level `orE`).

### Soundness (`PLLKripke.lean:97`)

```lean
theorem soundness (p : LaxND Γ φ) : Γ ⊨- φ
```
with `Consequence Γ φ := ∀ (C : ConstraintModel) (w : C.W), (∀ ψ ∈ Γ, C.force w
ψ) → C.force w φ` (`PLLKripke.lean:91`).  This is F&M Thm 3.3 in *sequent* form
(the paper lifts validity to sequents in the proof, lines 860–863).  The
constraint model structure (`PLLKripke.lean:28`) reproduces Def 3.1 exactly: two
preorders (`refl_i/trans_i/refl_m/trans_m`), `Rₘ ⊆ Rᵢ` (`sub_mi`), hereditary
`F` and `V` (`hered_F/hered_V`), `V` full on `F` (`full_F`); `force`
(`PLLKripke.lean:52`) reproduces Def 3.2, with `⊥` forced exactly on `F` and the
∀∃ clause for `◯`.  **Verified.**

**Universe restriction (the one genuine fidelity caveat).**  `ConstraintModel.W
: Type` (`PLLKripke.lean:29`) fixes the carrier to `Type 0`, so
`ConstraintModel : Type 1` and `Consequence` quantifies **only over
`Type 0`-carrier models**.  Consequences:

* *Soundness is, as stated, marginally weaker than a universe-polymorphic
  soundness.*  The induction never inspects the carrier, so replacing `W : Type`
  by `W : Type u` would give `⊢ φ → φ` valid in *all* models of *every* universe
  at zero proof cost; as written it only asserts the `u = 0` instance.  This is a
  real but immaterial loss: a propositional logic's semantic content is fully
  captured by `Type 0` (indeed finite/countable) models, and no `Type 1`-carrier
  model is ever used.
* *Completeness is unaffected — if anything strengthened.*  Restricting the
  model quantifier makes the hypothesis `Γ ⊨- φ` *easier* to satisfy, so
  `completeness` (`PLLCompleteness.lean:614`) is a *stronger* implication, and it
  is discharged because the canonical model is a `Type 0` model: `MaxTheory =
  {T : Theory // MaxConsistent T}` and `Theory` (three `Set PLLFormula`) both
  live in `Type 0`, so `canonical.W : Type 0` inhabits the quantified class.
  **Verified.**
* *The direction feeding underivability is legitimate.*  `not_provable_*` use
  soundness at *finite* (hence `Type 0`) models — `⊢ φ` would force `φ` valid at
  `modelX`, contradicting a `decide` that it is not.  Only `Type 0` soundness is
  needed there.  **Verified.**

So `consequence_iff_derivable : Γ ⊨- φ ↔ Nonempty (LaxND Γ φ)` is an *internally
coherent* iff over one fixed class of models — the `⊨-` on both sides is
literally the same `Consequence` — and both halves are honest for that class.
The only recommendation is cosmetic: make `W : Type u` so soundness is stated at
full generality (see §4).

### Completeness (`PLLCompleteness.lean:614`, `:634`, `:639`)

`completeness : Γ ⊨- φ → Nonempty (LaxND Γ φ)` and its packaging
`consequence_iff_derivable`.  This is F&M Thm 4.4 **strengthened from validity
to sequent consequence** (the paper states `⊢ M iff ⊨ M`, theoremhood vs
validity); the weak form is recovered as `valid_iff_provable`
(`PLLCompleteness.lean:639`).  Crucially, soundness and completeness quantify the
*same* list-based `Consequence`, so the strengthening is sound (the set-based
`SetDeriv` used inside the proof never surfaces in the final statement).
**Verified.**

### `consequence_iff_derivable` — same notion both directions

`⟨completeness, fun ⟨p⟩ => soundness p⟩` (`PLLCompleteness.lean:634`).  Both
arms use list contexts and the identical `Consequence`.  **Verified** no
equivocation between the soundness `⊨-` and the completeness `⊨-`.

### Conservativity (`PLLNDCore.lean:193`, `:211`, `:258`)

Three faithful renderings of F&M Thm 2.4:

* `conservativity_prop : LaxND Γ φ → IPLND (Γ.map erase) (erase φ)`
  (`:193`) — every PLL derivation erases to an IPL derivation of the erased
  sequent, `IPLND` being a standalone lax-free judgment (`:167`).
* `conservativity_IPL : isIPL φ → (∀ ψ ∈ Γ, isIPL ψ) → LaxND Γ φ → IPLND Γ φ`
  (`:211`) — the classical statement (no new IPL theorems), via
  `erase`-idempotence.
* `conservativity : (p : LaxND Γ φ) → p.erased.isIPLProof` (`:258`) — the
  proof-term form, exactly the statement `sorry`ed as `PLLconservative` in the
  legacy files.

`erase` (`:32`) and `isIPL` (`:42`) are the expected structural definitions.
The lax cases are the interesting ones: `laxIntro` erases to the identity on the
subderivation (`:206`, `:235`), and `laxElim` erases to `impElim (impIntro …) …`
(`:207`, `:236`) — i.e. `◯`-elimination becomes a cut, the standard erasure.
**Verified.**

### Truth lemma (`PLLCompleteness.lean:504`)

```lean
theorem truth_lemma (φ) : ∀ T : MaxTheory,
  (φ ∈ T.1.val → canonical.force T φ) ∧ (φ ∈ T.1.fal → ¬ canonical.force T φ)
```
This is a **two-clause** rendering of F&M's **three-clause** Lemma 4.3 (paper
1439–1455: `M∈Γ ⇒ T⊨M`; `M∈Δ ⇒ T⊭M`; `M∈Θ ⇒ ∀T′, T Rₘ T′ ⇒ T′⊭M`).  The
Θ-clause is not stated; where F&M would use it — the `fal` case of `◯` at
`:590–608` — the proof instead extends to a theory with `φ ∈ mfal`, extracts an
`Rₘ`-successor `T₂` forcing `φ` from the ∀∃ clause, observes `φ ∈ T₂.mfal`, and
*converts* it to `φ ∈ T₂.fal` via `mfal_sub_fal` (Lemma 4.2(vi), `Θ ⊆ Δ`,
`:448`) before applying the second clause of the IH.  This is a clean
factoring, not a gap.  **Verified faithful** (the `Θ`-clause is a corollary of
`Θ ⊆ Δ` plus the `fal`-clause).

### The `not_provable_*` results (`PLLFrames.lean:88`, `:142`, `:205`)

Each states `¬ Nonempty (LaxND [] φ)` for one of F&M Figure 3's non-theorems
(`¬◯⊥`, `◯(A∨B) ⊃ ◯A∨◯B`, `(◯A⊃◯B) ⊃ ◯(A⊃B)`).  The proof pattern is uniform:
`rintro ⟨p⟩; exact absurd (soundness_valid p modelX w) (by decide)`.  What the
kernel is asked to trust:

* the `Decidable (modelX.force w φ)` instance from `ConstraintModel.decForce`
  (`:30`), a structural recursion that discharges `∀ v …` / `∃ u …` by the
  `Fintype` quantifier instances on the two/three-world carriers; and
* `Decidable.decide` reduction in the kernel.

This is `decide`, **not** `native_decide` — so the trusted base is the Lean
kernel's own reduction of the `Decidable` instance, with **no compiled code and
no external oracle**.  The models are genuinely *evaluated* (quantifiers, both
frames, `V`, `F`), so these are runnable counter-examples.  **Verified** (kind
of trust; I did not re-run the kernel).  The frame conditions of the three
models are themselves discharged by `by decide` over `Bool`/`W3`
(`:72–80,123–133,182–197`), again kernel-checked.

### Strong extensionality (`PLLTheorems.lean:178`)

```lean
theorem strong_extensionality (a M N C) :
  Nonempty (LaxND [] ((iffPLL M N).ifThen (iffPLL (substProp a M C) (substProp a N C))))
```
F&M Thm 2.5, with a syntactic context `C[·]` rendered as substitution
`substProp a · C` for a designated propositional constant `a` (`:68`).  Proved
by induction on `C` through per-connective congruences (`iff_congr_and/or/imp/
somehow`, `:105–150`) at the set-derivability level, discharged to
`Nonempty (LaxND [] …)` at the end.  The `◯` case is `somehow_mono` back-to-back
(`:140–150`).  **Verified** the statement is the schematic `(M ≡ N) ⊃ (C[M] ≡
C[N])`.

### `hilbert_to_ND` (`PLLHilbert.lean:82`)

```lean
theorem hilbert_to_ND (h : p.isProofOf φ) : Nonempty (LaxND [] φ)
```
Genuinely *half* of F&M Thm 2.3, honestly labelled.  `isProofOf p φ`
(`PLLProof.lean:118`) unfolds to `p`'s last recorded formula `= φ` **and**
`p.isValid`.  `axiomDeriv` (`PLLHilbert.lean:33`) derives all **twelve**
`PLLAxiom` schemes (`PLLAxiom.lean:6–21`) in `LaxND`; `formulas_derivable`
(`:61`) inducts on valid proofs to make every recorded formula an `LaxND`
theorem; `hilbert_to_ND` extracts the last one.  Two prerequisite fixes are
recorded and verified against their own comments: the `orElim` axiom now reads
`(A∨B) ⊃ C` (`PLLAxiom.lean:69`, was `and A B`), and `isValid`'s `modusPonens`
case now re-checks `isValid prev` (`PLLProof.lean:91`), closing the
formula-laundering hole.  **Verified.**  Caveat: this trusts the checker's
*own* semantics of "valid Hilbert proof"; the converse (ND → Hilbert) is future
work, so the bridge is one-directional as claimed.

---

## 2. Proof-architecture divergences from F&M

### Natural deduction + membership identity vs. Gentzen sequent calculus — *cosmetic for the results, methodologically real*

F&M run a **sequent calculus** with explicit structural rules `id`, `cut`,
`∨L`, `⊃L/R`, `◯L/R` and derive their metatheorems by manipulating sequent
derivations; "structural reasoning" (paper 1230–1281) names the admissible
cut/∨-under-disjunction rules they lean on.  Lean uses **natural deduction** with
`iden {Γ φ} (h : φ ∈ Γ)` (`PLLNDCore.lean:73`): weakening/exchange/contraction
are *admissible* by one traversal `LaxND.rename` (`:108`), never structural
rules.  F&M's "structural reasoning" is reconstructed as an explicit toolkit in
`PLLConsequence.lean` (`cut :40`, `bigOrElim :61`, `somehowMono :75`, and the
set-level `deduct/orE/somehow_bind/somehow_or_absorb`).  The *theorems proved
are the same consequence relation*; the calculus underneath is different.  This
is the design decision that removes the transport problem — **essential to the
mechanisation, cosmetic to the mathematics.**

### Zorn vs. formula enumeration in Lindenbaum — *essential method change, same theorem*

F&M enumerate `B₀, B₁, …` and build a chain with a three-way case split at each
stage (paper 1108–1229).  Lean uses `zorn_le_nonempty₀`
(`PLLCompleteness.lean:230`) over the `Preorder Theory` instance (`:38`).  Two
points worth flagging to a reader who knows the paper:

* **Only a preorder is used; antisymmetry is never invoked.**  `MaxConsistent`
  (`:167`) takes maximality in the *preorder* sense — `∀ T′, Consistent T′ → T ≤
  T′ → T′ ≤ T` — which is exactly what `zorn_le_nonempty₀` delivers.  (Aside:
  `Theory` *would* support a `PartialOrder` — mutual `≤` forces set equality,
  hence `Theory` equality by `@[ext]` — but the development deliberately declares
  and uses only `Preorder`.)  **Verified.**
* **No countability instance is needed.**  Finite character of consistency does
  all the work: `chain_cover` (`:170`) and `chain_ub₂` (`:192`) show a chain's
  componentwise union is again consistent because any consistency-violating
  derivation uses only finitely many formulas, all covered by one chain member.
  F&M's enumeration would instead require `Encodable PLLFormula`.  **Verified**
  the Zorn route sidesteps this.

Essential divergence in technique; identical conclusion (F&M Lemma 4.2, first
bullet).

### Weak → strong completeness — *deliberate strengthening*

Covered under §1.  F&M Thm 4.4 is validity↔theoremhood; the Lean endpoint is
sequent-consequence↔derivability, with the paper's statement recovered as
`valid_iff_provable`.  Sound because soundness is proved in the same sequent
form.  **Verified.**

### Fallible set `F = {T | ⊥ ∈ T.val}` vs. F&M's singleton `F* = {(all, ∅, ∅)}` — *provably the same set; refuted as a divergence*

`canonical.F := {T | PLLFormula.falsePLL ∈ T.1.val}` (`PLLCompleteness.lean:490`)
is an *intensional* condition; F&M's `F* = {(⊥_set, ∅, ∅)}` (paper 1434) is an
*extensional* singleton.  **They coincide on `MaxTheory`, and F&M say so
themselves** (their remark, paper 1084–1086: a maximally consistent theory has
`false ∈ Γ` iff `Δ = Θ = ∅`, and `(all-formulas, ∅, ∅)` is maximally
consistent).  In this development's terms, for maximally consistent `T`:

> If `⊥ ∈ T.val` then `T.val ⊩ ⊥`, so by deductive closure (`ded_closed :245`,
> via `SetDeriv.falso`) *every* formula is in `T.val`, i.e. `T.val =
> all-formulas` — this is precisely how `full_F` is discharged at `:499`.
> Moreover `T.val ⊩ ⊥` makes `T.val ⊩ disjOf Ds Ts` derivable for *any* lists
> (falsity elimination), so `Consistent T` (`:66`) can only hold if there is no
> nonempty `(Ds,Ts)` to test — i.e. `T.fal = ∅` and `T.mfal = ∅`.  Hence `T =
> (all, ∅, ∅)`.  Conversely `(all, ∅, ∅)` has `⊥ ∈ val`.  So `{T | ⊥ ∈ T.val} =
> {(all, ∅, ∅)}` as subsets of `MaxTheory`.

**Verified in prose** (I did not mechanise this equality; the development never
needs it — it only needs `F` hereditary and `V`-full, which the intensional
definition gives directly at `:497–500`).  The intensional form is the *better*
formalisation choice: heredity `hered_F` is one line (`h hw`, `:497`), whereas
the singleton would need a lemma that `⊆`-extension out of `(all,∅,∅)` stays
`(all,∅,∅)`.  No divergence of substance.

### Consistency guard `Ds ++ Ts ≠ []` and `disjOf` vs. F&M's `n+k ≥ 1` with absent empty disjunction — *faithful, and the guard is load-bearing*

F&M consistency (paper 1058–1082): for all `N₁…Nₙ ∈ Δ`, `K₁…Kₖ ∈ Θ` with `n+k ≥
1`, not `Γ ⊢ ⋁Nᵢ ∨ ◯(⋁Kⱼ)`, "when `Z` is empty the corresponding disjunct `⋁Z`
is dropped" and "the empty disjunction is the empty formula rather than false."
Lean:

* `Consistent` (`PLLCompleteness.lean:66`) uses `(∀ φ ∈ Ds, φ ∈ T.fal) → (∀ φ ∈
  Ts, φ ∈ T.mfal) → Ds ++ Ts ≠ [] → ¬ T.val ⊩ disjOf Ds Ts` — the guard `Ds ++
  Ts ≠ []` is exactly `n + k ≥ 1`.
* `disjOf` (`:49`) case-splits so that the *absent* disjunct is genuinely
  dropped, not read as `⊥`:
  `disjOf Ds [] = bigOr Ds`; `disjOf [] (K::Ts) = ◯(bigOr (K::Ts))`;
  `disjOf (D::Ds) (K::Ts) = bigOr(D::Ds) ∨ ◯(bigOr(K::Ts))`.
  This is a line-for-line render of `⋁Δ′ ∨ ◯⋁Θ′` with the drop convention.
  **Verified.**
* `bigOr [] = ⊥` (`PLLConsequence.lean:31`) is the only junk value, and it never
  leaks: `disjOf [] [] = ⊥` is reachable only when `Ds ++ Ts = []`, which every
  use guards out; the sole place `bigOr []` is *eliminated* is `bigOrElim` on
  `[]` (`:64`), where `falsoElim` gives the logically correct vacuous branch.
  **Verified** the guard is what makes `(all, ∅, ∅)` consistent "for trivial
  reasons" (F&M 1081) — with `fal = mfal = ∅`, the only test list is `([],[])`,
  guarded away — and hence the single fallible world exists.  Reading the empty
  disjunction as `⊥` would make `(all, ∅, ∅)` *inconsistent* (`all ⊢ ⊥`) and
  destroy the fallible world; the development gets this exactly right.

The `disjOf` intro/elim/transform lemmas (`disjOf_intro_fal/_lax`, `disjOf_elim`,
`disjOf_transform`, `disjOf_mono`, `:83–148`) encapsulate the case analysis so
that Lemma 4.2 reads uniformly.  **Inspected**; the delicate one is
`disjOf_transform` (`:129`), which handles each `fal`-disjunct and injects the
modal part into a superlist — this is the workhorse behind `or_mem`, `imp_mem`,
`fal_and`, `mfal_sub_fal`.

---

## 3. Constructivity analysis

**Classical (and where classicality enters).**

* `exists_maxConsistent_extension` (`PLLCompleteness.lean:203`) — the **only use
  of choice**, via `zorn_le_nonempty₀` (`:230`), which rests on
  `Classical.choice`.  Everything classical downstream flows from here or from
  excluded middle in the next items.
* The `MaxConsistent` lemmas use **excluded middle**, not choice:
  `mem_val_or_mem_fal` (`:277`, `by_cases`), `or_mem` (`:316`), `imp_mem`
  (`:338`), `fal_and` (`:400`), `fal_or` (`:372`) (`by_contra`/`push_neg`),
  `mfal_sub_fal` (`:448`, `by_contra`); `not_consistent_iff` (`:70`, `push_neg`
  through `¬∀…¬`); `val_ext`/`fal_ext` (`:255`,`:266`, `¬¬`-elimination via
  `not_consistent_iff`).
* `truth_lemma` (`:504`) is classical *by dependence* — it invokes the
  `MaxConsistent` lemmas — even though its own skeleton is an induction.
* `completeness` (`:614`, `by_contra`), `consequence_iff_derivable`,
  `valid_iff_provable` — classical through `truth_lemma` and Zorn.

**Constructive.**

* `soundness` (`PLLKripke.lean:97`) — a pure induction producing `Prop` proofs;
  I checked every case for `Classical`/`by_contra`/`by_cases`/`push_neg`/choice
  and found **none** (case analysis is `rcases List.mem_cons.mp`, all
  constructive).  **Verified constructive.**  Likewise `force_hered` (`:61`) and
  `force_of_fallible` (`:75`).
* The erasure translation `LaxND.erased` (`PLLNDCore.lean:223`) is a **total,
  cast-free function on proof terms** (structural recursion), and
  `conservativity`/`conservativity_prop` are structural inductions — no
  classical content.  **Verified constructive.**
* The admissible-rule toolkit `LaxND.rename/cut/bigOrElim/somehowMono`
  (`PLLConsequence.lean`) are recursive functions on derivations —
  **constructive**.
* Counter-model evaluations (`decForce :30`, the `not_provable_*`) are
  **constructive**: `Decidable` instances plus kernel computation, and soundness
  is constructive, so no result reached this way touches choice or LEM.
  **Verified.**  (The finite `∀`/`∃` decidability comes from `Fintype`
  instances, i.e. finite conjunction/disjunction — constructive.)
* `hilbert_to_ND`/`formulas_derivable`/`axiomDeriv` (`PLLHilbert.lean`) and
  `deduction_iff` (`PLLTheorems.lean:28`) are structural — **constructive**.

**The `decide`/`filter` uses are decidability, not choice.**  Both
`SetDeriv.extract` (`PLLConsequence.lean:163`) and `rmv`
(`PLLCompleteness.lean:151`) filter with `fun χ => decide (χ ≠ φ)`.  `PLLFormula`
`deriving DecidableEq` (`PLLFormula.lean:10`) supplies `Decidable (χ = φ)`, hence
`Decidable (χ ≠ φ)`, so `decide` runs the *derived decision procedure* — this is
genuinely decidable filtering, **not** `Classical.dec`.  **Verified.**
Similarly the `by_cases b = a` in `extensionality_setDeriv`
(`PLLTheorems.lean:160`) is over `DecidableEq String`, so it is constructively
justifiable even if the tactic happens to insert a classical instance.

**What a constructive completeness would require.**  Decidable equality of
formulas is already available; String atoms are countable, so `PLLFormula` is
`Encodable`, and F&M's enumeration *could* replace Zorn — but that only trades
`Classical.choice` for excluded middle, because each enumeration step must
*decide* whether the candidate extension is consistent, and consistency of a
theory is a `Π`-statement over all finite tests, not decidable.  Prime/maximal
theory existence therefore fails constructively in general.  The relevant
folklore (stated with appropriate hedging): completeness of intuitionistic logic
with respect to Kripke/Tarski semantics is entangled with non-constructive
principles — Kreisel and later McCarty showed that in the *predicate* case
completeness implies Markov's principle, and Gödel-style arguments make full
completeness fan-theorem-/`MP`-adjacent.  For *propositional* logic the tension
is milder, and — a pleasant connection to this very paper — the device that
buys a constructive propositional completeness in the literature is precisely
**fallible ("exploding") worlds**, introduced by Veldman (1976) and de Swart for
exactly this purpose; F&M's `F` is the same device.  So a constructive
completeness for PLL is plausibly reachable, but *not* by the maximal-theory
route used here: it would need a Veldman/de Swart-style construction (or a
Beth-model detour) rather than `zorn_le_nonempty₀`.  I state this as folklore and
would want to re-derive the exact Kreisel/McCarty statements before asserting
them sharply.

---

## 4. Gaps and risks

* **Universe-monomorphism of models (main item).**  `ConstraintModel.W : Type`
  (`PLLKripke.lean:29`) — see §1.  Recommendation: change to `W : Type u` (a
  one-token edit).  Soundness then becomes fully universe-polymorphic; every use
  site, including the canonical model and the finite counter-models, instantiates
  at `u = 0`, so nothing else changes.  As it stands the development is *sound
  and complete for `Type 0` models*, which is the whole of the mathematics — the
  risk is only that a reader might over-read `soundness` as a statement about
  arbitrary-universe models.

* **`Consequence` list-based, theories set-based — no boundary mismatch.**  The
  final theorems (`soundness`, `completeness`, `consequence_iff_derivable`)
  quantify the *same* list-based `Consequence`; the set-based `SetDeriv` (`⊩`) is
  internal scaffolding.  The list↔set bridge inside `completeness` (`:617–628`)
  is correct: the theory `⟨{ψ | ψ ∈ Γ}, {φ}, ∅⟩` uses `{ψ | ψ ∈ Γ}` whose
  membership unfolds to list membership, and `p.rename hL` (`:625`) transports
  the extracted `LaxND L φ` back to `Γ`.  **Verified.**

* **Canonical worlds as a `Type 0` subtype** — `MaxTheory := {T // MaxConsistent
  T}` (`:477`).  Fine; this is what keeps `canonical.W : Type 0` and makes
  completeness land inside the quantified class.

* **`force`/`isIPLProof` equation lemmas.**  Minor correction to the brief:
  `force` is a **plain `def`** (`PLLKripke.lean:52`), *not* `@[simp]`.  Its
  equations hold definitionally because it is structural recursion on the
  formula, which is exactly what `decForce`'s `inferInstanceAs (Decidable
  (C.force w …))` (`PLLFrames.lean:34–51`) and the `… from rfl` rewrite in
  `force_not_somehow_false_of_F_empty` (`:220`) rely on.  `isIPLProof` **is**
  `@[simp]` (`PLLNDCore.lean:240`) and its equations feed the `conservativity`
  induction.  Both are structurally recursive, so the equation lemmas are
  definitional and the reliance is low-risk.  **Verified** `force` is not
  `@[simp]`.

* **The two `▸` in `PLLConsequence.lean` are Prop-level, not data transport.**
  `:175` (`h ▸ List.mem_cons_self ..` in `extract`, with `h : ψ = φ`) rewrites
  inside a membership goal `ψ ∈ φ :: …`, which is a `Prop`.  `:235`
  (`hsub φ hφ ▸ of_mem …` in `bigOr_collapse`, with `hsub φ hφ : φ = χ`) rewrites
  inside `insert φ Γ ⊩ χ`, and `SetDeriv _ _ : Prop`.  Neither transports a
  `Type`-valued derivation.  **Verified** — consistent with the development's
  "no `▸`-transport of data" claim (the claim is about data, i.e. `Type`-valued
  `LaxND`; Prop rewrites are unrestricted and harmless).

* **Trusted surfaces to keep in mind.**  (a) The `decide` counter-models trust
  the kernel's reduction of `decForce` and the frame-condition `Decidable`
  instances — strong (no `native_decide`), but unchecked by me at the kernel
  level.  (b) `hilbert_to_ND` trusts the proof-checker's `isValid`/`isProofOf`
  semantics as the definition of "Hilbert-provable"; it is only half of Thm 2.3.
  (c) `PLLProof.lean` contains `#eval`/`Repr`/`test*` dev scaffolding
  (`:149–201`) that is not part of the metatheory.

* **No `sorry`/`admit`/`native_decide`** in the nine root-imported files
  (grep-verified); the legacy inconsistent systems are not reachable from any
  theorem in this report.  I did **not** run `lake build`; a clean build is the
  one remaining check I would run before signing off kernel-level.

---

### One-para bottom line

The formal statements say what their names claim, with a single caveat worth the
author's attention: `ConstraintModel.W : Type 0` makes `soundness` a `Type
0`-only statement (immaterial to every use, and it strengthens rather than
weakens completeness) — I would still make `W` universe-polymorphic so the
soundness theorem reads at full generality.  Everything else checks out:
`orElim` carries its major premise and matches F&M ∨-E; the truth lemma's
missing third clause is a genuine corollary of `Θ ⊆ Δ`; the canonical `F = {⊥ ∈
val}` provably equals F&M's singleton `F*` (a fact F&M themselves note); the
`disjOf`/guard machinery renders the `n+k ≥ 1` convention faithfully; and the
`decide` counter-models are kernel-checked with no `native_decide`.  The
substantive divergences (ND-with-membership over Gentzen sequents; Zorn over
enumeration; strong over weak completeness) are all method changes that reach the
same theorems, and the only irreducibly classical ingredient is Zorn in
Lindenbaum plus excluded middle in the maximal-theory lemmas — soundness, the
erasure, the counter-models, and the Hilbert bridge are constructive.
