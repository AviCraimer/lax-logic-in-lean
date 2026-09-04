# Strictness of the ◯-chain at every step: the plan

*2026-08-02, written before execution, as documentation not for approval.*

## The statement to be proved

Write `c_k := ◯(rn(2k+1)[p := ◯⊥])` for the boxed odd rungs — so
`c_1 = ◯rn3 ≡ q5`, `c_2 = ◯rn5 ≡ q12`, `c_3 = ◯rn7 = ◯q11`, the chain
whose first three strict steps are already certified one at a time.
The goal is both halves at **every** index:

    (≤)  c_k ⊢ c_{k+1}                 for all k
    (≠)  c_{k+1} ⊬ c_k                 for all k

together with the consequences: `c_j ⊢ c_k` and `c_k ⊬ c_j` for all
`j < k`, hence the `c_k` are pairwise non-interderivable — an infinite
strictly ascending chain of boxed classes in RN(◯,{}).

## Why concrete countermodels cannot do this

Every refutation so far in this development is a single finite model
checked by `decide`.  That method proves one instance per model.  Here
the instances are indexed by `k`, and no fixed finite model can refute
all of them: a model with `N` worlds has at most `2^N` candidate truth
sets, so the sequence of force-sets of the `c_k` in it must repeat,
and from a repetition the model validates some step `c_{k+1} ⊢ c_k`.
The sizes of any refuting models must grow with `k`.  So the proof
must quantify over a **family** of models — equivalently, evaluate one
**infinite** model — and establish the forcing facts by induction and
arithmetic rather than by computation.  The bridge from semantics to
`⊬` is soundness alone; completeness is never needed for refutation.

## The terms

**Constraint model** (Fairtlough–Mendler, `PLLKripke.lean`): a set of
worlds `W`; a preorder `Rᵢ` (intuitionistic accessibility); a
reflexive transitive `Rₘ ⊆ Rᵢ` (the modal step); an `Rᵢ`-upward-closed
set `F` of *fallible* worlds, which force every formula, `⊥` included;
a hereditary valuation.  Forcing is the standard intuitionistic
clauses plus

    w ⊨ ◯N   iff   for every v with w Rᵢ v there is u with v Rₘ u and u ⊨ N.

**Soundness** (`PLLKripke.soundness`, sorry-free): a natural-deduction
derivation of `Γ ⊢ φ` forces `φ` at every world of every constraint
model forcing `Γ`.

**The ladder skeleton** (`rnEmbed.ladder`): worlds `ℕ`;
`le w v ↔ v = w ∨ v + 2 ≤ w` (each world sees itself and everything at
least two below); `U = {0}`.  On it the ◯-free rungs have the truth
sets already pinned by `sat_rn_odd` / `sat_rn_even`:

    T(rn(2k+1)) = { w : w ≤ k },      T(rn(2k+2)) = { w : w < k } ∪ {k+1}.

**The abyss lift** (`Skel.cm`): any skeleton `S` becomes a constraint
model on `Option S.W` by adding one fallible world `none` above
everything, with `Rₘ` = identity on the skeleton plus `w ⇝ none`
exactly for `w ∈ U`.  Two facts are already proved for it:
`force_oBot` (the truth set of `◯⊥` on the skeleton part is exactly
`U`) and `Skel.transfer` (for ◯-free `A`, the lift forces
`A[p := ◯⊥]` at `some w` iff the skeleton IPC-forces `A` at `w`).  So
on the lifted ladder every `rnSub n` wears its rung truth set.

## The two computations that constitute the proof

**Step 1 — how ◯ evaluates on any abyss lift.**  At a skeleton world
the only `Rₘ`-moves are staying put or (from `U`) jumping to the
fallible top, which forces everything.  Unwinding the ◯-clause:

    some x ⊨ ◯N   iff   for every y ≥ x :  y ∈ U  or  some y ⊨ N.       (†)

This is `Skel.box_force` below, proved once for all skeletons and all
`N` — the induction Matthew asked for lives here and in the transfer
lemma it composes with.

**Step 2 — the refutation at world `k+1`.**  On the lifted ladder,
with `N = rnSub m`, (†) plus the transfer reads: `some x ⊨ c`-style
boxes iff every `y ∈ ↑x` is `0` or lies in `T(m)`.  Take
`x = k + 1`, whose cone is `↑(k+1) = {k+1} ∪ [0, k−1]`:

* `◯rnSub(2k+3)`: every `y` in the cone has `y ≤ k+1`, and
  `T(2k+3) = [0, k+1]` — **forced**;
* `◯rnSub(2k+1)`: the point `y = k+1` is neither `0` nor `≤ k` —
  **not forced**.

Soundness then refutes `c_{k+1} ⊢ c_k`.  The positive half is
◯-monotonicity (a two-line derivation) over `odd_chain`
(`rungLe (2k+1) (2k+3)`, pure arithmetic, already in `ladder8`), and
the pairwise versions follow from single steps by cut.

## What this model deliberately cannot see

On any abyss lift, (†) forces `T(◯N)` on the skeleton part to be
`T(N)` itself (the point `x` belongs to its own cone), apart from the
`U`-escape.  So this model will never separate `◯rnSub m` from
`rnSub m` — which is consistent with history: those separations
(`q5 ≠ q4`, `◯q11 ≠ q11`) each needed a five-world model with an
`Rₘ`-edge *between distinct infallible worlds*, something `rmL` does
not have.  The strictness theorem needs no such separation, which is
exactly why this lift suffices for it.

## What comes next, stated as a construction (not yet carried out)

The complement-infinitude question needs, beyond strictness, that each
`c_k` is off the ladder image at every `k` — the general-`k` analogue
of `q5_not_any_rung`.  The missing ingredient is a *second* lift: the
ladder with one added internal `Rₘ`-edge `(k+1) ⇝ 0`.  At `k+1` this
makes `◯rnSub(2k+1)` true while `rnSub(2k+1)` stays false — the
general-`k` version of the `◯q11` countermodel.  The side condition to
maintain is `force_oBot` (the added edge must not enlarge `T(◯⊥)`);
for `k ≥ 2` the world `1` witnesses that it does not.  CONJECTURED
here, to be attempted after the main theorem lands:
`◯rnSub(2k+1) ⊬ rnSub(2k+1)` for all `k ≥ 2`, by that lift.

## Discipline

Everything below is to be sorry-free with pinned axiom audits;
searcher output, if any is used, enters only as kernel-checked pinned
terms.  PROVED / REFUTED / OPEN kept distinct throughout; the
conjecture above stays labelled OPEN until the second lift is built.

---

## Postscript, same evening: both parts landed

`wip/chainStrict.lean` (the main theorem) and `wip/chainOff.lean` (the
second lift) both compiled on first attempt, sorry-free, audits
pinned.  The second lift needed one design change from the sketch: the
edge sits at `k+3 ⇝ 0` rather than `k+1 ⇝ 0`, which removes all side
conditions on `k` (the `force_oBot` witness is world `1`, present as
soon as the edge world is ≥ 3).  The off-image argument simplified
further than planned: no `q5`-style squeeze is needed — on the plain
abyss lift `chainF k` wears the truth set `[0,k]`, so an
identification with any rung forces `n = 2k+1` via `rnSub_deriv_iff`
and `rn_pairwise_pll`, and that one identification is what
`box_not_fix` refutes.  Result:

    complement_infinite : for every k ≥ 2, chainF k is interderivable
    with no rung and not with ⊤; the chainF k are pairwise distinct.

So RN(◯,{}) ∖ im h is infinite, modulo the standing caveat that the
classical classification of the one-variable fragment (im h = rungs
∪ {⊤}) is not yet mechanised.  Mechanising that classification is now
the single remaining gap between "interderivable with no rung and not
⊤" and "off the image" simpliciter, for everything: `q5`, `◯q11`, and
the whole chain.
