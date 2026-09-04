# Mechanising the RN classification: im(h) = rungs ∪ {⊤}

*2026-08-02, plan written before execution.  Discharges the standing
caveat on `q5_not_any_rung`, `chain_not_any_rung`, `complement_infinite`.*

## The statement

For every ◯-free formula `A` in the single variable `p`:

    ∃ n, Interd (embed A) (rnSub n)      or      Interd (embed A) q1.

With it, "interderivable with no rung and not ⊤" becomes `∉ im h`
outright, for `q5`, `◯q11`, and the whole chain at once
(`Interd` is symmetric and transitive, so a class matching `embed A`
would match a rung or `⊤`).

## The route: classify by ladder truth set, derive by schema

**Up-sets of the ladder are exactly the rung truth sets plus ℕ.**
If an up-set `S` contains arbitrarily large `w` it contains `[0, w−2]`
for unboundedly many `w`, hence is ℕ.  Otherwise `S` is one of

    ∅ = T(rn 0),   O_a = [0,a] = T(rn(2a+1)),   E_a = [0,a−1] ∪ {a+1} = T(rn(2a+2)).

So codes: `UpCode ::= rung n | top`, with `memC (rung n) = rungMem n`,
`memC top = ⊤`.

**The tables** (worked out here so implementation is transcription;
`⊥ = rung 0`, and the ℕ-truncation `2·0−1 = 0` makes the `b = 0`
degenerate cases come out right by themselves):

meet (symmetric; ⊥ absorbs, top neutral):
* `O_a ∧ O_b = O_min(a,b)`
* `O_a ∧ E_b` : `a ≤ b−1 → O_a`;  `a = b → rung(2b−1)`;  `a ≥ b+1 → E_b`
* `E_a ∧ E_b` (a ≤ b) : `b ≥ a+2 → E_a`;  `b = a+1 → rung(2a−1)`;  `a = b → E_a`

join (⊥ neutral, top absorbs):
* `O_a ∨ O_b = O_max(a,b)`
* `O_a ∨ E_b` : `a ≥ b+1 → O_a`;  `a = b → rung(2b+3)`;  `a ≤ b−1 → E_b`
* `E_a ∨ E_b` (a < b) : `b ≥ a+2 → E_b`;  `b = a+1 → rung(2a+5)`;  `a = b → E_a`

imp (`c ⊃ d`): `top` whenever `T(c) ⊆ T(d)` (decidable by index
arithmetic); `top ⊃ d = d`; otherwise compute
`T(c→d) = { w : ↑w ∩ T(c) ⊆ T(d) }` per parity pair — to be filled in
by the `memC` arithmetic during implementation, with the low cases
already checked by hand: `¬O_0 = E_0`, `¬O_a = ⊥ (a ≥ 1)`,
`¬E_0 = E_1`, `¬E_1 = E_0`, `¬E_a = ⊥ (a ≥ 2)`,
`O_{b+1} ⊃ O_b = E_{b+1}` (definitional), `O_a ⊃ O_b = O_b (a ≥ b+2)`.

**The schema derivations.**  The easy sides are all rung-order
(`rungD := (rnSub_order _ _).mpr`, over index lemmas in the style of
`odd_chain`).  The hard sides each collapse in ≤ 4 steps through the
RN recursion — worked examples that fix the pattern:

* `rn(2k+3) ∧ rn(2k+4) ⊢ rn(2k+1)`: modus ponens of the conjuncts
  (`rn(2k+4) = rn(2k+3) ⊃ rn(2k+1)` definitionally).
* `rn(2b+5) ⊢ rn(2b+2) ∨ rn(2b+4)` (the `E ∨ E` join): unfold
  `O_{b+2} = O_{b+1} ∨ E_{b+1}`, then `O_{b+1} = O_b ∨ E_b`; the
  `E`-branches inject, the `O_b`-branch goes by rung order
  `O_b ≤ E_{b+1}`.
* `(O_{b+2} ⊃ O_b) ⊢ O_b`: from the hypothesis `H` derive
  `E_{b+1} = O_{b+1} ⊃ O_b` (assume `O_{b+1}`, weaken to `O_{b+2}`
  by rung order, apply `H`); inject `E_{b+1}` into `O_{b+2}`, apply
  `H` again.  `(O_a ⊃ O_b) ⊢ O_b` for `a ≥ b+2` follows by weakening
  the antecedent (contravariance over rung order).

## Stages, each pushed on completion

1. **This document.**
2. `wip/rnClass.lean` part 1 — `UpCode`, `memC`, the three tables,
   and their pointwise correctness over the ladder:
   `memC_meet`, `memC_join`, and `memC_imp`
   (`memC (impC c d) w ↔ ∀ y ≥ w, memC c y → memC d y`) — pure
   arithmetic, `omega`-driven, no logic.  The imp table is the bulk.
3. `cls : PLLFormula → UpCode` (structural recursion over the tables)
   and `sat_cls : boxFree A → varsP A → (ladder.sat A w ↔ memC (cls A) w)`.
4. The schema derivations and the three `Interd` table lemmas
   (`meet_lemma`, `join_lemma`, `imp_lemma`), glued by `rungD` and the
   congruence lemmas (`Interd.and_congr` etc., already in the library).
5. `rn_classification : boxFree A → varsP A →
   Interd (embed A) (embed (toF (cls A)))` by induction with the
   congruences; then the caveat dischargers:
   `q5` and `chainF k` off the image simpliciter, and
   `complement_infinite` restated without caveat.

Risk ledger: the imp-table arithmetic is the fiddly part (the gap in
`E_a` makes the Heyting implication's case split delicate); the
derivations are short but must be written longhand.  If a session
boundary interrupts, resume from the stage list — each stage compiles
and pushes independently.

---

## Postscript, 2026-08-03: all five stages landed

Stages 2–3 in `wip/rnClass.lean`, stages 4–5 in `wip/rnClassify.lean`;
sorry-free, axiom audits pinned at `[propext, Classical.choice,
Quot.sound]` throughout.  The final statements:

    rn_classification : boxFree A → onlyP A →
        Interd (embed A) (toS (cls A))
    image_classification : boxFree A → onlyP A →
        (∃ n, Interd (embed A) (rnSub n)) ∨ Interd (embed A) q1

and the caveat dischargers, now unconditional:

    q5_off_image              : ¬ InImage q5
    boxq11_off_image          : ¬ InImage (q11.somehow)
    chain_off_image  (k ≥ 2)  : ¬ InImage (chainF k)
    complement_infinite_final : the chainF k (k ≥ 2) are pairwise
                                distinct and all off the image

where `InImage X := ∃ A, boxFree A ∧ onlyP A ∧ Interd X (embed A)`.

Two deviations from the plan as written.  (1) The codes kept `bot /
odd a / even a / top` rather than `rung n | top`; the parity split is
what the tables case on, so it is the right normal form.  (2) The
implication table needed one more row than the sketch (`E_a ⊃ O_b`
splits four ways, not three); the ℕ-truncated recursion equation
`rnSub (2a+2) = rnSub (2a+1) ⊃ rnSub (2a−1)` (valid at `a = 0` as
`¬◯⊥ = ◯⊥ ⊃ ⊥`) let every degenerate case share the general
derivation, exactly as hoped.

A dividend: `Interd q11 (rnSub 7)` (hence `◯q11 ≡ chainF 3`) fell out
as an *instance* of `rn_classification` at `A = ¬¬p ∨ (¬¬p ⊃ p)`, with
`cls A = odd 3` computed by `decide` — the classification is already
paying for itself as a decision procedure for the ◯-free fragment.
