# Uniform interpolation: the two live routes, and where each one bites

*Written 2026-08-08, after `docs/lax-logic-interpolation-handoff.md` reopened
the question. Companion to `docs/next-session.md` §1 (which records why the
nine-round campaign was shelved) and `docs/calculus-map.md` (which says which
calculus each claim is about). Nothing here is mechanised unless it says so.*

---

## 0. What changed

The handoff proposes a polarised/focused route. Separately, work on 2026-08-07
identified the ∨-free fragment of PLL with the **bounded nuclear implicative
semilattices** of Bezhanishvili–Bezhanishvili–Carai–Gabelaia–Ghilardi–Jibladze
(arXiv:2001.11060), and that paper's main theorem is that the variety is
**locally finite** (their Thm 6.18 for `NIS`, Thm 7.12 for the bounded case).

Putting those together splits uniform interpolation into two halves of very
unequal difficulty. That split is the main content of this note.

---

## 1. The split: `∃p` is free, `∀p` is the whole problem

Fix a finite set of variables. Write `L` for the ∨-free fragment (formulas
built from `⊥`, `∧`, `⊃`, `◯`; no `∨`), and `L_p` for its `p`-free part.

**`∃p φ` exists for ∨-free `φ`, by local finiteness.** By the handoff's
definition, `∃p φ` is the weakest `p`-free formula that `φ` entails — the
`p`-free summary of the antecedent. Consider

> `S = { ψ ∈ L_p : φ ⊢ ψ }`, taken up to interderivability.

By local finiteness of bounded NIS, `L_p` is **finite**, so `S` is finite.
Its conjunction `χ = ⋀S` is again `p`-free and again ∨-free, `φ ⊢ χ`, and
every `p`-free consequence of `φ` follows from `χ`. So `χ` *is* `∃p φ`, and it
exists for the reason that there are only finitely many candidates. No
construction, no proof search, no interpolation machinery.

**`∀p φ` is the hard half — but NOT for the reason first given here.**

*Corrected 2026-08-08, Matthew having declined to accept the first version.*
The first draft argued: `∀p φ` is a **join**, the ∨-free fragment is an
implicative semilattice with no joins, therefore `∀p` is inexpressible. That is
**wrong**, and the error is instructive. `L_p` is *finite* (local finiteness)
and has all finite meets and a top, so every subset has a least upper bound in
it — a finite meet-semilattice with `⊤` is automatically a lattice, indeed here
a finite Heyting algebra. `L_p` does have joins.

The real obstruction is that the join *internal to* `L_p` — call it `⊔`, the
least ∨-free upper bound — **overshoots** the true join `∨` of the ambient
algebra. Concretely, in the eight-element ∨-free algebra of Figure 6 the
antichain `¬¬◯⊥`, `◯¬◯⊥` has `⊔` equal to one of the third-layer elements,
whereas the genuine `¬¬◯⊥ ∨ ◯¬◯⊥` is strictly smaller and is not ∨-free.

So put `T = { ψ ∈ L_p : ψ ⊢ φ }`, finite. If `ψ₁, ψ₂ ∈ T` then
`ψ₁ ∨ ψ₂ ⊢ φ`, but `ψ₁ ⊔ ψ₂` may not, since `⊔` sits above `∨`. Hence `T`
need not be closed under `⊔`, and `max T` — which is what `∀p φ` must be —
need not exist. Precisely:

> **`∀p φ` exists in the ∨-free fragment iff `T` is directed.**

That is a checkable criterion rather than an impossibility, and it is the right
statement of where the difficulty lives. It is still asymmetric with `∃p`,
because `S = { ψ : φ ⊢ ψ }` *is* closed under `∧` and `∧` preserves
∨-freeness, which is why `∃p` goes through unconditionally.

**Why this is more than bookkeeping.** It matches everything else found in the
closed fragment on 2026-08-07: RN(◯,{}) is infinite but its ∨-free part has
exactly eight elements; the booleanization `𝔟⊥` has exactly four; adding a
nucleus preserves local finiteness for `∧,⊃` and destroys it for `∧,∨,⊃`
already at zero generators. In every one of these, **`∨` is the source of the
infinitude**. The conjecture this suggests is that `∨` is also the source of
the interpolation difficulty, and that `◯` — long treated as the villain — is
not.

### What to do with it

1. **Check the `∃p` argument properly.** It is three lines of algebra on top of
   someone else's theorem, which is exactly the shape of claim this project has
   been burned by (`docs/llm-formalisation-case-study.md`: the failures were
   *statement* failures). Machine-check it, or find the reason it is wrong.
2. **State the residue.** If `∃p` is free, uniform interpolation for PLL
   reduces to the existence of `∀p`, i.e. to expressing certain finite joins.
   That is a much smaller target than the general problem.
3. **PCLL as the fallback is now motivated, not merely optimistic.** PCLL adds
   `◯(A∨B) ⊃ (◯A∨◯B)` and is complete for mutually confluent models
   (`derivU_iff_confluent_valid`). Since the difficulty has been localised at
   `∨`, an axiom governing `◯` *over* `∨` is aimed at the right thing.

---

## 2. The polarised route: what is settled and what is not

Verified 2026-08-08, machine-checked parts in `wip/polarity.lean`.

* `◯` is **negative** in the two-judgment Pfenning–Davies setting, as the Twelf
  `lax-logic` development declares (`circ : prop pos → prop neg`). Its `circR`
  is invertible because the premise is `P lax`, not `P true`.
* In our **single-judgment** `SC`/`LaxND` the corresponding inversion
  `Γ ⊢ ◯A ⟹ Γ ⊢ A` is **false** (`box_right_not_invertible`, `[propext,
  Quot.sound]`). So the negative assignment is bought entirely by the second
  judgment. Polarities cannot be painted onto the existing calculus; the
  two-judgment structure has to be adopted first.
* `◯`-left inversion **is** available unrestricted in the succedent, via the
  unit (`box_left_invertible`, `[propext]`). So `SC`'s `laxL` goal-restriction
  is a property of the rule, not a semantic necessity.
* The handoff's "real monster" — `◯`-left firing only when the goal is
  `◯`-shaped — becomes, in the target, `circL`'s succedent being `A lax`. A
  condition on the **shape of the succedent formula** becomes a condition on
  **which judgment we are in**, and a judgment is what a focusing phase
  tracks. This is the mechanism by which polarisation could dissolve the
  entanglement.
* `circL` **retains** `◯P` in its premise, exactly as `G4c`'s three retention
  repairs do. The "contraction by the back door" is already present, and
  already tamed, in the target.

**Caveats on the references.** Twelf proves cut admissibility in the target,
**not** focusing completeness. Simmons's *Structural focalization* covers
propositional **intuitionistic** logic only — no modality — and the part he
calls his major contribution is *identity expansion*, which is therefore the
part most likely to be the work. **None of the three references concerns
interpolation**; step 3 of the handoff's programme has no precedent in them.

---

## 3. Matthew's contraction-bound route (2026-08-08)

> Can one determine, purely by inspecting the antecedent, a bound on the number
> of contractions needed in backwards search? If so, pre-expand the antecedent
> by that many duplicates and prove uniform interpolation for the expanded
> antecedent.

This attacks the handoff's core diagnosis head-on. The diagnosis was that
contraction tracking is **proof-dependent**, which is what uniform
interpolation forbids. A bound computed from the antecedent alone is
**proof-independent** by construction, so if it exists the objection
evaporates.

**What is already known.** The separating sequent
`◯((◯p→r)→◯p), ◯p→r ⇒ r` needs exactly **2** copies of `◯p→r`
(`PLLG4Gap.lean`); the naive tower also needs only 2 (`PLLG4Tower.lean`).
Whether any sequent needs **3** is open, and is HANDOFF §7 item 5 — the
multiplicity-3 hunt, untouched since it was written.

**Why the bound should track `◯`, not size.** `G4c` is a *localization*
result: all contraction that remains lives in the `◯`-rules, absorbed by the
three retention repairs (`docs/calculus-map.md`). So the natural conjecture is

> `mult(Γ) ≤ f(number of ◯-occurrences in Γ)`,

not a function of `|Γ|`. The cheapest possible version, consistent with all
present evidence, is `mult(Γ) ≤ 2` outright.

**The stake.** If `mult` is computable from `Γ`, pre-expansion yields a
terminating analytic calculus in which no contraction is needed. That is close
to a refutation of Howe's conjecture that lax logic admits no contraction-free
calculus — a conjecture this repository has so far *supported* (HANDOFF §4;
`PLLG4Gap` shows contraction is inadmissible in Iemhoff's `G4iLL`, which is the
evidence *for* Howe). So the route is not a safe fallback: it is a bet against
a standing conjecture, and its failure would be informative in its own right.

### 3.1 Two escalation families, both refuted — and the reason

*2026-08-08. Matthew's instruction: "your task is to prove rather than search;
the interplay is delicate and you tend towards brute force." Both results below
are structural, and the second needed no computation at all.*

**Why the gap needs exactly 2.** With `F = ◯p ⊃ r` and goal `r`, the boxed
hypothesis `◯(F ⊃ ◯p)` can only be used by `laxL`, which fires **only when the
goal is `◯`-shaped**. The goal is `r`. So one copy of `F` is spent *converting
the goal*: `→L` on `F` replaces goal `r` by goal `◯p`. Only then can `laxL`
strip the box, yielding `F ⊃ ◯p`, and firing that needs a **second** copy. The
count decomposes as **one goal-conversion + one use inside the box**.

**Family A — nest the scopes** (`wip/multiplicity.lean`, computed).
`K 0 = ◯p`, `K (n+1) = ◯(F ⊃ K n)`; test `K n, Fᵏ ⇒ r`. Measured least `k`:

    K 0 → 1     K 1 → 2     K 2 → 2     K 3 → 2

Refuted. The reason: once inside the modal phase the goal **stays** `◯`-shaped,
so no further conversion is demanded, and the copies available inside are
shared across the layers. This is also why `PLLG4Tower.lean`'s naive tower caps
at 2.

**Family B — Matthew's recursion** (`F(n+1) = ◯G(n) ⊃ r`). Refuted **by
inspection, not by search**: `F(n+1)` is again an implication with a boxed
antecedent and conclusion `r`, so `[◯(F(n) ⊃ ◯p), F(n)] ⇒ r` is the gap's own
shape for every `n` — the same two roles, hence the same two copies. Nesting
the *conversion* fails for the same reason as nesting the *host*.

### 3.1a WHICH CALCULUS — the check that undercuts §3.1

*Matthew, 2026-08-08: "are you using the right decision procedure? G4??"  He is
right to ask, and the answer is that it is right for the datum and wrong for
the purpose.*

`PLLDecide` decides **`G4`** — Iemhoff's naive calculus, the **incomplete**
one. That is deliberate and protected: HANDOFF §8 says do not "fix" it, since
deciding `G4`-original is its job in the refutation, and it does **not** decide
PLL. So every number in §3.1 is a fact about `G4`.

The contraction-bound route, however, is about the search the interpolant
construction would actually run over, and that is **`G4c`** — the tables
`itpE`/`itpA` are over `G4c` (`docs/calculus-map.md`). In `G4c` contraction is
**already admissible cut-free** (`G4c.contract`), absorbed into the three
retention rules. So "how many copies does the antecedent need" is not the right
question there at all: the answer is none, and the multiplicity has been
**hidden inside the rule shapes** rather than removed — which is exactly the
localisation HANDOFF §4 insists is *not* a refutation of strong Howe.

Consequences, and they matter:

* the two refutations in §3.1 stand, but they are statements about `G4`;
* the conjecture in §3.2 is likewise about `G4`, and is therefore **not**
  directly the bound the route needs;
* the *right* formulation of Matthew's idea over `G4c` is not a count of
  antecedent copies but a bound on **how often the retention rules re-use a
  formula along a branch** — and that is a property of derivations, which
  returns us to the handoff's proof-dependence problem rather than escaping it.

Restating the route over `G4c` is therefore the first thing to do, before any
more measurement. Until that is done, §§3.1–3.2 are about the wrong object.

### 3.2 The conjecture this forces (about `G4`, see §3.1a)

> **Multiplicity in `G4` is capped at 2.**

Reason, not evidence: the intuitionistic part of `G4iLL` is Dyckhoff-style and
already contraction-free, so `◯` is the only source of contraction; the `◯`
demand is the goal-conversion; and **at most one goal-conversion is ever
needed**, the outermost, because inside the modal phase goals remain
`◯`-shaped.

**If true**, Matthew's contraction-bound route works immediately with the
constant 2 — pre-duplicate every antecedent formula once and search
contraction-free — and Howe's conjecture that lax logic admits no
contraction-free calculus is in serious trouble. Given that this repository has
so far *supported* Howe (`PLLG4Gap` shows contraction inadmissible in Iemhoff's
calculus, which is evidence **for** him), that is a claim to attack rather than
to hope for.

**If false**, the witness must break the phase-sharing, and no nesting
construction can do that — the two refuted families show why. It would need
two goal-conversions genuinely separated by a non-modal step, which is a
specific structural demand and the thing to design against.

**How to settle it, without sweeping.** `PLLG4Gap`'s `not_S0`…`not_S5` chain is
the model: G4-underivability proved by exhaustive case analysis on the rules,
each branch either impossible or reduced to a smaller refutation, with the
bottom case (`not_S5`) failing precisely because a needed *occurrence* is
absent. Multiplicity is a resource count, and that chain is where the count is
visible. Generalising that invariant — rather than deciding instances — is the
proof obligation.

---

## 4. Suggested order

1. **Machine-check the `∃p`-from-local-finiteness argument** (§1). Cheapest,
   and it either halves the problem or exposes a statement error early.
2. **Multiplicity-3 hunt** (§3). Cheap, uses existing tooling, settles whether
   the contraction-bound route starts at `2`.
3. **Polarised syntax, two judgments, translation, cut admissibility** (§2) —
   the Twelf port. This is the first substantial build.
4. **Identity expansion** for the focused lax system. The risk.
5. **Interpolant by recursion on phases.** No precedent; only attempt after 3
   and 4.

Steps 1 and 2 are days; 3 is a session or two; 4 and 5 are the research.

---

## 5. Standing constraints that apply here

* The machine-checked mandate: anything in §1 or §3 that is to stand in a paper
  needs a `sorry`-free Lean proof with a pinned `#print axioms`. The arguments
  above are **prose**, and §1 in particular is exactly the kind of short
  algebraic claim that has misled this project before.
* `lake build` does **not** check `wip/`; use `lake build wipshared`
  (`docs/belief-mechanisation-index.md`).
* Do not claim Howe refuted, or PLL-UI settled either way, anywhere
  (HANDOFF §8).

---

## 6. Built so far, and the next obstacle located (2026-08-08)

### Done, in the library, sorry-free

| file | content | audit |
|---|---|---|
| `LaxLogic/PLLJudgmental.lean` | two-judgment PLL (`true`/`lax`), `rename`, `erase`, soundness both judgments, **completeness**, `equiv_nd`, `equiv_lax` | **no axioms at all** |
| `LaxLogic/PLLPolar.lean` | polarised syntax `Pos`/`Neg` with `circ : Pos → Neg`, erasure, `polPos`/`polNeg`, roundtrip, `phase` | `[propext]` / axiom-free |
| `wip/polarity.lean` | `box_right_not_invertible`, `box_left_invertible` | `[propext, Quot.sound]` / `[propext]` |

Two findings worth keeping from the build:

* **`CircInvert` was free.** The plan was to assume `PD .tru Γ ◯φ → PD .lax Γ φ`
  as an explicit hypothesis and discharge it later by normalisation. It is
  `circE` with the identity continuation — the monad law `bind m return = m`.
  So completeness of the judgmental system is unconditional and step 1 carries
  no debt.
* **The phase measure is proof-independent for free, and that is not the
  content.** `phase : PLLFormula → ℕ` obviously does not depend on a
  derivation. The programme needs the *other* half — that the interpolant
  recursion **descends** on it — and nothing built so far bears on that.

### The next obstacle, precisely

Focusing needs three judgments: right focus `Γ ⊢ [P]`, left focus
`Γ ; [N] ⊢ Q`, and inversion `Γ ; Ω ⊢ N`. The rules for `∨`, `∧`, `⊃` and the
shifts are standard. **`◯` is not**, and the reason is the same one that has
been shadowing this problem throughout:

> Left-focusing on `◯P` may only fire when the stable goal is **lax**.

In `SC` that appeared as "the succedent must be `◯`-shaped". In the judgmental
system it became "the conclusion is in the `lax` judgment", which was progress
because a judgment is a phase. But in the *focused* system the stable goal is a
parameter of the left-focus judgment, so the consequence is concrete:

> **the stable goal must carry the judgment flag** — the focused judgments are
> `RFoc : List Neg → JD → Pos → Type`, `LFoc : List Neg → Neg → JD → Pos → Type`,
> `Inv : List Neg → List Pos → JD → Neg → Type`,

and the `◯` rules are the only ones that change it. That is a design decision
with consequences for every subsequent proof (soundness, focalization, identity
expansion), so it is recorded here before being committed to code rather than
discovered halfway through a soundness induction.

**Why this is not merely bookkeeping.** If the flag threads through
untouched by every rule except `◯`'s, then the phase structure genuinely
separates the modal content, and the interpolant recursion has two smaller
things to descend on rather than one — which is exactly the handoff's bet
("because the Lax modality is a box-then-diamond composite, it may give two
smaller pieces to descend on"). If instead the flag has to be inspected by the
`⊃` or `∨` rules, the separation fails and the polarised route inherits the
entanglement it was meant to dissolve. **Which of these happens is the next
thing to determine, and it is a question about the rules, not a search.**

### Order from here

1. Write the three focused judgments with the `JD` flag; check by inspection
   whether any rule other than `◯`'s must read it.
2. Soundness into `PD` — mechanical, one induction.
3. Focalization (completeness). State as an explicit hypothesis if costly;
   `wip/polarity.lean` and Simmons both say identity expansion is the risk.
4. Only then the interpolant recursion.
