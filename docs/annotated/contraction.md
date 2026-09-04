# Contraction for G4iLL″, cut-free

Source: `LaxLogic/PLLG4HCtr.lean`. Two theorems are read here:
`G4h.contract_atom` (height-preserving contraction of an atom, the
pilot case) and `G4c.contract_bounded`/`G4c.contract` (full
contraction for an arbitrary formula, with **no cut anywhere in the
proof**). Extraction method and abbreviation conventions:
`docs/annotated/README.md`. Design history of the calculus these
proofs run over — three revisions, the last forced by a nucleus
countermodel — `docs/g4p-ladder.md`.

## The calculus

`G4h : Nat → List PLLFormula → PLLFormula → Prop` (`PLLG4H.lean:49`)
is G4iLL (Iemhoff's contraction-free calculus for PLL) height-indexed
in the manner of this repository's `SCh`, with two rules revised
against the textbook G4 shape. The revision that matters for
contraction is that both rules touching the lax modality **keep** the
hypothesis they act on, rather than trading it for its content:

```
Γ, ◯χ, χ ⇒ ◯B                        Γ, ◯χ, ◯φ→ψ, χ ⇒ ◯φ    Γ, ◯χ, ψ ⇒ Δ
-------------- laxL                  ------------------------------------ L◯→″
Γ, ◯χ ⇒ ◯B                                    Γ, ◯χ, ◯φ→ψ ⇒ Δ

Γ, ◯φ→ψ ⇒ φ    Γ, ψ ⇒ Δ
------------------------ R◯→″
Γ, ◯φ→ψ ⇒ Δ
```

`laxL` is G3iLL's `L◯` exactly; `L◯→″`'s first premise keeps both the
box `◯χ` and the implication `◯φ→ψ`, adding only the opening `χ`;
`R◯→″`'s first premise keeps the whole conclusion context, matching
G3's `L⊃` premise-1 discipline (this is design revision 3 — an earlier
form that *consumed* `◯φ→ψ` in `R◯→`'s first premise admits a
counterexample to the contraction case it would need, in a Heyting
algebra with nucleus; see `docs/g4p-ladder.md` §"Design revision 3").
The working judgment is `G4c Γ C := ∃ n, G4h n Γ C`
(`PLLG4H.lean:97`) — derivability at *some* height, which is what the
two contraction theorems below conclude.

## `G4h.contract_atom`

### Statement

```lean
theorem contract_atom {p : String} :
    ∀ {n : Nat} {Γ' : List PLLFormula} {E : PLLFormula}, G4h n Γ' E →
    ∀ {Γ : List PLLFormula}, Γ'.Perm (prop p :: prop p :: Γ) →
    G4h n (prop p :: Γ) E
```

In words: if `Γ'` is some permutation of `p, p, Γ` (two occurrences of
an atomic formula `p` alongside a remainder `Γ`) and `G4h n Γ' E`
holds, then the single-copy context `p :: Γ` derives `E` **at the same
height** `n`. This is the atomic base case that the (separately
mechanised) additive cut theorem's `init` case consumes; it is proved
before, and independently of, the general theorem below.

### Proof architecture

Plain structural induction on the derivation `d : G4h n Γ' E` — no
weight induction is needed because atoms cannot be the *principal*
formula of any left rule other than `init` (whose conclusion mentions
them directly) and `impLProp`'s side condition (whose membership
premise mentions them, but which is not principal on `p` itself in the
generic case). Every other rule's principal formula is compound, so
`p, p` always travel together into every premise as *two* spectator
copies, and the case reduces to permutation bookkeeping: locate the
two designated copies via `cross_split`, recurse, and permute the
single surviving copy back to the front. The two private lemmas
`push2` and `pushL` package the recurring "push a fresh head past the
two copies" and "push a block of new heads past the two copies"
permutation shuffles that every rule case needs once for each
new context entry its premise introduces.

### Key stages with snapshots

**The `laxL` case — the box-keeping payoff, atomic level.**
Anchor: `PLLG4HCtr.lean:88` (immediately after `intro Γ hp`, entering
the case for `G4h`'s `laxL` constructor).

```
case laxL
p : String
n : ℕ
Γ' : List PLLFormula
E : PLLFormula
n✝ : ℕ
Γ✝ : List PLLFormula
A B✝ : PLLFormula
h : A.somehow ∈ Γ✝
a✝ : G4h n✝ (A :: Γ✝) B✝.somehow
ih : ∀ {Γ}, (A :: Γ✝).Perm (prop p :: prop p :: Γ) → G4h n✝ (prop p :: Γ) B✝.somehow
Γ : List PLLFormula
hp : Γ✝.Perm (prop p :: prop p :: Γ)
⊢ G4h (n✝ + 1) (prop p :: Γ) B✝.somehow
```

`laxL`'s premise is `G4h n✝ (A :: Γ✝) B✝.somehow` — the *whole*
conclusion context `Γ✝` plus the opened witness `A`, because `laxL`
keeps its box (`h : A.somehow ∈ Γ✝`, not consumed). The two atom
copies are therefore still present in the premise context exactly as
they were in the conclusion, so `ih` can be invoked at `hp` transported
past the fresh head `A` (`push2`) with no other bookkeeping: this case
never has to reason about whether one of the two `p` copies *is* `A`,
because `A.somehow` and `prop p` are never equal formulas. Compare the
`impLLaxLax` case of the *general* theorem below, where a genuine
formula-vs-atom disjointness argument would be needed if the same
design point were not doing the same job one level up.

## `G4c.contract` / `G4c.contract_bounded`

### Statement

```lean
theorem contract_bounded : ∀ (w : Nat) {A : PLLFormula}, A.weight ≤ w →
    ∀ {n : Nat} {Γ' : List PLLFormula} {E : PLLFormula}, G4h n Γ' E →
    ∀ {Γ : List PLLFormula}, Γ'.Perm (A :: A :: Γ) → G4c (A :: Γ) E

theorem contract {Γ' Γ : List PLLFormula} {A E : PLLFormula}
    (d : G4c Γ' E) (hp : Γ'.Perm (A :: A :: Γ)) : G4c (A :: Γ) E
```

In words: two occurrences of an arbitrary formula `A` in a derivable
sequent collapse to one — full contraction, for every connective and
for the lax modality, stated first with an explicit weight bound `w`
(`contract_bounded`, whose induction needs the bound as a slack
variable) and then specialised to `contract` at `w := A.weight`. This
is the Dyckhoff–Negri-style admissibility result: contraction is
proved *before* cut, and the proof of `contract_bounded` uses no cut
theorem, no self-absorption lemma, nothing beyond induction and the
inversions of `PLLG4HInv.lean`.

### Proof architecture

Two nested inductions, exactly as the brief for this document
anticipates:

* **Outer: induction on `w`, a `Nat` bound with `A.weight ≤ w`.**
  Plain `Nat` induction suffices — no well-founded recursion on
  `PLLFormula` weight is needed — because every appeal to the
  induction hypothesis `ihw` in a principal case is at a *strictly
  smaller* weight than `A.weight`, and `A.weight ≤ w` gives that
  smaller weight a comfortable slack against `w` itself: `omega`
  closes every side condition of the form "the immediate subformula's
  weight is `≤ w`" directly from `hA : A.weight ≤ w + 1` after
  unfolding `PLLFormula.weight` at the principal formula. The `zero`
  case is vacuous (`weight_pos` gives `0 < A.weight`, contradicting
  `A.weight ≤ 0`).
* **Inner: structural induction on the derivation** `d : G4h n Γ' E`,
  *for a fixed* `w`/`ihw`. Every left-rule case first asks
  `cross_split3` (a three-way disjoint-or-overlapping-context lemma,
  the general-formula analogue of `contract_atom`'s `cross_split`)
  whether the rule's own principal formula *is* one of the two
  designated copies of `A` (the **principal** branch) or lives beside
  them (the **parametric** branch, closed by `ih`/`ih₁`/`ih₂` plus
  permutation bookkeeping exactly as in `contract_atom`).

The principal branch is where the mathematical content lives, and it
splits into three families:

1. **IPC-style principal cases** (`andL`, `orL`, `impLProp`,
   `impLAnd`, `impLOr`): invert the *surviving* copy of the rule's
   principal formula against its one derivation `d₁` (`PLLG4HInv.lean`'s
   height-preserving master inversion), then contract the exposed
   subformula pieces, which are strictly lighter by `A.weight`'s
   definition (`PLLG4.lean:63`, e.g. `(A.and B).weight = A.weight +
   B.weight + 2`). This is Dyckhoff–Negri verbatim for the
   propositional fragment.
2. **The `impLImp` principal case** (`⊃⊃`, `(A→B)→D`): the
   Dyckhoff–Negri duplication recipe, needing the separately
   mechanised lemma `impLImp_dup` (`PLLG4HStr.lean:166`, Dyckhoff–Negri
   Lemma 4.2) because the naive inversion of `(A→B)→D` does not by
   itself expose enough structure to close the case. Detailed below.
3. **The lax-modal principal cases** (`laxL`, `impLLax`, `impLLaxLax`):
   close by the *inner* induction directly, with no self-absorption
   lemma, because the box-keeping and context-keeping rule shapes
   (§"The calculus" above) arrange for the doubled hypothesis to be
   presented, doubled, to exactly one premise. Detailed below for
   `impLLaxLax`, the case that exercises both the box-keeping and the
   two-premise interaction at once.

No case anywhere in `contract_bounded` invokes a cut theorem: contexts
are only ever *split*, *inverted*, or *permuted*, never *merged* across
two independently-derived sequents.

### Key stages with snapshots

**Entry to the inner induction — an easy case (`init`).**
Anchor: `PLLG4HCtr.lean:211` (immediately after `intro Γ hp`, entering
the very first case of `induction d with`, i.e. right where the double
induction's bookkeeping — outer bound, inner derivation — has just
settled).

```
case succ.init
w : ℕ
ihw : ∀ {A}, A.weight ≤ w → ∀ {n Γ' E}, G4h n Γ' E → ∀ {Γ}, Γ'.Perm (A :: A :: Γ) → G4c (A :: Γ) E
A : PLLFormula
hA : A.weight ≤ w + 1
n : ℕ
Γ' E : …
n✝ : ℕ
Γ✝ : List PLLFormula
a✝ : String
h : PLLFormula.prop a✝ ∈ Γ✝
⊢ ∀ {Γ}, Γ✝.Perm (A :: A :: Γ) → G4c (A :: Γ) (PLLFormula.prop a✝)
```

This is the state right where a reader of the source needs to see the
whole double-induction scaffold at once: `ihw` (the outer weight
hypothesis, available for *any* formula of weight `≤ w`, not just
`A` — the outer induction has already generalised over the contracted
formula), `hA` (the *current* bound, `A.weight ≤ w + 1`, matching
`succ w`), and then the inner case's own data (`h`, the atom-conclusion
membership). Every subsequent case snapshot in this section is a
refinement of this same scaffold.

**Easy case: `andL` principal, entry.**
Anchor: `PLLG4HCtr.lean:241` (immediately after `subst e`, having
matched the `cross_split3` disjunction's first branch — the rule's own
principal formula, `A₁.and B₁`, *is* one of the two designated copies).

```
case succ.andL.inl.intro
w : ℕ
ihw : …
n Γ' E : …
n✝ : ℕ
Γ✝ Θ : List PLLFormula
A₁ B₁ E₀ : PLLFormula
h : Γ✝.Perm (A₁.and B₁ :: Θ)
d₁ : G4h n✝ (A₁ :: B₁ :: Θ) E₀
Γ : List PLLFormula
hA : (A₁.and B₁).weight ≤ w + 1
ih : ∀ {Γ}, (A₁ :: B₁ :: Θ).Perm (A₁.and B₁ :: A₁.and B₁ :: Γ) → G4c (A₁.and B₁ :: Γ) E₀
hp : Γ✝.Perm (A₁.and B₁ :: A₁.and B₁ :: Γ)
hΔ : Θ.Perm (A₁.and B₁ :: Γ)
⊢ G4c (A₁.and B₁ :: Γ) E₀
```

The goal still names the *conjunction* `A₁.and B₁` as the formula to
contract — nothing about `andL`'s own shape has been used yet. What
follows in the source (not separately snapshotted) is exactly the IPC
recipe: `d₁.inv (.and A₁ B₁) …` inverts the surviving copy of
`A₁.and B₁` sitting in `d₁`'s premise context, producing a derivation
of `A₁ :: B₁ :: A₁ :: B₁ :: Γ ⊢ E₀` (both conjuncts, doubled); then
`ihw` is invoked twice at the strictly smaller weights `A₁.weight ≤ w`
and `B₁.weight ≤ w` (from `hA : A₁.weight + B₁.weight + 2 ≤ w + 1`, so
`omega` gives both bounds room to spare) to contract each doubled
conjunct in turn.

**Easy case: `andL` principal, immediately before closing.**
Anchor: `PLLG4HCtr.lean:251` (the last `have`, right before the final
`exact andL …` of this branch).

```
case succ.andL.inl.intro.intro
w : ℕ
ihw : …
n Γ' E : …
n✝ : ℕ
Γ✝ Θ : List PLLFormula
A₁ B₁ E₀ : PLLFormula
h : Γ✝.Perm (A₁.and B₁ :: Θ)
d₁ : G4h n✝ (A₁ :: B₁ :: Θ) E₀
Γ : List PLLFormula
hA : A₁.weight + B₁.weight + 2 ≤ w + 1
ih : …
hp hΔ : …
hw₁ : A₁.weight ≤ w
hw₂ : B₁.weight ≤ w
hinv : G4h n✝ (A₁ :: B₁ :: A₁ :: B₁ :: Γ) E₀
n₁ : ℕ
c₁' : G4h n₁ (A₁ :: B₁ :: B₁ :: Γ) E₀
c₂ : G4c (B₁ :: A₁ :: Γ) E₀
⊢ G4c (A₁.and B₁ :: Γ) E₀
```

`hinv` is the inversion (both conjuncts, doubled); `c₁'` is the result
of contracting `A₁`'s doubled copy first (`ihw hw₁ hinv …`); `c₂` is
the result of then also contracting `B₁`'s doubled copy
(`ihw hw₂ c₁' push2`). Two applications of `ihw`, each strictly
decreasing in weight, replace a doubled compound formula by a single
copy — nothing about this case needed `w` to decrease by more than the
`A₁`/`B₁` subformula relation already guarantees. Two calls, not one,
is the price of a two-place connective: `impLOr`'s principal case
(not separately snapshotted, structurally identical) pays the same
price for the same reason.

**Hardest case: `impLImp` principal, the Dyckhoff–Negri recipe.**
Four snapshots trace the recipe from entry to closing. The rule
displayed is `(A₁ ⊃ B₁) ⊃ D₁ ⇒ E₀`, doubled.

*Entry*, anchor `PLLG4HCtr.lean:350` (immediately after `subst e`):

```
case succ.impLImp.inl.intro
w : ℕ
ihw : …
n Γ' E : …
n✝ : ℕ
Γ✝ Θ : List PLLFormula
A₁ B₁ D₁ E₀ : PLLFormula
h : Γ✝.Perm ((A₁.ifThen B₁).ifThen D₁ :: Θ)
d₁ : G4h n✝ (B₁.ifThen D₁ :: Θ) (A₁.ifThen B₁)
d₂ : G4h n✝ (D₁ :: Θ) E₀
Γ : List PLLFormula
ih₁ ih₂ : …
hp : Γ✝.Perm ((A₁.ifThen B₁).ifThen D₁ :: (A₁.ifThen B₁).ifThen D₁ :: Γ)
hΔ : Θ.Perm ((A₁.ifThen B₁).ifThen D₁ :: Γ)
⊢ G4c ((A₁.ifThen B₁).ifThen D₁ :: Γ) E₀
```

Abbreviate `K := B₁.ifThen D₁` (the "kept implication") for the
remaining commentary, following the source's own comment ("duplicate
the spectator copy into premise 1"). `impLImp`'s two premises are
`d₁ : Θ, K ⊢ A₁.ifThen B₁` and `d₂ : Θ, D₁ ⊢ E₀` — the rule *consumes*
the implication `(A₁ ⊃ B₁) ⊃ D₁` from the conclusion context, offering
only `K` and `D₁` to its premises respectively. Naively inverting the
surviving copy against `d₁`/`d₂` the way the IPC cases above did would
not directly reproduce two copies of `K` or of anything else useful:
this is exactly the shape that needs the separately proved
`impLImp_dup`.

*After `impLImp_dup`*, anchor `PLLG4HCtr.lean:361` (right after the
`obtain ⟨n₀, r₀⟩ := impLImp_dup d₁ …` call; `K` abbreviates
`B₁.ifThen D₁` throughout this block, as introduced above):

```
case succ.impLImp.inl.intro.intro
… (as above, plus:)
hwA : A₁.weight ≤ w
hwK : K.weight ≤ w
hwD : D₁.weight ≤ w
n₀ : ℕ
r₀ : G4h n₀ (A₁ :: K :: K :: K :: Γ) (A₁.ifThen B₁)
⊢ G4c ((A₁.ifThen B₁).ifThen D₁ :: Γ) E₀
```

`impLImp_dup d₁ …` (Dyckhoff–Negri Lemma 4.2, `PLLG4HStr.lean:166`)
turns `d₁ : Θ, K ⊢ A₁.ifThen B₁` — with `Θ` known to carry one copy of
the doubled principal — into `r₀`, a derivation of the *same*
conclusion `A₁.ifThen B₁` from a context with `A₁` and **three**
copies of `K`. This is exactly the "context implication may be
replaced by `A, B→D, B→D`" duplication the theorem's own docstring
describes, applied where `A := A₁`, `B := B₁`, `D := D₁`. Two of the
three `K` copies are then peeled off by two further applications of
`ihw hwK` (not separately snapshotted — routine weight-bounded
contraction, closing to a single `K`), and the resulting two-copy
state (`r₁`) is contracted once more to a single `K`, giving `r₂`.

*After `impR_inv`*, anchor `PLLG4HCtr.lean:367` (right after
`obtain ⟨n₂, r₃⟩ := r₂.impR_inv`; `K` again abbreviates `B₁.ifThen D₁`):

```
case succ.impLImp.inl.intro.intro.intro.intro
… (as above, plus:)
r₂ : G4c (K :: A₁ :: Γ) (A₁.ifThen B₁)
n₂ : ℕ
r₃ : G4h n₂ (A₁ :: K :: A₁ :: Γ) B₁
⊢ G4c ((A₁.ifThen B₁).ifThen D₁ :: Γ) E₀
```

`r₂ : K, A₁, Γ ⊢ A₁.ifThen B₁` — a single copy of `K`, a fresh `A₁`
(from the duplication) and `Γ`, deriving `A₁ ⊃ B₁`. `impR_inv`
(`PLLG4HInv.lean:267`) inverts the right-implication conclusion itself,
exposing `B₁` with `A₁` added to the antecedent — `r₃`. The right
implication `A₁.ifThen B₁` that `impLImp_dup` manufactured has now
served its purpose and is gone from the state; what is left,
`A₁, K, A₁, Γ ⊢ B₁`, has a doubled `A₁` ready for one more
`ihw hwA` contraction.

*Pre-final-`exact`*, anchor `PLLG4HCtr.lean:373` (`K` again abbreviates
`B₁.ifThen D₁`):

```
case succ.impLImp.inl.intro.intro.intro.intro
… (as above, plus:)
r₄ : G4c (A₁ :: K :: Γ) B₁
q₂ : G4h n✝ (D₁ :: D₁ :: Γ) E₀
⊢ G4c ((A₁.ifThen B₁).ifThen D₁ :: Γ) E₀
```

`r₄ : A₁, K, Γ ⊢ B₁` is the fully contracted, single-copy witness for
premise 1 of a *fresh* `impLImp` instance; `impR r₄` re-abstracts it
back to `K :: Γ ⊢ A₁.ifThen B₁` — the re-abstraction step the case
comment promises. In parallel, `q₂` is `d₂`'s doubled-`D₁` premise
inverted against `.impImp A₁ B₁ D₁` and waiting for its own `ihw hwD`
contraction. The closing line,
`exact impLImp (List.Perm.refl _) (impR r₄) (ihw hwD q₂ (List.Perm.refl _))`,
reassembles both pieces under one application of `impLImp` at the
single-copy context `(A₁.ifThen B₁).ifThen D₁ :: Γ` — the theorem's
conclusion.

**Modal case: `impLLaxLax` principal — the box-keeping payoff.**
`impLLaxLax` is the rule for `A.somehow.ifThen B` (an implication whose
*antecedent* is itself boxed) firing against an *already-present* box
witness `X.somehow` in the context, rather than manufacturing a fresh
one. Two premises: `d₁ : X, Γ ⊢ A.somehow` (opens the witness) and
`d₂ : Θ, B ⊢ E₀` (consumes the implication's consequent).

*Entry*, anchor `PLLG4HCtr.lean:400` (immediately after `subst e`):

```
case succ.impLLaxLax.inl.intro
w : ℕ
ihw : …
n Γ' E : …
n✝ : ℕ
Γ✝ Θ : List PLLFormula
A₁ B₁ X E₀ : PLLFormula
h : Γ✝.Perm (A₁.somehow.ifThen B₁ :: Θ)
hX : X.somehow ∈ Θ
d₁ : G4h n✝ (X :: Γ✝) A₁.somehow
d₂ : G4h n✝ (B₁ :: Θ) E₀
Γ : List PLLFormula
ih₁ ih₂ : …
hp : Γ✝.Perm (A₁.somehow.ifThen B₁ :: A₁.somehow.ifThen B₁ :: Γ)
hΔ : Θ.Perm (A₁.somehow.ifThen B₁ :: Γ)
⊢ G4c (A₁.somehow.ifThen B₁ :: Γ) E₀
```

The premise that matters here is `d₁ : G4h n✝ (X :: Γ✝) A₁.somehow` —
note it is stated over `X :: Γ✝`, the **entire pre-split conclusion
context** `Γ✝` (which is exactly `A₁.somehow.ifThen B₁` doubled, plus
`Γ`) with the opened witness `X` added on top. Because the rule kept
its box, `d₁` did not lose either of the two copies of the doubled
principal formula on its way from conclusion to premise: they are
still both there, inside `Γ✝`, available to `ih₁` unchanged.

*Pre-final-`exact`*, anchor `PLLG4HCtr.lean:409`:

```
case succ.impLLaxLax.inl.intro
… (as above, plus:)
hw : B₁.weight ≤ w
hX' : X.somehow ∈ Γ
q₂ : G4h n✝ (B₁ :: B₁ :: Γ) E₀
⊢ G4c (A₁.somehow.ifThen B₁ :: Γ) E₀
```

The closing line is
`exact impLLaxLax (List.Perm.refl _) hX' ((ih₁ ((hp.cons X).trans push2)).perm …) (ihw hw q₂ (List.Perm.refl _))`:
`ih₁` is called **directly** — `d₁`'s doubled context is pushed past
the fresh witness `X` (`push2`, the same permutation shuffle
`contract_atom` used) and handed straight to the *inner* induction
hypothesis, no inversion, no `S`-style self-absorption lemma, because
`d₁`'s premise already carried both copies of the doubled principal.
The second premise `d₂ : Θ, B₁ ⊢ E₀` is inverted against
`.impLax A₁ B₁` to expose a doubled `B₁` (`q₂`), which closes by one
ordinary `ihw` weight-decreasing contraction — the same pattern as
every non-modal principal case. This is the single sentence
`docs/g4p-ladder.md` promises under "Contraction is proved, cut-free":
*"all three lax rules close by the inner induction because their
premises now carry both copies"* — visible here, concretely, as the
absence of any inversion step on `d₁` at all.

## What changed from the pre-revision-3 design

`docs/g4p-ladder.md`'s design revision 2 (2026-07-08) already made the
`laxL`/`L◯→″` box-keeping change and found that contraction's
`◯`-principal cases became purely structural under it, but left
`R◯→` in its original, context-consuming form. Revision 3
(2026-07-09) discovered — while writing this very case table in Lean —
that a doubled `◯φ→ψ` fired by the *consuming* `R◯→` genuinely cannot
be reconstructed from its inverted premises: the required inference
fails in a Heyting algebra with nucleus at `φ := p`, `ψ := p ∧ q`,
`E := q`. `docs/g4p-ladder.md` records this as *"no proof was being
overlooked, the rule shape itself was the obstacle."* The fix
(`R◯→″` keeping its context, matching G3's `L⊃` premise-1 discipline)
is what let `impLLax`'s principal case above close the same way
`impLLaxLax`'s does — by the inner induction alone, no self-absorption
lemma `S` anywhere in this file.

## Provenance

`#print axioms PLLND.G4c.contract`, `#print axioms
PLLND.G4c.contract_bounded`, and `#print axioms
PLLND.G4h.contract_atom` each report only `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`. Checked immediately before writing this
document; see `docs/annotated/README.md` for the full audit.
