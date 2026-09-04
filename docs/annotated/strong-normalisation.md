# Strong normalisation of the full reduction, via Lindley–Stark ⊤⊤-lifting

Source: `LaxLogic/PLLTopTop.lean`, 1308 lines. This is the main
theorem of the two documents in this directory: strong normalisation
of **every** one-step reduction of the PLL proof-term calculus,
β for every connective *and* the monadic `let`-associativity law,
freely interleaved — `SNt t` for every typed term `t`. Extraction
method and reading conventions: `docs/annotated/README.md`. The proof
term calculus itself — `Tm`, its de Bruijn variables `Var`, renaming,
substitution, and the reduction relation `Step` — lives in
`LaxLogic/PLLTerms.lean`, skimmed below.

## The calculus the reduction lives on (`PLLTerms.lean`)

`Tm : List PLLFormula → PLLFormula → Type` (`PLLTerms.lean:60`) is an
intrinsically-typed term calculus: Moggi's computational metalanguage,
the term assignment for lax logic (Benton–Bierman–de Paiva's
computational logic), with `◯` — PLL's lax modality — realised as a
strong monad. `val` is the unit (`laxIntro`'s computational content)
and `bind` is monadic `let` (`laxElim`'s). Because typing is intrinsic
— `Step : ∀ {Γ φ}, Tm Γ φ → Tm Γ φ → Prop` (`PLLTerms.lean:182`) only
ever relates two terms of one sequent — subject reduction is free: it
is not a theorem to prove, it is the shape of the relation's type.

`Step` (`PLLTerms.lean:182`–`234`) is: one β-rule per connective
(`app`/`lam`, `fst`/`snd`/`pair`, `case`/`inl`/`inr`), the two monadic
laws

```
bind (val s) t    ⟶  t[s]                        (let-β)
bind (bind s t) u ⟶  bind s (bind t u↑)           (let-assoc)
```

and congruence closure at every constructor. `let`-β is ordinary
monadic unit-cancellation; `let`-assoc is monad associativity read as
a rewrite — re-nesting two sequential `let`s so the outer scrutinee is
evaluated first. `Tm.cut = subst1` (`PLLTerms.lean:174`): cut at the
term level just *is* substitution, and the file's header table records
the exact correspondence between each reduction rule and the
matching principal case of the separately mechanised sequent-calculus
cut elimination (`PLLSequent.lean`) — `bind`-`val`-β corresponds to
the `laxR` vs `laxL` principal case, Fairtlough–Mendler's Figure 2.

## Why a semantic method is forced

`PLLReducibility.lean` proves strong normalisation of the β-fragment
alone (`RStep`, i.e. `Step` minus `bindAssoc`) by ordinary Tait
reducibility, then closes with two machine-checked terms
(`PLLReducibility.lean:1035`–`1091`, `section Counterexamples`) showing
the β-fragment and the assoc-fragment do not compose:

* `ce₁ := bind (bind z (val x)) (val y)` (over a free variable
  `z : ◯A`) is **β-normal** — no β-step applies anywhere in it
  (`PLLReducibility.lean:1049`) — but one `let`-assoc step reassociates
  it to `ce₁assoc := bind z (bind (val x) (val y))`
  (`:1061`), which now contains a **freshly created** `let`-β redex
  (`:1064`).
* `ce₂ := (λf. bind f (val x)) (bind z (val x))` is **assoc-normal** —
  no assoc-step applies anywhere in it (`:1073`) — but one β-step
  substitutes the `bind`-headed argument into scrutinee position,
  producing an assoc redex; indeed the β-step reduces `ce₂` to `ce₁`
  exactly (`:1089`), closing the two counterexamples into a single
  ping-pong.

So neither Bachmair–Dershowitz quasi-commutation inclusion
(`assoc;β ⊆ β;(β∪assoc)*` or its mirror) can hold, and no syntactic
argument for interleaved termination is available: a **semantic**
method is needed. `PLLTopTop.lean` supplies Lindley–Stark ⊤⊤-lifting
(TLCA 2005) — the *biorthogonal* upgrade of the ordinary
value-oriented reducibility clause at `◯`. The only prior mechanisation
of ⊤⊤-lifting the file's header is aware of is Doczkal–Schwinghammer
(Isabelle/HOL-Nominal, LFMTP 2009), for a calculus without sums; this
appears to be the first in Lean, and the first with sums and an
intrinsically-typed syntax.

## The idea, in one paragraph

Ordinary (value-style) reducibility interprets `◯A` by: `t` is
reducible iff every value it reduces to has a reducible payload — a
first-orthogonal, "positive" clause. That clause is exactly what makes
the β-fragment reducibility argument go through, and exactly what
breaks under `let`-assoc, because `let`-assoc's redex is not `t`
itself reducing to a value, it is `t` appearing as the scrutinee of an
*outer* `bind` whose own scrutinee is *itself* a `bind`. ⊤⊤-lifting
fixes this by reinterpreting `◯A` biorthogonally: a **continuation
stack** `K` (a list of pending `bind`-bodies, `Kont Γ C A`,
`PLLTopTop.lean:497`) is *reducible* when plugging any reducible value
into it stays SN (`KRedP`, `:748`); a term is reducible at `◯A` when
plugging it into *every* reducible stack, under *every* renaming
extension, stays SN (`SRed`'s `somehow` clause, `:768`). The ordinary
value-style clause is exactly the `K = []` (`Kont.nil`) shadow of this
definition. Under this reading, `bind t u` at stack `K` is
*definitionally* the same obligation as `t` at the *extended* stack
`cons u K` — so proving `bind`s of reducibles reducible reduces to
proving that extending a reducible stack keeps it reducible, which is
where the **principal lemma** — the file's mathematical heart — does
its work.

## The principal lemma

### Statement

```lean
theorem principal : ∀ {Γ : List PLLFormula} {A B C : PLLFormula}
    (s : Tm Γ A) (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B),
    SNt s → SNt (K.plug (u.subst1 s)) →
    SNt (K.plug (.bind (.val s) u))
```

In words: fix a stack `K` awaiting a scrutinee of type `◯B` to produce
`◯C`, and a `let`-β redex `bind (val s) u` of type `◯B` sitting where
that scrutinee goes. If the value part `s` is SN, and the *contractum*
plugged into the stack, `K[u[s]]`, is SN, then the *redex* plugged
into the stack, `K[bind (val s) u]`, is SN. This is a one-step-back
SN-transfer lemma — an SN-expansion, in the reducibility-candidate
sense — stated at the level of a whole continuation, not just a bare
term, which is exactly the generality the assoc-fragment forces.

### Proof architecture: why bare `Acc`-induction is not enough

The natural induction is on the SN witness of `K[bind (val s) u]`
itself — but that witness does not yet exist; it is what the lemma is
constructing. The proof instead inducts on a **well-founded surrogate
measure** built from the *hypotheses*: the lexicographic triple

```lean
def Lex₃ : Ordinal × ℕ × Ordinal → Ordinal × ℕ × Ordinal → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
```

instantiated at `μ = (Acc.rank hKu, K.size, Acc.rank hs)` — the
**ordinal rank** (`Acc.rank`, a genuine Mathlib primitive from
`Mathlib.SetTheory.Ordinal.Rank`, imported at `PLLTopTop.lean:2`) of
the *given* SN witness for `K[u[s]]`, the stack's frame count, and the
ordinal rank of the given SN witness for `s`. Three of the lemma's
four step cases decrease strictly in the first component (a step in
`K[u[s]]`'s SN witness, or in `s`'s, is reflected by `rank_lt_of_step`
into a strict ordinal decrease, since `Acc.rank` is *proof-irrelevant*
— any two `Acc` proofs of the same point are equal, so ranks attach to
terms, not to which witness happened to be supplied). The remaining
case — **interface assoc** — is the one none of that machinery
handles by itself, and is why the measure has three components rather
than one.

### Key stages with snapshots

**Entry to the induction.**
Anchor: `PLLTopTop.lean:686` (`subst hμ`, immediately after entering
the body of `induction μ using lex₃_wf.induction with | _ μ IH`, i.e.
the point at which the ambient measure, the induction hypothesis, and
the two SN hypotheses are all simultaneously in view).

```
case h
Γ : List PLLFormula
A B C : PLLFormula
s : Tm Γ A
u : Tm (A :: Γ) B.somehow
K : Kont Γ C B
hs : SNt s
hKu : SNt (K.plug (u.subst1 s))
IH : ∀ (y : Ordinal × ℕ × Ordinal),
       Lex₃ y (Acc.rank hKu, K.size, Acc.rank hs) →
       ∀ {Γ A B C} (s : Tm Γ A) (u : Tm (A :: Γ) B.somehow) (K : Kont Γ C B)
         (hs : SNt s) (hKu : SNt (K.plug (u.subst1 s))),
         y = (Acc.rank hKu, K.size, Acc.rank hs) → SNt (K.plug (s.val.bind u))
⊢ SNt (K.plug (s.val.bind u))
```

(`s.val.bind u` is Lean's notation for `Tm.bind (Tm.val s) u`, the
dot-projection rendering of `bind (val s) u`.) `IH` is stated at
**every** `μ` strictly below the *current* triple, for **arbitrary**
`Γ, A, B, C, s, u, K` — the induction has been fully generalised over
the term data, which is exactly what licenses re-using it later with a
*different* `u`, or a *shorter* `K`, so long as the measure drops.
This is the shape the `suffices H : …` wrapper (immediately preceding,
not separately snapshotted) exists to set up: the theorem statement
itself has no measure in it, so the induction is run over an auxiliary
statement carrying one, then specialised back down at `μ := (Acc.rank
hKu, K.size, Acc.rank hs)` for the caller's own `hs`/`hKu`.

**The interface-assoc branch — the case bare `Acc`-induction cannot
reach.**
This is the fourth and last branch of the case split on
`plug_step_cases K _ hy` (which classifies every step of a plugged
term as: the redex part stepped; the stack stepped; impossible; or
—here — the redex's own head meets the stack's innermost frame). The
scrutinee here is itself a `bind`, so plugging it one layer deeper
merges two adjacent frames by `let`-assoc.

*Entry*, anchor `PLLTopTop.lean:715` (`subst hKeq`, immediately after
the pattern match commits to this branch):

```
case h.inr.inr.inr.intro.intro.intro.intro.intro.intro.intro.intro.refl
Γ : List PLLFormula
A B C : PLLFormula
s : Tm Γ A
u : Tm (A :: Γ) B.somehow
hs : SNt s
B' : PLLFormula
u₀ : Tm (B :: Γ) B'.somehow
K₀ : Kont Γ C B'
hKu : SNt ((Kont.cons u₀ K₀).plug (u.subst1 s))
IH : … (as above, at the ambient μ)
hy : Step ((Kont.cons u₀ K₀).plug (s.val.bind u))
       (K₀.plug (s.val.bind (u.bind (u₀.rename Ren.skip1))))
⊢ Acc (fun a b => Step b a) (K₀.plug (s.val.bind (u.bind (u₀.rename Ren.skip1))))
```

`K` has specialised to `Kont.cons u₀ K₀` — an *explicit* outer frame
`u₀` on top of a shorter stack `K₀` — because the case being examined
is precisely the one where the outer frame merges with the redex's
inner `bind`. `hy` records the actual reduction step Lean has just
classified: plugging `bind (val s) u` into `cons u₀ K₀` steps, by
`let`-assoc at the interface, to plugging the *merged* term
`bind (val s) (bind u (u₀.rename Ren.skip1))` into the *shorter* stack
`K₀`. The goal (`Acc` unfolded, since this is inside `Acc.intro`'s
step case) is to show that merged-term-at-shorter-stack is itself SN.

*Pre-final-`exact`* (right before invoking `IH`), anchor
`PLLTopTop.lean:720`:

```
case h.inr.inr.inr.intro.intro.intro.intro.intro.intro.intro.intro.refl
… (as above, plus:)
heq : K₀.plug ((u.bind (u₀.rename Ren.skip1)).subst1 s) = K₀.plug ((u.subst1 s).bind u₀)
hKu' : SNt (K₀.plug ((u.bind (u₀.rename Ren.skip1)).subst1 s))
⊢ Acc (fun a b => Step b a) (K₀.plug (s.val.bind (u.bind (u₀.rename Ren.skip1))))
```

`heq` is the algebraic fact that makes this case work at all:
substituting into a *merged* frame is the same as binding the
substituted inner part against the *original* outer frame
(`bind_subst1_merge`, proved once, generically, just above `principal`
in the source) — so the contractum-in-context for the *new*, merged
redex is *literally, propositionally equal* to `K₀.plug ((u.subst1
s).bind u₀)`, which is already known SN because it is a sub-part of
the *original* `hKu` (obtained by `heq ▸ hKu`, giving `hKu'`). The
closing call,
`IH _ (lex₃_of_le_lt (rank_eq_of_eq heq hKu' hKu).le (Nat.lt_succ_self _)) s _ K₀ hs hKu' rfl`,
supplies the measure argument the whole three-component design exists
for: `rank_eq_of_eq heq hKu' hKu` shows the *first* component of the
triple is literally **unchanged** (same underlying SN witness, up to
the propositional equality `heq`, so `Acc.rank` — proof-irrelevant —
agrees), while `K.size` has strictly **decreased** (`K₀` has one fewer
frame than `Kont.cons u₀ K₀`). `lex₃_of_le_lt` packages exactly
"first component `≤`, second component `<`" into a `Lex₃` step. This
is the case a bare induction on `Acc.rank hKu` alone cannot handle —
the rank does not decrease here, so a plain ordinal induction would
refuse to recurse — and is exactly why the measure needed a second,
`ℕ`-valued component in the first place.

## `sred_bind`: the stack-extension trick

### Statement

```lean
theorem sred_bind {Γ : List PLLFormula} {A B : PLLFormula}
    {t : Tm Γ (somehow A)} {u : Tm (A :: Γ) (somehow B)}
    (ht : SRed (somehow A) t)
    (H : ∀ {Δ} (ρ : Ren Γ Δ) (s : Tm Δ A), SRed A s →
      SRed (somehow B) ((u.rename ρ.lift).subst1 s)) :
    SRed (somehow B) (.bind t u)
```

In words: if the scrutinee `t` is reducible at `◯A`, and every
reducible instance of the body `u` is reducible at `◯B` (stated with
full generality over renaming extensions and substituted values, the
standard reducibility-candidate closure condition for a binder), then
`bind t u` is reducible at `◯B`.

### Key stage: the `◯`-clause becomes the extended-stack obligation

Anchor: `PLLTopTop.lean:1152`, immediately after the `show` that makes
the design point explicit in the source itself.

```
Γ : List PLLFormula
A B : PLLFormula
t : Tm Γ A.somehow
u : Tm (A :: Γ) B.somehow
ht : SRed A.somehow t
H : ∀ {Δ} (ρ : Ren Γ Δ) (s : Tm Δ A), SRed A s →
      SRed B.somehow ((u.rename ρ.lift).subst1 s)
Δ : List PLLFormula
ρ : Ren Γ Δ
C : PLLFormula
K : Kont Δ C B
hK : KRedP (fun {Δ} => SRed B) K
⊢ SNt ((Kont.cons (u.rename ρ.lift) K).plug (t.rename ρ))
```

The obligation to discharge, per `SRed`'s `somehow` clause, is
`SNt (K.plug ((bind t u).rename ρ))` for an arbitrary reducible stack
`K` — but the source's `show` tactic rewrites this goal, *before* any
proof step, to `SNt ((Kont.cons (u.rename ρ.lift) K).plug (t.rename
ρ))`, which is **definitionally** the same term (`Kont.plug`'s `cons`
equation reduces by iota, `PLLTopTop.lean:507`–`510`) but reads as a
different obligation: *"`t` is SN when plugged into the stack `K`
extended by one more frame `u`."* This is precisely the sentence in
§"The idea, in one paragraph" above, exhibited as a single line of
Lean: `ht.2 ρ (Kont.cons (u.rename ρ.lift) K) …`, three lines later
(not separately snapshotted), discharges it by invoking `t`'s own
`◯`-clause at the *extended* stack — and proving that extended stack
reducible (`KRedP`) is exactly where `principal` is called, supplying
the value case the extended stack must handle.

## The fundamental theorem

### Statement

```lean
theorem fundamental_step : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) {Δ : List PLLFormula} (σ : Sub Γ Δ),
    SRedS σ → SRed φ (t.subst σ)
```

The Kripke–Tait fundamental theorem of the logical relation:
substituting reducible terms for every free variable of `t` yields a
reducible instance of `t`. Structural induction on `t`, one case per
constructor, each closed by the corresponding `sred_*` closure lemma
(`sred_lam`, `sred_pair`, `sred_inl`/`sred_inr`, `sred_case`,
`sred_val`, `sred_bind`) applied to the induction hypothesis. This is
the retrofitted Tait argument of `PLLReducibility.lean` re-run over the
full `Step` relation; only the `val`/`bind` cases are new relative to
that file, since the reducibility predicate `SRed` only changes at the
`◯`-clause.

### Key stages with snapshots

**An easy case: `var`.**
Anchor: `PLLTopTop.lean:1210`, immediately after `intro Δ σ hσ` on
entering the first case of `induction t with`.

```
case var
Γ : List PLLFormula
φ : PLLFormula
Γ✝ : List PLLFormula
φ✝ : PLLFormula
v : Var Γ✝ φ✝
Δ : List PLLFormula
σ : Sub Γ✝ Δ
hσ : SRedS σ
⊢ SRed φ✝ (Tm.subst σ (Tm.var v))
```

Closed in one line, `exact hσ v` (not separately snapshotted): `σ v`
is reducible by hypothesis (`hσ`, unfolding `SRedS`'s definition
exactly at `v`), and `Tm.subst σ (Tm.var v)` is *definitionally*
`σ v` (`Tm.subst`'s `var` equation). No closure lemma is even needed —
the reducibility-of-substitution-instances discipline does all the
work at the leaves.

**An ordinary β case, for contrast: `app`.**
Anchor: `PLLTopTop.lean:1223`.

```
case app
Γ : List PLLFormula
φ : PLLFormula
Γ✝ : List PLLFormula
φ✝ ψ✝ : PLLFormula
t : Tm Γ✝ (φ✝.ifThen ψ✝)
s : Tm Γ✝ φ✝
iht : ∀ {Δ} (σ : Sub Γ✝ Δ), SRedS σ → SRed (φ✝.ifThen ψ✝) (Tm.subst σ t)
ihs : ∀ {Δ} (σ : Sub Γ✝ Δ), SRedS σ → SRed φ✝ (Tm.subst σ s)
Δ : List PLLFormula
σ : Sub Γ✝ Δ
hσ : SRedS σ
⊢ SRed ψ✝ (Tm.subst σ (t.app s))
```

Closed by unfolding `SRed`'s `ifThen` clause at the identity renaming:
`(iht σ hσ).2` is exactly the function "apply a reducible argument,
get a reducible result" that `SRed (φ✝.ifThen ψ✝) _` packages, so
applying it to `ihs σ hσ` (the reducible substituted argument) at the
identity renaming and rewriting `Tm.rename_id` closes the goal. No
new machinery relative to the β-fragment: `SRed`'s `ifThen` clause is
untouched by the move to the full relation.

**The modal case: `bind`.**
Anchor: `PLLTopTop.lean:1255`.

```
case bind
Γ : List PLLFormula
φ : PLLFormula
Γ✝ : List PLLFormula
φ✝ ψ✝ : PLLFormula
t : Tm Γ✝ φ✝.somehow
u : Tm (φ✝ :: Γ✝) ψ✝.somehow
iht : ∀ {Δ} (σ : Sub Γ✝ Δ), SRedS σ → SRed φ✝.somehow (Tm.subst σ t)
ihu : ∀ {Δ} (σ : Sub (φ✝ :: Γ✝) Δ), SRedS σ → SRed ψ✝.somehow (Tm.subst σ u)
Δ : List PLLFormula
σ : Sub Γ✝ Δ
hσ : SRedS σ
⊢ SRed ψ✝.somehow (Tm.subst σ (t.bind u))
```

Structurally this case is the same shape as `app`'s — apply the
scrutinee's induction hypothesis, discharge a closure condition on the
body against the extended substitution — but the *closure lemma* it
calls is `sred_bind`, whose obligation, as read above, is the
extended-stack argument that only exists because of the ⊤⊤-lifting
upgrade: everywhere else in this induction, moving from the
β-fragment file to this one is a no-op; here alone, it is where the
whole apparatus of continuation stacks, `KRedP`, and `principal`
actually gets exercised, once per `bind` node in the term being
normalised.

## Strong normalisation and the total normaliser

### Statement

```lean
theorem strong_normalisation {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) : SNt t
```

Every well-typed term is strongly normalising. The proof is three
lines: instantiate `fundamental_step` at the identity substitution
(every variable is trivially reducible, `SRedS.ids`), simplify
`t.subst Sub.ids` to `t` (`Tm.subst_ids`), and extract SN from
reducibility (`SRed.sn`, CR1, immediate from the definition of `SRed`
at every formula shape).

Anchor: `PLLTopTop.lean:1267`, immediately after
`have h := fundamental_step t Sub.ids SRedS.ids`.

```
Γ : List PLLFormula
φ : PLLFormula
t : Tm Γ φ
h : SRed φ (Tm.subst Sub.ids t)
⊢ SNt t
```

Everything above this file — the whole reducibility-candidate
apparatus, the principal lemma, the stack machinery — has been spent
to produce exactly this `h`; what remains is bookkeeping
(`Tm.subst_ids` to align `h`'s subject with the goal's `t`, then
`.sn`). The brevity of this proof, relative to the file, is the point:
the fundamental theorem is where the mathematics is, and
`strong_normalisation` is its corollary in the textbook sense.

### The total normaliser

Strong normalisation upgrades `Tm.step?` (`PLLStrongNorm.lean:181`,
`Option {t' // Step t t'}`, a certified but *fuelled* one-step
reducer — proof-carrying, but requiring an external decreasing measure
to iterate) into a **total** normaliser, by supplying
`strong_normalisation` itself as the well-founded relation:

```lean
instance (priority := high) instWFStep {Γ φ} : WellFoundedRelation (Tm Γ φ) :=
  ⟨fun a b => Step b a, ⟨fun t => strong_normalisation t⟩⟩

def Tm.normalize {Γ φ} (t : Tm Γ φ) : Tm Γ φ :=
  match t.step? with
  | some t' => t'.1.normalize
  | none => t
termination_by t
decreasing_by exact t'.2
```

`Tm.normalize` is now an ordinary total, computable Lean function —
`termination_by t` with `decreasing_by exact t'.2` discharges every
recursive call against `instWFStep`, i.e. against strong normalisation
itself, exactly the sense in which the SN theorem is what makes the
"keep stepping" procedure terminate rather than merely "keep stepping
until you happen to stop."

**Final snapshot**: `Tm.normalize_spec`, the correctness statement —
`Steps t t.normalize ∧ Nf t.normalize` (every term multi-step-reduces
to its normalisation, which is genuinely a normal form in the `Nf`
grammar of `PLLNormal.lean`). Anchor: `PLLTopTop.lean:1299`,
immediately after `intro t _ ih`, entering the body of the
`Acc.selfInduction` that drives the correctness proof.

```
Γ : List PLLFormula
φ : PLLFormula
t✝ t : Tm Γ φ
a✝ : Acc (fun a b => Step b a) t
ih : ∀ (a' : Tm Γ φ), Step t a' → Steps a' a'.normalize ∧ Nf a'.normalize
⊢ Steps t t.normalize ∧ Nf t.normalize
```

`a✝` is the local `Acc` witness for `t` that `Acc.selfInduction`
(`PLLTactics.lean:58`, a house-built eliminator — see the technique
box below) re-supplies to the step case, and `ih` is available at
*every* one-step successor of `t`. What follows (not separately
snapshotted) is a case split on `t.step?`: if it returns `some t'`,
`ih` at `t'.1` finishes by prepending one step; if `none`, `t` is
already a normal form by construction of `step?` itself
(`Tm.step?_none`). The `Nf`/`Ne` grammar this bottoms out in
(`PLLNormal.lean:38`–`71`) is worth one remark: `bind` is *not* a
constructor of `Ne` (neutral terms), because `bind (bind s t) u` is a
`let`-assoc redex even when the inner `bind` is itself stuck — normal
`bind`-chains are forced to be right-nested with non-`bind`, non-`val`
scrutinees, matching `SNeut`'s definition in this very file
(`PLLTopTop.lean:730`, `| _, _, .bind _ _ => False`, with the comment
*"this matches `PLLNormal.lean`, where `bind` is not `Ne`"*). The
semantic reducibility argument and the syntactic normal-form grammar
agree, independently, on exactly which terms count as "stuck" — a
consistency check that is not automatic and is worth pointing out to a
proof-theory reader who might otherwise wonder whether the two
notions of neutrality could quietly diverge.

## Technique boxes

**(a) `Perm`-hypothesis left rules.** Not used in this file directly
(that convention belongs to the sequent calculus, `PLLG4H.lean` and
`docs/annotated/contraction.md`) — the term calculus has no analogous
context-exchange bookkeeping, because `Tm`'s contexts are ordered
lists tracked by de Bruijn `Var`, not `List.Perm`-quotiented sets.

**(b) Height-preserving vs height-bumping.** Also not directly
applicable here: there is no height index on `Tm`/`Step`. The
analogous distinction in this file is between the ordinary
(β-fragment) reducibility-candidate closure lemmas, all of which are
"free" re-runs of `PLLReducibility.lean` unchanged, and the two new
closure lemmas (`sred_val`, `sred_bind`) that exist only because `◯`'s
clause changed — see §"`sred_bind`" above for the one that matters.

**(c) The weight-with-≤-slack induction pattern.** Not the measure
used here — `principal`'s induction is over `Lex₃`, a genuine ordinal
× ℕ × ordinal lexicographic well-founded relation, needed precisely
because no `Nat`-valued measure survives the interface-assoc case (the
term does not shrink; only the *stack* does, and only some of the
time). Contrast `docs/annotated/contraction.md`, where a plain
`Nat`-with-slack measure *does* suffice, because contraction's
recursive calls are always at a subformula, which is genuinely smaller
by an integer amount.

**(d) The index-generalisation gotcha.** Present in spirit throughout
`fundamental_step`'s `induction t with`: because `t`'s type `Tm Γ φ`
indexes the very statement being proved (`SRed φ (t.subst σ)`),
`induction t` generalises `Γ` and `φ` to the case-local binders shown
in every snapshot above as `Γ✝`/`φ✝` (daggered because the *outer*
`Γ`/`φ` in scope, from the theorem's own binders, are still separately
named and now shadow them). Every case's `have`/closure-lemma call
must therefore refer to the case-local `φ✝`, `ψ✝`, etc., not the
theorem's outer `φ` — visible directly in, for instance, the `app`
snapshot above, where the goal names `ψ✝` (case-local) while the
theorem statement's own binder was `φ` (now referring to something
else, the *original* whole-term's type, no longer relevant inside this
case).

**(e) Machine-checked axiom audits.** No `#guard_msgs`/`#print axioms`
call is pinned inside `PLLTopTop.lean` itself, but the convention is
worth applying externally, as documentation: see
`docs/annotated/README.md`'s provenance check, re-run immediately
before this document was written, confirming `strong_normalisation`
and `Tm.normalize` depend on no axiom beyond
`[propext, Classical.choice, Quot.sound]`.

**(f) House-built `Acc` eliminators (new, specific to this file).**
`Acc.of_inversion`/`Acc.of_inversion₂` (`PLLTactics.lean:88`, `:99`)
and `Acc.selfInduction`/`Acc.pairInduction`/`Acc.tripleInduction`
(`:58`, `:67`, `:112`) are **local** lemmas — not Mathlib primitives,
confirmed by direct `#check` against a bare `import
Mathlib.SetTheory.Ordinal.Rank` (only `Acc.rank` and
`Acc.rank_lt_of_rel` resolve there). They were extracted from
`PLLReducibility.lean` because, per `PLLTactics.lean`'s own header
comment, "the hand-rolled version (revert invariants / nest `induction
… with | intro` / re-intro / rebuild `Acc` witnesses with `.intro`)
was the single most error-prone move in the reducibility file" — the
congruence lemmas at the top of this file (`SNt.abort`, `SNt.lam`,
`SNt.pair`, …) are one-line consequences of `Acc.of_inversion`/`₂`, and
the closure lemmas further down (`sred_beta_exp`, `sred_pair`,
`sred_case`) are one-line consequences of `Acc.pairInduction`/
`Acc.tripleInduction`, where a hand-rolled version of each would have
been a small multi-case proof apiece.

## Provenance

`#print axioms PLLND.strong_normalisation` and `#print axioms
PLLND.Tm.normalize` each report only `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`. Checked immediately before writing this
document; see `docs/annotated/README.md` for the full audit, including
the two contraction theorems.
