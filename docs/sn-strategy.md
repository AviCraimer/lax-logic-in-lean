# What reduction strategy does the SN proof suggest?

> *"Actually I am unsure what strategy that SN proof would indicate; perhaps
> the proof itself suggests an optimal one?"* — the question this note
> answers, for the strong-normalisation proof in `LaxLogic/PLLTopTop.lean`.

Short answer, up front. Strong normalisation is **strategy-independent** —
it says *every* reduction order terminates — so the proof cannot, and does
not, single out a strategy for *termination*. What its architecture does
carry is an efficiency recommendation, and a fairly specific one: **run the
monadic spine as an abstract machine — walk it scrutinee-first with an
explicit continuation stack, keeping it right-associated — and reduce values
by value.** The implemented normaliser `Tm.normalize` gets the value part
right (it is call-by-value) but walks the spine tree-recursively rather than
as a machine, which is exactly the part an optimal implementation would
change. The rest of this note argues each clause from the code, and is
careful to separate what the proof *determines* from what is merely a good
heuristic it happens to be compatible with.

---

## 0. The relation `Step`, and why "optimal" ≠ "terminating"

`Step` (`PLLTerms.lean`) is β for every connective plus two monadic rules,
freely interleaved with all congruences:

```lean
bindVal   : Step (.bind (.val s) u)      (u.subst1 s)                          -- let-β
bindAssoc : Step (.bind (.bind s t) u)   (.bind s (.bind t (u.rename Ren.skip1)))  -- let-assoc
```

`strong_normalisation : ∀ t, SNt t` proves the reverse relation is
well-founded — `Acc (fun a b => Step b a) t` for every `t`. Because SN is
accessibility of *the whole one-step relation*, it is invariant under the
choice of which redex you fire next: from any term, every maximal reduction
sequence is finite. So there is no "the strategy that makes it terminate";
they all do. "Optimal" can therefore only mean **efficient** — fewest steps,
least copying, smallest intermediate terms — and that is what we can read
off the proof's shape.

The reason a *semantic* proof was needed at all already tells us the two
fragments are not cleanly separable; that is worth pinning down first,
because it is the direct sequel to the earlier "phased β-then-assoc"
question.

---

## 1. The phased-strategy question: β and assoc do not stage

`PLLReducibility.lean` proves each fragment SN in isolation —
`beta_sn` (β) and `assoc_sn` (assoc, via `AStep.weight_lt`: every assoc step
strictly *decreases* term weight, so assoc alone terminates in linearly many
steps) — and then closes the door on combining them phase-by-phase, with two
machine-checked counterexamples:

- **assoc creates β.** `ce₁ = let y ⇐ (let x ⇐ z in val x) in val y` is
  β-normal, but one re-association moves a `val` from body into scrutinee
  position, creating a `let`-β redex.
- **β creates assoc.** `ce₂ = (λf. let x ⇐ f in val x) (let x ⇐ z in val x)`
  is assoc-normal, but its single β step substitutes a `bind` into scrutinee
  position — and reduces *exactly to `ce₁`*, closing a β/assoc ping-pong.

The file draws the consequence explicitly (its closing docstring): a
**phased** strategy "β to completion; assoc to completion; repeat" would at
best prove that *one* strategy normalises — a weak-normalisation statement
already available from cut elimination — not SN over all interleavings; and
because each phase regenerates the other's redexes, no simple size or count
measure survives both phases. Both orientations of Bachmair–Dershowitz
quasi-commutation fail. So:

> The proof's very existence is a verdict on the naive phased strategy: you
> cannot normalise by "all β, then all assoc". They genuinely interleave.

That is the negative half. The positive half — *how* they should interleave
— is the content of the principal lemma.

---

## 2. The architecture, read as an algorithm

### 2a. The `Kont` stack is an abstract machine over the ◯-spine

The heart of the proof reifies the monadic spine as an explicit stack of
`bind`-bodies (`PLLTopTop.lean`):

```lean
inductive Kont (Γ) (C) : PLLFormula → Type
  | nil  : Kont Γ C C
  | cons (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B) : Kont Γ C A

def plug : Kont Γ C A → Tm Γ (somehow A) → Tm Γ (somehow C)
  | .nil,      t => t
  | .cons u K, t => plug K (.bind t u)          -- innermost frame first
```

`K.plug t` builds the left-nested spine `bind (bind (bind t u₁) u₂) …` with
`t` at the *scrutinee* (deepest) end and the head frame `u₁` closest to it.
The `⊤⊤` reducibility clause for `◯A` quantifies over these stacks
(`SRed (◯A) t` iff `K[t ρ]` is SN for every reducible `K`) — a **continuation
/ CPS reading**: a computation is good iff it behaves in every good
continuation, and the `K = nil` case is the value-style clause of the
β-fragment. That is precisely the data and control of an abstract machine
(Krivine/CEK-flavoured, specialised to the monad): the "control" is the
`bind` being evaluated, `K` is the stack of pending continuations, and you
drive evaluation *along the spine from the scrutinee outward* — run the first
action to a `val`, hand its value to the continuation, repeat. This is
spine-directed, demand-along-the-◯-structure evaluation, not tree-walking.

### 2b. The principal lemma is the machine's transition, and its measure is a priority order

```lean
theorem principal (s) (u) (K) :
    SNt s → SNt (K.plug (u.subst1 s)) → SNt (K.plug (.bind (.val s) u))
```

"a `let`-β redex `bind (val s) u` under a stack `K` is SN as soon as its
contractum-in-context `K[u[s]]` and its value part `s` are." The induction
is over the lexicographic triple

```lean
Lex₃  on  (Acc.rank of K[u[s]],  K.size,  Acc.rank of s)
      =   (rank of the contractum-in-context,  spine length,  rank of the value)
```

The **order of the three components is the interesting datum** — it ranks
what the induction treats as "large" vs "cheap" work. Reading off which
component each reduct decreases (from the four cases of `principal`):

| a reduct of `K[bind (val s) u]` where… | measure lemma | which slot drops |
|---|---|---|
| the **body** `u` steps (`bindCong₂`) | `lex₃_of_lt` | 1st: `<` |
| the **stack** `K` steps (`KStep`) | `lex₃_of_lt` | 1st: `<` |
| an **interface re-association** fires | `lex₃_of_le_lt` | 1st: `=`, 2nd: `<` |
| the **value** `s` steps (`valCong`) | `lex₃_of_le_eq_lt` | 1st: `≤`, 2nd: `=`, 3rd: `<` |

The stratification could hardly be sharper:

1. **Most significant — progress in the contractum-in-context.** β-work in
   the body or the surrounding context reduces the top component. These are
   the reductions that make genuine progress toward the normal form.
2. **Middle — re-association of the spine.** The interface-assoc case keeps
   the top component *exactly equal* (the proof's own comment: "the
   underlying term is literally unchanged") and only shortens the stack. So
   re-association is *strictly subordinate* to β-progress: it is bookkeeping
   you can always flush "for free" against the contractum's rank.
3. **Least significant — reducing the bound value.** A step inside `s` sits
   in the innermost slot.

So the measure says: **context/body-β dominates re-association dominates
value-reduction**, and it certifies that eager re-association never
increases the quantity the outer induction is really tracking. This is the
proof telling you re-association is cheap and can be done aggressively.

### 2c. The assoc orientation: keep the spine right-associated

`bindAssoc` is oriented **left-nested → right-nested**:

```
bind (bind s t) u   ⟶   bind s (bind t u↑)
```

Iterating it drives a left-nested spine into a right-linear sequence of
binds — do-notation / A-normal form — headed, at the end, by a *neutral*
scrutinee (the normal-form grammar `Nf.bind : Ne t → Nf u → Nf (.bind t u)`
requires exactly that). Combined with §2b, the algorithm the proof most
naturally describes is: **linearise the spine to the right, then fire
`let`-β at the head.**

There is a known efficiency reason this orientation matters, and it is the
classic quadratic pitfall of naive `let`-normalisation (Sabry–Wadler
A-normalisation): each `bindAssoc` step copies the trailing body
(`u.rename Ren.skip1` in the rule), so re-associating a chain of *n* lets by
*repeatedly firing the outermost assoc* re-traverses the tail each time — Θ(n²)
copying. The `Kont` machine of §2a avoids this: it collects the whole spine
onto the stack in **one pass** and plugs, so each body is traversed once —
Θ(n). The proof's stack is thus not just a proof device; it is the data
structure that makes right-re-association linear.

---

## 3. What `Tm.normalize` actually does — and does not do

Strategy in this development lives entirely in `Tm.step?`
(`PLLStrongNorm.lean`); `Tm.normalize` merely iterates it:

```lean
def Tm.normalize (t) : Tm Γ φ :=
  match t.step? with | some t' => t'.1.normalize | none => t
```

`step?`'s own docstring states its discipline: *"congruences (innermost
subterms first), then head-redex dispatch."* Concretely, at every node it
recurses into the children **before** testing the node for a redex; for a
bind:

```lean
| .bind t u =>
    match t.step? with                       -- 1. reduce the scrutinee
    | some ⟨t',h⟩ => .bind t' u
    | none => match u.step? with             -- 2. then the body
      | some ⟨u',h⟩ => .bind t u'
      | none => t.bindRedex? u               -- 3. only now the head (β or assoc)
```

This is **leftmost-innermost (call-by-value)**, tree-recursive. Measured
against the proof's architecture:

- **Value part — agrees, and this is a good call.** `step?` reduces `s`
  inside `val s` early, as part of normalising the scrutinee. So when a
  `let`-β finally fires, the substituted value is already normal and its
  redexes are not duplicated across multiple occurrences of the bound
  variable. This is the right cost choice — and note it is the *opposite* of
  what the measure's "value in the least-significant slot" would suggest if
  read naively as a runtime priority (see §4).
- **Spine — disagrees.** `step?` re-associates *bottom-up*: it fires
  `bindAssoc` at a node only once that node's scrutinee subterm is already
  normal, reached by tree recursion. It never performs the eager global
  right-re-association pass, and it uses no stack. On a deep left-nested
  spine this is where the Θ(n²) re-association copying of §2c can bite,
  precisely because there is no one-pass spine collection.

`Tm.normalize` is, to be clear, correct and terminating — `normalize_spec`
certifies `Steps t t.normalize ∧ Nf t.normalize`. It is a perfectly
reasonable strategy. It simply is not the abstract-machine strategy the
proof's `Kont`/⊤⊤ architecture describes.

---

## 4. Recommendation, and an honest ledger

**The strategy the proof most naturally certifies:**

> Evaluate the ◯-spine as an abstract machine — descend scrutinee-first with
> an explicit continuation stack, re-associating eagerly so the spine stays
> right-linear (one pass, Θ(n)) — fire `let`-β against the stack top, and
> keep values call-by-value (reduce `s` before substituting). Non-monadic
> β/projection/case reductions ride along in the usual congruence order.

**Does `Tm.normalize` follow it?** Partly. It is call-by-value on values
(✓, and the proof's ⊤⊤ semantics assumes SN values, consistent with this),
but it walks the monadic spine by tree recursion with bottom-up
re-association rather than as a one-pass stack machine (✗).

**What an optimal implementation would change.** Replace the tree recursion
over `bind` with the `Kont` machine already present in the proof: push
`bind`-bodies onto a stack while descending the scrutinee, which linearises
left-nested spines in one traversal (avoiding the quadratic
re-association), and contract `bind (val s) u` against the stack top. The
value discipline (`step?`'s call-by-value) can stay; only the spine
traversal is refactored. This is a faithful reading of the principal
lemma's transition as executable code.

### Where the proof genuinely determines the strategy, and where it does not

*Determined by the proof:*

- **Re-association is subordinate and can be eager.** The measure's middle
  slot (§2b) certifies that firing `bindAssoc` never increases the
  contractum's rank — eager right-re-association is always safe and cheap.
  This is a real theorem-level fact, not a heuristic.
- **A stack/continuation architecture is the natural one.** The ⊤⊤ clause
  for `◯` is definitionally a quantification over continuation stacks; the
  proof cannot even be stated without them. Reading them as a machine is not
  a stretch — it is the semantics.
- **The spine's canonical form is right-associated with a neutral head.**
  Forced by `bindAssoc`'s orientation and the `Nf.bind` grammar.

*Not determined — any choice terminates, and the proof is neutral:*

- **Call-by-value vs call-by-name on values.** SN holds for both; the proof
  handles value-reduction in its innermost slot only because that is where
  the induction naturally places it, **not** because "value last" is
  optimal at runtime. In fact CBV (what `normalize` does) is usually the
  better cost choice, since it avoids duplicating value-redexes through
  substitution — so here the sensible engineering choice runs *against* a
  naive reading of the measure order. The measure is a termination
  well-order, not a cost model, and should not be over-read as one.
- **Order among independent non-monadic redexes.** β at disjoint positions,
  projection vs case in separate subterms, etc. — the congruence structure
  leaves these free and the proof says nothing about them.
- **Uniqueness of the result under a *different* strategy.** `normalize` is
  deterministic, so it always returns the same normal form; but that
  *different* strategies reach the *same* normal form is confluence, which
  this development does not prove. No claim of strategy-invariance of the
  normal form is made here.

**Bottom line.** The SN proof does not pick a strategy for termination —
nothing could, since all terminate. But its ⊤⊤/`Kont` architecture and the
component order of its lexicographic measure do jointly recommend a specific
*efficient* one: an abstract machine over the monadic spine, right-associating
eagerly and reducing values by value. `Tm.normalize` realises the value half
of that recommendation and leaves the spine-machine half — the part that
turns naive Θ(n²) re-association into Θ(n) — on the table.
