# The verified algorithms, running — a guided tour

*Companion to `LaxLogic/PLLDemos.lean`. Every verdict quoted here is pinned
in that file by `#guard_msgs`, so it is re-checked on every build.*

*Note: the `find` discussed below is the older **fuelled** search of
`PLLG4Dec.lean`. For the current tooling — the fuel-free searcher
`G4cTm.find`, the certified countermodel search, and the two-sided
procedure `Search.decide` — see [`search-manual.md`](search-manual.md).*

This development mechanises Fairtlough–Mendler Propositional Lax Logic. Two
of its results are not just theorems but **algorithms** — a decision
procedure and a normaliser — and both are ordinary Lean `def`s that run
under `#eval`. This note walks a reader through watching them run, reports
wall-clock timings, and is honest about where the practical limits sit.

Timings were taken with `#time` on a warm build (Lean 4.22.0-rc3, Apple
silicon); they are indicative, not benchmarks. Reproduce any of them with

```
lake env lean LaxLogic/PLLDemos.lean
```

which compiles the whole suite (≈ 3.3 s including import loading) and runs
every pinned `#eval`.

---

## 1. The decider — F&M Theorem 2.8

`PLLG4Dec.lean` gives `Decidable (G4c Γ C)` and
`Decidable (Nonempty (Tm Γ φ))`: PLL provability is decidable, by backward
proof search for the *repaired, complete* calculus **G4iLL″** (`G4c`). The
verdict is kernel-honest — plain `decide`, no `native_decide`, no trusted
compiled evaluation.

### 1a. Signature (non)theorems, via the packaged `decide`

| Sequent | reading | verdict | time |
|---|---|---:|---:|
| `p ⊢ ◯p` | the ◯-unit (monadic `return`) | **true** | 72 ms |
| `◯p ⊬ p` | no escape — the defining lax constraint | **false** | 67 ms |
| `⊢ p → ◯p` | unit as a theorem | **true** | 125 ms |
| `⊬ ◯p → p` | no escape as a (non)theorem | **false** | 64 ms |
| `p→q, p ⊢ q` | modus ponens (pure intuitionistic) | **true** | 75 ms |
| `p→q, q ⊬ p` | its converse | **false** | 75 ms |
| `Nonempty (Tm [p] ◯p)` | Thm 2.8 at the *term* level | **true** | 72 ms |

Every one of these is weight ≤ 4 over ≤ 2 atoms, and each returns in well
under a fifth of a second. The last row is the literal statement of F&M
Theorem 2.8 — "is this type inhabited by a proof term?" — decided by
`decidablePLL`.

### 1b. Heavier theorems, via the search itself (`find`)

The lax *laws* one actually wants — multiplication and strength — and the
contraction-free intuitionistic examples Dyckhoff's calculus was built for
are all too heavy for the packaged `decide` (see §3). They run instantly
through the **search** with a hand-supplied fuel, `find` in the demo file.
By `search_sound`, a `true` verdict is sound for *any* fuel — it exhibits a
real G4iLL″ (hence PLL) derivation:

| Sequent | reading | weight | verdict | time |
|---|---|---:|---:|---:|
| `⊢ ◯◯p → ◯p` | ◯-multiplication (monad `join`) | 6 | **true** | 39 ms |
| `⊢ p ∧ ◯q → ◯(p∧q)` | monad strength | 11 | **true** | 34 ms |
| `⊢ (p→q→r)→(p→q)→p→r` | the S combinator (Dyckhoff) | 13 | **true** | ~30 ms |

(`find` only certifies positives; a `false` from it would mean merely "not
found within fuel". Completeness — a trustworthy `false` — needs the full
`decideFuel` bound, which is exactly what §3 is about.)

### 1c. The showcase: the repaired calculus closes the G4iLL gap

`PLLG4Gap.sc_but_not_G4` machine-checks that Iemhoff's *original* G4iLL
(our `G4`) is **incomplete**: it misses the PLL-valid sequent

> `◯G', F' ⊢ r`,  where `F' = ◯p → r` and `G' = (◯p → r) → ◯p`

— Howe's duplication phenomenon one modal level up (the antecedent
implication needing contraction straddles a box-opening). The repaired
G4iLL″ proves it. The demo puts the two calculi side by side on the *same*
sequent:

| Calculus | decides | verdict | time |
|---|---|---:|---:|
| G4iLL″ (`G4c`, complete) | via `find` | **true** | 72 ms |
| G4iLL (`G4`, Iemhoff's original) | via `decide` | **false** | 45 ms |

Same sequent, opposite verdicts — this is the decidability payoff of the
repair, running. (The old `decide (G4 …)` does *not* blow up at weight 8,
because that decider terminates by a Dershowitz–Manna multiset order, not
by the `enum` fuel of §3.)

---

## 2. The normaliser — `Tm.normalize`

`PLLTopTop.lean`'s `strong_normalisation` upgrades the certified one-step
reducer `Tm.step?` from fuelled to total: `Tm.normalize` iterates it to a
fixed point, warranted by
`normalize_spec : Steps t t.normalize ∧ Nf t.normalize`. `Tm.pretty`
renders terms compactly: `#n` de Bruijn variables, `val` / `let val•` for
the ◯-monad, `⟨_,_⟩` pairs, `_.1`/`_.2` projections. All normaliser demos
are instant (sub-millisecond; the SN certificate is erased at runtime, so
the compiled normaliser is literally "iterate `step?`").

| Demo | before | after |
|---|---|---|
| `cascade` — 4-deep `let`-β chain | `let ⇐ (let ⇐ (let ⇐ (let ⇐ val #0 in val) …))` | `val #0` |
| `prog` — strength-style program | `let ⇐ val #0 in (let ⇐ #2 in val ⟨#1,#0⟩)` | `let ⇐ #1 in val ⟨#1,#0⟩` |
| `dup` — β + projection | `(λ. ⟨#0,#0⟩) ⟨#0,#0⟩.1` | `⟨#0,#0⟩` |
| `spine` — 3-deep neutral-head spine | `let ⇐ (let ⇐ (let ⇐ #0 in val) in val) in val` | `let ⇐ #0 in val #0` |

Things to notice:

- **`cascade`** collapses a four-deep nesting all the way to `val #0`: assoc
  re-associates the spine and each `let`-β fires. This is the "dramatically
  smaller normal form" — the source has 9 constructors, the result 2.
- **`prog`** is a real monadic program. `let x ⇐ val #0 in …` β-fires
  (substituting `#0`, shifting the free index `#2 → #1`), but the inner
  `let ⇐ #1 in …` has a **neutral** scrutinee and *survives*: the normal
  form is still a genuine computation, not a value.
- **`spine`** shows assoc + `let`-β compressing a three-frame left-nested
  spine of right-units down to a *single* residual bind.

### The reduction boundary: `Step` has no η and no right-unit

`Step` is β for every connective plus `let`-β and `let`-assoc — and
nothing else. Two equations that hold *semantically* but are deliberately
**not** oriented as reductions, so these terms are already normal:

| Term | law it would use | `normalize` result |
|---|---|---|
| `let x ⇐ #0 in val x` | monad right-unit `m >>= return = m` | **unchanged** |
| `λ. (#1 #0)` | function η `λx. f x = f` | **unchanged** |

The right-unit case is subtle and worth internalising: `val x` in *body*
position is not a redex — only a `val` in *scrutinee* position is a `let`-β
redex. This is exactly why `spine` bottoms out at `let ⇐ #0 in val #0`
rather than at `#0`, and it is the same shape that drives the
non-composition counterexamples of `PLLReducibility.lean`.

---

## 3. Where the practical limit sits, and why

The headline engineering finding. `decide (G4c Γ C)` routes through

```
decideFuel Γ C = 2 ^ (enum as W).card * (enum as W).card + 1
```

where `enum as W` (from `PLLG4Space.lean`) enumerates the weight-bounded
formula space over the end-sequent's atoms `as` up to its weight `W`. Since
the recent filter landed, each level `.filter`s to weight ≤ W+1, so the
**stored** set is exactly the weight-bounded space — small (e.g.
`(enum {p} 5).card = 170`). But *constructing* it still materialises the
per-level products **before** filtering,

```
enum as (W+1) = ((enum as W ×ˢ enum as W).image (·.and ·) ∪ … ).filter (weight ≤ W+1)
```

so each level builds `|enum as W|²` pairs and pays quadratic `Finset`
deduplication (structural formula equality) on them. That construction cost
is the bottleneck, and it is what Lean pays to read off `.card`.

### The frontier, measured (post-filter)

`decide (G4c …)`, growing the end-sequent's weight:

| weight | atoms | example | verdict | time |
|---:|---:|---|---:|---:|
| 2 | 1 | `p ⊢ ◯p` | true | 71 ms |
| 3 | 2 | `p→q, p ⊢ q` | true | 75 ms |
| 4 | 1 | `⊢ p → ◯p` | true | 124 ms |
| 5 | 1 | `⊢ ◯p → ◯p` | true | **6.0 s** |
| 5 | 2 | `p, ◯q ⊢ p∧◯q` | true | **> 30 s** (aborted) |
| 6 | 1 | `⊢ ◯◯p → ◯p` | true | **> 90 s** (aborted) |

The wall is sharp and lands around **weight 5**: a single-atom weight-5
sequent takes ~6 s, and one more atom or one more unit of weight tips it
well past the ~10 s budget into practical infeasibility. Atom count matters
because `enum`'s base level is `as.image prop`, so more atoms means larger
per-level products to build and dedup.

### Profiling the weight-5 point

For `⊢ ◯p → ◯p` (weight 5, one atom), the ~6 s decomposes cleanly:

| what | value | time |
|---|---|---:|
| `(enum {p} 5).card` | `170` | 6.06 s |
| `decideFuel [] (◯p→◯p)` = `2^170·170+1` | a 54-digit bignum | 5.83 s |
| full packaged `search … decideFuel …` | `true` | 5.86 s |

The reading is unambiguous: **all** of the cost is `enum` *construction*
(computing just `.card` already spends the whole 6 s); the fuel **bignum is
free** (`2^170` is 54 digits — the filter is precisely what keeps this
number sane); and the **search adds nothing measurable** on top of building
the fuel. The filter fixed the *bignum* half of the old blow-up but not the
*construction* half, so the frontier did not move — these numbers were taken
*after* the filter landed.

### The search is not the problem — proof

The decisive contrast. The **same** sequents that `decide (G4c …)` cannot
even set up run in tens of milliseconds through the search with an explicit
fuel of `10000` (`find` in the demo), because `find` never builds `enum`:

| Sequent | weight | `decide (G4c …)` | `find` (hand fuel) |
|---|---:|---:|---:|
| `⊢ ◯◯p → ◯p` | 6 | > 90 s (aborted) | **39 ms** |
| `◯G', F' ⊢ r` | 8 | (would blow up) | **72 ms** |
| `⊢ p ∧ ◯q → ◯(p∧q)` | 11 | (would blow up) | **34 ms** |

So the algorithm is fast; the *packaging* is what is expensive. The
`decideFuel`/`enum` construction exists only to certify **completeness**
(that a `false` verdict is trustworthy) via a pigeonhole bound on the
reachable space — it is a proof device, and using it as the runtime fuel is
what caps the packaged decider at weight ≈ 5.

### Takeaway

The permanent structural fact is: **search cheap, space-enumeration
expensive.** The landed filter made the fuel *number* small (so the
doubly-exponential *bignum* of the pre-filter `enum` is gone), but reading
off `|enum|` still costs a quadratic-dedup construction per weight level,
which reasserts the same wall around weight 5–6. Making the packaged
`decide` scale would need `enum` (or the cardinality bound) computed without
materialising the per-level products at all. Until then, `find` — sound on
every positive verdict by `search_sound` — is the way to watch the decider
actually decide heavy sequents.
