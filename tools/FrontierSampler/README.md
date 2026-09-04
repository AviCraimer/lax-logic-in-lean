# FrontierSampler

A thin campaign layer on top of a QuickCheck-style generator, extracted from
one use: screening the open lemma of a uniform-interpolation development for
propositional lax logic (`wip/frontier.lean` in the parent repository).

**Not published, not recommended for general use yet.** See `SHARING.md` for
why: the mechanisms have been exercised on one problem in one domain, which is
not evidence that they generalise.

---

## What it adds

Four things, for the case where the interesting instances of a property are
**sparse** — the statement carries side conditions (closure, coverage,
arithmetic bounds) that a random instance almost never satisfies, so an
ungated generator spends its budget on cells that prove nothing and reports a
clean run.

| layer | what it is |
|---|---|
| **Stratification** | a campaign is a list of named `Stratum`s, each a structural region with its own generator, sample count and seed range. Strata are the unit of reporting. |
| **Admissibility gate** | a `Gate` is a decidable clause of the statement's side condition. Failures are recorded as `gate=FAIL:<clause>` and excluded from every count — never counted as passes. |
| **Corpus** | one append-and-flush line per cell, so a run killed by a wall-clock cap loses nothing, and a hit is replayable and pinnable without re-running any search. |
| **Replay** | a cell is a pure function of `(stratum, seed, size)`, so the corpus can be re-driven against a *different* statement later. |

It supplies no generators, no shrinking, no tactic.

## What is generic and what is not

The generic core is `FrontierSampler/Core.lean` (~330 lines, **no
dependencies**). Everything PLL-specific — the cell type, the six gates, the
nineteen strata, the countermodel-only triage — lives in `wip/frontier.lean`
in the parent repository. `wip/frontierCore.lean` is a byte-identical copy of
`Core.lean`; `diff` is the sync check.

## Generation is delegated

```lean
abbrev SeedGen (ι : Type) : Type := Nat → Nat → Option ι   -- seed → size → instance
```

so the package depends on nothing, and
[Plausible](https://github.com/leanprover-community/plausible) — the Lean 4
QuickCheck descendant, formerly Mathlib's `SlimCheck`, split out and renamed by
[mathlib4 #18459](https://github.com/leanprover-community/mathlib4/pull/18459)
(merged 2024-11-01), present in any Mathlib-using package tree — plugs in with
one definition:

```lean
def ofGen {α : Type} (g : Plausible.Gen α) : FrontierSampler.SeedGen α := fun seed size =>
  ((Plausible.runRandWith seed g :
      ReaderT (ULift Nat) (Except Plausible.GenError) α).run ⟨size⟩).toOption
```

Two cautions, both measured rather than read:

* **`Gen.run` is not seeded.** It draws from the process-global `stdGenRef`.
  `runRandWith` takes the seed explicitly and is pure. Only the latter gives a
  replayable corpus. (`Plausible.Configuration.randomSeed` covers the *tactic*
  path; this is the `Gen`-level gap.)
* **`mkStdGen` diffuses seeds poorly.** Consecutive seeds give strongly
  correlated first draws — seeds 1000, 1009 and 1017 produced the same
  generated formula here. Mix the seed first; `Splitmix.step` is there for
  that, and the mixing is a pure function of the recorded seed.

`Splitmix` (25 lines) is a fallback for dependency-free use, not a competing
generator library.

## Prior art

Surveyed 2026-08; "absent" means *no evidence found*.

* **Gating**: Plausible already discards instances failing a decidable guard
  (`decGuardTestable`) and reports `gaveUp n`. What it does not do is report
  gate pressure on a *successful* run. Strong constrained *generation* exists
  in Lean only outside Plausible —
  [Chamelean](https://github.com/ngernest/chamelean) /
  [Specimen](https://github.com/strata-org/specimen) (`#derive_generator`,
  after Rocq/Coq QuickChick) and Palamedes
  ([arXiv 2511.12253](https://arxiv.org/abs/2511.12253), PLDI 2026). **If your
  side condition is inductively presented, use those instead**: a derived
  generator beats a gate. The gate here is for conditions cheap to *check* and
  awkward to *generate from*.
* **Strata with per-region budgets**: absent in Lean. QuickCheck
  `label`/`classify`/`cover`, Hedgehog `classify`, Hypothesis `event()` all
  classify *after* generation; none allocates budget to named regions. No tool
  found in any language that does.
* **Certificate-carrying corpus**: absent in Lean. Hypothesis's example
  database stores *failures* for replay, opaque, no certificates. Fuzzers keep
  input corpora; AWS's [cedar-spec](https://github.com/cedar-policy/cedar-spec)
  ships one per release for CI replay against its Lean model.
* **Cross-property replay**: absent in Lean; not a supported PBT mode anywhere
  (Hypothesis's database is keyed by test identity); routine in fuzzing.
* Also: [LSpec](https://github.com/argumentcomputer/LSpec) wraps Plausible for
  Hspec-style suites. [Etna](https://arxiv.org/abs/2603.27002), the field's PBT
  evaluation platform, covers Rocq, Haskell, OCaml, Racket, Rust — not Lean.
  Hackage's `leancheck` is a Haskell library, unrelated.

## Build and run

```
cd tools/FrontierSampler
lake build                     # library; no `lake update`, no network
lake build fsdemo
./.lake/build/bin/fsdemo
```

Toolchain `leanprover/lean4:v4.31.0` (pinned). The demo runs a four-stratum
campaign, writes `frontier_example_corpus.txt`, then replays that corpus
against a *different* property:

```
hits=0 quiet=15 skip=0 gated-out=65 gen-fail=0 counted=15
replay: 15 records, 10 agree, 5 changed (5 new hits), 0 unregenerable
```

(`gated-out=65` against `counted=15`: four fifths of the generated instances
were inadmissible. An ungated harness would have reported eighty passes. The
example's generator is deliberately loose to show this.)

## Corpus format

```
fs1|stratum=NAME|seed=N|size=N|<your columns…>|gate=ok|verdict=quiet|ms=N|cert=…
```

* `gate=ok` or `gate=FAIL:<clause>`.
* `verdict` ∈ `R!` (certificate found) | `quiet` (bounded hunt found nothing) |
  `SKIP` (not run).
* `#`-prefixed lines are comments and are skipped by the reader.
* Values sanitised against `|`; bump `formatVersion` if the contract changes.

Replay needs only `(stratum, seed, size)`; the other columns are for reading by
eye and for `awk`.

## Vocabulary

`quiet` is not `pass`. A clean screen is evidence about where certificates were
not found, not a proof that none exist. The verdict type has no constructor
called `pass`, deliberately.

## Design rationale

The critique this answers, from the development it was built for:

> The campaign's screening biases completeness over reach. Exhaustive sweeps
> over small bounded regions get re-run per formula as each new formula of
> interest arises; what never happens is probing a bunch of formulae of
> increasing / random structure to see if they cause future problems. You can
> generalise from sparse data as well as comprehensive data; seeing more shapes
> is good.

The concrete failure: the shape that mattered — spaces containing a
doubly-boxed clause `◯◯E ⊃ B` — sat one nesting level beyond the exhaustively
swept region, and was found by proof-side analysis two rounds later. Hence the
standing rule the tool exists to serve:

> Each round's residue shape defines the next campaign's stratum, and the
> campaign runs **before** the next proof build is scoped.

## Licence

Same as the enclosing repository.
