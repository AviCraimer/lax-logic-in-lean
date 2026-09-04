# Publishing FrontierSampler — options, and the prerequisites that gate them

**Status: nothing has been published, registered, or pushed.** No account, no
repository, no PR, no registry entry. This file records options only.

**This decision is not ripe, and the reason is not technical.** Matthew's
stated prerequisites, which govern:

1. **The mechanisms must be proved against tasks beyond proof theory and model
   theory.** Stratification, the certified corpus and replay have been
   exercised on exactly one problem, in one domain, by one person. That is not
   evidence that they generalise; it is one data point.
2. **The generalisation must come from that experience, not from anticipating
   it.** The current generic core was extracted from a single instantiation.
   Any API it has that was not forced by a second, different use is a guess.
3. **Documentation for general use comes last**, after 1 and 2.

Publishing also costs Matthew personally: it is his name on it, and the energy
goes away from guiding the campaign, which is where the value currently is.
So the default is **not to publish**, and the options below are recorded for
whenever the prerequisites are met — or discarded if they are not.

---

## The options, briefly

**1. Standalone repository under `fairflow`.** `lakefile.toml` and
`lean-toolchain` are already in place and the package builds offline, so this
is mechanical: create, push, tag. Cost ~1 hour. Prerequisite 1 unmet.

**2. Reservoir (the Lake registry).** Automatic once option 1 is done and the
repository is public; needs a Zulip post to be found at all. Prerequisite 1
unmet.

**3. Upstream into Plausible.** Plausible has absorbed an outside layer before
(the `DeriveArbitrary` / `ArbitraryFueled` modules, 2025, from the Chamelean /
AWS-Strata line), so it is a real path. But its contract is tactic-facing
(`plausible` on a goal, `TestResult` = success / failure / `gaveUp n`) and this
layer is campaign-facing (hundreds of cells, a file, minutes). Upstreaming
would lose the distinction that matters here — that a gate failure, a quiet
cell and an unrun cell are three different outcomes. **Not recommended even if
the prerequisites are met.**

There is one small piece that stands alone and is not gated by anything: a
PR to Plausible documenting that `Gen.run` draws from the process-global
`stdGenRef` (hence is not replayable) and that `mkStdGen` diffuses consecutive
seeds poorly — measured here: seeds 1000, 1009 and 1017 produced the same
generated formula — plus a pure `Gen.runWithSeed` that mixes the seed. That
is a Plausible bug-report-shaped observation, useful to everyone, an hour's
work, and commits nobody to the rest.

**4. Leave it in-tree.** Where it is now: `tools/FrontierSampler/`,
unreferenced by the main lakefile, costing nothing.

**5. Write to the neighbours instead of publishing.** The nearest active work
is [Chamelean](https://github.com/ngernest/chamelean) / its successor
[Specimen](https://github.com/strata-org/specimen) and **Palamedes**
([arXiv 2511.12253](https://arxiv.org/abs/2511.12253), PLDI 2026). All three
attack *generation under a constraint*; none has strata, a corpus or replay.
A note saying "your derived generators would slot into `SeedGen`" costs one
email and would test prerequisite 1 from the outside — someone else's problem
domain, someone else's generators.

---

## Recommendation

**Option 4 now.** Leave it in-tree. It is doing its job there.

**Option 3's small piece whenever convenient** — it is a Plausible
observation, not a publication of this tool, and it is not gated by the
prerequisites.

**Options 1, 2 and 5 only after prerequisite 1 is met**, i.e. after the
mechanisms have earned their keep on a task outside proof and model theory.
Until then the package is a by-product of one campaign, and saying so is more
useful than shipping it.

**Prune criterion.** If replay keeps yielding nothing across a real statement
change (see the campaign report), drop the replay layer rather than carry it:
explore first, prune later.

---

## What is generic and what is PLL-specific

| generic (`tools/FrontierSampler/`, no dependencies) | PLL-specific (`wip/frontier.lean`) |
|---|---|
| `SeedGen`, `Stratum`, `Gate`, `Triage`, `Outcome` | the cell type (space, context, goal body, fuels, budget) |
| corpus `Rec` / `Ledger` — render, parse, append-and-flush, read | the six admissibility gates, transcribed from the statement |
| `runStratum` / `runCampaign` | the nineteen strata and their generators |
| `replay` | countermodel-only triage via `PLLND.Search.refute?` |
| `Splitmix` (fallback PRNG) | the `Plausible.Gen` adapter and seed mixing |

`wip/frontierCore.lean` is a byte-identical copy of
`tools/FrontierSampler/FrontierSampler/Core.lean` (`diff` is the sync check),
because the main build cannot import across package boundaries.
