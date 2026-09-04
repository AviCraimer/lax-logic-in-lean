import FrontierSampler.Core
import FrontierSampler.Example

/-!
# FrontierSampler

Admissibility-gated, stratified, corpus-carrying property-based testing.

See `README.md`.  The two modules:

* `FrontierSampler.Core` — the layer itself: `SeedGen`, `Stratum`, `Gate`,
  `Triage`, the corpus `Ledger`, `runCampaign`, `replay`.
* `FrontierSampler.Example` — a complete worked instantiation, in 120 lines,
  with no dependencies.
-/
