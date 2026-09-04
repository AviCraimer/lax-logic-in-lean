# Propositional Lax Logic

A Lean 4 implementation of the paper [Propositional Lax Logic](https://www.sciencedirect.com/science/article/pii/S0890540197926274) by Matt Fairtlough and Michael Mendler.

## Work in progress

Tooling: [`docs/search-manual.md`](docs/search-manual.md) — proof search and
countermodel search for PLL sequents (`LaxLogic/PLLSearch.lean`, with the
`#search` / `#refute` / `#refuteConf` / `#draw` commands in
`LaxLogic/PLLSearchCmd.lean` and `LaxLogic/PLLDiagramCmd.lean`).  §0 of the
manual is a one-table answer to "which command do I want?", and the trap it
names is the important one: a countermodel refutes **PCLL** only if it is
mutually confluent, so a PCLL claim wants `#refuteConf`, not `#refute`.
`LaxLogic/PLLSearchDemo.lean` is the same manual as a file to step through in
the info view.

