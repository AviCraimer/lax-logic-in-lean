import frontier

/-! # Frontier sampler — campaign 1

Fifteen strata × 72 seeds, countermodel-only triage at a weight cap of
40 000.  Durable output: every cell appends and flushes one line to
`wip/frontier_corpus.txt` before the next cell starts, so a run stopped at
the wall-clock cap loses nothing.

Run it under the cap:

    zsh wip/_probe_elab.sh 3000 frontier_run
-/

open PLLND.Frontier

#eval campaign 40000 "c1"
