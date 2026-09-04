import frontier

/-! # Frontier sampler — campaign 2: the reachable `J = 1` band

Four strata aimed where campaign 1 measured the room-carrying statement to be
reachable at decide-feasible sizes.  `jb1-nbox` is a randomised generalisation
of PROGRESS §62's three residual `JB2` cells; `jb1-nbox2` is one `◯` beyond
them.  Appends to the same cumulative corpus.

    zsh wip/_probe_elab.sh 2400 frontier_run2
-/

open PLLND.Frontier

#eval campaignOf 40000 "c2" campaign2Strata
