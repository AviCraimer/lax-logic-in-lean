import frontier

/-! # Frontier sampler — replay of the cumulative corpus

Three passes, all driven from `wip/frontier_corpus.txt` alone:

1. **Regression** — regenerate every recorded admissible cell from its
   `(stratum, seed, size)` and compare the recomputed shape columns with the
   recorded ones.  No search.  This is the determinism audit that makes every
   other use of the corpus meaningful; it also certifies that the
   `goalBoxDepth` refactor (added for campaign 2) left campaign 1's cells
   byte-identical.
2. **Re-aim I** — screen a DIFFERENT statement over the same instances: the
   room-free descent at the UNBOXED goal `D` in place of `◯D`.  That
   statement is refuted in the repository's inventory
   (`AscRefute.not_roomFreeDescent`), so this measures how far the `◯` is
   load-bearing across the sampled region, where
   `Round4Probe3.box_is_load_bearing` measured it at one instance.
3. **Re-aim II** — the statement with the AMBIENT premise dropped.

Durable output: `wip/frontier_replay.txt`.
-/

open PLLND.Frontier

#eval replayRegression
#eval replayUnboxed 40000
#eval replayNoAmbient 40000
