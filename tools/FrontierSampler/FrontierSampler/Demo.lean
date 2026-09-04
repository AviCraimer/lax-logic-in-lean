import FrontierSampler

/-!
# The demo executable

    lake exe fsdemo          -- run the example campaign, then replay it

Writes `frontier_example_corpus.txt` in the working directory.
-/

open FrontierSampler

def main : IO Unit := do
  IO.FS.writeFile "frontier_example_corpus.txt" ""
  IO.println "== campaign =="
  Example.run
  IO.println "== replay against a different property =="
  Example.replayIdempotent
