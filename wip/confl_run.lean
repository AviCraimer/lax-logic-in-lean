import wip.confl_core
open PLLFormula PLLND PLLND.Search ConflCore
def main : IO Unit := do
  IO.println "########## SAMVAL same-trace refilter ##########"
  let vf := allCMs
  let vfC := vf.filter confluentB
  IO.println s!"### variable-free battery: {vf.length} models, {vfC.length} mutually confluent"
  let oa := allCMsA
  let oaC := oa.filter confluentB
  IO.println s!"### one-atom battery: {oa.length} models, {oaC.length} mutually confluent"
  -- decisive confluent passes FIRST (small, fast)
  runPass "one-atom CONFLUENT" formulasA closuresA oaC
  runPass "variable-free CONFLUENT" formulas closures vfC
  IO.println "########## MFORTH forth-m / fallible-pair refilter ##########"
  let allm := allCMs
  let confm := allm.filter confluentB
  IO.println s!"### mforth battery: {allm.length} frames, {confm.length} mutually confluent"
  runForthM "mforth CONFLUENT" confm
  -- slow unrestricted sanity reproductions LAST
  IO.println "########## SANITY (unrestricted, must reproduce pinned numbers) ##########"
  runForthM "mforth UNRESTRICTED (target 746108 / 0 / 22506)" allm
  runPass "one-atom UNRESTRICTED (target 499 / 44 / 12)" formulasA closuresA oa
