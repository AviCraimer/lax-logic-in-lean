import round5refute

/-! # ROUND 5 screen, stage 3 — the `⊃◯`-gate band (`J = 2`, room 4) and
the defect-2 rows (`J = 0` room 4, `J = 1` room 6, gate room 8). -/

open PLLND.Round5Refute

#eval banner "stage 3: gate band + defect 2"
#eval runInst cfg1 40000 i51
#eval runInst cfg1 40000 i52
#eval runInst cfg1 40000 i61
#eval runInst cfg1 40000 i42
#eval runInst cfg1 40000 i15
#eval runInst cfg1 40000 i53
#eval banner "stage 3 done"
