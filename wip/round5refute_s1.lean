import round5refute

/-! # ROUND 5 screen, stage 1 — calibration + the `J = 0` room-2 band
(atomic controls, nested `◯`, `∨`-bodies at defect 1). -/

open PLLND.Round5Refute

#eval banner "stage 1: calibration + J=0 room-2 band"
#eval runCalib cfg1
#eval runInst cfg1 30000 i35
#eval runInst cfg1 30000 i36
#eval runInst cfg1 30000 i31
#eval runInst cfg1 30000 i32
#eval runInst cfg1 30000 i33
#eval runInst cfg1 30000 i34
#eval runInst cfg1 30000 i41
#eval runInst cfg1 30000 i43
#eval banner "stage 1 done"
