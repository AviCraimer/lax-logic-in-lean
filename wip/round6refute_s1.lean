import round6refute

/-! # ROUND 6 screen, stage 1 — calibration (both directions) + the July
family at `ctx = Gk` (d=9/8) in the sub-room band `b = 1..3`. -/

open PLLND.Round5Refute PLLND.Round6Refute

#eval banner6 "round 6, stage 1: calibration + July ctx=Gk sub-room band"
#eval runCalib6 cfg1
#eval runInst6 cfg1 60000 j11
#eval runInst6 cfg1 60000 j12
#eval runInst6 cfg1 60000 j13
#eval runInst6 cfg1 60000 j1A
#eval runInst6 cfg1 60000 j1B
#eval banner6 "stage 1 done"
