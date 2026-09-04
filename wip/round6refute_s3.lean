import round6refute

/-! # ROUND 6 screen, stage 3 — the round-5 families' SUB-ROOM siblings

Every instance here was screened by round 5 only at or above its room
floor (2–8); `runInst6`'s default grid `b = 1..3` puts each into the band
its floor excluded.  `i15`/`i53` are re-instanced onto the adaptive fuel
grid (their round-5 fuels were sized for rooms 6 and 8). -/

open PLLND.Round5Refute PLLND.Round6Refute

def j31 : PLLND.Round5Refute.BInst := { i15 with fuels := [] }
def j32 : PLLND.Round5Refute.BInst := { i53 with fuels := [] }

#eval banner6 "round 6, stage 3: round-5 families sub-room (b=1..3)"
#eval runInst6 cfg1 60000 i11
#eval runInst6 cfg1 60000 i12
#eval runInst6 cfg1 60000 i13
#eval runInst6 cfg1 60000 i14
#eval runInst6 cfg1 60000 j31
#eval runInst6 cfg1 60000 i21
#eval runInst6 cfg1 60000 i22
#eval runInst6 cfg1 60000 i31
#eval runInst6 cfg1 60000 i32
#eval runInst6 cfg1 60000 i33
#eval runInst6 cfg1 60000 i34
#eval runInst6 cfg1 60000 i35
#eval runInst6 cfg1 60000 i36
#eval runInst6 cfg1 60000 i41
#eval runInst6 cfg1 60000 i42
#eval runInst6 cfg1 60000 i43
#eval runInst6 cfg1 60000 i51
#eval runInst6 cfg1 60000 i52
#eval runInst6 cfg1 60000 j32
#eval runInst6 cfg1 60000 i61
#eval banner6 "stage 3 done"
