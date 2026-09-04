import round5refute

/-! # ROUND 5 screen, stage 4 — the July `Skb` family at its OWN room
(`b = 63` at `ctx = Gk`; saturated `d = 1` variants at room 7), small
absolute fuels so the budget, not the fuel, is the live parameter. -/

open PLLND.Round5Refute

#eval banner "stage 4: July family at its own room"
#eval runInst cfg1 60000 i74
#eval runInst cfg1 60000 i75
#eval runInst cfg1 60000 i72
#eval runInst cfg1 60000 i73
#eval runInst cfg1 60000 i71
#eval banner "stage 4 done"
