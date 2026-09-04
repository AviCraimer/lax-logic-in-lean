import wip.rnDict2Hand

/-!
# The enlarged RN(◯,{}) dictionary round: 16 representatives

GENERATED FILE — do not edit by hand.  Produced by
`wip/rnDictGen.lean` (`pending2` / `cells2` / `assemble2` modes).

The 15 certified dictionary classes of `wip/rnDict.lean` enlarged by
the distinct classes among the §40 closure-failure witnesses after
pairwise separation (`wip/rnSep.lean`: w1 ≡ w2 ≡ w3, so q15 is the
class of q9 ⊃ q4 ≡ q8 ∧ q10 ≡ q12 ⊃ q4), closed under
∧/∨/⊃/◯ for ONE round with kernel-checked `Interd` certificates.
Old certified cells reference their `wip.rnDict` theorems by name;
old sorried cells and all new cells were re-resolved with the
escalated stages (exhaustive ≤4-world battery, exhaustive rooted
5-world battery, budgeted G4iLL″ search with cut-chains through all
19 representatives).  Cells that still resist are recorded as sorried
lemmas (OPEN, with candidate shortlists) or as REFUTED CELLS (new
classes beyond the 19 — the closure fails there; witness theorems in
`wip/rnDictRefute2.lean`).
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND2

open RND

/-! ## The four new representatives -/

def q15 : PLLFormula := (.ifThen q9 q4)

def repsL2 : List PLLFormula := [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]

def rep2 : Fin 16 → PLLFormula := fun i => repsL2.getD i.val .falsePLL

/-! ## The closure tables -/

def and2T : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [0, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
   [0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3],
   [0, 4, 2, 3, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4],
   [0, 5, 2, 3, 4, 5, 2, 4, 4, 5, 5, 5, 5, 5, 5, 4],
   [0, 6, 2, 0, 2, 2, 6, 6, 6, 6, 2, 6, 6, 6, 6, 2],
   [0, 7, 2, 3, 4, 4, 6, 7, 7, 7, 4, 7, 7, 7, 7, 4],
   [0, 8, 2, 3, 4, 4, 6, 7, 8, 7, 15, 0, 0, 8, 0, 15],
   [0, 9, 2, 3, 4, 5, 6, 7, 7, 9, 5, 9, 9, 9, 9, 4],
   [0, 10, 2, 3, 4, 5, 2, 4, 15, 5, 10, 10, 5, 0, 5, 15],
   [0, 11, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 9, 0, 9, 15],
   [0, 12, 2, 3, 4, 5, 6, 7, 0, 9, 5, 9, 12, 12, 12, 4],
   [0, 13, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 12, 13, 0, 15],
   [0, 14, 2, 3, 4, 5, 6, 7, 0, 9, 5, 9, 12, 0, 14, 4],
   [0, 15, 2, 3, 4, 4, 2, 4, 15, 4, 15, 15, 4, 15, 4, 15]]
def or2T : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [2, 1, 2, 4, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [3, 1, 4, 3, 4, 5, 7, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [4, 1, 4, 4, 4, 5, 7, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [5, 1, 5, 5, 5, 5, 9, 9, 0, 9, 10, 11, 12, 13, 14, 0],
   [6, 1, 6, 7, 7, 9, 6, 7, 8, 9, 11, 11, 12, 13, 14, 0],
   [7, 1, 7, 7, 7, 9, 7, 7, 8, 9, 11, 11, 12, 13, 14, 0],
   [8, 1, 8, 8, 8, 0, 8, 8, 8, 0, 0, 0, 0, 13, 0, 8],
   [9, 1, 9, 9, 9, 9, 9, 9, 0, 9, 11, 11, 12, 13, 14, 0],
   [10, 1, 10, 10, 10, 10, 11, 11, 0, 11, 10, 11, 0, 0, 0, 10],
   [11, 1, 11, 11, 11, 11, 11, 11, 0, 11, 11, 11, 0, 0, 0, 11],
   [12, 1, 12, 12, 12, 12, 12, 12, 0, 12, 0, 0, 12, 13, 14, 0],
   [13, 1, 13, 13, 13, 13, 13, 13, 13, 13, 0, 0, 13, 13, 0, 13],
   [14, 1, 14, 14, 14, 14, 14, 14, 0, 14, 0, 0, 14, 0, 14, 0],
   [15, 1, 15, 15, 15, 0, 0, 0, 8, 0, 10, 11, 0, 13, 0, 15]]
def imp2T : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [3, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [6, 1, 6, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 6, 3, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 6, 3, 8, 1, 6, 8, 8, 1, 1, 1, 1, 1, 1, 8],
   [3, 1, 10, 3, 10, 10, 1, 1, 1, 1, 10, 1, 1, 1, 1, 10],
   [0, 1, 2, 3, 10, 10, 6, 1, 1, 1, 10, 1, 1, 1, 1, 10],
   [0, 1, 2, 3, 0, 0, 6, 0, 1, 0, 10, 0, 0, 1, 0, 10],
   [0, 1, 2, 3, 15, 10, 6, 8, 8, 1, 10, 1, 1, 1, 1, 15],
   [0, 1, 6, 3, 0, 14, 6, 0, 8, 14, 1, 1, 14, 0, 14, 8],
   [0, 1, 2, 3, 4, 5, 6, 0, 8, 14, 10, 1, 14, 0, 14, 15],
   [0, 1, 2, 3, 15, 10, 6, 0, 8, 0, 10, 0, 1, 1, 1, 15],
   [0, 1, 2, 3, 4, 0, 6, 7, 8, 0, 10, 0, 0, 1, 0, 15],
   [0, 1, 2, 3, 15, 10, 6, 0, 8, 0, 10, 0, 0, 0, 1, 15],
   [0, 1, 6, 3, 0, 0, 6, 0, 1, 0, 1, 1, 0, 1, 0, 1]]

def box2T : List Nat := [2, 1, 2, 5, 5, 5, 6, 12, 13, 12, 10, 0, 12, 13, 14, 0]

def and2Idx (i j : Fin 16) : Fin 16 :=
  ⟨((and2T.getD i.val []).getD j.val 0) % 16, Nat.mod_lt _ (by decide)⟩

def or2Idx (i j : Fin 16) : Fin 16 :=
  ⟨((or2T.getD i.val []).getD j.val 0) % 16, Nat.mod_lt _ (by decide)⟩

def imp2Idx (i j : Fin 16) : Fin 16 :=
  ⟨((imp2T.getD i.val []).getD j.val 0) % 16, Nat.mod_lt _ (by decide)⟩

def box2Idx (i : Fin 16) : Fin 16 :=
  ⟨(box2T.getD i.val 0) % 16, Nat.mod_lt _ (by decide)⟩

/-! ## Searched-cell certificates (escalated round) -/

theorem cAnd_2_15 : Interd (q2.and q15) q2 :=
  ⟨(ofG4 (.andL (A := q2) (B := q15) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))))),
   (ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.impR (.orR1 (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_3_15 : Interd (q3.and q15) q3 :=
  ⟨(ofG4 (.impR (.andL (A := q3) (B := q15) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _)))))),
   (ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impR (.orR2 (.impR (.orL (A := q5) (B := q6) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.laxL (A := q0) (.tail _ (.tail _ (.head _))) (.botL (.head _))) (.botL (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

theorem cAnd_4_14 : Interd (q4.and q14) q4 := hand_cAnd_4_14

theorem cAnd_4_15 : Interd (q4.and q15) q4 :=
  ⟨(ofG4 (.andL (A := q4) (B := q15) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))),
   (ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q5) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cAnd_5_15 : Interd (q5.and q15) q4 :=
  ⟨(ofG4 (.andL (A := q5) (B := q15) (.head _) (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))),
   (ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q5) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cAnd_6_15 : Interd (q6.and q15) q2 :=
  ⟨(ofG4 (.andL (A := q6) (B := q15) (.head _) (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))),
   (ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))) (.impR (.orR1 (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_7_15 : Interd (q7.and q15) q4 :=
  ⟨(ofG4 (.andL (A := q7) (B := q15) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.tail _ (.head _))) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))),
   (ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q5) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cAnd_8_10 : Interd (q8.and q10) q15 := hand_cAnd_8_10

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cAnd_8_11 : Interd (q8.and q11) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cAnd_8_12 : Interd (q8.and q12) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cAnd_8_14 : Interd (q8.and q14) q0 := sorry

theorem cAnd_8_15 : Interd (q8.and q15) q15 := hand_cAnd_8_15

theorem cAnd_9_13 : Interd (q9.and q13) q9 := hand_cAnd_9_13

theorem cAnd_9_14 : Interd (q9.and q14) q9 := hand_cAnd_9_14

theorem cAnd_9_15 : Interd (q9.and q15) q4 := hand_cAnd_9_15

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cAnd_10_13 : Interd (q10.and q13) q0 := sorry

theorem cAnd_10_14 : Interd (q10.and q14) q5 := hand_cAnd_10_14

theorem cAnd_10_15 : Interd (q10.and q15) q15 := hand_cAnd_10_15

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cAnd_11_13 : Interd (q11.and q13) q0 := sorry

theorem cAnd_11_14 : Interd (q11.and q14) q9 := hand_cAnd_11_14

theorem cAnd_11_15 : Interd (q11.and q15) q15 := hand_cAnd_11_15

theorem cAnd_12_13 : Interd (q12.and q13) q12 := hand_cAnd_12_13

theorem cAnd_12_14 : Interd (q12.and q14) q12 := hand_cAnd_12_14

theorem cAnd_12_15 : Interd (q12.and q15) q4 := hand_cAnd_12_15

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cAnd_13_14 : Interd (q13.and q14) q0 := sorry

theorem cAnd_13_15 : Interd (q13.and q15) q15 := hand_cAnd_13_15

theorem cAnd_14_15 : Interd (q14.and q15) q4 := hand_cAnd_14_15

theorem cOr_2_13 : Interd (q2.or q13) q13 := hand_cOr_2_13

theorem cOr_2_14 : Interd (q2.or q14) q14 := hand_cOr_2_14

theorem cOr_2_15 : Interd (q2.or q15) q15 := hand_cOr_2_15

theorem cOr_3_13 : Interd (q3.or q13) q13 := hand_cOr_3_13

theorem cOr_3_14 : Interd (q3.or q14) q14 := hand_cOr_3_14

theorem cOr_3_15 : Interd (q3.or q15) q15 := hand_cOr_3_15

theorem cOr_4_14 : Interd (q4.or q14) q14 := hand_cOr_4_14

theorem cOr_4_15 : Interd (q4.or q15) q15 := hand_cOr_4_15

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_5_8 : Interd (q5.or q8) q0 := sorry

theorem cOr_5_14 : Interd (q5.or q14) q14 := hand_cOr_5_14

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_5_15 : Interd (q5.or q15) q0 := sorry

theorem cOr_6_13 : Interd (q6.or q13) q13 := hand_cOr_6_13

theorem cOr_6_14 : Interd (q6.or q14) q14 := hand_cOr_6_14

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_6_15 : Interd (q6.or q15) q0 := sorry

theorem cOr_7_13 : Interd (q7.or q13) q13 := hand_cOr_7_13

theorem cOr_7_14 : Interd (q7.or q14) q14 := hand_cOr_7_14

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_7_15 : Interd (q7.or q15) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_8_9 : Interd (q8.or q9) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_8_10 : Interd (q8.or q10) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_8_11 : Interd (q8.or q11) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_8_12 : Interd (q8.or q12) q0 := sorry

theorem cOr_8_13 : Interd (q8.or q13) q13 := hand_cOr_8_13

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_8_14 : Interd (q8.or q14) q0 := sorry

theorem cOr_8_15 : Interd (q8.or q15) q8 := hand_cOr_8_15

theorem cOr_9_13 : Interd (q9.or q13) q13 := hand_cOr_9_13

theorem cOr_9_14 : Interd (q9.or q14) q14 := hand_cOr_9_14

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_9_15 : Interd (q9.or q15) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_10_12 : Interd (q10.or q12) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_10_13 : Interd (q10.or q13) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_10_14 : Interd (q10.or q14) q0 := sorry

theorem cOr_10_15 : Interd (q10.or q15) q10 :=
  ⟨(ofG4 (.impR (.orL (A := q10) (B := q15) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))) (.impLOr (A := q5) (B := q6) (D := q4) (.head _) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))),
   (ofG4 (.orR1 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_11_12 : Interd (q11.or q12) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_11_13 : Interd (q11.or q13) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_11_14 : Interd (q11.or q14) q0 := sorry

theorem cOr_11_15 : Interd (q11.or q15) q11 := hand_cOr_11_15

theorem cOr_12_13 : Interd (q12.or q13) q13 := hand_cOr_12_13

theorem cOr_12_14 : Interd (q12.or q14) q14 := hand_cOr_12_14

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_12_15 : Interd (q12.or q15) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_13_14 : Interd (q13.or q14) q0 := sorry

theorem cOr_13_15 : Interd (q13.or q15) q13 := hand_cOr_13_15

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cOr_14_15 : Interd (q14.or q15) q0 := sorry

theorem cImp_2_15 : Interd (q2.ifThen q15) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.orR1 (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))))⟩

theorem cImp_3_15 : Interd (q3.ifThen q15) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.orR2 (.impR (.orL (A := q5) (B := q6) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.laxL (A := q0) (.tail _ (.tail _ (.head _))) (.botL (.head _))) (.botL (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))))))))⟩

theorem cImp_4_15 : Interd (q4.ifThen q15) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.orL (A := q5) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cImp_5_15 : Interd (q5.ifThen q15) q8 := hand_cImp_5_15

theorem cImp_6_15 : Interd (q6.ifThen q15) q10 :=
  ⟨(ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q15) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLOr (A := q5) (B := q6) (D := q4) (.head _) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))),
   (ofG4 (.impR (.impR (.orR1 (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cImp_7_15 : Interd (q7.ifThen q15) q10 := hand_cImp_7_15

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_8_4 : Interd (q8.ifThen q4) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_8_5 : Interd (q8.ifThen q5) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_8_7 : Interd (q8.ifThen q7) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_8_9 : Interd (q8.ifThen q9) q0 := sorry

theorem cImp_8_10 : Interd (q8.ifThen q10) q10 := hand_cImp_8_10

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_8_11 : Interd (q8.ifThen q11) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_8_12 : Interd (q8.ifThen q12) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_8_14 : Interd (q8.ifThen q14) q0 := sorry

theorem cImp_8_15 : Interd (q8.ifThen q15) q10 := hand_cImp_8_15

theorem cImp_9_8 : Interd (q9.ifThen q8) q8 := hand_cImp_9_8

theorem cImp_9_15 : Interd (q9.ifThen q15) q15 := hand_cImp_9_15

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_10_4 : Interd (q10.ifThen q4) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_10_7 : Interd (q10.ifThen q7) q0 := sorry

theorem cImp_10_8 : Interd (q10.ifThen q8) q8 := hand_cImp_10_8

theorem cImp_10_9 : Interd (q10.ifThen q9) q14 := hand_cImp_10_9

theorem cImp_10_12 : Interd (q10.ifThen q12) q14 := hand_cImp_10_12

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_10_13 : Interd (q10.ifThen q13) q0 := sorry

theorem cImp_10_14 : Interd (q10.ifThen q14) q14 := hand_cImp_10_14

theorem cImp_10_15 : Interd (q10.ifThen q15) q8 := hand_cImp_10_15

theorem cImp_11_4 : Interd (q11.ifThen q4) q4 := hand_cImp_11_4

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_11_7 : Interd (q11.ifThen q7) q0 := sorry

theorem cImp_11_8 : Interd (q11.ifThen q8) q8 := hand_cImp_11_8

theorem cImp_11_9 : Interd (q11.ifThen q9) q14 := hand_cImp_11_9

theorem cImp_11_12 : Interd (q11.ifThen q12) q14 := hand_cImp_11_12

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_11_13 : Interd (q11.ifThen q13) q0 := sorry

theorem cImp_11_14 : Interd (q11.ifThen q14) q14 := hand_cImp_11_14

theorem cImp_11_15 : Interd (q11.ifThen q15) q15 := hand_cImp_11_15

theorem cImp_12_4 : Interd (q12.ifThen q4) q15 := hand_cImp_12_4

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_12_7 : Interd (q12.ifThen q7) q0 := sorry

theorem cImp_12_8 : Interd (q12.ifThen q8) q8 := hand_cImp_12_8

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_12_9 : Interd (q12.ifThen q9) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_12_11 : Interd (q12.ifThen q11) q0 := sorry

theorem cImp_12_15 : Interd (q12.ifThen q15) q15 := hand_cImp_12_15

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_13_5 : Interd (q13.ifThen q5) q0 := sorry

theorem cImp_13_8 : Interd (q13.ifThen q8) q8 := hand_cImp_13_8

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_13_9 : Interd (q13.ifThen q9) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_13_11 : Interd (q13.ifThen q11) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_13_12 : Interd (q13.ifThen q12) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_13_14 : Interd (q13.ifThen q14) q0 := sorry

theorem cImp_13_15 : Interd (q13.ifThen q15) q15 := hand_cImp_13_15

theorem cImp_14_4 : Interd (q14.ifThen q4) q15 := coll_w2_w4.symm

theorem cImp_14_5 : Interd (q14.ifThen q5) q10 := hand_cImp_14_5

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_14_7 : Interd (q14.ifThen q7) q0 := sorry

theorem cImp_14_8 : Interd (q14.ifThen q8) q8 := hand_cImp_14_8

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_14_9 : Interd (q14.ifThen q9) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_14_11 : Interd (q14.ifThen q11) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_14_12 : Interd (q14.ifThen q12) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 16 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_14_13 : Interd (q14.ifThen q13) q0 := sorry

theorem cImp_14_15 : Interd (q14.ifThen q15) q15 := hand_cImp_14_15

theorem cImp_15_0 : Interd (q15.ifThen q0) q0 :=
  ⟨(ofG4 (.impLImp (A := q9) (B := q4) (D := q0) (.head _) (.impR (.orR1 (.laxR (.orL (A := q5) (B := q6) (.head _) (.impLOr (A := q2) (B := q3) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLOr (A := q2) (B := q3) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))))) (.botL (.head _)))),
   (ofG4 (.botL (.head _)))⟩

theorem cImp_15_2 : Interd (q15.ifThen q2) q6 :=
  ⟨(ofG4 (.impR (.impLImp (A := q9) (B := q4) (D := q2) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.orL (A := q5) (B := q6) (.head _) (.impLOr (A := q2) (B := q3) (D := q2) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q2) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLOr (A := q2) (B := q3) (D := q2) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))),
   (ofG4 (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.head _) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

theorem cImp_15_3 : Interd (q15.ifThen q3) q3 :=
  ⟨(ofG4 (.impR (.impLImp (A := q9) (B := q4) (D := q3) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.orL (A := q5) (B := q6) (.head _) (.impLOr (A := q2) (B := q3) (D := q3) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q3) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.laxL (A := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.botL (.head _))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLOr (A := q2) (B := q3) (D := q3) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLLaxLax (A := q0) (B := q3) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _)))))) (.botL (.head _))))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))),
   (ofG4 (.impR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLax (A := q3) (B := q4) (.head _) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _))))))))⟩

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_15_4 : Interd (q15.ifThen q4) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_15_5 : Interd (q15.ifThen q5) q0 := sorry

theorem cImp_15_6 : Interd (q15.ifThen q6) q6 :=
  ⟨(ofG4 (.impR (.impLImp (A := q9) (B := q4) (D := q6) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.orL (A := q5) (B := q6) (.head _) (.impLOr (A := q2) (B := q3) (D := q6) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q6) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q6) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLOr (A := q2) (B := q3) (D := q6) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))),
   (ofG4 (.impR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLax (A := q3) (B := q4) (.head _) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_15_7 : Interd (q15.ifThen q7) q0 := sorry

theorem cImp_15_8 : Interd (q15.ifThen q8) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))))⟩

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_15_9 : Interd (q15.ifThen q9) q0 := sorry

theorem cImp_15_10 : Interd (q15.ifThen q10) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cImp_15_11 : Interd (q15.ifThen q11) q1 :=
  ⟨topD,
   (ofG4 (.impR (.orR2 (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))))⟩

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_15_12 : Interd (q15.ifThen q12) q0 := sorry

theorem cImp_15_13 : Interd (q15.ifThen q13) q1 :=
  ⟨topD,
   (ofG4 (.impR (.laxR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))))))⟩

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cImp_15_14 : Interd (q15.ifThen q14) q0 := sorry

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cBox_11 : Interd q11.somehow q0 := sorry

theorem cBox_14 : Interd q14.somehow q14 := hand_cBox_14

/-- REFUTED CELL (new class): certified ≤5-world countermodels
eliminate EVERY candidate — this combination is not interderivable
with any of the 19 representatives, so the enlarged closure FAILS
here.  The stated collapse (to q0, a placeholder) is FALSE; the
`sorry` records the failure point. -/
theorem cBox_15 : Interd q15.somehow q0 := sorry

/-! ## The closure theorems -/

theorem and2_ok (i j : Fin 16) :
    Interd ((rep2 i).and (rep2 j)) (rep2 (and2Idx i j)) :=
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨1, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨2, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨3, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨4, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨5, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨6, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨7, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨8, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨9, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨10, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨11, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨12, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨13, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨14, _⟩ => bot_and_i _
  | ⟨0, _⟩, ⟨15, _⟩ => bot_and_i _
  | ⟨1, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨1, _⟩, ⟨1, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨2, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨3, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨4, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨5, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨6, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨7, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨8, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨9, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨10, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨11, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨12, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨13, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨14, _⟩ => top_and_i _
  | ⟨1, _⟩, ⟨15, _⟩ => top_and_i _
  | ⟨2, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨2, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨2, _⟩, ⟨2, _⟩ => and_idem_i _
  | ⟨2, _⟩, ⟨3, _⟩ => cAnd_2_3
  | ⟨2, _⟩, ⟨4, _⟩ => cAnd_2_4
  | ⟨2, _⟩, ⟨5, _⟩ => cAnd_2_5
  | ⟨2, _⟩, ⟨6, _⟩ => cAnd_2_6
  | ⟨2, _⟩, ⟨7, _⟩ => cAnd_2_7
  | ⟨2, _⟩, ⟨8, _⟩ => cAnd_2_8
  | ⟨2, _⟩, ⟨9, _⟩ => cAnd_2_9
  | ⟨2, _⟩, ⟨10, _⟩ => cAnd_2_10
  | ⟨2, _⟩, ⟨11, _⟩ => cAnd_2_11
  | ⟨2, _⟩, ⟨12, _⟩ => cAnd_2_12
  | ⟨2, _⟩, ⟨13, _⟩ => cAnd_2_13
  | ⟨2, _⟩, ⟨14, _⟩ => cAnd_2_14
  | ⟨2, _⟩, ⟨15, _⟩ => cAnd_2_15
  | ⟨3, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨3, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨3, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_3)
  | ⟨3, _⟩, ⟨3, _⟩ => and_idem_i _
  | ⟨3, _⟩, ⟨4, _⟩ => cAnd_3_4
  | ⟨3, _⟩, ⟨5, _⟩ => cAnd_3_5
  | ⟨3, _⟩, ⟨6, _⟩ => cAnd_3_6
  | ⟨3, _⟩, ⟨7, _⟩ => cAnd_3_7
  | ⟨3, _⟩, ⟨8, _⟩ => cAnd_3_8
  | ⟨3, _⟩, ⟨9, _⟩ => cAnd_3_9
  | ⟨3, _⟩, ⟨10, _⟩ => cAnd_3_10
  | ⟨3, _⟩, ⟨11, _⟩ => cAnd_3_11
  | ⟨3, _⟩, ⟨12, _⟩ => cAnd_3_12
  | ⟨3, _⟩, ⟨13, _⟩ => cAnd_3_13
  | ⟨3, _⟩, ⟨14, _⟩ => cAnd_3_14
  | ⟨3, _⟩, ⟨15, _⟩ => cAnd_3_15
  | ⟨4, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨4, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨4, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_4)
  | ⟨4, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_4)
  | ⟨4, _⟩, ⟨4, _⟩ => and_idem_i _
  | ⟨4, _⟩, ⟨5, _⟩ => cAnd_4_5
  | ⟨4, _⟩, ⟨6, _⟩ => cAnd_4_6
  | ⟨4, _⟩, ⟨7, _⟩ => cAnd_4_7
  | ⟨4, _⟩, ⟨8, _⟩ => cAnd_4_8
  | ⟨4, _⟩, ⟨9, _⟩ => cAnd_4_9
  | ⟨4, _⟩, ⟨10, _⟩ => cAnd_4_10
  | ⟨4, _⟩, ⟨11, _⟩ => cAnd_4_11
  | ⟨4, _⟩, ⟨12, _⟩ => cAnd_4_12
  | ⟨4, _⟩, ⟨13, _⟩ => cAnd_4_13
  | ⟨4, _⟩, ⟨14, _⟩ => cAnd_4_14
  | ⟨4, _⟩, ⟨15, _⟩ => cAnd_4_15
  | ⟨5, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨5, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨5, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_5)
  | ⟨5, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_5)
  | ⟨5, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_5)
  | ⟨5, _⟩, ⟨5, _⟩ => and_idem_i _
  | ⟨5, _⟩, ⟨6, _⟩ => cAnd_5_6
  | ⟨5, _⟩, ⟨7, _⟩ => cAnd_5_7
  | ⟨5, _⟩, ⟨8, _⟩ => cAnd_5_8
  | ⟨5, _⟩, ⟨9, _⟩ => cAnd_5_9
  | ⟨5, _⟩, ⟨10, _⟩ => cAnd_5_10
  | ⟨5, _⟩, ⟨11, _⟩ => cAnd_5_11
  | ⟨5, _⟩, ⟨12, _⟩ => cAnd_5_12
  | ⟨5, _⟩, ⟨13, _⟩ => cAnd_5_13
  | ⟨5, _⟩, ⟨14, _⟩ => cAnd_5_14
  | ⟨5, _⟩, ⟨15, _⟩ => cAnd_5_15
  | ⟨6, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨6, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨6, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_6)
  | ⟨6, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_6)
  | ⟨6, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_6)
  | ⟨6, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_6)
  | ⟨6, _⟩, ⟨6, _⟩ => and_idem_i _
  | ⟨6, _⟩, ⟨7, _⟩ => cAnd_6_7
  | ⟨6, _⟩, ⟨8, _⟩ => cAnd_6_8
  | ⟨6, _⟩, ⟨9, _⟩ => cAnd_6_9
  | ⟨6, _⟩, ⟨10, _⟩ => cAnd_6_10
  | ⟨6, _⟩, ⟨11, _⟩ => cAnd_6_11
  | ⟨6, _⟩, ⟨12, _⟩ => cAnd_6_12
  | ⟨6, _⟩, ⟨13, _⟩ => cAnd_6_13
  | ⟨6, _⟩, ⟨14, _⟩ => cAnd_6_14
  | ⟨6, _⟩, ⟨15, _⟩ => cAnd_6_15
  | ⟨7, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨7, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨7, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_7)
  | ⟨7, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_7)
  | ⟨7, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_7)
  | ⟨7, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_7)
  | ⟨7, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_7)
  | ⟨7, _⟩, ⟨7, _⟩ => and_idem_i _
  | ⟨7, _⟩, ⟨8, _⟩ => cAnd_7_8
  | ⟨7, _⟩, ⟨9, _⟩ => cAnd_7_9
  | ⟨7, _⟩, ⟨10, _⟩ => cAnd_7_10
  | ⟨7, _⟩, ⟨11, _⟩ => cAnd_7_11
  | ⟨7, _⟩, ⟨12, _⟩ => cAnd_7_12
  | ⟨7, _⟩, ⟨13, _⟩ => cAnd_7_13
  | ⟨7, _⟩, ⟨14, _⟩ => cAnd_7_14
  | ⟨7, _⟩, ⟨15, _⟩ => cAnd_7_15
  | ⟨8, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨8, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨8, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_8)
  | ⟨8, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_8)
  | ⟨8, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_8)
  | ⟨8, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_8)
  | ⟨8, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_8)
  | ⟨8, _⟩, ⟨7, _⟩ => (and_comm_i _ _).trans (cAnd_7_8)
  | ⟨8, _⟩, ⟨8, _⟩ => and_idem_i _
  | ⟨8, _⟩, ⟨9, _⟩ => cAnd_8_9
  | ⟨8, _⟩, ⟨10, _⟩ => cAnd_8_10
  | ⟨8, _⟩, ⟨11, _⟩ => cAnd_8_11
  | ⟨8, _⟩, ⟨12, _⟩ => cAnd_8_12
  | ⟨8, _⟩, ⟨13, _⟩ => cAnd_8_13
  | ⟨8, _⟩, ⟨14, _⟩ => cAnd_8_14
  | ⟨8, _⟩, ⟨15, _⟩ => cAnd_8_15
  | ⟨9, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨9, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨9, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_9)
  | ⟨9, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_9)
  | ⟨9, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_9)
  | ⟨9, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_9)
  | ⟨9, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_9)
  | ⟨9, _⟩, ⟨7, _⟩ => (and_comm_i _ _).trans (cAnd_7_9)
  | ⟨9, _⟩, ⟨8, _⟩ => (and_comm_i _ _).trans (cAnd_8_9)
  | ⟨9, _⟩, ⟨9, _⟩ => and_idem_i _
  | ⟨9, _⟩, ⟨10, _⟩ => cAnd_9_10
  | ⟨9, _⟩, ⟨11, _⟩ => cAnd_9_11
  | ⟨9, _⟩, ⟨12, _⟩ => cAnd_9_12
  | ⟨9, _⟩, ⟨13, _⟩ => cAnd_9_13
  | ⟨9, _⟩, ⟨14, _⟩ => cAnd_9_14
  | ⟨9, _⟩, ⟨15, _⟩ => cAnd_9_15
  | ⟨10, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨10, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨10, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_10)
  | ⟨10, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_10)
  | ⟨10, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_10)
  | ⟨10, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_10)
  | ⟨10, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_10)
  | ⟨10, _⟩, ⟨7, _⟩ => (and_comm_i _ _).trans (cAnd_7_10)
  | ⟨10, _⟩, ⟨8, _⟩ => (and_comm_i _ _).trans (cAnd_8_10)
  | ⟨10, _⟩, ⟨9, _⟩ => (and_comm_i _ _).trans (cAnd_9_10)
  | ⟨10, _⟩, ⟨10, _⟩ => and_idem_i _
  | ⟨10, _⟩, ⟨11, _⟩ => cAnd_10_11
  | ⟨10, _⟩, ⟨12, _⟩ => cAnd_10_12
  | ⟨10, _⟩, ⟨13, _⟩ => cAnd_10_13
  | ⟨10, _⟩, ⟨14, _⟩ => cAnd_10_14
  | ⟨10, _⟩, ⟨15, _⟩ => cAnd_10_15
  | ⟨11, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨11, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨11, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_11)
  | ⟨11, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_11)
  | ⟨11, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_11)
  | ⟨11, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_11)
  | ⟨11, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_11)
  | ⟨11, _⟩, ⟨7, _⟩ => (and_comm_i _ _).trans (cAnd_7_11)
  | ⟨11, _⟩, ⟨8, _⟩ => (and_comm_i _ _).trans (cAnd_8_11)
  | ⟨11, _⟩, ⟨9, _⟩ => (and_comm_i _ _).trans (cAnd_9_11)
  | ⟨11, _⟩, ⟨10, _⟩ => (and_comm_i _ _).trans (cAnd_10_11)
  | ⟨11, _⟩, ⟨11, _⟩ => and_idem_i _
  | ⟨11, _⟩, ⟨12, _⟩ => cAnd_11_12
  | ⟨11, _⟩, ⟨13, _⟩ => cAnd_11_13
  | ⟨11, _⟩, ⟨14, _⟩ => cAnd_11_14
  | ⟨11, _⟩, ⟨15, _⟩ => cAnd_11_15
  | ⟨12, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨12, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨12, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_12)
  | ⟨12, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_12)
  | ⟨12, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_12)
  | ⟨12, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_12)
  | ⟨12, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_12)
  | ⟨12, _⟩, ⟨7, _⟩ => (and_comm_i _ _).trans (cAnd_7_12)
  | ⟨12, _⟩, ⟨8, _⟩ => (and_comm_i _ _).trans (cAnd_8_12)
  | ⟨12, _⟩, ⟨9, _⟩ => (and_comm_i _ _).trans (cAnd_9_12)
  | ⟨12, _⟩, ⟨10, _⟩ => (and_comm_i _ _).trans (cAnd_10_12)
  | ⟨12, _⟩, ⟨11, _⟩ => (and_comm_i _ _).trans (cAnd_11_12)
  | ⟨12, _⟩, ⟨12, _⟩ => and_idem_i _
  | ⟨12, _⟩, ⟨13, _⟩ => cAnd_12_13
  | ⟨12, _⟩, ⟨14, _⟩ => cAnd_12_14
  | ⟨12, _⟩, ⟨15, _⟩ => cAnd_12_15
  | ⟨13, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨13, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨13, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_13)
  | ⟨13, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_13)
  | ⟨13, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_13)
  | ⟨13, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_13)
  | ⟨13, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_13)
  | ⟨13, _⟩, ⟨7, _⟩ => (and_comm_i _ _).trans (cAnd_7_13)
  | ⟨13, _⟩, ⟨8, _⟩ => (and_comm_i _ _).trans (cAnd_8_13)
  | ⟨13, _⟩, ⟨9, _⟩ => (and_comm_i _ _).trans (cAnd_9_13)
  | ⟨13, _⟩, ⟨10, _⟩ => (and_comm_i _ _).trans (cAnd_10_13)
  | ⟨13, _⟩, ⟨11, _⟩ => (and_comm_i _ _).trans (cAnd_11_13)
  | ⟨13, _⟩, ⟨12, _⟩ => (and_comm_i _ _).trans (cAnd_12_13)
  | ⟨13, _⟩, ⟨13, _⟩ => and_idem_i _
  | ⟨13, _⟩, ⟨14, _⟩ => cAnd_13_14
  | ⟨13, _⟩, ⟨15, _⟩ => cAnd_13_15
  | ⟨14, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨14, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨14, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_14)
  | ⟨14, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_14)
  | ⟨14, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_14)
  | ⟨14, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_14)
  | ⟨14, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_14)
  | ⟨14, _⟩, ⟨7, _⟩ => (and_comm_i _ _).trans (cAnd_7_14)
  | ⟨14, _⟩, ⟨8, _⟩ => (and_comm_i _ _).trans (cAnd_8_14)
  | ⟨14, _⟩, ⟨9, _⟩ => (and_comm_i _ _).trans (cAnd_9_14)
  | ⟨14, _⟩, ⟨10, _⟩ => (and_comm_i _ _).trans (cAnd_10_14)
  | ⟨14, _⟩, ⟨11, _⟩ => (and_comm_i _ _).trans (cAnd_11_14)
  | ⟨14, _⟩, ⟨12, _⟩ => (and_comm_i _ _).trans (cAnd_12_14)
  | ⟨14, _⟩, ⟨13, _⟩ => (and_comm_i _ _).trans (cAnd_13_14)
  | ⟨14, _⟩, ⟨14, _⟩ => and_idem_i _
  | ⟨14, _⟩, ⟨15, _⟩ => cAnd_14_15
  | ⟨15, _⟩, ⟨0, _⟩ => (and_comm_i _ _).trans (bot_and_i _)
  | ⟨15, _⟩, ⟨1, _⟩ => (and_comm_i _ _).trans (top_and_i _)
  | ⟨15, _⟩, ⟨2, _⟩ => (and_comm_i _ _).trans (cAnd_2_15)
  | ⟨15, _⟩, ⟨3, _⟩ => (and_comm_i _ _).trans (cAnd_3_15)
  | ⟨15, _⟩, ⟨4, _⟩ => (and_comm_i _ _).trans (cAnd_4_15)
  | ⟨15, _⟩, ⟨5, _⟩ => (and_comm_i _ _).trans (cAnd_5_15)
  | ⟨15, _⟩, ⟨6, _⟩ => (and_comm_i _ _).trans (cAnd_6_15)
  | ⟨15, _⟩, ⟨7, _⟩ => (and_comm_i _ _).trans (cAnd_7_15)
  | ⟨15, _⟩, ⟨8, _⟩ => (and_comm_i _ _).trans (cAnd_8_15)
  | ⟨15, _⟩, ⟨9, _⟩ => (and_comm_i _ _).trans (cAnd_9_15)
  | ⟨15, _⟩, ⟨10, _⟩ => (and_comm_i _ _).trans (cAnd_10_15)
  | ⟨15, _⟩, ⟨11, _⟩ => (and_comm_i _ _).trans (cAnd_11_15)
  | ⟨15, _⟩, ⟨12, _⟩ => (and_comm_i _ _).trans (cAnd_12_15)
  | ⟨15, _⟩, ⟨13, _⟩ => (and_comm_i _ _).trans (cAnd_13_15)
  | ⟨15, _⟩, ⟨14, _⟩ => (and_comm_i _ _).trans (cAnd_14_15)
  | ⟨15, _⟩, ⟨15, _⟩ => and_idem_i _
  | ⟨_+16, h⟩, _ => absurd h (by omega)
  | _, ⟨_+16, h⟩ => absurd h (by omega)

theorem or2_ok (i j : Fin 16) :
    Interd ((rep2 i).or (rep2 j)) (rep2 (or2Idx i j)) :=
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨1, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨2, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨3, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨4, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨5, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨6, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨7, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨8, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨9, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨10, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨11, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨12, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨13, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨14, _⟩ => bot_or_i _
  | ⟨0, _⟩, ⟨15, _⟩ => bot_or_i _
  | ⟨1, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨1, _⟩, ⟨1, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨2, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨3, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨4, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨5, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨6, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨7, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨8, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨9, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨10, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨11, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨12, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨13, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨14, _⟩ => top_or_i _
  | ⟨1, _⟩, ⟨15, _⟩ => top_or_i _
  | ⟨2, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨2, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨2, _⟩, ⟨2, _⟩ => or_idem_i _
  | ⟨2, _⟩, ⟨3, _⟩ => Interd.refl _
  | ⟨2, _⟩, ⟨4, _⟩ => cOr_2_4
  | ⟨2, _⟩, ⟨5, _⟩ => cOr_2_5
  | ⟨2, _⟩, ⟨6, _⟩ => cOr_2_6
  | ⟨2, _⟩, ⟨7, _⟩ => cOr_2_7
  | ⟨2, _⟩, ⟨8, _⟩ => cOr_2_8
  | ⟨2, _⟩, ⟨9, _⟩ => cOr_2_9
  | ⟨2, _⟩, ⟨10, _⟩ => cOr_2_10
  | ⟨2, _⟩, ⟨11, _⟩ => cOr_2_11
  | ⟨2, _⟩, ⟨12, _⟩ => cOr_2_12
  | ⟨2, _⟩, ⟨13, _⟩ => cOr_2_13
  | ⟨2, _⟩, ⟨14, _⟩ => cOr_2_14
  | ⟨2, _⟩, ⟨15, _⟩ => cOr_2_15
  | ⟨3, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨3, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨3, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (Interd.refl _)
  | ⟨3, _⟩, ⟨3, _⟩ => or_idem_i _
  | ⟨3, _⟩, ⟨4, _⟩ => cOr_3_4
  | ⟨3, _⟩, ⟨5, _⟩ => cOr_3_5
  | ⟨3, _⟩, ⟨6, _⟩ => Interd.refl _
  | ⟨3, _⟩, ⟨7, _⟩ => cOr_3_7
  | ⟨3, _⟩, ⟨8, _⟩ => cOr_3_8
  | ⟨3, _⟩, ⟨9, _⟩ => cOr_3_9
  | ⟨3, _⟩, ⟨10, _⟩ => cOr_3_10
  | ⟨3, _⟩, ⟨11, _⟩ => cOr_3_11
  | ⟨3, _⟩, ⟨12, _⟩ => cOr_3_12
  | ⟨3, _⟩, ⟨13, _⟩ => cOr_3_13
  | ⟨3, _⟩, ⟨14, _⟩ => cOr_3_14
  | ⟨3, _⟩, ⟨15, _⟩ => cOr_3_15
  | ⟨4, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨4, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨4, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_4)
  | ⟨4, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_4)
  | ⟨4, _⟩, ⟨4, _⟩ => or_idem_i _
  | ⟨4, _⟩, ⟨5, _⟩ => cOr_4_5
  | ⟨4, _⟩, ⟨6, _⟩ => cOr_4_6
  | ⟨4, _⟩, ⟨7, _⟩ => cOr_4_7
  | ⟨4, _⟩, ⟨8, _⟩ => cOr_4_8
  | ⟨4, _⟩, ⟨9, _⟩ => cOr_4_9
  | ⟨4, _⟩, ⟨10, _⟩ => cOr_4_10
  | ⟨4, _⟩, ⟨11, _⟩ => cOr_4_11
  | ⟨4, _⟩, ⟨12, _⟩ => cOr_4_12
  | ⟨4, _⟩, ⟨13, _⟩ => cOr_4_13
  | ⟨4, _⟩, ⟨14, _⟩ => cOr_4_14
  | ⟨4, _⟩, ⟨15, _⟩ => cOr_4_15
  | ⟨5, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨5, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨5, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_5)
  | ⟨5, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_5)
  | ⟨5, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_5)
  | ⟨5, _⟩, ⟨5, _⟩ => or_idem_i _
  | ⟨5, _⟩, ⟨6, _⟩ => Interd.refl _
  | ⟨5, _⟩, ⟨7, _⟩ => cOr_5_7
  | ⟨5, _⟩, ⟨8, _⟩ => cOr_5_8
  | ⟨5, _⟩, ⟨9, _⟩ => cOr_5_9
  | ⟨5, _⟩, ⟨10, _⟩ => cOr_5_10
  | ⟨5, _⟩, ⟨11, _⟩ => cOr_5_11
  | ⟨5, _⟩, ⟨12, _⟩ => cOr_5_12
  | ⟨5, _⟩, ⟨13, _⟩ => cOr_5_13
  | ⟨5, _⟩, ⟨14, _⟩ => cOr_5_14
  | ⟨5, _⟩, ⟨15, _⟩ => cOr_5_15
  | ⟨6, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨6, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨6, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_6)
  | ⟨6, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (Interd.refl _)
  | ⟨6, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_6)
  | ⟨6, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (Interd.refl _)
  | ⟨6, _⟩, ⟨6, _⟩ => or_idem_i _
  | ⟨6, _⟩, ⟨7, _⟩ => cOr_6_7
  | ⟨6, _⟩, ⟨8, _⟩ => cOr_6_8
  | ⟨6, _⟩, ⟨9, _⟩ => cOr_6_9
  | ⟨6, _⟩, ⟨10, _⟩ => Interd.refl _
  | ⟨6, _⟩, ⟨11, _⟩ => cOr_6_11
  | ⟨6, _⟩, ⟨12, _⟩ => cOr_6_12
  | ⟨6, _⟩, ⟨13, _⟩ => cOr_6_13
  | ⟨6, _⟩, ⟨14, _⟩ => cOr_6_14
  | ⟨6, _⟩, ⟨15, _⟩ => cOr_6_15
  | ⟨7, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨7, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨7, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_7)
  | ⟨7, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_7)
  | ⟨7, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_7)
  | ⟨7, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_7)
  | ⟨7, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (cOr_6_7)
  | ⟨7, _⟩, ⟨7, _⟩ => or_idem_i _
  | ⟨7, _⟩, ⟨8, _⟩ => cOr_7_8
  | ⟨7, _⟩, ⟨9, _⟩ => cOr_7_9
  | ⟨7, _⟩, ⟨10, _⟩ => cOr_7_10
  | ⟨7, _⟩, ⟨11, _⟩ => cOr_7_11
  | ⟨7, _⟩, ⟨12, _⟩ => cOr_7_12
  | ⟨7, _⟩, ⟨13, _⟩ => cOr_7_13
  | ⟨7, _⟩, ⟨14, _⟩ => cOr_7_14
  | ⟨7, _⟩, ⟨15, _⟩ => cOr_7_15
  | ⟨8, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨8, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨8, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_8)
  | ⟨8, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_8)
  | ⟨8, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_8)
  | ⟨8, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_8)
  | ⟨8, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (cOr_6_8)
  | ⟨8, _⟩, ⟨7, _⟩ => (or_comm_i _ _).trans (cOr_7_8)
  | ⟨8, _⟩, ⟨8, _⟩ => or_idem_i _
  | ⟨8, _⟩, ⟨9, _⟩ => cOr_8_9
  | ⟨8, _⟩, ⟨10, _⟩ => cOr_8_10
  | ⟨8, _⟩, ⟨11, _⟩ => cOr_8_11
  | ⟨8, _⟩, ⟨12, _⟩ => cOr_8_12
  | ⟨8, _⟩, ⟨13, _⟩ => cOr_8_13
  | ⟨8, _⟩, ⟨14, _⟩ => cOr_8_14
  | ⟨8, _⟩, ⟨15, _⟩ => cOr_8_15
  | ⟨9, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨9, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨9, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_9)
  | ⟨9, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_9)
  | ⟨9, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_9)
  | ⟨9, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_9)
  | ⟨9, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (cOr_6_9)
  | ⟨9, _⟩, ⟨7, _⟩ => (or_comm_i _ _).trans (cOr_7_9)
  | ⟨9, _⟩, ⟨8, _⟩ => (or_comm_i _ _).trans (cOr_8_9)
  | ⟨9, _⟩, ⟨9, _⟩ => or_idem_i _
  | ⟨9, _⟩, ⟨10, _⟩ => cOr_9_10
  | ⟨9, _⟩, ⟨11, _⟩ => cOr_9_11
  | ⟨9, _⟩, ⟨12, _⟩ => cOr_9_12
  | ⟨9, _⟩, ⟨13, _⟩ => cOr_9_13
  | ⟨9, _⟩, ⟨14, _⟩ => cOr_9_14
  | ⟨9, _⟩, ⟨15, _⟩ => cOr_9_15
  | ⟨10, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨10, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨10, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_10)
  | ⟨10, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_10)
  | ⟨10, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_10)
  | ⟨10, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_10)
  | ⟨10, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (Interd.refl _)
  | ⟨10, _⟩, ⟨7, _⟩ => (or_comm_i _ _).trans (cOr_7_10)
  | ⟨10, _⟩, ⟨8, _⟩ => (or_comm_i _ _).trans (cOr_8_10)
  | ⟨10, _⟩, ⟨9, _⟩ => (or_comm_i _ _).trans (cOr_9_10)
  | ⟨10, _⟩, ⟨10, _⟩ => or_idem_i _
  | ⟨10, _⟩, ⟨11, _⟩ => cOr_10_11
  | ⟨10, _⟩, ⟨12, _⟩ => cOr_10_12
  | ⟨10, _⟩, ⟨13, _⟩ => cOr_10_13
  | ⟨10, _⟩, ⟨14, _⟩ => cOr_10_14
  | ⟨10, _⟩, ⟨15, _⟩ => cOr_10_15
  | ⟨11, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨11, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨11, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_11)
  | ⟨11, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_11)
  | ⟨11, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_11)
  | ⟨11, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_11)
  | ⟨11, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (cOr_6_11)
  | ⟨11, _⟩, ⟨7, _⟩ => (or_comm_i _ _).trans (cOr_7_11)
  | ⟨11, _⟩, ⟨8, _⟩ => (or_comm_i _ _).trans (cOr_8_11)
  | ⟨11, _⟩, ⟨9, _⟩ => (or_comm_i _ _).trans (cOr_9_11)
  | ⟨11, _⟩, ⟨10, _⟩ => (or_comm_i _ _).trans (cOr_10_11)
  | ⟨11, _⟩, ⟨11, _⟩ => or_idem_i _
  | ⟨11, _⟩, ⟨12, _⟩ => cOr_11_12
  | ⟨11, _⟩, ⟨13, _⟩ => cOr_11_13
  | ⟨11, _⟩, ⟨14, _⟩ => cOr_11_14
  | ⟨11, _⟩, ⟨15, _⟩ => cOr_11_15
  | ⟨12, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨12, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨12, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_12)
  | ⟨12, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_12)
  | ⟨12, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_12)
  | ⟨12, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_12)
  | ⟨12, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (cOr_6_12)
  | ⟨12, _⟩, ⟨7, _⟩ => (or_comm_i _ _).trans (cOr_7_12)
  | ⟨12, _⟩, ⟨8, _⟩ => (or_comm_i _ _).trans (cOr_8_12)
  | ⟨12, _⟩, ⟨9, _⟩ => (or_comm_i _ _).trans (cOr_9_12)
  | ⟨12, _⟩, ⟨10, _⟩ => (or_comm_i _ _).trans (cOr_10_12)
  | ⟨12, _⟩, ⟨11, _⟩ => (or_comm_i _ _).trans (cOr_11_12)
  | ⟨12, _⟩, ⟨12, _⟩ => or_idem_i _
  | ⟨12, _⟩, ⟨13, _⟩ => cOr_12_13
  | ⟨12, _⟩, ⟨14, _⟩ => cOr_12_14
  | ⟨12, _⟩, ⟨15, _⟩ => cOr_12_15
  | ⟨13, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨13, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨13, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_13)
  | ⟨13, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_13)
  | ⟨13, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_13)
  | ⟨13, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_13)
  | ⟨13, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (cOr_6_13)
  | ⟨13, _⟩, ⟨7, _⟩ => (or_comm_i _ _).trans (cOr_7_13)
  | ⟨13, _⟩, ⟨8, _⟩ => (or_comm_i _ _).trans (cOr_8_13)
  | ⟨13, _⟩, ⟨9, _⟩ => (or_comm_i _ _).trans (cOr_9_13)
  | ⟨13, _⟩, ⟨10, _⟩ => (or_comm_i _ _).trans (cOr_10_13)
  | ⟨13, _⟩, ⟨11, _⟩ => (or_comm_i _ _).trans (cOr_11_13)
  | ⟨13, _⟩, ⟨12, _⟩ => (or_comm_i _ _).trans (cOr_12_13)
  | ⟨13, _⟩, ⟨13, _⟩ => or_idem_i _
  | ⟨13, _⟩, ⟨14, _⟩ => cOr_13_14
  | ⟨13, _⟩, ⟨15, _⟩ => cOr_13_15
  | ⟨14, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨14, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨14, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_14)
  | ⟨14, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_14)
  | ⟨14, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_14)
  | ⟨14, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_14)
  | ⟨14, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (cOr_6_14)
  | ⟨14, _⟩, ⟨7, _⟩ => (or_comm_i _ _).trans (cOr_7_14)
  | ⟨14, _⟩, ⟨8, _⟩ => (or_comm_i _ _).trans (cOr_8_14)
  | ⟨14, _⟩, ⟨9, _⟩ => (or_comm_i _ _).trans (cOr_9_14)
  | ⟨14, _⟩, ⟨10, _⟩ => (or_comm_i _ _).trans (cOr_10_14)
  | ⟨14, _⟩, ⟨11, _⟩ => (or_comm_i _ _).trans (cOr_11_14)
  | ⟨14, _⟩, ⟨12, _⟩ => (or_comm_i _ _).trans (cOr_12_14)
  | ⟨14, _⟩, ⟨13, _⟩ => (or_comm_i _ _).trans (cOr_13_14)
  | ⟨14, _⟩, ⟨14, _⟩ => or_idem_i _
  | ⟨14, _⟩, ⟨15, _⟩ => cOr_14_15
  | ⟨15, _⟩, ⟨0, _⟩ => (or_comm_i _ _).trans (bot_or_i _)
  | ⟨15, _⟩, ⟨1, _⟩ => (or_comm_i _ _).trans (top_or_i _)
  | ⟨15, _⟩, ⟨2, _⟩ => (or_comm_i _ _).trans (cOr_2_15)
  | ⟨15, _⟩, ⟨3, _⟩ => (or_comm_i _ _).trans (cOr_3_15)
  | ⟨15, _⟩, ⟨4, _⟩ => (or_comm_i _ _).trans (cOr_4_15)
  | ⟨15, _⟩, ⟨5, _⟩ => (or_comm_i _ _).trans (cOr_5_15)
  | ⟨15, _⟩, ⟨6, _⟩ => (or_comm_i _ _).trans (cOr_6_15)
  | ⟨15, _⟩, ⟨7, _⟩ => (or_comm_i _ _).trans (cOr_7_15)
  | ⟨15, _⟩, ⟨8, _⟩ => (or_comm_i _ _).trans (cOr_8_15)
  | ⟨15, _⟩, ⟨9, _⟩ => (or_comm_i _ _).trans (cOr_9_15)
  | ⟨15, _⟩, ⟨10, _⟩ => (or_comm_i _ _).trans (cOr_10_15)
  | ⟨15, _⟩, ⟨11, _⟩ => (or_comm_i _ _).trans (cOr_11_15)
  | ⟨15, _⟩, ⟨12, _⟩ => (or_comm_i _ _).trans (cOr_12_15)
  | ⟨15, _⟩, ⟨13, _⟩ => (or_comm_i _ _).trans (cOr_13_15)
  | ⟨15, _⟩, ⟨14, _⟩ => (or_comm_i _ _).trans (cOr_14_15)
  | ⟨15, _⟩, ⟨15, _⟩ => or_idem_i _
  | ⟨_+16, h⟩, _ => absurd h (by omega)
  | _, ⟨_+16, h⟩ => absurd h (by omega)

theorem imp2_ok (i j : Fin 16) :
    Interd ((rep2 i).ifThen (rep2 j)) (rep2 (imp2Idx i j)) :=
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => Interd.refl _
  | ⟨0, _⟩, ⟨1, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨2, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨3, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨4, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨5, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨6, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨7, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨8, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨9, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨10, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨11, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨12, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨13, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨14, _⟩ => bot_imp_i _
  | ⟨0, _⟩, ⟨15, _⟩ => bot_imp_i _
  | ⟨1, _⟩, ⟨0, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨1, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨2, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨3, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨4, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨5, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨6, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨7, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨8, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨9, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨10, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨11, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨12, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨13, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨14, _⟩ => top_imp_i _
  | ⟨1, _⟩, ⟨15, _⟩ => top_imp_i _
  | ⟨2, _⟩, ⟨0, _⟩ => Interd.refl _
  | ⟨2, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨2, _⟩, ⟨2, _⟩ => imp_self_i _
  | ⟨2, _⟩, ⟨3, _⟩ => cImp_2_3
  | ⟨2, _⟩, ⟨4, _⟩ => cImp_2_4
  | ⟨2, _⟩, ⟨5, _⟩ => cImp_2_5
  | ⟨2, _⟩, ⟨6, _⟩ => cImp_2_6
  | ⟨2, _⟩, ⟨7, _⟩ => cImp_2_7
  | ⟨2, _⟩, ⟨8, _⟩ => cImp_2_8
  | ⟨2, _⟩, ⟨9, _⟩ => cImp_2_9
  | ⟨2, _⟩, ⟨10, _⟩ => cImp_2_10
  | ⟨2, _⟩, ⟨11, _⟩ => cImp_2_11
  | ⟨2, _⟩, ⟨12, _⟩ => cImp_2_12
  | ⟨2, _⟩, ⟨13, _⟩ => cImp_2_13
  | ⟨2, _⟩, ⟨14, _⟩ => cImp_2_14
  | ⟨2, _⟩, ⟨15, _⟩ => cImp_2_15
  | ⟨3, _⟩, ⟨0, _⟩ => Interd.refl _
  | ⟨3, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨3, _⟩, ⟨2, _⟩ => cImp_3_2
  | ⟨3, _⟩, ⟨3, _⟩ => imp_self_i _
  | ⟨3, _⟩, ⟨4, _⟩ => cImp_3_4
  | ⟨3, _⟩, ⟨5, _⟩ => cImp_3_5
  | ⟨3, _⟩, ⟨6, _⟩ => cImp_3_6
  | ⟨3, _⟩, ⟨7, _⟩ => cImp_3_7
  | ⟨3, _⟩, ⟨8, _⟩ => cImp_3_8
  | ⟨3, _⟩, ⟨9, _⟩ => cImp_3_9
  | ⟨3, _⟩, ⟨10, _⟩ => cImp_3_10
  | ⟨3, _⟩, ⟨11, _⟩ => cImp_3_11
  | ⟨3, _⟩, ⟨12, _⟩ => cImp_3_12
  | ⟨3, _⟩, ⟨13, _⟩ => cImp_3_13
  | ⟨3, _⟩, ⟨14, _⟩ => cImp_3_14
  | ⟨3, _⟩, ⟨15, _⟩ => cImp_3_15
  | ⟨4, _⟩, ⟨0, _⟩ => cImp_4_0
  | ⟨4, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨4, _⟩, ⟨2, _⟩ => cImp_4_2
  | ⟨4, _⟩, ⟨3, _⟩ => cImp_4_3
  | ⟨4, _⟩, ⟨4, _⟩ => imp_self_i _
  | ⟨4, _⟩, ⟨5, _⟩ => cImp_4_5
  | ⟨4, _⟩, ⟨6, _⟩ => cImp_4_6
  | ⟨4, _⟩, ⟨7, _⟩ => cImp_4_7
  | ⟨4, _⟩, ⟨8, _⟩ => cImp_4_8
  | ⟨4, _⟩, ⟨9, _⟩ => cImp_4_9
  | ⟨4, _⟩, ⟨10, _⟩ => cImp_4_10
  | ⟨4, _⟩, ⟨11, _⟩ => cImp_4_11
  | ⟨4, _⟩, ⟨12, _⟩ => cImp_4_12
  | ⟨4, _⟩, ⟨13, _⟩ => cImp_4_13
  | ⟨4, _⟩, ⟨14, _⟩ => cImp_4_14
  | ⟨4, _⟩, ⟨15, _⟩ => cImp_4_15
  | ⟨5, _⟩, ⟨0, _⟩ => cImp_5_0
  | ⟨5, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨5, _⟩, ⟨2, _⟩ => cImp_5_2
  | ⟨5, _⟩, ⟨3, _⟩ => cImp_5_3
  | ⟨5, _⟩, ⟨4, _⟩ => Interd.refl _
  | ⟨5, _⟩, ⟨5, _⟩ => imp_self_i _
  | ⟨5, _⟩, ⟨6, _⟩ => cImp_5_6
  | ⟨5, _⟩, ⟨7, _⟩ => cImp_5_7
  | ⟨5, _⟩, ⟨8, _⟩ => cImp_5_8
  | ⟨5, _⟩, ⟨9, _⟩ => cImp_5_9
  | ⟨5, _⟩, ⟨10, _⟩ => cImp_5_10
  | ⟨5, _⟩, ⟨11, _⟩ => cImp_5_11
  | ⟨5, _⟩, ⟨12, _⟩ => cImp_5_12
  | ⟨5, _⟩, ⟨13, _⟩ => cImp_5_13
  | ⟨5, _⟩, ⟨14, _⟩ => cImp_5_14
  | ⟨5, _⟩, ⟨15, _⟩ => cImp_5_15
  | ⟨6, _⟩, ⟨0, _⟩ => cImp_6_0
  | ⟨6, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨6, _⟩, ⟨2, _⟩ => Interd.refl _
  | ⟨6, _⟩, ⟨3, _⟩ => cImp_6_3
  | ⟨6, _⟩, ⟨4, _⟩ => cImp_6_4
  | ⟨6, _⟩, ⟨5, _⟩ => cImp_6_5
  | ⟨6, _⟩, ⟨6, _⟩ => imp_self_i _
  | ⟨6, _⟩, ⟨7, _⟩ => cImp_6_7
  | ⟨6, _⟩, ⟨8, _⟩ => cImp_6_8
  | ⟨6, _⟩, ⟨9, _⟩ => cImp_6_9
  | ⟨6, _⟩, ⟨10, _⟩ => cImp_6_10
  | ⟨6, _⟩, ⟨11, _⟩ => cImp_6_11
  | ⟨6, _⟩, ⟨12, _⟩ => cImp_6_12
  | ⟨6, _⟩, ⟨13, _⟩ => cImp_6_13
  | ⟨6, _⟩, ⟨14, _⟩ => cImp_6_14
  | ⟨6, _⟩, ⟨15, _⟩ => cImp_6_15
  | ⟨7, _⟩, ⟨0, _⟩ => cImp_7_0
  | ⟨7, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨7, _⟩, ⟨2, _⟩ => cImp_7_2
  | ⟨7, _⟩, ⟨3, _⟩ => cImp_7_3
  | ⟨7, _⟩, ⟨4, _⟩ => cImp_7_4
  | ⟨7, _⟩, ⟨5, _⟩ => cImp_7_5
  | ⟨7, _⟩, ⟨6, _⟩ => cImp_7_6
  | ⟨7, _⟩, ⟨7, _⟩ => imp_self_i _
  | ⟨7, _⟩, ⟨8, _⟩ => cImp_7_8
  | ⟨7, _⟩, ⟨9, _⟩ => cImp_7_9
  | ⟨7, _⟩, ⟨10, _⟩ => cImp_7_10
  | ⟨7, _⟩, ⟨11, _⟩ => cImp_7_11
  | ⟨7, _⟩, ⟨12, _⟩ => cImp_7_12
  | ⟨7, _⟩, ⟨13, _⟩ => cImp_7_13
  | ⟨7, _⟩, ⟨14, _⟩ => cImp_7_14
  | ⟨7, _⟩, ⟨15, _⟩ => cImp_7_15
  | ⟨8, _⟩, ⟨0, _⟩ => cImp_8_0
  | ⟨8, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨8, _⟩, ⟨2, _⟩ => cImp_8_2
  | ⟨8, _⟩, ⟨3, _⟩ => cImp_8_3
  | ⟨8, _⟩, ⟨4, _⟩ => cImp_8_4
  | ⟨8, _⟩, ⟨5, _⟩ => cImp_8_5
  | ⟨8, _⟩, ⟨6, _⟩ => cImp_8_6
  | ⟨8, _⟩, ⟨7, _⟩ => cImp_8_7
  | ⟨8, _⟩, ⟨8, _⟩ => imp_self_i _
  | ⟨8, _⟩, ⟨9, _⟩ => cImp_8_9
  | ⟨8, _⟩, ⟨10, _⟩ => cImp_8_10
  | ⟨8, _⟩, ⟨11, _⟩ => cImp_8_11
  | ⟨8, _⟩, ⟨12, _⟩ => cImp_8_12
  | ⟨8, _⟩, ⟨13, _⟩ => cImp_8_13
  | ⟨8, _⟩, ⟨14, _⟩ => cImp_8_14
  | ⟨8, _⟩, ⟨15, _⟩ => cImp_8_15
  | ⟨9, _⟩, ⟨0, _⟩ => cImp_9_0
  | ⟨9, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨9, _⟩, ⟨2, _⟩ => cImp_9_2
  | ⟨9, _⟩, ⟨3, _⟩ => cImp_9_3
  | ⟨9, _⟩, ⟨4, _⟩ => Interd.refl _
  | ⟨9, _⟩, ⟨5, _⟩ => cImp_9_5
  | ⟨9, _⟩, ⟨6, _⟩ => cImp_9_6
  | ⟨9, _⟩, ⟨7, _⟩ => cImp_9_7
  | ⟨9, _⟩, ⟨8, _⟩ => cImp_9_8
  | ⟨9, _⟩, ⟨9, _⟩ => imp_self_i _
  | ⟨9, _⟩, ⟨10, _⟩ => cImp_9_10
  | ⟨9, _⟩, ⟨11, _⟩ => cImp_9_11
  | ⟨9, _⟩, ⟨12, _⟩ => cImp_9_12
  | ⟨9, _⟩, ⟨13, _⟩ => cImp_9_13
  | ⟨9, _⟩, ⟨14, _⟩ => cImp_9_14
  | ⟨9, _⟩, ⟨15, _⟩ => cImp_9_15
  | ⟨10, _⟩, ⟨0, _⟩ => cImp_10_0
  | ⟨10, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨10, _⟩, ⟨2, _⟩ => cImp_10_2
  | ⟨10, _⟩, ⟨3, _⟩ => cImp_10_3
  | ⟨10, _⟩, ⟨4, _⟩ => cImp_10_4
  | ⟨10, _⟩, ⟨5, _⟩ => Interd.refl _
  | ⟨10, _⟩, ⟨6, _⟩ => cImp_10_6
  | ⟨10, _⟩, ⟨7, _⟩ => cImp_10_7
  | ⟨10, _⟩, ⟨8, _⟩ => cImp_10_8
  | ⟨10, _⟩, ⟨9, _⟩ => cImp_10_9
  | ⟨10, _⟩, ⟨10, _⟩ => imp_self_i _
  | ⟨10, _⟩, ⟨11, _⟩ => cImp_10_11
  | ⟨10, _⟩, ⟨12, _⟩ => cImp_10_12
  | ⟨10, _⟩, ⟨13, _⟩ => cImp_10_13
  | ⟨10, _⟩, ⟨14, _⟩ => cImp_10_14
  | ⟨10, _⟩, ⟨15, _⟩ => cImp_10_15
  | ⟨11, _⟩, ⟨0, _⟩ => cImp_11_0
  | ⟨11, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨11, _⟩, ⟨2, _⟩ => cImp_11_2
  | ⟨11, _⟩, ⟨3, _⟩ => cImp_11_3
  | ⟨11, _⟩, ⟨4, _⟩ => cImp_11_4
  | ⟨11, _⟩, ⟨5, _⟩ => cImp_11_5
  | ⟨11, _⟩, ⟨6, _⟩ => cImp_11_6
  | ⟨11, _⟩, ⟨7, _⟩ => cImp_11_7
  | ⟨11, _⟩, ⟨8, _⟩ => cImp_11_8
  | ⟨11, _⟩, ⟨9, _⟩ => cImp_11_9
  | ⟨11, _⟩, ⟨10, _⟩ => cImp_11_10
  | ⟨11, _⟩, ⟨11, _⟩ => imp_self_i _
  | ⟨11, _⟩, ⟨12, _⟩ => cImp_11_12
  | ⟨11, _⟩, ⟨13, _⟩ => cImp_11_13
  | ⟨11, _⟩, ⟨14, _⟩ => cImp_11_14
  | ⟨11, _⟩, ⟨15, _⟩ => cImp_11_15
  | ⟨12, _⟩, ⟨0, _⟩ => cImp_12_0
  | ⟨12, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨12, _⟩, ⟨2, _⟩ => cImp_12_2
  | ⟨12, _⟩, ⟨3, _⟩ => cImp_12_3
  | ⟨12, _⟩, ⟨4, _⟩ => cImp_12_4
  | ⟨12, _⟩, ⟨5, _⟩ => cImp_12_5
  | ⟨12, _⟩, ⟨6, _⟩ => cImp_12_6
  | ⟨12, _⟩, ⟨7, _⟩ => cImp_12_7
  | ⟨12, _⟩, ⟨8, _⟩ => cImp_12_8
  | ⟨12, _⟩, ⟨9, _⟩ => cImp_12_9
  | ⟨12, _⟩, ⟨10, _⟩ => cImp_12_10
  | ⟨12, _⟩, ⟨11, _⟩ => cImp_12_11
  | ⟨12, _⟩, ⟨12, _⟩ => imp_self_i _
  | ⟨12, _⟩, ⟨13, _⟩ => cImp_12_13
  | ⟨12, _⟩, ⟨14, _⟩ => cImp_12_14
  | ⟨12, _⟩, ⟨15, _⟩ => cImp_12_15
  | ⟨13, _⟩, ⟨0, _⟩ => cImp_13_0
  | ⟨13, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨13, _⟩, ⟨2, _⟩ => cImp_13_2
  | ⟨13, _⟩, ⟨3, _⟩ => cImp_13_3
  | ⟨13, _⟩, ⟨4, _⟩ => cImp_13_4
  | ⟨13, _⟩, ⟨5, _⟩ => cImp_13_5
  | ⟨13, _⟩, ⟨6, _⟩ => cImp_13_6
  | ⟨13, _⟩, ⟨7, _⟩ => cImp_13_7
  | ⟨13, _⟩, ⟨8, _⟩ => cImp_13_8
  | ⟨13, _⟩, ⟨9, _⟩ => cImp_13_9
  | ⟨13, _⟩, ⟨10, _⟩ => cImp_13_10
  | ⟨13, _⟩, ⟨11, _⟩ => cImp_13_11
  | ⟨13, _⟩, ⟨12, _⟩ => cImp_13_12
  | ⟨13, _⟩, ⟨13, _⟩ => imp_self_i _
  | ⟨13, _⟩, ⟨14, _⟩ => cImp_13_14
  | ⟨13, _⟩, ⟨15, _⟩ => cImp_13_15
  | ⟨14, _⟩, ⟨0, _⟩ => cImp_14_0
  | ⟨14, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨14, _⟩, ⟨2, _⟩ => cImp_14_2
  | ⟨14, _⟩, ⟨3, _⟩ => cImp_14_3
  | ⟨14, _⟩, ⟨4, _⟩ => cImp_14_4
  | ⟨14, _⟩, ⟨5, _⟩ => cImp_14_5
  | ⟨14, _⟩, ⟨6, _⟩ => cImp_14_6
  | ⟨14, _⟩, ⟨7, _⟩ => cImp_14_7
  | ⟨14, _⟩, ⟨8, _⟩ => cImp_14_8
  | ⟨14, _⟩, ⟨9, _⟩ => cImp_14_9
  | ⟨14, _⟩, ⟨10, _⟩ => cImp_14_10
  | ⟨14, _⟩, ⟨11, _⟩ => cImp_14_11
  | ⟨14, _⟩, ⟨12, _⟩ => cImp_14_12
  | ⟨14, _⟩, ⟨13, _⟩ => cImp_14_13
  | ⟨14, _⟩, ⟨14, _⟩ => imp_self_i _
  | ⟨14, _⟩, ⟨15, _⟩ => cImp_14_15
  | ⟨15, _⟩, ⟨0, _⟩ => cImp_15_0
  | ⟨15, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨15, _⟩, ⟨2, _⟩ => cImp_15_2
  | ⟨15, _⟩, ⟨3, _⟩ => cImp_15_3
  | ⟨15, _⟩, ⟨4, _⟩ => cImp_15_4
  | ⟨15, _⟩, ⟨5, _⟩ => cImp_15_5
  | ⟨15, _⟩, ⟨6, _⟩ => cImp_15_6
  | ⟨15, _⟩, ⟨7, _⟩ => cImp_15_7
  | ⟨15, _⟩, ⟨8, _⟩ => cImp_15_8
  | ⟨15, _⟩, ⟨9, _⟩ => cImp_15_9
  | ⟨15, _⟩, ⟨10, _⟩ => cImp_15_10
  | ⟨15, _⟩, ⟨11, _⟩ => cImp_15_11
  | ⟨15, _⟩, ⟨12, _⟩ => cImp_15_12
  | ⟨15, _⟩, ⟨13, _⟩ => cImp_15_13
  | ⟨15, _⟩, ⟨14, _⟩ => cImp_15_14
  | ⟨15, _⟩, ⟨15, _⟩ => imp_self_i _
  | ⟨_+16, h⟩, _ => absurd h (by omega)
  | _, ⟨_+16, h⟩ => absurd h (by omega)

theorem box2_ok (i : Fin 16) :
    Interd (rep2 i).somehow (rep2 (box2Idx i)) :=
  match i with
  | ⟨0, _⟩ => Interd.refl _
  | ⟨1, _⟩ => cBox_1
  | ⟨2, _⟩ => box_idem_i _
  | ⟨3, _⟩ => Interd.refl _
  | ⟨4, _⟩ => cBox_4
  | ⟨5, _⟩ => box_idem_i _
  | ⟨6, _⟩ => cBox_6
  | ⟨7, _⟩ => Interd.refl _
  | ⟨8, _⟩ => Interd.refl _
  | ⟨9, _⟩ => cBox_9
  | ⟨10, _⟩ => cBox_10
  | ⟨11, _⟩ => cBox_11
  | ⟨12, _⟩ => box_idem_i _
  | ⟨13, _⟩ => box_idem_i _
  | ⟨14, _⟩ => cBox_14
  | ⟨15, _⟩ => cBox_15
  | ⟨_+16, h⟩ => absurd h (by omega)

end RND2

open RND2 in
/-- **The enlarged RN(◯,{}) dictionary round**: 16 variable-free
representatives, crank bound 8, connective-closure tables
kernel-checked away from the sorried cells (58 of 784; when that
count is 0 this record is a full certified dictionary). -/
def rnDict16 : RNDict where
  n := 16
  rep := RND2.rep2
  rep_varFree := by decide
  crankBound := 8
  rep_crank_le := by decide
  botIdx := ⟨0, by decide⟩
  bot_interd := Interd.refl _
  andIdx := RND2.and2Idx
  orIdx := RND2.or2Idx
  impIdx := RND2.imp2Idx
  boxIdx := RND2.box2Idx
  and_interd := RND2.and2_ok
  or_interd := RND2.or2_ok
  imp_interd := RND2.imp2_ok
  box_interd := RND2.box2_ok

/-! ## Axiom audit -/

-- PARTIAL instantiation: 58 cells are sorried (see the
-- per-cell doc comments: REFUTED/OPEN).  No #guard_msgs pin.
#print axioms rnDict16

end SemUI
end PLLND
