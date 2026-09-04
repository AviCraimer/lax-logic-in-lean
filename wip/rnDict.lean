import wip.stabilise
import wip.rnDictBase

/-!
# The certified RN(◯,{}) dictionary: `rnDict15 : RNDict`

GENERATED FILE — do not edit by hand.  Produced by
`wip/rnDictGen.lean` (`lake build rnDictGen && .lake/build/bin/rnDictGen > wip/rnDict.lean`).

The fifteen interderivability-class representatives of the
variable-free PLL fragment (the RN(◯,{}) dictionary computed by the
v2quant probe, wip/v2quant_out3.txt), with KERNEL-CHECKED closure
tables: for every pair of representatives and each of ∧, ∨, ⊃ (and
every representative under ◯), an `Interd` certificate collapsing the
combination onto its representative.  Nontrivial cells carry G4iLL″
proof terms found by offline search (`G4cTm.findBounded`, pinned as
source per the repo's discover-then-pin discipline) and are bridged to
`LaxND` by `RND.ofG4`; trivial cells go through the generic laws of
`wip/rnDictBase.lean`.

The instantiation plugs into `wip/stabilise.lean`: `dict_collapse`,
`dict_agree_stab`, `vfB_mforthResidue` and
`restricted_amalgamation_oneVar` become unconditional in the
`RNDict` argument.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND

/-! ## The fifteen representatives (probe order) -/

def q0 : PLLFormula := .falsePLL
def q1 : PLLFormula := (.ifThen q0 q0)
def q2 : PLLFormula := (.somehow q0)
def q3 : PLLFormula := (.ifThen q2 q0)
def q4 : PLLFormula := (.or q2 q3)
def q5 : PLLFormula := (.somehow q3)
def q6 : PLLFormula := (.ifThen q3 q0)
def q7 : PLLFormula := (.or q3 q6)
def q8 : PLLFormula := (.ifThen q5 q4)
def q9 : PLLFormula := (.or q5 q6)
def q10 : PLLFormula := (.ifThen q6 q2)
def q11 : PLLFormula := (.or q6 q10)
def q12 : PLLFormula := (.somehow q7)
def q13 : PLLFormula := (.somehow q8)
def q14 : PLLFormula := (.ifThen q10 q5)

def repsL : List PLLFormula := [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14]

def rep15 : Fin 15 → PLLFormula := fun i => repsL.getD i.val .falsePLL

/-! ## The closure tables -/

def andT : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
   [0, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
   [0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 3],
   [0, 4, 2, 3, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 4],
   [0, 5, 2, 3, 4, 5, 2, 4, 4, 5, 5, 5, 5, 5, 5],
   [0, 6, 2, 0, 2, 2, 6, 6, 6, 6, 2, 6, 6, 6, 6],
   [0, 7, 2, 3, 4, 4, 6, 7, 7, 7, 4, 7, 7, 7, 7],
   [0, 8, 2, 3, 4, 4, 6, 7, 8, 7, 0, 8, 7, 8, 7],
   [0, 9, 2, 3, 4, 5, 6, 7, 7, 9, 5, 9, 9, 9, 9],
   [0, 10, 2, 3, 4, 5, 2, 4, 0, 5, 10, 10, 5, 10, 5],
   [0, 11, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 9, 1, 9],
   [0, 12, 2, 3, 4, 5, 6, 7, 7, 9, 5, 9, 12, 9, 9],
   [0, 13, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 9, 13, 9],
   [0, 14, 2, 3, 4, 5, 6, 7, 7, 9, 5, 9, 9, 9, 14]]
def orT : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [2, 1, 2, 4, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1, 9],
   [3, 1, 4, 3, 4, 5, 7, 7, 8, 9, 10, 11, 12, 1, 9],
   [4, 1, 4, 4, 4, 5, 7, 7, 8, 9, 10, 11, 12, 13, 9],
   [5, 1, 5, 5, 5, 5, 9, 9, 1, 9, 10, 11, 12, 13, 9],
   [6, 1, 6, 7, 7, 9, 6, 7, 8, 9, 11, 11, 12, 1, 9],
   [7, 1, 7, 7, 7, 9, 7, 7, 8, 9, 11, 11, 12, 1, 9],
   [8, 1, 8, 8, 8, 1, 8, 8, 8, 1, 1, 1, 1, 1, 1],
   [9, 1, 9, 9, 9, 9, 9, 9, 1, 9, 11, 11, 12, 1, 9],
   [10, 1, 10, 10, 10, 10, 11, 11, 1, 11, 10, 11, 1, 1, 1],
   [11, 1, 11, 11, 11, 11, 11, 11, 1, 11, 11, 11, 1, 1, 1],
   [12, 1, 12, 12, 12, 12, 12, 12, 1, 12, 1, 1, 12, 1, 9],
   [13, 1, 1, 1, 13, 13, 1, 1, 1, 1, 1, 1, 1, 13, 1],
   [14, 1, 9, 9, 9, 9, 9, 9, 1, 9, 1, 1, 9, 1, 14]]
def impT : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
   [3, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [6, 1, 6, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 6, 3, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 6, 3, 8, 1, 6, 8, 8, 1, 1, 1, 1, 1, 1],
   [3, 1, 10, 3, 10, 10, 1, 1, 1, 1, 10, 1, 1, 1, 1],
   [0, 1, 2, 3, 10, 10, 6, 1, 1, 1, 10, 1, 1, 1, 1],
   [0, 1, 2, 3, 5, 5, 6, 9, 1, 9, 10, 1, 9, 1, 9],
   [0, 1, 2, 3, 0, 10, 6, 8, 8, 1, 10, 1, 1, 1, 1],
   [0, 1, 6, 3, 7, 14, 6, 7, 8, 9, 1, 1, 9, 1, 9],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 9, 1, 9],
   [0, 1, 2, 3, 0, 10, 6, 8, 8, 1, 10, 1, 1, 1, 1],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 9, 1, 9],
   [0, 1, 2, 3, 0, 10, 6, 8, 8, 1, 10, 1, 1, 1, 1]]

def boxT : List Nat := [2, 1, 2, 5, 5, 5, 6, 12, 13, 12, 10, 1, 12, 13, 9]

def andIdx15 (i j : Fin 15) : Fin 15 :=
  ⟨((andT.getD i.val []).getD j.val 0) % 15, Nat.mod_lt _ (by decide)⟩

def orIdx15 (i j : Fin 15) : Fin 15 :=
  ⟨((orT.getD i.val []).getD j.val 0) % 15, Nat.mod_lt _ (by decide)⟩

def impIdx15 (i j : Fin 15) : Fin 15 :=
  ⟨((impT.getD i.val []).getD j.val 0) % 15, Nat.mod_lt _ (by decide)⟩

def boxIdx15 (i : Fin 15) : Fin 15 :=
  ⟨(boxT.getD i.val 0) % 15, Nat.mod_lt _ (by decide)⟩

/-! ## Searched-cell certificates (offline G4iLL″ terms, kernel-checked here) -/

theorem cAnd_2_3 : Interd (q2.and q3) q0 :=
  ⟨ofG4 (.andL (A := q2) (B := q3) (.head _) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))),
   ofG4 (.botL (.head _))⟩

theorem cAnd_2_4 : Interd (q2.and q4) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q4) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))))⟩

theorem cAnd_2_5 : Interd (q2.and q5) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q5) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))))⟩

theorem cAnd_2_6 : Interd (q2.and q6) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q6) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cAnd_2_7 : Interd (q2.and q7) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q7) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cAnd_2_8 : Interd (q2.and q8) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q8) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_2_9 : Interd (q2.and q9) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q9) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))))⟩

theorem cAnd_2_10 : Interd (q2.and q10) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q10) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))⟩

theorem cAnd_2_11 : Interd (q2.and q11) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q11) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cAnd_2_12 : Interd (q2.and q12) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q12) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_2_13 : Interd (q2.and q13) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q13) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cAnd_2_14 : Interd (q2.and q14) q2 :=
  ⟨ofG4 (.andL (A := q2) (B := q14) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))⟩

theorem cAnd_3_4 : Interd (q3.and q4) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cAnd_3_5 : Interd (q3.and q5) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q5) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.head _)) (.laxL (A := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cAnd_3_6 : Interd (q3.and q6) q0 :=
  ⟨ofG4 (.andL (A := q3) (B := q6) (.head _) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))),
   ofG4 (.botL (.head _))⟩

theorem cAnd_3_7 : Interd (q3.and q7) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q7) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cAnd_3_8 : Interd (q3.and q8) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q8) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_3_9 : Interd (q3.and q9) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q9) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_3_10 : Interd (q3.and q10) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q10) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cAnd_3_11 : Interd (q3.and q11) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q11) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.orR2 (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_3_12 : Interd (q3.and q12) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q12) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.head _)) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_3_13 : Interd (q3.and q13) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q13) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q8) (.head _) (.tail _ (.head _)) (.laxR (.impLLax (A := q3) (B := q4) (.head _) (.impLLaxLax (A := q3) (B := q4) (X := q8) (.head _) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.botL (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q8) (.tail _ (.tail _ (.head _))) (.tail _ (.tail _ (.tail _ (.head _)))) (.laxL (A := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.botL (.head _))) (.botL (.head _))))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_3_14 : Interd (q3.and q14) q3 :=
  ⟨ofG4 (.impR (.andL (A := q3) (B := q14) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impR (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_4_5 : Interd (q4.and q5) q4 :=
  ⟨ofG4 (.andL (A := q4) (B := q5) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_4_6 : Interd (q4.and q6) q2 :=
  ⟨ofG4 (.andL (A := q4) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))),
   ofG4 (.andR (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cAnd_4_7 : Interd (q4.and q7) q4 :=
  ⟨ofG4 (.andL (A := q4) (B := q7) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_4_8 : Interd (q4.and q8) q4 :=
  ⟨ofG4 (.andL (A := q4) (B := q8) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_4_9 : Interd (q4.and q9) q4 :=
  ⟨ofG4 (.andL (A := q4) (B := q9) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_4_10 : Interd (q4.and q10) q4 :=
  ⟨ofG4 (.andL (A := q4) (B := q10) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_4_11 : Interd (q4.and q11) q4 :=
  ⟨ofG4 (.andL (A := q4) (B := q11) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cAnd_4_12 : Interd (q4.and q12) q4 :=
  ⟨ofG4 (.andL (A := q4) (B := q12) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.laxR (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_4_13 : Interd (q4.and q13) q4 :=
  ⟨ofG4 (.andL (A := q4) (B := q13) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.laxR (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

/-- OPEN CELL: candidates [4] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_4_14 : Interd (q4.and q14) q4 := sorry

theorem cAnd_5_6 : Interd (q5.and q6) q2 :=
  ⟨ofG4 (.andL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))),
   ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cAnd_5_7 : Interd (q5.and q7) q4 :=
  ⟨ofG4 (.andL (A := q5) (B := q7) (.head _) (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_5_8 : Interd (q5.and q8) q4 :=
  ⟨ofG4 (.andL (A := q5) (B := q8) (.head _) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_5_9 : Interd (q5.and q9) q5 :=
  ⟨ofG4 (.andL (A := q5) (B := q9) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_5_10 : Interd (q5.and q10) q5 :=
  ⟨ofG4 (.andL (A := q5) (B := q10) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_5_11 : Interd (q5.and q11) q5 :=
  ⟨ofG4 (.andL (A := q5) (B := q11) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cAnd_5_12 : Interd (q5.and q12) q5 :=
  ⟨ofG4 (.andL (A := q5) (B := q12) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_5_13 : Interd (q5.and q13) q5 :=
  ⟨ofG4 (.andL (A := q5) (B := q13) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.laxL (A := q3) (.head _) (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cAnd_5_14 : Interd (q5.and q14) q5 :=
  ⟨ofG4 (.andL (A := q5) (B := q14) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.andR (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cAnd_6_7 : Interd (q6.and q7) q6 :=
  ⟨ofG4 (.impR (.andL (A := q6) (B := q7) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cAnd_6_8 : Interd (q6.and q8) q6 :=
  ⟨ofG4 (.impR (.andL (A := q6) (B := q8) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cAnd_6_9 : Interd (q6.and q9) q6 :=
  ⟨ofG4 (.impR (.andL (A := q6) (B := q9) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cAnd_6_10 : Interd (q6.and q10) q2 :=
  ⟨ofG4 (.andL (A := q6) (B := q10) (.head _) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))) (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))⟩

theorem cAnd_6_11 : Interd (q6.and q11) q6 :=
  ⟨ofG4 (.impR (.andL (A := q6) (B := q11) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cAnd_6_12 : Interd (q6.and q12) q6 :=
  ⟨ofG4 (.impR (.andL (A := q6) (B := q12) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_6_13 : Interd (q6.and q13) q6 :=
  ⟨ofG4 (.impR (.andL (A := q6) (B := q13) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxR (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

theorem cAnd_6_14 : Interd (q6.and q14) q6 :=
  ⟨ofG4 (.impR (.andL (A := q6) (B := q14) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLImp (A := q6) (B := q2) (D := q5) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impLLaxLax (A := q0) (B := q5) (X := q0) (.tail _ (.tail _ (.head _))) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.andR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cAnd_7_8 : Interd (q7.and q8) q7 :=
  ⟨ofG4 (.andL (A := q7) (B := q8) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

theorem cAnd_7_9 : Interd (q7.and q9) q7 :=
  ⟨ofG4 (.andL (A := q7) (B := q9) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_7_10 : Interd (q7.and q10) q4 :=
  ⟨ofG4 (.andL (A := q7) (B := q10) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_7_11 : Interd (q7.and q11) q7 :=
  ⟨ofG4 (.andL (A := q7) (B := q11) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_7_12 : Interd (q7.and q12) q7 :=
  ⟨ofG4 (.andL (A := q7) (B := q12) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cAnd_7_13 : Interd (q7.and q13) q7 :=
  ⟨ofG4 (.andL (A := q7) (B := q13) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q8) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.laxR (.impLLax (A := q3) (B := q4) (.head _) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q8) (.tail _ (.tail _ (.head _))) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.laxR (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cAnd_7_14 : Interd (q7.and q14) q7 :=
  ⟨ofG4 (.andL (A := q7) (B := q14) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cAnd_8_9 : Interd (q8.and q9) q7 :=
  ⟨ofG4 (.andL (A := q8) (B := q9) (.head _) (.orL (A := q5) (B := q6) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.andR (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

/-- REFUTED CELL (new class): certified ≤4-world countermodels
eliminate EVERY candidate class — this combination is not
interderivable with any of the 15 representatives, so the 15-class
closure FAILS here.  The stated collapse (to q0, a placeholder) is
FALSE; the `sorry` records the failure point. -/
theorem cAnd_8_10 : Interd (q8.and q10) q0 := sorry

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_8_11 : Interd (q8.and q11) q8 := sorry

/-- OPEN CELL: candidates [7] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_8_12 : Interd (q8.and q12) q7 := sorry

theorem cAnd_8_13 : Interd (q8.and q13) q8 :=
  ⟨ofG4 (.impR (.andL (A := q8) (B := q13) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q8) (.head _) (.tail _ (.head _)) (.laxL (A := q3) (.tail _ (.tail _ (.tail _ (.head _)))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))),
   ofG4 (.andR (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))) (.laxR (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))))⟩

/-- OPEN CELL: candidates [7] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_8_14 : Interd (q8.and q14) q7 := sorry

theorem cAnd_9_10 : Interd (q9.and q10) q5 :=
  ⟨ofG4 (.andL (A := q9) (B := q10) (.head _) (.orL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.andR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_9_11 : Interd (q9.and q11) q9 :=
  ⟨ofG4 (.andL (A := q9) (B := q11) (.head _) (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q5) (B := q6) (.head _) (.orR2 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cAnd_9_12 : Interd (q9.and q12) q9 :=
  ⟨ofG4 (.andL (A := q9) (B := q12) (.head _) (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.andR (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.laxR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_9_13 : Interd (q9.and q13) q9 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_9_14 : Interd (q9.and q14) q9 := sorry

theorem cAnd_10_11 : Interd (q10.and q11) q10 :=
  ⟨ofG4 (.impR (.andL (A := q10) (B := q11) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.andR (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cAnd_10_12 : Interd (q10.and q12) q5 :=
  ⟨ofG4 (.andL (A := q10) (B := q12) (.head _) (.laxL (A := q7) (.tail _ (.head _)) (.orL (A := q3) (B := q6) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))),
   ofG4 (.andR (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

/-- OPEN CELL: candidates [10] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_10_13 : Interd (q10.and q13) q10 := sorry

/-- OPEN CELL: candidates [5] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_10_14 : Interd (q10.and q14) q5 := sorry

theorem cAnd_11_12 : Interd (q11.and q12) q9 :=
  ⟨ofG4 (.andL (A := q11) (B := q12) (.head _) (.orL (A := q6) (B := q10) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.botL (.head _))))) (.orR1 (.laxL (A := q7) (.tail _ (.tail _ (.head _))) (.orL (A := q3) (B := q6) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))),
   ofG4 (.andR (.orL (A := q5) (B := q6) (.head _) (.orR2 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.laxR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_11_13 : Interd (q11.and q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_11_14 : Interd (q11.and q14) q9 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_12_13 : Interd (q12.and q13) q9 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_12_14 : Interd (q12.and q14) q9 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cAnd_13_14 : Interd (q13.and q14) q9 := sorry

theorem cOr_2_4 : Interd (q2.or q4) q4 :=
  ⟨ofG4 (.orL (A := q2) (B := q4) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cOr_2_5 : Interd (q2.or q5) q5 :=
  ⟨ofG4 (.orL (A := q2) (B := q5) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.orR2 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cOr_2_6 : Interd (q2.or q6) q6 :=
  ⟨ofG4 (.impR (.orL (A := q2) (B := q6) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

theorem cOr_2_7 : Interd (q2.or q7) q7 :=
  ⟨ofG4 (.orL (A := q2) (B := q7) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_2_8 : Interd (q2.or q8) q8 :=
  ⟨ofG4 (.impR (.orL (A := q2) (B := q8) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))),
   ofG4 (.orR2 (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cOr_2_9 : Interd (q2.or q9) q9 :=
  ⟨ofG4 (.orL (A := q2) (B := q9) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_2_10 : Interd (q2.or q10) q10 :=
  ⟨ofG4 (.impR (.orL (A := q2) (B := q10) (.tail _ (.head _)) (.laxL (A := q0) (.head _) (.botL (.head _))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cOr_2_11 : Interd (q2.or q11) q11 :=
  ⟨ofG4 (.orL (A := q2) (B := q11) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))),
   ofG4 (.orR2 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cOr_2_12 : Interd (q2.or q12) q12 :=
  ⟨ofG4 (.orL (A := q2) (B := q12) (.head _) (.laxR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))) (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))),
   ofG4 (.orR2 (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_2_13 : Interd (q2.or q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_2_14 : Interd (q2.or q14) q9 := sorry

theorem cOr_3_4 : Interd (q3.or q4) q4 :=
  ⟨ofG4 (.orL (A := q3) (B := q4) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cOr_3_5 : Interd (q3.or q5) q5 :=
  ⟨ofG4 (.orL (A := q3) (B := q5) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.orR2 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cOr_3_7 : Interd (q3.or q7) q7 :=
  ⟨ofG4 (.orL (A := q3) (B := q7) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_3_8 : Interd (q3.or q8) q8 :=
  ⟨ofG4 (.impR (.orL (A := q3) (B := q8) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))),
   ofG4 (.orR2 (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cOr_3_9 : Interd (q3.or q9) q9 :=
  ⟨ofG4 (.orL (A := q3) (B := q9) (.head _) (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_3_10 : Interd (q3.or q10) q10 :=
  ⟨ofG4 (.impR (.orL (A := q3) (B := q10) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cOr_3_11 : Interd (q3.or q11) q11 :=
  ⟨ofG4 (.orL (A := q3) (B := q11) (.head _) (.orR2 (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))),
   ofG4 (.orR2 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cOr_3_12 : Interd (q3.or q12) q12 :=
  ⟨ofG4 (.orL (A := q3) (B := q12) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))),
   ofG4 (.orR2 (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_3_13 : Interd (q3.or q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_3_14 : Interd (q3.or q14) q9 := sorry

theorem cOr_4_5 : Interd (q4.or q5) q5 :=
  ⟨ofG4 (.orL (A := q4) (B := q5) (.head _) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.orR2 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cOr_4_6 : Interd (q4.or q6) q7 :=
  ⟨ofG4 (.orL (A := q4) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))),
   ofG4 (.orL (A := q3) (B := q6) (.head _) (.orR1 (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cOr_4_7 : Interd (q4.or q7) q7 :=
  ⟨ofG4 (.orL (A := q4) (B := q7) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_4_8 : Interd (q4.or q8) q8 :=
  ⟨ofG4 (.impR (.orL (A := q4) (B := q8) (.tail _ (.head _)) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))),
   ofG4 (.orR2 (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cOr_4_9 : Interd (q4.or q9) q9 :=
  ⟨ofG4 (.orL (A := q4) (B := q9) (.head _) (.orR1 (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_4_10 : Interd (q4.or q10) q10 :=
  ⟨ofG4 (.impR (.orL (A := q4) (B := q10) (.tail _ (.head _)) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cOr_4_11 : Interd (q4.or q11) q11 :=
  ⟨ofG4 (.orL (A := q4) (B := q11) (.head _) (.orR2 (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))),
   ofG4 (.orR2 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cOr_4_12 : Interd (q4.or q12) q12 :=
  ⟨ofG4 (.orL (A := q4) (B := q12) (.head _) (.laxR (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))),
   ofG4 (.orR2 (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))))))⟩

theorem cOr_4_13 : Interd (q4.or q13) q13 :=
  ⟨ofG4 (.orL (A := q4) (B := q13) (.head _) (.laxR (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))) (.laxL (A := q8) (.head _) (.laxR (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))))),
   ofG4 (.orR2 (.laxL (A := q8) (.head _) (.laxR (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))))⟩

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_4_14 : Interd (q4.or q14) q9 := sorry

theorem cOr_5_7 : Interd (q5.or q7) q9 :=
  ⟨ofG4 (.orL (A := q5) (B := q7) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_5_8 : Interd (q5.or q8) q1 := sorry

theorem cOr_5_9 : Interd (q5.or q9) q9 :=
  ⟨ofG4 (.orL (A := q5) (B := q9) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_5_10 : Interd (q5.or q10) q10 :=
  ⟨ofG4 (.impR (.orL (A := q5) (B := q10) (.tail _ (.head _)) (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cOr_5_11 : Interd (q5.or q11) q11 :=
  ⟨ofG4 (.orL (A := q5) (B := q11) (.head _) (.orR2 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))),
   ofG4 (.orR2 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cOr_5_12 : Interd (q5.or q12) q12 :=
  ⟨ofG4 (.orL (A := q5) (B := q12) (.head _) (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))),
   ofG4 (.orR2 (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))))))⟩

theorem cOr_5_13 : Interd (q5.or q13) q13 :=
  ⟨ofG4 (.orL (A := q5) (B := q13) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))))) (.laxL (A := q8) (.head _) (.laxR (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))))),
   ofG4 (.orR2 (.laxL (A := q8) (.head _) (.laxR (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))))⟩

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_5_14 : Interd (q5.or q14) q9 := sorry

theorem cOr_6_7 : Interd (q6.or q7) q7 :=
  ⟨ofG4 (.orL (A := q6) (B := q7) (.head _) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_6_8 : Interd (q6.or q8) q8 :=
  ⟨ofG4 (.impR (.orL (A := q6) (B := q8) (.tail _ (.head _)) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))),
   ofG4 (.orR2 (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cOr_6_9 : Interd (q6.or q9) q9 :=
  ⟨ofG4 (.orL (A := q6) (B := q9) (.head _) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_6_11 : Interd (q6.or q11) q11 :=
  ⟨ofG4 (.orL (A := q6) (B := q11) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))),
   ofG4 (.orR2 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cOr_6_12 : Interd (q6.or q12) q12 :=
  ⟨ofG4 (.orL (A := q6) (B := q12) (.head _) (.laxR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))),
   ofG4 (.orR2 (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_6_13 : Interd (q6.or q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_6_14 : Interd (q6.or q14) q9 := sorry

theorem cOr_7_8 : Interd (q7.or q8) q8 :=
  ⟨ofG4 (.impR (.orL (A := q7) (B := q8) (.tail _ (.head _)) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.tail _ (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))),
   ofG4 (.orR2 (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cOr_7_9 : Interd (q7.or q9) q9 :=
  ⟨ofG4 (.orL (A := q7) (B := q9) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.orR2 (.orL (A := q5) (B := q6) (.head _) (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cOr_7_10 : Interd (q7.or q10) q11 :=
  ⟨ofG4 (.orL (A := q7) (B := q10) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))),
   ofG4 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cOr_7_11 : Interd (q7.or q11) q11 :=
  ⟨ofG4 (.orL (A := q7) (B := q11) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))),
   ofG4 (.orR2 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cOr_7_12 : Interd (q7.or q12) q12 :=
  ⟨ofG4 (.orL (A := q7) (B := q12) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))),
   ofG4 (.orR2 (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_7_13 : Interd (q7.or q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_7_14 : Interd (q7.or q14) q9 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_8_9 : Interd (q8.or q9) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_8_10 : Interd (q8.or q10) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_8_11 : Interd (q8.or q11) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_8_12 : Interd (q8.or q12) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_8_13 : Interd (q8.or q13) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_8_14 : Interd (q8.or q14) q1 := sorry

theorem cOr_9_10 : Interd (q9.or q10) q11 :=
  ⟨ofG4 (.orL (A := q9) (B := q10) (.head _) (.orL (A := q5) (B := q6) (.head _) (.orR2 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))),
   ofG4 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cOr_9_11 : Interd (q9.or q11) q11 :=
  ⟨ofG4 (.orL (A := q9) (B := q11) (.head _) (.orL (A := q5) (B := q6) (.head _) (.orR2 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))) (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))),
   ofG4 (.orR2 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cOr_9_12 : Interd (q9.or q12) q12 :=
  ⟨ofG4 (.orL (A := q9) (B := q12) (.head _) (.orL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.laxR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))),
   ofG4 (.orR2 (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_9_13 : Interd (q9.or q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_9_14 : Interd (q9.or q14) q9 := sorry

theorem cOr_10_11 : Interd (q10.or q11) q11 :=
  ⟨ofG4 (.orL (A := q10) (B := q11) (.head _) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))) (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))),
   ofG4 (.orR2 (.orL (A := q6) (B := q10) (.head _) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_10_12 : Interd (q10.or q12) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_10_13 : Interd (q10.or q13) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_10_14 : Interd (q10.or q14) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_11_12 : Interd (q11.or q12) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_11_13 : Interd (q11.or q13) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_11_14 : Interd (q11.or q14) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_12_13 : Interd (q12.or q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_12_14 : Interd (q12.or q14) q9 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cOr_13_14 : Interd (q13.or q14) q1 := sorry

theorem cImp_2_3 : Interd (q2.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLLaxLax (A := q0) (B := q3) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cImp_2_4 : Interd (q2.ifThen q4) q1 :=
  ⟨topD, ofG4 (.impR (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))))⟩

theorem cImp_2_5 : Interd (q2.ifThen q5) q1 :=
  ⟨topD, ofG4 (.impR (.laxL (A := q0) (.head _) (.botL (.head _))))⟩

theorem cImp_2_6 : Interd (q2.ifThen q6) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cImp_2_7 : Interd (q2.ifThen q7) q1 :=
  ⟨topD, ofG4 (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cImp_2_8 : Interd (q2.ifThen q8) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_2_9 : Interd (q2.ifThen q9) q1 :=
  ⟨topD, ofG4 (.impR (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))))⟩

theorem cImp_2_10 : Interd (q2.ifThen q10) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))⟩

theorem cImp_2_11 : Interd (q2.ifThen q11) q1 :=
  ⟨topD, ofG4 (.impR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cImp_2_12 : Interd (q2.ifThen q12) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cImp_2_13 : Interd (q2.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cImp_2_14 : Interd (q2.ifThen q14) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))⟩

theorem cImp_3_2 : Interd (q3.ifThen q2) q6 :=
  ⟨ofG4 (.impR (.impLImp (A := q2) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

theorem cImp_3_4 : Interd (q3.ifThen q4) q1 :=
  ⟨topD, ofG4 (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cImp_3_5 : Interd (q3.ifThen q5) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cImp_3_6 : Interd (q3.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLImp (A := q2) (B := q0) (D := q6) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

theorem cImp_3_7 : Interd (q3.ifThen q7) q1 :=
  ⟨topD, ofG4 (.impR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))⟩

theorem cImp_3_8 : Interd (q3.ifThen q8) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cImp_3_9 : Interd (q3.ifThen q9) q1 :=
  ⟨topD, ofG4 (.impR (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cImp_3_10 : Interd (q3.ifThen q10) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cImp_3_11 : Interd (q3.ifThen q11) q1 :=
  ⟨topD, ofG4 (.impR (.orR2 (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cImp_3_12 : Interd (q3.ifThen q12) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cImp_3_13 : Interd (q3.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_3_14 : Interd (q3.ifThen q14) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cImp_4_0 : Interd (q4.ifThen q0) q0 :=
  ⟨ofG4 (.impLOr (A := q2) (B := q3) (D := q0) (.head _) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))),
   ofG4 (.botL (.head _))⟩

theorem cImp_4_2 : Interd (q4.ifThen q2) q6 :=
  ⟨ofG4 (.impR (.impLOr (A := q2) (B := q3) (D := q2) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))))),
   ofG4 (.impR (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cImp_4_3 : Interd (q4.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLOr (A := q2) (B := q3) (D := q3) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q3) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cImp_4_5 : Interd (q4.ifThen q5) q1 :=
  ⟨topD, ofG4 (.impR (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cImp_4_6 : Interd (q4.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLOr (A := q2) (B := q3) (D := q6) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q6) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q6) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

theorem cImp_4_7 : Interd (q4.ifThen q7) q1 :=
  ⟨topD, ofG4 (.impR (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cImp_4_8 : Interd (q4.ifThen q8) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_4_9 : Interd (q4.ifThen q9) q1 :=
  ⟨topD, ofG4 (.impR (.orR1 (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_4_10 : Interd (q4.ifThen q10) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cImp_4_11 : Interd (q4.ifThen q11) q1 :=
  ⟨topD, ofG4 (.impR (.orR2 (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cImp_4_12 : Interd (q4.ifThen q12) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_4_13 : Interd (q4.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cImp_4_14 : Interd (q4.ifThen q14) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_5_0 : Interd (q5.ifThen q0) q0 :=
  ⟨ofG4 (.impLLax (A := q3) (B := q0) (.head _) (.impR (.impLLax (A := q3) (B := q0) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))),
   ofG4 (.botL (.head _))⟩

theorem cImp_5_2 : Interd (q5.ifThen q2) q6 :=
  ⟨ofG4 (.impR (.impLLax (A := q3) (B := q2) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cImp_5_3 : Interd (q5.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLLax (A := q3) (B := q3) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q3) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cImp_5_6 : Interd (q5.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLLax (A := q3) (B := q6) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))⟩

theorem cImp_5_7 : Interd (q5.ifThen q7) q8 :=
  ⟨ofG4 (.impR (.impLLaxLax (A := q3) (B := q7) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.tail _ (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))),
   ofG4 (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_5_8 : Interd (q5.ifThen q8) q8 :=
  ⟨ofG4 (.impR (.impLLaxLax (A := q3) (B := q8) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.tail _ (.head _))) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cImp_5_9 : Interd (q5.ifThen q9) q1 :=
  ⟨topD, ofG4 (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_5_10 : Interd (q5.ifThen q10) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cImp_5_11 : Interd (q5.ifThen q11) q1 :=
  ⟨topD, ofG4 (.impR (.orR2 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cImp_5_12 : Interd (q5.ifThen q12) q1 :=
  ⟨topD, ofG4 (.impR (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_5_13 : Interd (q5.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.laxL (A := q3) (.head _) (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))))))⟩

theorem cImp_5_14 : Interd (q5.ifThen q14) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_6_0 : Interd (q6.ifThen q0) q3 :=
  ⟨ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))),
   ofG4 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))⟩

theorem cImp_6_3 : Interd (q6.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q3) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

theorem cImp_6_4 : Interd (q6.ifThen q4) q10 :=
  ⟨ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.impR (.orR1 (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cImp_6_5 : Interd (q6.ifThen q5) q10 :=
  ⟨ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q5) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))⟩

theorem cImp_6_7 : Interd (q6.ifThen q7) q1 :=
  ⟨topD, ofG4 (.impR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cImp_6_8 : Interd (q6.ifThen q8) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cImp_6_9 : Interd (q6.ifThen q9) q1 :=
  ⟨topD, ofG4 (.impR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cImp_6_10 : Interd (q6.ifThen q10) q10 :=
  ⟨ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q10) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cImp_6_11 : Interd (q6.ifThen q11) q1 :=
  ⟨topD, ofG4 (.impR (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

theorem cImp_6_12 : Interd (q6.ifThen q12) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cImp_6_13 : Interd (q6.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

theorem cImp_6_14 : Interd (q6.ifThen q14) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cImp_7_0 : Interd (q7.ifThen q0) q0 :=
  ⟨ofG4 (.impLOr (A := q3) (B := q6) (D := q0) (.head _) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLImp (A := q3) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))),
   ofG4 (.botL (.head _))⟩

theorem cImp_7_2 : Interd (q7.ifThen q2) q2 :=
  ⟨ofG4 (.impLOr (A := q3) (B := q6) (D := q2) (.head _) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))),
   ofG4 (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _))))⟩

theorem cImp_7_3 : Interd (q7.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLOr (A := q3) (B := q6) (D := q3) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q3) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q3) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cImp_7_4 : Interd (q7.ifThen q4) q10 :=
  ⟨ofG4 (.impR (.impLOr (A := q3) (B := q6) (D := q4) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))),
   ofG4 (.impR (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cImp_7_5 : Interd (q7.ifThen q5) q10 :=
  ⟨ofG4 (.impR (.impLOr (A := q3) (B := q6) (D := q5) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q5) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q5) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.head _)) (.head _) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))) (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))),
   ofG4 (.impR (.orL (A := q3) (B := q6) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cImp_7_6 : Interd (q7.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLOr (A := q3) (B := q6) (D := q6) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q6) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q6) (.tail _ (.tail _ (.head _))) (.impLImp (A := q3) (B := q0) (D := q6) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

theorem cImp_7_8 : Interd (q7.ifThen q8) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

theorem cImp_7_9 : Interd (q7.ifThen q9) q1 :=
  ⟨topD, ofG4 (.impR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cImp_7_10 : Interd (q7.ifThen q10) q10 :=
  ⟨ofG4 (.impR (.impLOr (A := q3) (B := q6) (D := q10) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q10) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q10) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))))),
   ofG4 (.impR (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cImp_7_11 : Interd (q7.ifThen q11) q1 :=
  ⟨topD, ofG4 (.impR (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cImp_7_12 : Interd (q7.ifThen q12) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cImp_7_13 : Interd (q7.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cImp_7_14 : Interd (q7.ifThen q14) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cImp_8_0 : Interd (q8.ifThen q0) q0 :=
  ⟨ofG4 (.impLImp (A := q5) (B := q4) (D := q0) (.head _) (.impR (.orR1 (.laxR (.impLOr (A := q2) (B := q3) (D := q0) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))) (.botL (.head _))),
   ofG4 (.botL (.head _))⟩

theorem cImp_8_2 : Interd (q8.ifThen q2) q2 :=
  ⟨ofG4 (.impLImp (A := q5) (B := q4) (D := q2) (.head _) (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLOr (A := q2) (B := q3) (D := q2) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q2) (X := q3) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _))))))))) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _))))⟩

theorem cImp_8_3 : Interd (q8.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLImp (A := q5) (B := q4) (D := q3) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.impLOr (A := q2) (B := q3) (D := q3) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q3) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.laxL (A := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.botL (.head _))) (.botL (.head _)))))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))))⟩

/-- OPEN CELL: candidates [5] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_8_4 : Interd (q8.ifThen q4) q5 := sorry

/-- OPEN CELL: candidates [5] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_8_5 : Interd (q8.ifThen q5) q5 := sorry

theorem cImp_8_6 : Interd (q8.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLImp (A := q5) (B := q4) (D := q6) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.impLOr (A := q2) (B := q3) (D := q6) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q6) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q6) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_8_7 : Interd (q8.ifThen q7) q9 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_8_9 : Interd (q8.ifThen q9) q9 := sorry

/-- OPEN CELL: candidates [10] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_8_10 : Interd (q8.ifThen q10) q10 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_8_11 : Interd (q8.ifThen q11) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_8_12 : Interd (q8.ifThen q12) q9 := sorry

theorem cImp_8_13 : Interd (q8.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.laxR (.impR (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))))⟩

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_8_14 : Interd (q8.ifThen q14) q9 := sorry

theorem cImp_9_0 : Interd (q9.ifThen q0) q0 :=
  ⟨ofG4 (.impLOr (A := q5) (B := q6) (D := q0) (.head _) (.impLLax (A := q3) (B := q0) (.head _) (.impR (.impLLax (A := q3) (B := q0) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))),
   ofG4 (.botL (.head _))⟩

theorem cImp_9_2 : Interd (q9.ifThen q2) q2 :=
  ⟨ofG4 (.impLOr (A := q5) (B := q6) (D := q2) (.head _) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))),
   ofG4 (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _))))⟩

theorem cImp_9_3 : Interd (q9.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLOr (A := q5) (B := q6) (D := q3) (.tail _ (.head _)) (.impLLax (A := q3) (B := q3) (.head _) (.impLLaxLax (A := q3) (B := q3) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.orL (A := q5) (B := q6) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.laxL (A := q0) (.tail _ (.tail _ (.head _))) (.botL (.head _))) (.botL (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))⟩

/-- REFUTED CELL (new class): certified ≤4-world countermodels
eliminate EVERY candidate class — this combination is not
interderivable with any of the 15 representatives, so the 15-class
closure FAILS here.  The stated collapse (to q0, a placeholder) is
FALSE; the `sorry` records the failure point. -/
theorem cImp_9_4 : Interd (q9.ifThen q4) q0 := sorry

theorem cImp_9_5 : Interd (q9.ifThen q5) q10 :=
  ⟨ofG4 (.impR (.impLOr (A := q5) (B := q6) (D := q5) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q5) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q5) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.head _)) (.head _) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))) (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))),
   ofG4 (.impR (.orL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cImp_9_6 : Interd (q9.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLOr (A := q5) (B := q6) (D := q6) (.tail _ (.head _)) (.impLLax (A := q3) (B := q6) (.head _) (.impR (.impLLax (A := q3) (B := q6) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q6) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

theorem cImp_9_7 : Interd (q9.ifThen q7) q8 :=
  ⟨ofG4 (.impR (.impLOr (A := q5) (B := q6) (D := q7) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q7) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))),
   ofG4 (.impR (.orL (A := q5) (B := q6) (.head _) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.tail _ (.tail _ (.head _))) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_9_8 : Interd (q9.ifThen q8) q8 := sorry

theorem cImp_9_10 : Interd (q9.ifThen q10) q10 :=
  ⟨ofG4 (.impR (.impLOr (A := q5) (B := q6) (D := q10) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q10) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q10) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))))),
   ofG4 (.impR (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

theorem cImp_9_11 : Interd (q9.ifThen q11) q1 :=
  ⟨topD, ofG4 (.impR (.orL (A := q5) (B := q6) (.head _) (.orR2 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.orR1 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))⟩

theorem cImp_9_12 : Interd (q9.ifThen q12) q1 :=
  ⟨topD, ofG4 (.impR (.orL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.laxR (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cImp_9_13 : Interd (q9.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.orL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))))) (.laxR (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cImp_9_14 : Interd (q9.ifThen q14) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.orL (A := q5) (B := q6) (.tail _ (.head _)) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cImp_10_0 : Interd (q10.ifThen q0) q0 :=
  ⟨ofG4 (.impLImp (A := q6) (B := q2) (D := q0) (.head _) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.botL (.head _))),
   ofG4 (.botL (.head _))⟩

theorem cImp_10_2 : Interd (q10.ifThen q2) q6 :=
  ⟨ofG4 (.impR (.impLImp (A := q6) (B := q2) (D := q2) (.tail _ (.head _)) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))⟩

theorem cImp_10_3 : Interd (q10.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLImp (A := q6) (B := q2) (D := q3) (.tail _ (.head _)) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q3) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))⟩

/-- OPEN CELL: candidates [7] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_10_4 : Interd (q10.ifThen q4) q7 := sorry

theorem cImp_10_6 : Interd (q10.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLImp (A := q6) (B := q2) (D := q6) (.tail _ (.head _)) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))⟩

/-- OPEN CELL: candidates [7] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_10_7 : Interd (q10.ifThen q7) q7 := sorry

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_10_8 : Interd (q10.ifThen q8) q8 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_10_9 : Interd (q10.ifThen q9) q9 := sorry

theorem cImp_10_11 : Interd (q10.ifThen q11) q1 :=
  ⟨topD, ofG4 (.impR (.orR2 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_10_12 : Interd (q10.ifThen q12) q9 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_10_13 : Interd (q10.ifThen q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_10_14 : Interd (q10.ifThen q14) q9 := sorry

theorem cImp_11_0 : Interd (q11.ifThen q0) q0 :=
  ⟨ofG4 (.impLOr (A := q6) (B := q10) (D := q0) (.head _) (.impLImp (A := q3) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLImp (A := q6) (B := q2) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))),
   ofG4 (.botL (.head _))⟩

theorem cImp_11_2 : Interd (q11.ifThen q2) q2 :=
  ⟨ofG4 (.impLOr (A := q6) (B := q10) (D := q2) (.head _) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q6) (B := q2) (D := q2) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))),
   ofG4 (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _))))⟩

theorem cImp_11_3 : Interd (q11.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLOr (A := q6) (B := q10) (D := q3) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q3) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.orL (A := q6) (B := q10) (.tail _ (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))))⟩

/-- OPEN CELL: candidates [4] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_11_4 : Interd (q11.ifThen q4) q4 := sorry

theorem cImp_11_5 : Interd (q11.ifThen q5) q5 :=
  ⟨ofG4 (.impLOr (A := q6) (B := q10) (D := q5) (.head _) (.impLImp (A := q6) (B := q2) (D := q5) (.tail _ (.head _)) (.impR (.impLImp (A := q3) (B := q0) (D := q5) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.laxL (A := q3) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))),
   ofG4 (.impR (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cImp_11_6 : Interd (q11.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLOr (A := q6) (B := q10) (D := q6) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q6) (.head _) (.impR (.impLImp (A := q6) (B := q2) (D := q6) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

/-- OPEN CELL: candidates [7] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_11_7 : Interd (q11.ifThen q7) q7 := sorry

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_11_8 : Interd (q11.ifThen q8) q8 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_11_9 : Interd (q11.ifThen q9) q9 := sorry

theorem cImp_11_10 : Interd (q11.ifThen q10) q10 :=
  ⟨ofG4 (.impR (.impLOr (A := q6) (B := q10) (D := q10) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q10) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q10) (.tail _ (.tail _ (.head _))) (.impLImp (A := q6) (B := q2) (D := q10) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q10) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))))),
   ofG4 (.impR (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_11_12 : Interd (q11.ifThen q12) q9 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_11_13 : Interd (q11.ifThen q13) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_11_14 : Interd (q11.ifThen q14) q9 := sorry

theorem cImp_12_0 : Interd (q12.ifThen q0) q0 :=
  ⟨ofG4 (.impLLax (A := q7) (B := q0) (.head _) (.orR1 (.impR (.impLLax (A := q7) (B := q0) (.tail _ (.head _)) (.orR1 (.impLLaxLax (A := q7) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.botL (.head _))),
   ofG4 (.botL (.head _))⟩

theorem cImp_12_2 : Interd (q12.ifThen q2) q2 :=
  ⟨ofG4 (.impLLax (A := q7) (B := q2) (.head _) (.orR2 (.impR (.impLLax (A := q7) (B := q2) (.tail _ (.head _)) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.impR (.laxL (A := q7) (.head _) (.laxL (A := q0) (.tail _ (.tail _ (.head _))) (.botL (.head _)))))⟩

theorem cImp_12_3 : Interd (q12.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLLax (A := q7) (B := q3) (.tail _ (.head _)) (.orR1 (.impLLaxLax (A := q7) (B := q3) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))⟩

/-- REFUTED CELL (new class): certified ≤4-world countermodels
eliminate EVERY candidate class — this combination is not
interderivable with any of the 15 representatives, so the 15-class
closure FAILS here.  The stated collapse (to q0, a placeholder) is
FALSE; the `sorry` records the failure point. -/
theorem cImp_12_4 : Interd (q12.ifThen q4) q0 := sorry

theorem cImp_12_5 : Interd (q12.ifThen q5) q10 :=
  ⟨ofG4 (.impR (.impLLax (A := q7) (B := q5) (.tail _ (.head _)) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.impR (.laxL (A := q7) (.head _) (.orL (A := q3) (B := q6) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cImp_12_6 : Interd (q12.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLLax (A := q7) (B := q6) (.tail _ (.head _)) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.botL (.head _)))))⟩

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_12_7 : Interd (q12.ifThen q7) q8 := sorry

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_12_8 : Interd (q12.ifThen q8) q8 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_12_9 : Interd (q12.ifThen q9) q1 := sorry

theorem cImp_12_10 : Interd (q12.ifThen q10) q10 :=
  ⟨ofG4 (.impR (.impLLax (A := q7) (B := q10) (.tail _ (.head _)) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.laxL (A := q7) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_12_11 : Interd (q12.ifThen q11) q1 := sorry

theorem cImp_12_13 : Interd (q12.ifThen q13) q1 :=
  ⟨topD, ofG4 (.impR (.laxL (A := q7) (.head _) (.laxR (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))))⟩

theorem cImp_12_14 : Interd (q12.ifThen q14) q1 :=
  ⟨topD, ofG4 (.impR (.impR (.laxL (A := q7) (.tail _ (.head _)) (.orL (A := q3) (B := q6) (.head _) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cImp_13_0 : Interd (q13.ifThen q0) q0 :=
  ⟨ofG4 (.impLLax (A := q8) (B := q0) (.head _) (.impR (.orR1 (.laxR (.impLLax (A := q8) (B := q0) (.tail _ (.head _)) (.impLLaxLax (A := q8) (B := q0) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.botL (.head _))) (.botL (.head _)))))) (.botL (.head _))),
   ofG4 (.botL (.head _))⟩

theorem cImp_13_2 : Interd (q13.ifThen q2) q2 :=
  ⟨ofG4 (.impLLax (A := q8) (B := q2) (.head _) (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLLax (A := q8) (B := q2) (.tail _ (.tail _ (.head _))) (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.impR (.laxL (A := q8) (.head _) (.laxL (A := q0) (.tail _ (.tail _ (.head _))) (.botL (.head _)))))⟩

theorem cImp_13_3 : Interd (q13.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLLax (A := q8) (B := q3) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.impLLax (A := q8) (B := q3) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q8) (B := q3) (X := q3) (.tail _ (.tail _ (.head _))) (.head _) (.laxR (.impR (.orR1 (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _))))))) (.impR (.orR1 (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _))))))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.head _)) (.laxL (A := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _))) (.botL (.head _))))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))⟩

theorem cImp_13_4 : Interd (q13.ifThen q4) q4 :=
  ⟨ofG4 (.impLLax (A := q8) (B := q4) (.head _) (.impR (.impLLax (A := q8) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q8) (B := q4) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.impR (.orL (A := q2) (B := q3) (.tail _ (.head _)) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

/-- OPEN CELL: candidates [5] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_13_5 : Interd (q13.ifThen q5) q5 := sorry

theorem cImp_13_6 : Interd (q13.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLLax (A := q8) (B := q6) (.tail _ (.head _)) (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q8) (.head _) (.tail _ (.head _)) (.laxR (.impLLax (A := q3) (B := q4) (.head _) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q8) (.tail _ (.tail _ (.head _))) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))) (.botL (.head _)))))⟩

theorem cImp_13_7 : Interd (q13.ifThen q7) q7 :=
  ⟨ofG4 (.impLLax (A := q8) (B := q7) (.head _) (.impR (.impLLax (A := q8) (B := q7) (.tail _ (.head _)) (.impLLaxLax (A := q8) (B := q7) (X := q3) (.tail _ (.head _)) (.head _) (.laxR (.impR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.laxL (A := q3) (.tail _ (.tail _ (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))) (.orL (A := q3) (B := q6) (.head _) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))),
   ofG4 (.impR (.orL (A := q3) (B := q6) (.tail _ (.head _)) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q8) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impLLax (A := q3) (B := q4) (.head _) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q8) (.tail _ (.tail _ (.head _))) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))) (.botL (.head _)))))))⟩

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_13_8 : Interd (q13.ifThen q8) q8 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_13_9 : Interd (q13.ifThen q9) q9 := sorry

theorem cImp_13_10 : Interd (q13.ifThen q10) q10 :=
  ⟨ofG4 (.impR (.impLLax (A := q8) (B := q10) (.tail _ (.head _)) (.impR (.orR1 (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.laxL (A := q8) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q8) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q8) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impLLax (A := q3) (B := q4) (.head _) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_13_11 : Interd (q13.ifThen q11) q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_13_12 : Interd (q13.ifThen q12) q9 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_13_14 : Interd (q13.ifThen q14) q9 := sorry

theorem cImp_14_0 : Interd (q14.ifThen q0) q0 :=
  ⟨ofG4 (.impLImp (A := q10) (B := q5) (D := q0) (.head _) (.impR (.laxR (.impR (.impLLax (A := q3) (B := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q3) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))))) (.botL (.head _))),
   ofG4 (.botL (.head _))⟩

theorem cImp_14_2 : Interd (q14.ifThen q2) q2 :=
  ⟨ofG4 (.impLImp (A := q10) (B := q5) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLLax (A := q3) (B := q2) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))),
   ofG4 (.impR (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _))))⟩

theorem cImp_14_3 : Interd (q14.ifThen q3) q3 :=
  ⟨ofG4 (.impR (.impLImp (A := q10) (B := q5) (D := q3) (.tail _ (.head _)) (.impR (.laxR (.impR (.impLLaxLax (A := q3) (B := q3) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLImp (A := q6) (B := q2) (D := q5) (.tail _ (.head _)) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q5) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) (.tail _ (.head _)) (.laxL (A := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _))) (.botL (.head _))) (.botL (.head _))))) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.laxL (A := q0) (.tail _ (.tail _ (.head _))) (.botL (.head _))) (.botL (.head _))))))⟩

/-- REFUTED CELL (new class): certified ≤4-world countermodels
eliminate EVERY candidate class — this combination is not
interderivable with any of the 15 representatives, so the 15-class
closure FAILS here.  The stated collapse (to q0, a placeholder) is
FALSE; the `sorry` records the failure point. -/
theorem cImp_14_4 : Interd (q14.ifThen q4) q0 := sorry

/-- OPEN CELL: candidates [10] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_14_5 : Interd (q14.ifThen q5) q10 := sorry

theorem cImp_14_6 : Interd (q14.ifThen q6) q6 :=
  ⟨ofG4 (.impR (.impLImp (A := q10) (B := q5) (D := q6) (.tail _ (.head _)) (.impR (.laxR (.impR (.impLLax (A := q3) (B := q6) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q3) (B := q6) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))),
   ofG4 (.impR (.impR (.impLImp (A := q6) (B := q2) (D := q5) (.tail _ (.head _)) (.impR (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q5) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.head _)) (.head _) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))⟩

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_14_7 : Interd (q14.ifThen q7) q8 := sorry

/-- OPEN CELL: candidates [8] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_14_8 : Interd (q14.ifThen q8) q8 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_14_9 : Interd (q14.ifThen q9) q1 := sorry

theorem cImp_14_10 : Interd (q14.ifThen q10) q10 :=
  ⟨ofG4 (.impR (.impLImp (A := q10) (B := q5) (D := q10) (.tail _ (.head _)) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.impR (.impR (.impLImp (A := q6) (B := q2) (D := q5) (.tail _ (.head _)) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))) (.laxL (A := q3) (.head _) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_14_11 : Interd (q14.ifThen q11) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_14_12 : Interd (q14.ifThen q12) q1 := sorry

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cImp_14_13 : Interd (q14.ifThen q13) q1 := sorry

theorem cBox_1 : Interd q1.somehow q1 :=
  ⟨ofG4 (.impR (.botL (.head _))),
   ofG4 (.laxR (.impR (.botL (.head _))))⟩

theorem cBox_4 : Interd q4.somehow q5 :=
  ⟨ofG4 (.laxL (A := q4) (.head _) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))),
   ofG4 (.laxL (A := q3) (.head _) (.laxR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))⟩

theorem cBox_6 : Interd q6.somehow q6 :=
  ⟨ofG4 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q6) (.head _) (.tail _ (.head _)) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))) (.botL (.head _)))),
   ofG4 (.laxR (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))⟩

theorem cBox_9 : Interd q9.somehow q12 :=
  ⟨ofG4 (.laxL (A := q9) (.head _) (.orL (A := q5) (B := q6) (.head _) (.laxL (A := q3) (.head _) (.laxR (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))) (.laxR (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q9) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))))))),
   ofG4 (.laxL (A := q7) (.head _) (.laxR (.orL (A := q3) (B := q6) (.head _) (.orR1 (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q7) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))⟩

theorem cBox_10 : Interd q10.somehow q10 :=
  ⟨ofG4 (.impR (.laxL (A := q10) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q10) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))),
   ofG4 (.laxR (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))⟩

/-- OPEN CELL: candidates [1, 11, 13] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cBox_11 : Interd q11.somehow q1 := sorry

/-- OPEN CELL: candidates [9, 12, 14] neither proved (both searchers) nor
refuted (exhaustive ≤4-world battery).  Sorried at the first open
candidate. -/
theorem cBox_14 : Interd q14.somehow q9 := sorry

/-! ## The closure theorems -/

theorem and_ok (i j : Fin 15) :
    Interd ((rep15 i).and (rep15 j)) (rep15 (andIdx15 i j)) :=
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
  | ⟨_+15, h⟩, _ => absurd h (by omega)
  | _, ⟨_+15, h⟩ => absurd h (by omega)

theorem or_ok (i j : Fin 15) :
    Interd ((rep15 i).or (rep15 j)) (rep15 (orIdx15 i j)) :=
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
  | ⟨_+15, h⟩, _ => absurd h (by omega)
  | _, ⟨_+15, h⟩ => absurd h (by omega)

theorem imp_ok (i j : Fin 15) :
    Interd ((rep15 i).ifThen (rep15 j)) (rep15 (impIdx15 i j)) :=
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
  | ⟨9, _⟩, ⟨0, _⟩ => cImp_9_0
  | ⟨9, _⟩, ⟨1, _⟩ => imp_top_i _
  | ⟨9, _⟩, ⟨2, _⟩ => cImp_9_2
  | ⟨9, _⟩, ⟨3, _⟩ => cImp_9_3
  | ⟨9, _⟩, ⟨4, _⟩ => cImp_9_4
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
  | ⟨_+15, h⟩, _ => absurd h (by omega)
  | _, ⟨_+15, h⟩ => absurd h (by omega)

theorem box_ok (i : Fin 15) :
    Interd (rep15 i).somehow (rep15 (boxIdx15 i)) :=
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
  | ⟨_+15, h⟩ => absurd h (by omega)

end RND

open RND in
/-- **The (PARTIAL) certified RN(◯,{}) dictionary**: 15 variable-free
representatives, crank bound 8, with kernel-checked closure tables at
603 of the 690 cells.  87 cells are sorried: 4 are REFUTED (see
`wip/rnDictRefute.lean` — the closure genuinely fails there, so this
record is NOT completable at these 15 representatives), 83 are OPEN. -/
def rnDict15 : RNDict where
  n := 15
  rep := rep15
  rep_varFree := by decide
  crankBound := 8
  rep_crank_le := by decide
  botIdx := ⟨0, by decide⟩
  bot_interd := Interd.refl _
  andIdx := andIdx15
  orIdx := orIdx15
  impIdx := impIdx15
  boxIdx := boxIdx15
  and_interd := and_ok
  or_interd := or_ok
  imp_interd := imp_ok
  box_interd := box_ok

/-! ## Axiom audit -/

-- PARTIAL instantiation: 87 cells are sorried (see the
-- per-cell doc comments: REFUTED/OPEN/SEARCHER-GAP).  No #guard_msgs pin.
#print axioms rnDict15

end SemUI
end PLLND
