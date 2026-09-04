import wip.rnc_probe

/-!
# Kernel-checked PCLL refutation certificates for RNC(◯,{})

GENERATED from wip/rnc_out.txt (scratchpad gen_cert.py) — the refuted
cells of the 19×19 PCLL-entailment matrix (15 representatives q0…q14 +
the four §40 closure witnesses w15…w18).  Each theorem is
`¬ ConfluentU.DerivU [X] Y`, discharged by `not_derivU_of_checkConf`
on a pinned MUTUALLY CONFLUENT finite countermodel: mutual confluence
(`confB`) and the countermodel check (`FinCM.checkB`) are both closed
Boolean computations, so `by decide` is kernel evaluation.  Confluent
models validate every distribution instance
(`force_somehow_or_dist_of_confluent`), hence these refute PLL + the
distribution scheme (PCLL), not merely PLL.
-/

namespace PLLND
namespace RNC

theorem rnc_ref_1_0 : ¬ ConfluentU.DerivU [q1] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_1_2 : ¬ ConfluentU.DerivU [q1] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_1_3 : ¬ ConfluentU.DerivU [q1] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_1_4 : ¬ ConfluentU.DerivU [q1] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_1_5 : ¬ ConfluentU.DerivU [q1] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_1_6 : ¬ ConfluentU.DerivU [q1] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_1_7 : ¬ ConfluentU.DerivU [q1] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_1_8 : ¬ ConfluentU.DerivU [q1] q8 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_1_9 : ¬ ConfluentU.DerivU [q1] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_1_10 : ¬ ConfluentU.DerivU [q1] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_1_11 : ¬ ConfluentU.DerivU [q1] q11 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_1_12 : ¬ ConfluentU.DerivU [q1] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_1_13 : ¬ ConfluentU.DerivU [q1] q13 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (4, 3)], [(1, 2), (4, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_1_14 : ¬ ConfluentU.DerivU [q1] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_1_15 : ¬ ConfluentU.DerivU [q1] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_1_16 : ¬ ConfluentU.DerivU [q1] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_1_17 : ¬ ConfluentU.DerivU [q1] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_1_18 : ¬ ConfluentU.DerivU [q1] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_2_0 : ¬ ConfluentU.DerivU [q2] q0 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_2_3 : ¬ ConfluentU.DerivU [q2] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_3_0 : ¬ ConfluentU.DerivU [q3] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_3_2 : ¬ ConfluentU.DerivU [q3] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_3_6 : ¬ ConfluentU.DerivU [q3] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_4_0 : ¬ ConfluentU.DerivU [q4] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_4_2 : ¬ ConfluentU.DerivU [q4] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_4_3 : ¬ ConfluentU.DerivU [q4] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_4_6 : ¬ ConfluentU.DerivU [q4] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_5_0 : ¬ ConfluentU.DerivU [q5] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_5_2 : ¬ ConfluentU.DerivU [q5] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_5_3 : ¬ ConfluentU.DerivU [q5] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_5_4 : ¬ ConfluentU.DerivU [q5] q4 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_5_6 : ¬ ConfluentU.DerivU [q5] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_5_7 : ¬ ConfluentU.DerivU [q5] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_5_8 : ¬ ConfluentU.DerivU [q5] q8 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_5_15 : ¬ ConfluentU.DerivU [q5] w15 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_5_16 : ¬ ConfluentU.DerivU [q5] w16 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_5_17 : ¬ ConfluentU.DerivU [q5] w17 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_5_18 : ¬ ConfluentU.DerivU [q5] w18 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_6_0 : ¬ ConfluentU.DerivU [q6] q0 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_6_2 : ¬ ConfluentU.DerivU [q6] q2 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_6_3 : ¬ ConfluentU.DerivU [q6] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_6_4 : ¬ ConfluentU.DerivU [q6] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_6_5 : ¬ ConfluentU.DerivU [q6] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_6_10 : ¬ ConfluentU.DerivU [q6] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_6_15 : ¬ ConfluentU.DerivU [q6] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_6_16 : ¬ ConfluentU.DerivU [q6] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_6_17 : ¬ ConfluentU.DerivU [q6] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_6_18 : ¬ ConfluentU.DerivU [q6] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_7_0 : ¬ ConfluentU.DerivU [q7] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_7_2 : ¬ ConfluentU.DerivU [q7] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_7_3 : ¬ ConfluentU.DerivU [q7] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_7_4 : ¬ ConfluentU.DerivU [q7] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_7_5 : ¬ ConfluentU.DerivU [q7] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_7_6 : ¬ ConfluentU.DerivU [q7] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_7_10 : ¬ ConfluentU.DerivU [q7] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_7_15 : ¬ ConfluentU.DerivU [q7] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_7_16 : ¬ ConfluentU.DerivU [q7] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_7_17 : ¬ ConfluentU.DerivU [q7] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_7_18 : ¬ ConfluentU.DerivU [q7] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_8_0 : ¬ ConfluentU.DerivU [q8] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_8_2 : ¬ ConfluentU.DerivU [q8] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_8_3 : ¬ ConfluentU.DerivU [q8] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_8_4 : ¬ ConfluentU.DerivU [q8] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_8_5 : ¬ ConfluentU.DerivU [q8] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_8_6 : ¬ ConfluentU.DerivU [q8] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_8_7 : ¬ ConfluentU.DerivU [q8] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_8_9 : ¬ ConfluentU.DerivU [q8] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_8_10 : ¬ ConfluentU.DerivU [q8] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_8_11 : ¬ ConfluentU.DerivU [q8] q11 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_8_12 : ¬ ConfluentU.DerivU [q8] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_8_14 : ¬ ConfluentU.DerivU [q8] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_8_15 : ¬ ConfluentU.DerivU [q8] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_8_16 : ¬ ConfluentU.DerivU [q8] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_8_17 : ¬ ConfluentU.DerivU [q8] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_8_18 : ¬ ConfluentU.DerivU [q8] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_9_0 : ¬ ConfluentU.DerivU [q9] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_9_2 : ¬ ConfluentU.DerivU [q9] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_9_3 : ¬ ConfluentU.DerivU [q9] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_9_4 : ¬ ConfluentU.DerivU [q9] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_9_5 : ¬ ConfluentU.DerivU [q9] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_9_6 : ¬ ConfluentU.DerivU [q9] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_9_7 : ¬ ConfluentU.DerivU [q9] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_9_8 : ¬ ConfluentU.DerivU [q9] q8 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_9_10 : ¬ ConfluentU.DerivU [q9] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_9_15 : ¬ ConfluentU.DerivU [q9] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_9_16 : ¬ ConfluentU.DerivU [q9] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_9_17 : ¬ ConfluentU.DerivU [q9] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_9_18 : ¬ ConfluentU.DerivU [q9] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_10_0 : ¬ ConfluentU.DerivU [q10] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_10_2 : ¬ ConfluentU.DerivU [q10] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_10_3 : ¬ ConfluentU.DerivU [q10] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_10_4 : ¬ ConfluentU.DerivU [q10] q4 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_5 : ¬ ConfluentU.DerivU [q10] q5 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_6 : ¬ ConfluentU.DerivU [q10] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_10_7 : ¬ ConfluentU.DerivU [q10] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_8 : ¬ ConfluentU.DerivU [q10] q8 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_9 : ¬ ConfluentU.DerivU [q10] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_12 : ¬ ConfluentU.DerivU [q10] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_13 : ¬ ConfluentU.DerivU [q10] q13 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (4, 3)], [(1, 2), (4, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_10_14 : ¬ ConfluentU.DerivU [q10] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_15 : ¬ ConfluentU.DerivU [q10] w15 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_16 : ¬ ConfluentU.DerivU [q10] w16 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_17 : ¬ ConfluentU.DerivU [q10] w17 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_10_18 : ¬ ConfluentU.DerivU [q10] w18 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_11_0 : ¬ ConfluentU.DerivU [q11] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_11_2 : ¬ ConfluentU.DerivU [q11] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_11_3 : ¬ ConfluentU.DerivU [q11] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_11_4 : ¬ ConfluentU.DerivU [q11] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_11_5 : ¬ ConfluentU.DerivU [q11] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_11_6 : ¬ ConfluentU.DerivU [q11] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_11_7 : ¬ ConfluentU.DerivU [q11] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_11_8 : ¬ ConfluentU.DerivU [q11] q8 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_11_9 : ¬ ConfluentU.DerivU [q11] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_11_10 : ¬ ConfluentU.DerivU [q11] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_11_12 : ¬ ConfluentU.DerivU [q11] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_11_13 : ¬ ConfluentU.DerivU [q11] q13 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (4, 3)], [(1, 2), (4, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_11_14 : ¬ ConfluentU.DerivU [q11] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_11_15 : ¬ ConfluentU.DerivU [q11] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_11_16 : ¬ ConfluentU.DerivU [q11] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_11_17 : ¬ ConfluentU.DerivU [q11] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_11_18 : ¬ ConfluentU.DerivU [q11] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_12_0 : ¬ ConfluentU.DerivU [q12] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_12_2 : ¬ ConfluentU.DerivU [q12] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_12_3 : ¬ ConfluentU.DerivU [q12] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_12_4 : ¬ ConfluentU.DerivU [q12] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_12_5 : ¬ ConfluentU.DerivU [q12] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_12_6 : ¬ ConfluentU.DerivU [q12] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_12_7 : ¬ ConfluentU.DerivU [q12] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_12_8 : ¬ ConfluentU.DerivU [q12] q8 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_12_10 : ¬ ConfluentU.DerivU [q12] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_12_15 : ¬ ConfluentU.DerivU [q12] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_12_16 : ¬ ConfluentU.DerivU [q12] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_12_17 : ¬ ConfluentU.DerivU [q12] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_12_18 : ¬ ConfluentU.DerivU [q12] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_13_0 : ¬ ConfluentU.DerivU [q13] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_13_2 : ¬ ConfluentU.DerivU [q13] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_13_3 : ¬ ConfluentU.DerivU [q13] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_13_4 : ¬ ConfluentU.DerivU [q13] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_13_5 : ¬ ConfluentU.DerivU [q13] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_13_6 : ¬ ConfluentU.DerivU [q13] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_13_7 : ¬ ConfluentU.DerivU [q13] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_13_8 : ¬ ConfluentU.DerivU [q13] q8 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_13_9 : ¬ ConfluentU.DerivU [q13] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_13_10 : ¬ ConfluentU.DerivU [q13] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_13_11 : ¬ ConfluentU.DerivU [q13] q11 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_13_12 : ¬ ConfluentU.DerivU [q13] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_13_14 : ¬ ConfluentU.DerivU [q13] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_13_15 : ¬ ConfluentU.DerivU [q13] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_13_16 : ¬ ConfluentU.DerivU [q13] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_13_17 : ¬ ConfluentU.DerivU [q13] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_13_18 : ¬ ConfluentU.DerivU [q13] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_14_0 : ¬ ConfluentU.DerivU [q14] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_14_2 : ¬ ConfluentU.DerivU [q14] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_14_3 : ¬ ConfluentU.DerivU [q14] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_14_4 : ¬ ConfluentU.DerivU [q14] q4 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_14_5 : ¬ ConfluentU.DerivU [q14] q5 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_14_6 : ¬ ConfluentU.DerivU [q14] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_14_7 : ¬ ConfluentU.DerivU [q14] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_14_8 : ¬ ConfluentU.DerivU [q14] q8 :=
  not_derivU_of_checkConf (M := ⟨4, [(1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], [(2, 0), (3, 1)], [0], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_14_9 : ¬ ConfluentU.DerivU [q14] q9 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_14_10 : ¬ ConfluentU.DerivU [q14] q10 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_14_11 : ¬ ConfluentU.DerivU [q14] q11 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_14_12 : ¬ ConfluentU.DerivU [q14] q12 :=
  not_derivU_of_checkConf (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_14_15 : ¬ ConfluentU.DerivU [q14] w15 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_14_16 : ¬ ConfluentU.DerivU [q14] w16 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_14_17 : ¬ ConfluentU.DerivU [q14] w17 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_14_18 : ¬ ConfluentU.DerivU [q14] w18 :=
  not_derivU_of_checkConf (M := ⟨3, [(1, 0), (2, 0), (2, 1)], [(1, 0)], [0], []⟩) (w := 2) (by decide) (by decide)

theorem rnc_ref_15_0 : ¬ ConfluentU.DerivU [w15] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_15_2 : ¬ ConfluentU.DerivU [w15] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_15_3 : ¬ ConfluentU.DerivU [w15] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_15_4 : ¬ ConfluentU.DerivU [w15] q4 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_15_5 : ¬ ConfluentU.DerivU [w15] q5 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_15_6 : ¬ ConfluentU.DerivU [w15] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_15_7 : ¬ ConfluentU.DerivU [w15] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_15_9 : ¬ ConfluentU.DerivU [w15] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_15_12 : ¬ ConfluentU.DerivU [w15] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_15_14 : ¬ ConfluentU.DerivU [w15] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_16_0 : ¬ ConfluentU.DerivU [w16] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_16_2 : ¬ ConfluentU.DerivU [w16] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_16_3 : ¬ ConfluentU.DerivU [w16] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_16_4 : ¬ ConfluentU.DerivU [w16] q4 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_16_5 : ¬ ConfluentU.DerivU [w16] q5 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_16_6 : ¬ ConfluentU.DerivU [w16] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_16_7 : ¬ ConfluentU.DerivU [w16] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_16_9 : ¬ ConfluentU.DerivU [w16] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_16_12 : ¬ ConfluentU.DerivU [w16] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_16_14 : ¬ ConfluentU.DerivU [w16] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_17_0 : ¬ ConfluentU.DerivU [w17] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_17_2 : ¬ ConfluentU.DerivU [w17] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_17_3 : ¬ ConfluentU.DerivU [w17] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_17_4 : ¬ ConfluentU.DerivU [w17] q4 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_17_5 : ¬ ConfluentU.DerivU [w17] q5 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_17_6 : ¬ ConfluentU.DerivU [w17] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_17_7 : ¬ ConfluentU.DerivU [w17] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_17_9 : ¬ ConfluentU.DerivU [w17] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_17_12 : ¬ ConfluentU.DerivU [w17] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_17_14 : ¬ ConfluentU.DerivU [w17] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_18_0 : ¬ ConfluentU.DerivU [w18] q0 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_18_2 : ¬ ConfluentU.DerivU [w18] q2 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_18_3 : ¬ ConfluentU.DerivU [w18] q3 :=
  not_derivU_of_checkConf (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide) (by decide)

theorem rnc_ref_18_4 : ¬ ConfluentU.DerivU [w18] q4 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_18_5 : ¬ ConfluentU.DerivU [w18] q5 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_18_6 : ¬ ConfluentU.DerivU [w18] q6 :=
  not_derivU_of_checkConf (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) (by decide)

theorem rnc_ref_18_7 : ¬ ConfluentU.DerivU [w18] q7 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_18_9 : ¬ ConfluentU.DerivU [w18] q9 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_18_12 : ¬ ConfluentU.DerivU [w18] q12 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

theorem rnc_ref_18_14 : ¬ ConfluentU.DerivU [w18] q14 :=
  not_derivU_of_checkConf (M := ⟨4, [(2, 1), (3, 0), (3, 1), (3, 2)], [(2, 1)], [1], []⟩) (w := 3) (by decide) (by decide)

end RNC
end PLLND