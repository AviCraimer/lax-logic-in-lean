import wip.rnc_probe

/-!
# Kernel-checked PCLL derivability certificates: the RNC(◯,{}) merges

Hand-written natural-deduction terms for the positive cells the
G4-backward searcher misses (its visited-set keys are context-order
sensitive, so weakening-shaped goals blow it up), composed into
`ConfluentU.DerivU` certificates.  Together with `wip/rncCert.lean`
(the 207 confluent-countermodel refutations) these settle the PCLL
quotient of the 19 candidates up to the two recorded open cells.

The two PCLL-proper ingredients are

* `P_12_9  : DerivU [q12] q9` — ONE application of distribution at
  `(q3, q6)`: `q12 = ◯(q3∨q6)` is the antecedent of
  `distF q3 q6` on the nose, and `[◯q3 ∨ ◯q6] ⊢ q9` is plain PLL;
* every direction INTO `w17 = q12⊃q4` (they route through `P_12_9`).

Everything else is plain PLL (`DerivU.of_nd`).
-/

open PLLFormula

namespace PLLND
namespace RNC

open ConfluentU

/-- Cut at the `DerivU` level: `[X] ⊢ᵤ M` and `[M] ⊢ Y` (PLL) give
`[X] ⊢ᵤ Y`. -/
theorem cutU {X M Y : PLLFormula} (h1 : DerivU [X] M) (p : LaxND [M] Y) :
    DerivU [X] Y :=
  DerivU.mp
    (DerivU.of_nd ((LaxND.impIntro p).rename fun ψ h => absurd h (by simp)))
    h1

/-! ## Plain-PLL LaxND cores -/

/-- `[q9] ⊢ q14` : case split on `q9 = q5∨q6`; the `q6` branch turns
`q10 q6 = ◯⊥` into `◯q3` by ex falso under `◯`. -/
def nd_9_14 : LaxND [q9] q14 :=
  .impIntro <|
    .orElim (.iden (show q9 ∈ [q10, q9] by decide))
      (.iden (show q5 ∈ q5 :: [q10, q9] by decide))
      (.laxElim
        (.impElim (.iden (show q10 ∈ q6 :: [q10, q9] by decide))
          (.iden (show q6 ∈ q6 :: [q10, q9] by decide)))
        (.laxIntro (.falsoElim q3
          (.iden (show falsePLL ∈ q0 :: q6 :: [q10, q9] by decide)))))

/-- `[q9] ⊢ q11` : `q5 ⊢ q10` (bind `¬B` against `q6`), `q6 ⊢ q6`. -/
def nd_9_11 : LaxND [q9] q11 :=
  .orElim (.iden (show q9 ∈ [q9] by decide))
    (.orIntro2 (.impIntro
      (.laxElim (.iden (show q5 ∈ q6 :: q5 :: [q9] by decide))
        (.laxIntro (.impElim
          (.iden (show q6 ∈ q3 :: q6 :: q5 :: [q9] by decide))
          (.iden (show q3 ∈ q3 :: q6 :: q5 :: [q9] by decide)))))))
    (.orIntro1 (.iden (show q6 ∈ q6 :: [q9] by decide)))

/-- `[w15] ⊢ w16` : case split on `q9`; each disjunct fires a conjunct
of `w15`. -/
def nd_15_16 : LaxND [w15] w16 :=
  .impIntro <|
    .orElim (.iden (show q9 ∈ [q9, w15] by decide))
      (.impElim (.andElim1 (.iden (show w15 ∈ q5 :: [q9, w15] by decide)))
        (.iden (show q5 ∈ q5 :: [q9, w15] by decide)))
      (.orIntro1 (.impElim
        (.andElim2 (.iden (show w15 ∈ q6 :: [q9, w15] by decide)))
        (.iden (show q6 ∈ q6 :: [q9, w15] by decide))))

/-- `[w16] ⊢ q8` : `q5 ⊢ q9` by left injection, then fire `w16`. -/
def nd_16_8 : LaxND [w16] q8 :=
  .impIntro <|
    .impElim (.iden (show w16 ∈ q5 :: [w16] by decide))
      (.orIntro1 (.iden (show q5 ∈ q5 :: [w16] by decide)))

/-- `[w16] ⊢ w15` : the `q8` conjunct as above; the `q10` conjunct
case-splits the `q4` that `w16` returns on `q6 ⊢ q9`. -/
def nd_16_15 : LaxND [w16] w15 :=
  .andIntro
    (.impIntro <|
      .impElim (.iden (show w16 ∈ q5 :: [w16] by decide))
        (.orIntro1 (.iden (show q5 ∈ q5 :: [w16] by decide))))
    (.impIntro <|
      .orElim
        (.impElim (.iden (show w16 ∈ q6 :: [w16] by decide))
          (.orIntro2 (.iden (show q6 ∈ q6 :: [w16] by decide))))
        (.iden (show q2 ∈ q2 :: q6 :: [w16] by decide))
        (.falsoElim q2 (.impElim
          (.iden (show q6 ∈ q3 :: q6 :: [w16] by decide))
          (.iden (show q3 ∈ q3 :: q6 :: [w16] by decide)))))

/-- `[w15] ⊢ w18` : `q14 q10 = q5`, then `q8 q5 = q4`. -/
def nd_15_18 : LaxND [w15] w18 :=
  .impIntro <|
    .impElim (.andElim1 (.iden (show w15 ∈ q14 :: [w15] by decide)))
      (.impElim (.iden (show q14 ∈ q14 :: [w15] by decide))
        (.andElim2 (.iden (show w15 ∈ q14 :: [w15] by decide))))

/-- `[w18] ⊢ q8` : `q5 ⊢ q14` by weakening (`q14 = q10⊃q5`), then fire
`w18`. -/
def nd_18_8 : LaxND [w18] q8 :=
  .impIntro <|
    .impElim (.iden (show w18 ∈ q5 :: [w18] by decide))
      (.impIntro (.iden (show q5 ∈ q10 :: q5 :: [w18] by decide)))

/-- `[w18] ⊢ q10` : under `q6`, `q10 q6 = ◯⊥` gives `q5` ex falso, so
`q14` holds and `w18` returns `q4`; both `q4` cases yield `q2`. -/
def nd_18_10 : LaxND [w18] q10 :=
  .impIntro <|
    .orElim
      (.impElim (.iden (show w18 ∈ q6 :: [w18] by decide))
        (.impIntro
          (.laxElim
            (.impElim (.iden (show q10 ∈ q10 :: q6 :: [w18] by decide))
              (.iden (show q6 ∈ q10 :: q6 :: [w18] by decide)))
            (.laxIntro (.falsoElim q3
              (.iden (show falsePLL ∈ q0 :: q10 :: q6 :: [w18] by decide)))))))
      (.iden (show q2 ∈ q2 :: q6 :: [w18] by decide))
      (.falsoElim q2 (.impElim
        (.iden (show q6 ∈ q3 :: q6 :: [w18] by decide))
        (.iden (show q3 ∈ q3 :: q6 :: [w18] by decide))))

/-- `[w18] ⊢ w16` : `q9 ⊢ q14` (as in `nd_9_14`), then fire `w18`. -/
def nd_18_16 : LaxND [w18] w16 :=
  .impIntro <|
    .impElim (.iden (show w18 ∈ q9 :: [w18] by decide))
      (.impIntro
        (.orElim (.iden (show q9 ∈ q10 :: q9 :: [w18] by decide))
          (.iden (show q5 ∈ q5 :: q10 :: q9 :: [w18] by decide))
          (.laxElim
            (.impElim (.iden (show q10 ∈ q6 :: q10 :: q9 :: [w18] by decide))
              (.iden (show q6 ∈ q6 :: q10 :: q9 :: [w18] by decide)))
            (.laxIntro (.falsoElim q3
              (.iden (show falsePLL ∈ q0 :: q6 :: q10 :: q9 :: [w18] by decide)))))))

/-- `[w17] ⊢ w16` : `q9 ⊢ q12` (both disjuncts inject into `◯q7`),
then fire `w17`. -/
def nd_17_16 : LaxND [w17] w16 :=
  .impIntro <|
    .impElim (.iden (show w17 ∈ q9 :: [w17] by decide))
      (.orElim (.iden (show q9 ∈ q9 :: [w17] by decide))
        (.laxElim (.iden (show q5 ∈ q5 :: q9 :: [w17] by decide))
          (.laxIntro (.orIntro1
            (.iden (show q3 ∈ q3 :: q5 :: q9 :: [w17] by decide)))))
        (.laxIntro (.orIntro2
          (.iden (show q6 ∈ q6 :: q9 :: [w17] by decide)))))

/-- `[◯q3 ∨ ◯q6, q12] ⊢ q9` — the PLL leg of the distribution cut:
left disjunct is `q5` itself; right disjunct lowers `◯q6` to `q6`
(bind `q6` against `q3`, discharge through `q3 = ◯⊥⊃⊥`). -/
def nd_dist_12_9 : LaxND [q5.or (.somehow q6), q12] q9 :=
  .orElim (.iden (show q5.or (.somehow q6) ∈ [q5.or (.somehow q6), q12] by decide))
    (.orIntro1 (.iden (show q5 ∈ q5 :: [q5.or (.somehow q6), q12] by decide)))
    (.orIntro2 (.impIntro
      (.impElim
        (.iden (show q3 ∈ q3 :: PLLFormula.somehow q6 :: [q5.or (.somehow q6), q12] by decide))
        (.laxElim
          (.iden (show PLLFormula.somehow q6 ∈ q3 :: PLLFormula.somehow q6 :: [q5.or (.somehow q6), q12] by decide))
          (.laxIntro (.impElim
            (.iden (show q6 ∈ q6 :: q3 :: PLLFormula.somehow q6 :: [q5.or (.somehow q6), q12] by decide))
            (.iden (show q3 ∈ q6 :: q3 :: PLLFormula.somehow q6 :: [q5.or (.somehow q6), q12] by decide))))))))

/-! ## The DerivU certificates -/

/-- **`[q12] ⊢ᵤ q9`** — the first PCLL-proper merge: one application
of distribution at `(q3, q6)` (note `q12 = ◯(q3∨q6)` is the instance's
antecedent on the nose). -/
theorem P_12_9 : DerivU [q12] q9 :=
  DerivU.mp (DerivU.of_nd (.impIntro nd_dist_12_9))
    (DerivU.mp (DerivU.dist q3 q6) (DerivU.hyp (by decide)))

/-- `[q12] ⊢ᵤ q11` (through `q9`). -/
theorem P_12_11 : DerivU [q12] q11 := cutU P_12_9 nd_9_11

/-- With `[q9] ⊢ q12` (PLL: `orT`), `q9 ≡ᵤ q12`: the classes of `q9`
and `q12` MERGE under distribution. -/
theorem P_9_12 : DerivU [q9] q12 :=
  DerivU.of_nd <|
    .orElim (.iden (show q9 ∈ [q9] by decide))
      (.laxElim (.iden (show q5 ∈ q5 :: [q9] by decide))
        (.laxIntro (.orIntro1 (.iden (show q3 ∈ q3 :: q5 :: [q9] by decide)))))
      (.laxIntro (.orIntro2 (.iden (show q6 ∈ q6 :: [q9] by decide))))

/-! ### The witness cluster `{w15, w16, w17, w18}` collapses to ONE
PCLL class.  Directions into `w17` need distribution (they route
through `P_12_9`); all others are plain PLL. -/

theorem P_15_16 : DerivU [w15] w16 := DerivU.of_nd nd_15_16
theorem P_16_15 : DerivU [w16] w15 := DerivU.of_nd nd_16_15
theorem P_15_18 : DerivU [w15] w18 := DerivU.of_nd nd_15_18
theorem P_17_16 : DerivU [w17] w16 := DerivU.of_nd nd_17_16
theorem P_18_16 : DerivU [w18] w16 := DerivU.of_nd nd_18_16
theorem P_18_15 : DerivU [w18] w15 :=
  DerivU.of_nd (.andIntro nd_18_8 nd_18_10)
theorem P_16_18 : DerivU [w16] w18 := cutU (DerivU.of_nd nd_16_15) nd_15_18
theorem P_17_15 : DerivU [w17] w15 := cutU (DerivU.of_nd nd_17_16) nd_16_15
theorem P_17_18 : DerivU [w17] w18 := cutU P_17_15 nd_15_18

/-- `[w16] ⊢ᵤ w17` : deduction + the distribution merge. -/
theorem P_16_17 : DerivU [w16] w17 :=
  DerivU.deduction <|
    DerivU.mp (DerivU.hyp (show w16 ∈ [q12, w16] by simp))
      (P_12_9.rename (by intro ψ h; simp at h; simp [h]))

theorem P_15_17 : DerivU [w15] w17 :=
  DerivU.deduction <|
    DerivU.mp
      ((DerivU.of_nd nd_15_16).rename
        (show ∀ ψ ∈ [w15], ψ ∈ [q12, w15] by intro ψ h; simp at h; simp [h]))
      (P_12_9.rename (by intro ψ h; simp at h; simp [h]))

theorem P_18_17 : DerivU [w18] w17 :=
  DerivU.deduction <|
    DerivU.mp
      ((DerivU.of_nd nd_18_16).rename
        (show ∀ ψ ∈ [w18], ψ ∈ [q12, w18] by intro ψ h; simp at h; simp [h]))
      (P_12_9.rename (by intro ψ h; simp at h; simp [h]))

/-! ### Remaining searcher-missed plain-PLL cells -/

theorem P_15_8 : DerivU [w15] q8 :=
  DerivU.of_nd (.andElim1 (.iden (show w15 ∈ [w15] by decide)))
theorem P_15_13 : DerivU [w15] q13 :=
  DerivU.of_nd (.laxIntro (.andElim1 (.iden (show w15 ∈ [w15] by decide))))
theorem P_16_8 : DerivU [w16] q8 := DerivU.of_nd nd_16_8
theorem P_16_13 : DerivU [w16] q13 := DerivU.of_nd (.laxIntro nd_16_8)
theorem P_18_8 : DerivU [w18] q8 := DerivU.of_nd nd_18_8
theorem P_18_13 : DerivU [w18] q13 := DerivU.of_nd (.laxIntro nd_18_8)
theorem P_18_10 : DerivU [w18] q10 := DerivU.of_nd nd_18_10
/-- `[w18] ⊢ᵤ q11` by composition: `w18 ⊢ᵤ w15`, and `w15`'s `q10`
conjunct right-injects into `q11 = q6∨q10`.  (Resolves the last
witness-row unknown; the sole surviving open cell is `[q14] ⊢ q13`.) -/
theorem P_18_11 : DerivU [w18] q11 :=
  cutU P_18_15
    (.orIntro2 (.andElim2 (.iden (show w15 ∈ [w15] by decide))))

/-! ## Axiom audit -/

/-- info: 'PLLND.RNC.P_12_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_12_9

/-- info: 'PLLND.RNC.P_18_17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_18_17

end RNC
end PLLND
