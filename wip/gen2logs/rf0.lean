import wip.rnDict2

/-!
# Machine-checked closure failure of the enlarged (16-class) round

GENERATED FILE (`rnDictGen refute2 ...`) — do not edit by hand.

For each witness cell below, the theorem eliminates EVERY candidate
class among the 16: one direction of the would-be collapse is refuted
by a pinned finite countermodel (staged batteries up to the exhaustive
rooted 5-world sweep), checked by the kernel via `FinCM.checkB` +
`FinCM.not_provable_of_check` (`by decide` on closed data).  Each
witness is therefore a NEW interderivability class beyond the 19.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND2

open RND

/-- `q8.and q11` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cAnd_8_11 : ∀ k : Fin 16, ¬ Interd (q8.and q11) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (Γ := [q8]) (by decide) h.2
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q11]) (by decide) h.2
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q15.somehow` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cBox_15 : ∀ k : Fin 16, ¬ Interd (q15.somehow) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (Γ := [q10]) (by decide) h.2
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q11]) (by decide) h.2
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q11.ifThen q13` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_11_13 : ∀ k : Fin 16, ¬ Interd (q11.ifThen q13) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q12.ifThen q9` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_12_9 : ∀ k : Fin 16, ¬ Interd (q12.ifThen q9) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q13.ifThen q9` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_13_9 : ∀ k : Fin 16, ¬ Interd (q13.ifThen q9) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q14.ifThen q7` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_14_7 : ∀ k : Fin 16, ¬ Interd (q14.ifThen q7) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (Γ := [q8]) (by decide) h.2
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(3, 4)], [4], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q15.ifThen q4` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_15_4 : ∀ k : Fin 16, ¬ Interd (q15.ifThen q4) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q8.ifThen q11` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_8_11 : ∀ k : Fin 16, ¬ Interd (q8.ifThen q11) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q8.ifThen q5` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_8_5 : ∀ k : Fin 16, ¬ Interd (q8.ifThen q5) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (Γ := [q10]) (by decide) h.2
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q11]) (by decide) h.2
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q10.or q13` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cOr_10_13 : ∀ k : Fin 16, ¬ Interd (q10.or q13) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q11.or q14` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cOr_11_14 : ∀ k : Fin 16, ¬ Interd (q11.or q14) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(3, 4)], [4], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q5.or q15` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cOr_5_15 : ∀ k : Fin 16, ¬ Interd (q5.or q15) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (Γ := [q10]) (by decide) h.2
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q11]) (by decide) h.2
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q8.or q10` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cOr_8_10 : ∀ k : Fin 16, ¬ Interd (q8.or q10) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (C := q13) (by decide) h.1
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-- `q8.or q9` matches NO class of the 19: every candidate is
countermodel-eliminated. -/
theorem refute_cOr_8_9 : ∀ k : Fin 16, ¬ Interd (q8.or q9) (rep2 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (C := q8) (by decide) h.1
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q10) (by decide) h.1
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q11) (by decide) h.1
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(0, 2), (1, 4), (3, 4)], [4], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨15, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (C := q15) (by decide) h.1
  | ⟨_+16, hh⟩ => absurd hh (by omega)

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.RND2.refute_cAnd_8_11' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cAnd_8_11

/--
info: 'PLLND.SemUI.RND2.refute_cBox_15' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cBox_15

/--
info: 'PLLND.SemUI.RND2.refute_cImp_11_13' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_11_13

/--
info: 'PLLND.SemUI.RND2.refute_cImp_12_9' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_12_9

/--
info: 'PLLND.SemUI.RND2.refute_cImp_13_9' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_13_9

/--
info: 'PLLND.SemUI.RND2.refute_cImp_14_7' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_14_7

/--
info: 'PLLND.SemUI.RND2.refute_cImp_15_4' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_15_4

/--
info: 'PLLND.SemUI.RND2.refute_cImp_8_11' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_8_11

/--
info: 'PLLND.SemUI.RND2.refute_cImp_8_5' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_8_5

/--
info: 'PLLND.SemUI.RND2.refute_cOr_10_13' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cOr_10_13

/--
info: 'PLLND.SemUI.RND2.refute_cOr_11_14' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cOr_11_14

/--
info: 'PLLND.SemUI.RND2.refute_cOr_5_15' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cOr_5_15

/--
info: 'PLLND.SemUI.RND2.refute_cOr_8_10' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cOr_8_10

/--
info: 'PLLND.SemUI.RND2.refute_cOr_8_9' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cOr_8_9

end RND2
end SemUI
end PLLND
