import wip.rnDict

/-!
# Machine-checked closure failure of the 15-class dictionary

GENERATED FILE (`rnDictGen refute ...`) — do not edit by hand.

For each witness cell below, the theorem eliminates EVERY candidate
class: one direction of the would-be collapse is refuted by a pinned
finite countermodel, checked by the kernel via `FinCM.checkB` +
`FinCM.not_provable_of_check` (`by decide` on closed data).  Hence the
variable-free fragment does NOT collapse onto the 15 representatives:
the RN(◯,{}) dictionary of the v2quant probe (size-capped) is not
connective-closed, and `RNDict` is NOT instantiable with these 15
representatives and ANY tables at the witnessed connectives.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND

/-- `q8.and q10` matches NO dictionary class: every candidate is
countermodel-eliminated. -/
theorem refute_cAnd_8_10 : ∀ k : Fin 15, ¬ Interd (q8.and q10) (rep15 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q8]) (by decide) h.2
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q10]) (by decide) h.2
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q11]) (by decide) h.2
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨_+15, hh⟩ => absurd hh (by omega)

/-- `q9.ifThen q4` matches NO dictionary class: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_9_4 : ∀ k : Fin 15, ¬ Interd (q9.ifThen q4) (rep15 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q8]) (by decide) h.2
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q10]) (by decide) h.2
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q11]) (by decide) h.2
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨_+15, hh⟩ => absurd hh (by omega)

/-- `q12.ifThen q4` matches NO dictionary class: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_12_4 : ∀ k : Fin 15, ¬ Interd (q12.ifThen q4) (rep15 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q8]) (by decide) h.2
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q10]) (by decide) h.2
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q11]) (by decide) h.2
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨_+15, hh⟩ => absurd hh (by omega)

/-- `q14.ifThen q4` matches NO dictionary class: every candidate is
countermodel-eliminated. -/
theorem refute_cImp_14_4 : ∀ k : Fin 15, ¬ Interd (q14.ifThen q4) (rep15 k) :=
  fun k => match k with
  | ⟨0, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q0) (by decide) h.1
  | ⟨1, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q1]) (by decide) h.2
  | ⟨2, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q2) (by decide) h.1
  | ⟨3, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (C := q3) (by decide) h.1
  | ⟨4, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q4) (by decide) h.1
  | ⟨5, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q5) (by decide) h.1
  | ⟨6, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (C := q6) (by decide) h.1
  | ⟨7, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q7) (by decide) h.1
  | ⟨8, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q8]) (by decide) h.2
  | ⟨9, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q9) (by decide) h.1
  | ⟨10, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (Γ := [q10]) (by decide) h.2
  | ⟨11, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q11]) (by decide) h.2
  | ⟨12, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q12) (by decide) h.1
  | ⟨13, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (Γ := [q13]) (by decide) h.2
  | ⟨14, _⟩ => fun h => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (C := q14) (by decide) h.1
  | ⟨_+15, hh⟩ => absurd hh (by omega)

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.RND.refute_cAnd_8_10' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cAnd_8_10

/--
info: 'PLLND.SemUI.RND.refute_cImp_9_4' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_9_4

/--
info: 'PLLND.SemUI.RND.refute_cImp_12_4' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_12_4

/--
info: 'PLLND.SemUI.RND.refute_cImp_14_4' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refute_cImp_14_4

end RND
end SemUI
end PLLND
