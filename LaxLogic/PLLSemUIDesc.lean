import LaxLogic.PLLSemUIBox

/-!
# The description graft — the second wave's frame layer

The general `BoxRowAmalg` residues call for implanting CANONICAL
material above a world of an arbitrary model as a p-variant.  The
construction here is the general form: given any target model K (the
finite canonical model `canonFin cl` is the intended instance — its
worlds are the closure triples, and the truth lemma turns forcing
questions into membership) and a **description-realisation pack**
`DescPack C K p dom` — a relation `R` from C-worlds to K-worlds with
bisimulation-style clauses, two fallibility covers, and atom-agreement
only on the tracked alphabet `dom` — fibre K over C along R:

* fibres = R-related pairs (c, k), climbing both coordinates, with
  K-edges relaxed into fallible K-worlds (`∨ ∈ K.F`) so that paths
  through the fallible base re-enter the fibres legally;
* fibres exit to the base only at fallible worlds (which force
  everything, so constrain nothing);
* all atoms read from the BASE coordinate — this dissolves the
  filtration problem (canonFin forces every out-of-closure atom, so no
  direct `PBisim C (canonFin cl)` can exist; on the graft the
  protected atoms are c's, and agreement with the triple is required
  only on `dom` = the closure, exactly where the forcing lemma needs
  it);
* `p` is redecorated from the K-coordinate (`descSet`).

The full machine is here, sorry-free: the pack, the graft model with
all legality proofs, the decoration, `descGraft_pbisim`
(base-identity ∪ projection — no atom or fallibility clause consumed,
both read the base coordinate), the forcing lemma
`descGraft_force_iff` (a fibre forces θ iff its K-coordinate does,
for θ whose atoms other than p are tracked — ◯ INCLUDED: constraint
witnesses transfer through the pack's m-clauses, fallible escapes
absorb on both sides), and the residue discharges
`boxRowAmalg{All,Ex}_of_desc`.  The second wave is thereby reduced to
the finite combinatorics of triples: per (C, x), exhibit a pack into
`canonFin cl` and a closure triple with `◯φ ∈ fal` (∀-side) resp.
`◯φ ∈ val` (∃-side) realised over x — membership statements,
decidable per closure, with the truth lemma converting them to the
forcing facts the discharges consume.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-- **Description-realisation pack**: a relation from C-worlds to
K-worlds with bisimulation-style clauses.  `atoms` is demanded only on
the tracked alphabet `dom` (for `canonFin cl`: the closure's atoms);
`iforth`/`mforth` may escape at fallible base-worlds, `mforth` pairing
them with fallible K-witnesses (the promise-side fallibility cover);
`kback`/`mback` pull K-moves back to C-moves. -/
structure DescPack (C K : ConstraintModel) (p : String)
    (dom : String → Prop) where
  R : C.W → K.W → Prop
  atoms : ∀ {c k}, R c k → ∀ q, q ≠ p → dom q →
    (c ∈ C.V q ↔ k ∈ K.V q)
  fall : ∀ {c k}, R c k → (c ∈ C.F ↔ k ∈ K.F)
  iforth : ∀ {c k}, R c k → ∀ {v}, C.Ri c v →
    (∃ k', K.Ri k k' ∧ R v k') ∨ v ∈ C.F
  kback : ∀ {c k}, R c k → ∀ {k'}, K.Ri k k' →
    ∃ v, C.Ri c v ∧ R v k'
  mforth : ∀ {c k}, R c k → ∀ {u}, C.Rm c u →
    ∃ s, K.Rm k s ∧ (R u s ∨ (u ∈ C.F ∧ s ∈ K.F))
  mback : ∀ {c k}, R c k → ∀ {s}, K.Rm k s →
    ∃ u, C.Rm c u ∧ (R u s ∨ u ∈ C.F)

variable {C K : ConstraintModel} {p : String} {dom : String → Prop}

/-- The graft frame: base ⊎ R-related fibres.  Fibres climb both
coordinates, with the K-side edge relaxed into fallible K-worlds;
fibres re-enter the base only at fallible worlds; all valuations and
fallibility from the base coordinate. -/
def descGraftBase (P : DescPack C K p dom) : ConstraintModel where
  W := C.W ⊕ {q : C.W × K.W // P.R q.1 q.2}
  Ri := fun a b =>
    match a, b with
    | .inl y, .inl y' => C.Ri y y'
    | .inl y, .inr q => C.Ri y q.1.1
    | .inr q, .inl y => C.Ri q.1.1 y ∧ y ∈ C.F
    | .inr q, .inr q' => C.Ri q.1.1 q'.1.1 ∧
        (K.Ri q.1.2 q'.1.2 ∨ q'.1.2 ∈ K.F)
  Rm := fun a b =>
    match a, b with
    | .inl y, .inl y' => C.Rm y y'
    | .inl _, .inr _ => False
    | .inr q, .inl y => C.Rm q.1.1 y ∧ y ∈ C.F
    | .inr q, .inr q' => C.Rm q.1.1 q'.1.1 ∧ K.Rm q.1.2 q'.1.2
  F := fun a => match a with
    | .inl y => y ∈ C.F
    | .inr q => q.1.1 ∈ C.F
  V := fun a b => match b with
    | .inl y => y ∈ C.V a
    | .inr q => q.1.1 ∈ C.V a
  refl_i := by
    intro a
    rcases a with y | q
    · exact C.refl_i y
    · exact ⟨C.refl_i q.1.1, Or.inl (K.refl_i q.1.2)⟩
  trans_i := by
    intro a b c h₁ h₂
    rcases a with y | q <;> rcases b with y' | q' <;> rcases c with y'' | q''
    · exact C.trans_i h₁ h₂
    · exact C.trans_i h₁ h₂
    · exact C.trans_i h₁ h₂.1
    · exact C.trans_i h₁ h₂.1
    · exact ⟨C.trans_i h₁.1 h₂, C.hered_F h₂ h₁.2⟩
    · refine ⟨C.trans_i h₁.1 h₂, Or.inr ?_⟩
      exact (P.fall q''.2).mp (C.hered_F h₂ h₁.2)
    · exact ⟨C.trans_i h₁.1 h₂.1, h₂.2⟩
    · refine ⟨C.trans_i h₁.1 h₂.1, ?_⟩
      rcases h₁.2 with hk | hF
      · rcases h₂.2 with hk' | hF'
        · exact Or.inl (K.trans_i hk hk')
        · exact Or.inr hF'
      · rcases h₂.2 with hk' | hF'
        · exact Or.inr (K.hered_F hk' hF)
        · exact Or.inr hF'
  refl_m := by
    intro a
    rcases a with y | q
    · exact C.refl_m y
    · exact ⟨C.refl_m q.1.1, K.refl_m q.1.2⟩
  trans_m := by
    intro a b c h₁ h₂
    rcases a with y | q <;> rcases b with y' | q' <;> rcases c with y'' | q''
    · exact C.trans_m h₁ h₂
    · exact h₂.elim
    · exact h₁.elim
    · exact h₁.elim
    · exact ⟨C.trans_m h₁.1 h₂, C.hered_F (C.sub_mi h₂) h₁.2⟩
    · exact h₂.elim
    · exact ⟨C.trans_m h₁.1 h₂.1, h₂.2⟩
    · exact ⟨C.trans_m h₁.1 h₂.1, K.trans_m h₁.2 h₂.2⟩
  sub_mi := by
    intro a b h
    rcases a with y | q <;> rcases b with y' | q'
    · exact C.sub_mi h
    · exact h.elim
    · exact ⟨C.sub_mi h.1, h.2⟩
    · exact ⟨C.sub_mi h.1, Or.inl (K.sub_mi h.2)⟩
  hered_F := by
    intro a b h hF
    rcases a with y | q <;> rcases b with y' | q'
    · exact C.hered_F h hF
    · exact C.hered_F h hF
    · exact h.2
    · exact C.hered_F h.1 hF
  hered_V := by
    intro a x y h hV
    rcases x with y' | q <;> rcases y with y'' | q'
    · exact C.hered_V h hV
    · exact C.hered_V h hV
    · exact C.hered_V h.1 hV
    · exact C.hered_V h.1 hV
  full_F := by
    intro a x hF
    rcases x with y | q
    · exact C.full_F hF
    · exact C.full_F hF

/-- The graft decoration: `p` from the K-coordinate on the fibres, the
fallible worlds on the base. -/
def descSet (P : DescPack C K p dom) : Set (descGraftBase P).W :=
  fun b => match b with
    | .inl y => y ∈ C.F
    | .inr q => q.1.2 ∈ K.V p

theorem descSet_hered (P : DescPack C K p dom) :
    ∀ {a b}, (descGraftBase P).Ri a b → a ∈ descSet P → b ∈ descSet P := by
  intro a b h hS
  rcases a with y | q <;> rcases b with y' | q'
  · exact C.hered_F h hS
  · exact K.full_F ((P.fall q'.2).mp (C.hered_F h hS))
  · exact h.2
  · rcases h.2 with hk | hF
    · exact K.hered_V hk hS
    · exact K.full_F hF

theorem descSet_full (P : DescPack C K p dom) :
    ∀ {a}, a ∈ (descGraftBase P).F → a ∈ descSet P := by
  intro a hF
  rcases a with y | q
  · exact hF
  · exact K.full_F ((P.fall q.2).mp hF)

/-- The description graft: the frame with `p` redecorated from the
K-coordinate. -/
def descGraft (P : DescPack C K p dom) : ConstraintModel :=
  redecorate (descGraftBase P) p (descSet P)
    (descSet_hered P) (descSet_full P)

/-- **The graft is a p-variant of the base**: base-identity ∪
projection to the base coordinate.  No atom or fallibility condition
is consumed — both read the base coordinate by design. -/
def descGraft_pbisim (P : DescPack C K p dom) :
    PBisim p C (descGraft P) where
  Z := fun c b => match b with
    | .inl y => y = c
    | .inr q => q.1.1 = c
  atoms := by
    intro c b hZ q hq
    rcases b with y | ⟨⟨c', k⟩, hR⟩
    · obtain rfl : y = c := hZ
      show y ∈ C.V q ↔ _ ∈ (if q = p then descSet P else (descGraftBase P).V q)
      rw [if_neg hq]
      exact Iff.rfl
    · obtain rfl : c' = c := hZ
      show c' ∈ C.V q ↔ _ ∈ (if q = p then descSet P else (descGraftBase P).V q)
      rw [if_neg hq]
      exact Iff.rfl
  fall := by
    intro c b hZ
    rcases b with y | ⟨⟨c', k⟩, hR⟩
    · obtain rfl : y = c := hZ
      exact Iff.rfl
    · obtain rfl : c' = c := hZ
      exact Iff.rfl
  iforth := by
    intro c b hZ v hv
    rcases b with y | ⟨⟨c', k⟩, hR⟩
    · obtain rfl : y = c := hZ
      exact ⟨.inl v, hv, rfl⟩
    · obtain rfl : c' = c := hZ
      rcases P.iforth hR hv with ⟨k', hkk', hR'⟩ | hvF
      · exact ⟨.inr ⟨(v, k'), hR'⟩, ⟨hv, Or.inl hkk'⟩, rfl⟩
      · exact ⟨.inl v, ⟨hv, hvF⟩, rfl⟩
  iback := by
    intro c b hZ b' hb'
    rcases b with y | ⟨⟨c', k⟩, hR⟩
    · obtain rfl : y = c := hZ
      rcases b' with y' | ⟨⟨c'', k'⟩, hR'⟩
      · exact ⟨y', hb', rfl⟩
      · exact ⟨c'', hb', rfl⟩
    · obtain rfl : c' = c := hZ
      rcases b' with y' | ⟨⟨c'', k'⟩, hR'⟩
      · exact ⟨y', hb'.1, rfl⟩
      · exact ⟨c'', hb'.1, rfl⟩
  mforth := by
    intro c b hZ u hu
    rcases b with y | ⟨⟨c', k⟩, hR⟩
    · obtain rfl : y = c := hZ
      exact ⟨.inl u, hu, rfl⟩
    · obtain rfl : c' = c := hZ
      rcases P.mforth hR hu with ⟨s, hks, hR' | ⟨huF, hsF⟩⟩
      · exact ⟨.inr ⟨(u, s), hR'⟩, ⟨hu, hks⟩, rfl⟩
      · exact ⟨.inl u, ⟨hu, huF⟩, rfl⟩
  mback := by
    intro c b hZ b' hb'
    rcases b with y | ⟨⟨c', k⟩, hR⟩
    · obtain rfl : y = c := hZ
      rcases b' with y' | ⟨⟨c'', k'⟩, hR'⟩
      · exact ⟨y', hb', rfl⟩
      · exact hb'.elim
    · obtain rfl : c' = c := hZ
      rcases b' with y' | ⟨⟨c'', k'⟩, hR'⟩
      · exact ⟨y', hb'.1, rfl⟩
      · exact ⟨c'', hb'.1, rfl⟩

/-- **A fibre forces exactly what its K-coordinate forces** — for
formulas whose atoms other than p are tracked by `dom`, and with ◯
INCLUDED: constraint witnesses transfer through the pack's m-clauses,
fallible escapes are absorbed on both sides (a fallible base witness
pairs with a fallible K-witness by `mforth`; an unpaired fallible
K-future is itself fallible in the graft by `fall`). -/
theorem descGraft_force_iff (P : DescPack C K p dom) :
    ∀ {θ : PLLFormula}, (∀ q ∈ θ.atoms, q ≠ p → dom q) →
    ∀ (c : C.W) (k : K.W) (hR : P.R c k),
    ((descGraft P).force (.inr ⟨(c, k), hR⟩) θ ↔ K.force k θ) := by
  intro θ
  induction θ with
  | prop a =>
      intro hat c k hR
      by_cases ha : a = p
      · show _ ∈ (if a = p then descSet P else (descGraftBase P).V a) ↔ _
        rw [if_pos ha, ha]
        exact Iff.rfl
      · show _ ∈ (if a = p then descSet P else (descGraftBase P).V a) ↔ _
        rw [if_neg ha]
        exact P.atoms hR a ha (hat a (by simp) ha)
  | falsePLL =>
      intro _ c k hR
      exact P.fall hR
  | and φ ψ ihφ ihψ =>
      intro hat c k hR
      have hat1 : ∀ q ∈ φ.atoms, q ≠ p → dom q :=
        fun q hq => hat q (by simp [hq])
      have hat2 : ∀ q ∈ ψ.atoms, q ≠ p → dom q :=
        fun q hq => hat q (by simp [hq])
      simp only [ConstraintModel.force]
      exact and_congr (ihφ hat1 c k hR) (ihψ hat2 c k hR)
  | or φ ψ ihφ ihψ =>
      intro hat c k hR
      have hat1 : ∀ q ∈ φ.atoms, q ≠ p → dom q :=
        fun q hq => hat q (by simp [hq])
      have hat2 : ∀ q ∈ ψ.atoms, q ≠ p → dom q :=
        fun q hq => hat q (by simp [hq])
      simp only [ConstraintModel.force]
      exact or_congr (ihφ hat1 c k hR) (ihψ hat2 c k hR)
  | ifThen φ ψ ihφ ihψ =>
      intro hat c k hR
      have hat1 : ∀ q ∈ φ.atoms, q ≠ p → dom q :=
        fun q hq => hat q (by simp [hq])
      have hat2 : ∀ q ∈ ψ.atoms, q ≠ p → dom q :=
        fun q hq => hat q (by simp [hq])
      simp only [ConstraintModel.force]
      constructor
      · intro hf k' hkk' hφ
        obtain ⟨v, hcv, hR'⟩ := P.kback hR hkk'
        exact (ihψ hat2 v k' hR').mp
          (hf (.inr ⟨(v, k'), hR'⟩) ⟨hcv, Or.inl hkk'⟩
            ((ihφ hat1 v k' hR').mpr hφ))
      · intro hf b hb hφ
        rcases b with y | ⟨⟨c', k'⟩, hR'⟩
        · exact (descGraft P).force_of_fallible hb.2
        · rcases hb.2 with hkk' | hk'F
          · exact (ihψ hat2 c' k' hR').mpr
              (hf k' hkk' ((ihφ hat1 c' k' hR').mp hφ))
          · exact (descGraft P).force_of_fallible
              ((P.fall hR').mpr hk'F)
  | somehow φ ih =>
      intro hat c k hR
      simp only [ConstraintModel.force]
      constructor
      · intro hf k' hkk'
        obtain ⟨v, hcv, hR'⟩ := P.kback hR hkk'
        obtain ⟨d, hd, hφ⟩ := hf (.inr ⟨(v, k'), hR'⟩) ⟨hcv, Or.inl hkk'⟩
        rcases d with u | ⟨⟨u, s⟩, hR''⟩
        · -- fallible base witness: pair it with a fallible K-witness
          rcases P.mforth hR' hd.1 with ⟨s, hks, hR'' | ⟨-, hsF⟩⟩
          · exact ⟨s, hks, K.force_of_fallible ((P.fall hR'').mp hd.2)⟩
          · exact ⟨s, hks, K.force_of_fallible hsF⟩
        · exact ⟨s, hd.2, (ih hat u s hR'').mp hφ⟩
      · intro hf b hb
        rcases b with y | ⟨⟨c', k'⟩, hR'⟩
        · exact ⟨.inl y, C.refl_m y, (descGraft P).force_of_fallible hb.2⟩
        · rcases hb.2 with hkk' | hk'F
          · obtain ⟨s, hk's, hsφ⟩ := hf k' hkk'
            obtain ⟨u, hc'u, hR'' | huF⟩ := P.mback hR' hk's
            · exact ⟨.inr ⟨(u, s), hR''⟩, ⟨hc'u, hk's⟩,
                (ih hat u s hR'').mpr hsφ⟩
            · exact ⟨.inl u, ⟨hc'u, huF⟩,
                (descGraft P).force_of_fallible huF⟩
          · exact ⟨.inr ⟨(c', k'), hR'⟩, (descGraft P).refl_m _,
              (descGraft P).force_of_fallible ((P.fall hR').mpr hk'F)⟩

/-- **The ∀-residue reduces to description-realisation**: per (C, x)
with a ψ-refuting row, exhibit a target model and a pack pairing x
with a ◯φ-refuting K-world; the graft does the rest.  With
K := `canonFin cl` the condition is finite combinatorics: a closure
triple with `◯φ ∈ fal`, realised over x (truth lemma). -/
theorem boxRowAmalgAll_of_desc {p : String} {φ ψ : PLLFormula}
    {dom : String → Prop} (hat : ∀ q ∈ φ.atoms, q ≠ p → dom q)
    (h : ∀ (C : ConstraintModel) (x : C.W),
      (∀ y, C.Rm x y → ¬ C.force y ψ) →
      ∃ (K : ConstraintModel) (P : DescPack C K p dom) (k : K.W),
        P.R x k ∧ ¬ K.force k φ.somehow) :
    BoxRowAmalgAll p φ ψ := by
  intro C x hrow
  obtain ⟨K, P, k, hRk, hk⟩ := h C x hrow
  refine ⟨descGraft P, descGraft_pbisim P, .inr ⟨(x, k), hRk⟩, rfl, ?_⟩
  intro hbox
  exact hk ((descGraft_force_iff P (θ := φ.somehow) hat x k hRk).mp hbox)

/-- **The ∃-residue reduces to description-realisation** dually: a
pack pairing w with a ◯φ-forcing K-world (`◯φ ∈ val` canonically). -/
theorem boxRowAmalgEx_of_desc {p : String} {φ ψ : PLLFormula}
    {dom : String → Prop} (hat : ∀ q ∈ φ.atoms, q ≠ p → dom q)
    (h : ∀ (C : ConstraintModel) (w : C.W),
      (∀ x, C.Ri w x → ∃ y, C.Rm x y ∧ C.force y ψ) →
      ∃ (K : ConstraintModel) (P : DescPack C K p dom) (k : K.W),
        P.R w k ∧ K.force k φ.somehow) :
    BoxRowAmalgEx p φ ψ := by
  intro C w hw
  obtain ⟨K, P, k, hRk, hk⟩ := h C w hw
  exact ⟨descGraft P, descGraft_pbisim P, .inr ⟨(w, k), hRk⟩, rfl,
    (descGraft_force_iff P (θ := φ.somehow) hat w k hRk).mpr hk⟩

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.descGraft_force_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms descGraft_force_iff

/--
info: 'PLLND.SemUI.boxRowAmalgAll_of_desc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms boxRowAmalgAll_of_desc

end SemUI
end PLLND
