import LaxLogic.PLLSemUISplit

/-!
# The parametric point-adjunction: one construction, three surgeries

The three frame-changing p-variant surgeries — the doubling
(`emVariant`), the levelled model (`lobVariant`), the split
(`splitVariant`) — are unified here as instances of ONE parametric
construction:

    adjoin N n₀ U R : adjoin a single point ⋆ to N, anchored at n₀:
      • position: everything below n₀ sees ⋆; ⋆ sees exactly U
        (an up-closed subset of the strict data above n₀);
      • constraint row: ⋆ reaches itself and exactly R ⊆ U
        (closed under N.Rm);
      • fallibility and every valuation copied from n₀.

The compositional lemma `adjoin_pbisim` extends any p-bisimulation
`B : PBisim p C N` along an anchored pair `(z, n₀) ∈ B.Z` to the
adjoined model, given five COVER conditions routing z's relational
data through the accumulated Z.  The m-back cover is the **promise
mechanism** isolated: ⋆ may constraint-reach any world Z-equivalent
to a constraint successor of its anchor — this is the sideways
degree of freedom that split towers provably lack
(`splitTower_oneW_forces_lob`).

Because Z accumulates, adjunctions ITERATE: each new point may cite
previously adjoined points in its U and R.  Instances (all PROVED):

* **the doubling's core** — `adjoinAtP_not_em`: one point with strict
  parameters over a non-fallible trivial-cluster world refutes
  `p ∨ ¬p` there;
* **the split's core** — `adjoinAtP_not_frontier`: the same instance
  refutes the frontier row `((p⊃◯⊥)⊃p)⊃p` when the anchor's
  constraint row is fallibility-free;
* **the levelled model's core** — `lobTower_not_lob`: the two-storey
  tower (first ⋆₁ over z with empty row, then ⋆₂ between z and ⋆₁
  with row R = {⋆₁}) refutes `◯(◯p ⊃ p)` at a constraint-rigid
  anchor; `adjoin_reaches_lob` instantiates it over the one-world
  model — exactly where split towers provably force the row.

The global surgeries are the UNIFORMIZATIONS of these cores over
multiplicities the single point cannot carry: a fat Rᵢ-cluster needs
one point per cluster-mate (the split's cluster duplication — the
pointwise m-zigzag demands it), and the levelled model repeats the
two-storey core over every world and level.  The evidence reading:
the transform tower is not "constructions that keep changing" but ONE
construction with changing parameters (U, R, iteration depth) —
matching the ◯-depth grading observed on the ◯-free fragment.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-! ## Composition of bisimulations -/

/-- A-bisimulations compose (relational composition). -/
def ABisim.comp {A : String → Prop} {M N O : ConstraintModel}
    (B₁ : ABisim A M N) (B₂ : ABisim A N O) : ABisim A M O where
  Z := fun w w'' => ∃ w', B₁.Z w w' ∧ B₂.Z w' w''
  atoms := by
    rintro w w'' ⟨w', h1, h2⟩ a hA
    exact (B₁.atoms h1 a hA).trans (B₂.atoms h2 a hA)
  fall := by
    rintro w w'' ⟨w', h1, h2⟩
    exact (B₁.fall h1).trans (B₂.fall h2)
  iforth := by
    rintro w w'' ⟨w', h1, h2⟩ v hv
    obtain ⟨v', hv', hZ1⟩ := B₁.iforth h1 hv
    obtain ⟨v'', hv'', hZ2⟩ := B₂.iforth h2 hv'
    exact ⟨v'', hv'', v', hZ1, hZ2⟩
  iback := by
    rintro w w'' ⟨w', h1, h2⟩ v'' hv''
    obtain ⟨v', hv', hZ2⟩ := B₂.iback h2 hv''
    obtain ⟨v, hv, hZ1⟩ := B₁.iback h1 hv'
    exact ⟨v, hv, v', hZ1, hZ2⟩
  mforth := by
    rintro w w'' ⟨w', h1, h2⟩ u hu
    obtain ⟨u', hu', hZ1⟩ := B₁.mforth h1 hu
    obtain ⟨u'', hu'', hZ2⟩ := B₂.mforth h2 hu'
    exact ⟨u'', hu'', u', hZ1, hZ2⟩
  mback := by
    rintro w w'' ⟨w', h1, h2⟩ u'' hu''
    obtain ⟨u', hu', hZ2⟩ := B₂.mback h2 hu''
    obtain ⟨u, hu, hZ1⟩ := B₁.mback h1 hu'
    exact ⟨u, hu, u', hZ1, hZ2⟩

/-! ## The parametric point-adjunction -/

/-- Adjoin one point ⋆ to N, anchored at `n₀`: below-⋆ = below-n₀,
above-⋆ = the up-closed `U` over n₀, constraint row `{⋆} ∪ R` with
`R ⊆ U` closed under `N.Rm`; fallibility and valuations copied from
n₀. -/
def adjoin (N : ConstraintModel) (n₀ : N.W) (U R : Set N.W)
    (uUp : ∀ {y y'}, y ∈ U → N.Ri y y' → y' ∈ U)
    (uAbove : ∀ {y}, y ∈ U → N.Ri n₀ y)
    (rU : ∀ {u}, u ∈ R → u ∈ U)
    (rClosed : ∀ {u v}, u ∈ R → N.Rm u v → v ∈ R) : ConstraintModel where
  W := N.W ⊕ Unit
  Ri := fun a b =>
    match a, b with
    | .inl x, .inl y => N.Ri x y
    | .inl x, .inr _ => N.Ri x n₀
    | .inr _, .inl y => y ∈ U
    | .inr _, .inr _ => True
  Rm := fun a b =>
    match a, b with
    | .inl x, .inl y => N.Rm x y
    | .inl _, .inr _ => False
    | .inr _, .inl y => y ∈ R
    | .inr _, .inr _ => True
  F := fun a => match a with
    | .inl x => x ∈ N.F
    | .inr _ => n₀ ∈ N.F
  V := fun q a => match a with
    | .inl x => x ∈ N.V q
    | .inr _ => n₀ ∈ N.V q
  refl_i := by
    intro a
    rcases a with x | u
    · exact N.refl_i x
    · exact True.intro
  trans_i := by
    intro a b c h₁ h₂
    rcases a with x | u <;> rcases b with y | t <;> rcases c with y' | s
    · exact N.trans_i h₁ h₂
    · exact N.trans_i h₁ h₂
    · exact N.trans_i h₁ (uAbove h₂)
    · exact h₁
    · exact uUp h₁ h₂
    · exact True.intro
    · exact h₂
    · exact True.intro
  refl_m := by
    intro a
    rcases a with x | u
    · exact N.refl_m x
    · exact True.intro
  trans_m := by
    intro a b c h₁ h₂
    rcases a with x | u <;> rcases b with y | t <;> rcases c with y' | s
    · exact N.trans_m h₁ h₂
    · exact h₂.elim
    · exact h₁.elim
    · exact h₁.elim
    · exact rClosed h₁ h₂
    · exact h₂.elim
    · exact h₂
    · exact True.intro
  sub_mi := by
    intro a b h
    rcases a with x | u <;> rcases b with y | t
    · exact N.sub_mi h
    · exact h.elim
    · exact rU h
    · exact True.intro
  hered_F := by
    intro a b h hF
    rcases a with x | u <;> rcases b with y | t
    · exact N.hered_F h hF
    · exact N.hered_F h hF
    · exact N.hered_F (uAbove h) hF
    · exact hF
  hered_V := by
    intro q a b h hV
    rcases a with x | u <;> rcases b with y | t
    · exact N.hered_V h hV
    · exact N.hered_V h hV
    · exact N.hered_V (uAbove h) hV
    · exact hV
  full_F := by
    intro q a hF
    rcases a with x | u
    · exact N.full_F hF
    · exact N.full_F hF

/-- **Point-adjunction extends a p-bisimulation**: given a p-variant N
of C, an anchored pair `(z, n₀) ∈ B.Z`, and five cover conditions
routing z's relational data through the accumulated Z, the adjoined
model is again a p-variant, with ⋆ a p-variant of z.  `mback_cover`
is the promise mechanism: ⋆ may constraint-reach any world
Z-equivalent to a constraint successor of its anchor. -/
def adjoin_pbisim {p : String} {C N : ConstraintModel}
    (B : PBisim p C N) {z : C.W} {n₀ : N.W} (hzn : B.Z z n₀)
    (U R : Set N.W)
    (uUp : ∀ {y y'}, y ∈ U → N.Ri y y' → y' ∈ U)
    (uAbove : ∀ {y}, y ∈ U → N.Ri n₀ y)
    (rU : ∀ {u}, u ∈ R → u ∈ U)
    (rClosed : ∀ {u v}, u ∈ R → N.Rm u v → v ∈ R)
    (anchor_down : ∀ {c n}, B.Z c n → N.Ri n n₀ → C.Ri c z)
    (iforth_cover : ∀ {v}, C.Ri z v → v = z ∨ ∃ n' ∈ U, B.Z v n')
    (iback_cover : ∀ {n'}, n' ∈ U → ∃ v, C.Ri z v ∧ B.Z v n')
    (mforth_cover : ∀ {u}, C.Rm z u → u = z ∨ ∃ n' ∈ R, B.Z u n')
    (mback_cover : ∀ {n'}, n' ∈ R → ∃ u, C.Rm z u ∧ B.Z u n') :
    PBisim p C (adjoin N n₀ U R uUp uAbove rU rClosed) where
  Z := fun c b => match b with
    | .inl n => B.Z c n
    | .inr _ => c = z
  atoms := by
    intro c b hZ q hq
    rcases b with n | u
    · exact B.atoms hZ q hq
    · obtain rfl : c = z := hZ
      exact B.atoms hzn q hq
  fall := by
    intro c b hZ
    rcases b with n | u
    · exact B.fall hZ
    · obtain rfl : c = z := hZ
      exact B.fall hzn
  iforth := by
    intro c b hZ v hv
    rcases b with n | u
    · obtain ⟨n', hn', hZ'⟩ := B.iforth hZ hv
      exact ⟨.inl n', hn', hZ'⟩
    · obtain rfl : c = z := hZ
      rcases iforth_cover hv with rfl | ⟨n', hn'U, hZ'⟩
      · exact ⟨.inr (), True.intro, rfl⟩
      · exact ⟨.inl n', hn'U, hZ'⟩
  iback := by
    intro c b hZ b' hb'
    rcases b with n | u
    · rcases b' with n' | u'
      · obtain ⟨v, hv, hZ'⟩ := B.iback hZ hb'
        exact ⟨v, hv, hZ'⟩
      · exact ⟨z, anchor_down hZ hb', rfl⟩
    · obtain rfl : c = z := hZ
      rcases b' with n' | u'
      · obtain ⟨v, hzv, hZ'⟩ := iback_cover hb'
        exact ⟨v, hzv, hZ'⟩
      · exact ⟨c, C.refl_i c, rfl⟩
  mforth := by
    intro c b hZ u hu
    rcases b with n | t
    · obtain ⟨n', hn', hZ'⟩ := B.mforth hZ hu
      exact ⟨.inl n', hn', hZ'⟩
    · obtain rfl : c = z := hZ
      rcases mforth_cover hu with rfl | ⟨n', hn'R, hZ'⟩
      · exact ⟨.inr (), True.intro, rfl⟩
      · exact ⟨.inl n', hn'R, hZ'⟩
  mback := by
    intro c b hZ b' hb'
    rcases b with n | t
    · rcases b' with n' | u'
      · obtain ⟨u, hu, hZ'⟩ := B.mback hZ hb'
        exact ⟨u, hu, hZ'⟩
      · exact hb'.elim
    · obtain rfl : c = z := hZ
      rcases b' with n' | u'
      · obtain ⟨u, hzu, hZ'⟩ := mback_cover hb'
        exact ⟨u, hzu, hZ'⟩
      · exact ⟨c, C.refl_m c, rfl⟩

/-! ## The basic instance: strict parameters over a trivial cluster -/

/-- The strict Rᵢ-cone over `z`. -/
def strictCone (C : ConstraintModel) (z : C.W) : Set C.W :=
  {y | C.Ri z y ∧ ¬ C.Ri y z}

/-- The strict constraint row of `z`. -/
def strictRow (C : ConstraintModel) (z : C.W) : Set C.W :=
  {u | C.Rm z u ∧ ¬ C.Ri u z}

theorem strictCone_up {C : ConstraintModel} {z : C.W} :
    ∀ {y y'}, y ∈ strictCone C z → C.Ri y y' → y' ∈ strictCone C z :=
  fun hy h => ⟨C.trans_i hy.1 h, fun h' => hy.2 (C.trans_i h h')⟩

theorem strictCone_above {C : ConstraintModel} {z : C.W} :
    ∀ {y}, y ∈ strictCone C z → C.Ri z y := fun hy => hy.1

theorem strictRow_cone {C : ConstraintModel} {z : C.W} :
    ∀ {u}, u ∈ strictRow C z → u ∈ strictCone C z :=
  fun hu => ⟨C.sub_mi hu.1, hu.2⟩

theorem strictRow_closed {C : ConstraintModel} {z : C.W} :
    ∀ {u v}, u ∈ strictRow C z → C.Rm u v → v ∈ strictRow C z :=
  fun hu h => ⟨C.trans_m hu.1 h, fun h' => hu.2 (C.trans_i (C.sub_mi h) h')⟩

/-- One point over `z` with strict parameters. -/
def adjoinAt (C : ConstraintModel) (z : C.W) : ConstraintModel :=
  adjoin C z (strictCone C z) (strictRow C z)
    strictCone_up strictCone_above strictRow_cone strictRow_closed

/-- `z`'s Rᵢ-cluster is trivial. -/
def TrivialCluster (C : ConstraintModel) (z : C.W) : Prop :=
  ∀ v, C.Ri z v → C.Ri v z → v = z

/-- Over a trivial cluster the strict instance is a p-variant (the
identity bisimulation extended by `(z, ⋆)`). -/
def adjoinAt_pbisim (C : ConstraintModel) (p : String) (z : C.W)
    (htc : TrivialCluster C z) : PBisim p C (adjoinAt C z) :=
  adjoin_pbisim (ABisim.id _ C)
    (show (ABisim.id (fun a => a ≠ p) C).Z z z from rfl)
    (strictCone C z) (strictRow C z)
    strictCone_up strictCone_above strictRow_cone strictRow_closed
    (by intro c n hcn h
        obtain rfl : c = n := hcn
        exact h)
    (by intro v hv
        by_cases hvz : C.Ri v z
        · exact Or.inl (htc v hv hvz)
        · exact Or.inr ⟨v, ⟨hv, hvz⟩, rfl⟩)
    (by intro n' hn'
        exact ⟨n', hn'.1, rfl⟩)
    (by intro u hu
        by_cases huz : C.Ri u z
        · exact Or.inl (htc u (C.sub_mi hu) huz)
        · exact Or.inr ⟨u, ⟨hu, huz⟩, rfl⟩)
    (by intro n' hn'
        exact ⟨n', hn'.1, rfl⟩)

/-- The generic decoration set: `p` on ⋆'s upset plus the fallible
worlds. -/
def adjoinAtPSet (C : ConstraintModel) (z : C.W) : Set (adjoinAt C z).W :=
  fun b => match b with
    | .inl y => y ∈ strictCone C z ∨ y ∈ C.F
    | .inr _ => True

theorem adjoinAtPSet_hered (C : ConstraintModel) (z : C.W) :
    ∀ {a b}, (adjoinAt C z).Ri a b → a ∈ adjoinAtPSet C z →
      b ∈ adjoinAtPSet C z := by
  intro a b h hS
  rcases a with y | u <;> rcases b with y' | t
  · rcases hS with hy | hF
    · exact Or.inl (strictCone_up hy h)
    · exact Or.inr (C.hered_F h hF)
  · exact True.intro
  · exact Or.inl h
  · exact True.intro

theorem adjoinAtPSet_full (C : ConstraintModel) (z : C.W) :
    ∀ {a}, a ∈ (adjoinAt C z).F → a ∈ adjoinAtPSet C z := by
  intro a hF
  rcases a with y | u
  · exact Or.inr hF
  · exact True.intro

/-- The decorated instance. -/
def adjoinAtP (C : ConstraintModel) (p : String) (z : C.W) :
    ConstraintModel :=
  redecorate (adjoinAt C z) p (adjoinAtPSet C z)
    (adjoinAtPSet_hered C z) (adjoinAtPSet_full C z)

/-- The decorated instance is a p-variant over a trivial cluster. -/
def adjoinAtP_pbisim (C : ConstraintModel) (p : String) (z : C.W)
    (htc : TrivialCluster C z) : PBisim p C (adjoinAtP C p z) :=
  (adjoinAt_pbisim C p z htc).comp
    (redecorate_pbisim (adjoinAt C z) p (adjoinAtPSet C z)
      (adjoinAtPSet_hered C z) (adjoinAtPSet_full C z))

/-! ## Instance 1: the doubling's core — `p ∨ ¬p` refuted -/

/-- **The doubling's job by one point**: at a non-fallible anchor, the
decorated instance refutes `p ∨ ¬p` — z is not in the decoration, its
point ⋆ is.  (No cluster or row hypothesis: the refutation is
frame-legal always; triviality is needed only for the BISIMULATION.) -/
theorem adjoinAtP_not_em (C : ConstraintModel) (p : String) (z : C.W)
    (hzF : z ∉ C.F) :
    ¬ (adjoinAtP C p z).force (.inl z)
      ((PLLFormula.prop p).or ((PLLFormula.prop p).ifThen .falsePLL)) := by
  rintro (hp | hnp)
  · have hp' : (Sum.inl z : (adjoinAt C z).W) ∈
        (if p = p then adjoinAtPSet C z else (adjoinAt C z).V p) := hp
    rw [if_pos rfl] at hp'
    rcases hp' with ⟨-, hns⟩ | hF
    · exact hns (C.refl_i z)
    · exact hzF hF
  · have hstar_p : (adjoinAtP C p z).force (.inr ()) (.prop p) := by
      show (Sum.inr () : (adjoinAt C z).W) ∈
        (if p = p then adjoinAtPSet C z else (adjoinAt C z).V p)
      rw [if_pos rfl]
      exact True.intro
    exact hzF (hnp (.inr ()) (C.refl_i z) hstar_p)

/-! ## Instance 2: the split's core — the frontier row refuted -/

/-- **The split's job by one point**: with a fallibility-free
constraint row at the anchor, the decorated instance refutes
`((p ⊃ ◯⊥) ⊃ p) ⊃ p` — ⋆ forces `p` but not `◯⊥` (its row is z's
strict row), so no world below ⋆ can force `p ⊃ ◯⊥`, and every other
future of z is decorated. -/
theorem adjoinAtP_not_frontier (C : ConstraintModel) (p : String)
    (z : C.W) (hz : ∀ u, C.Rm z u → u ∉ C.F) :
    ¬ (adjoinAtP C p z).force (.inl z)
      ((((PLLFormula.prop p).ifThen PLLFormula.falsePLL.somehow).ifThen
        (.prop p)).ifThen (.prop p)) := by
  intro hM
  have hzF : z ∉ C.F := hz z (C.refl_m z)
  have hstar_p : (adjoinAtP C p z).force (.inr ()) (.prop p) := by
    show (Sum.inr () : (adjoinAt C z).W) ∈
      (if p = p then adjoinAtPSet C z else (adjoinAt C z).V p)
    rw [if_pos rfl]
    exact True.intro
  have hstar_nbox : ¬ (adjoinAtP C p z).force (.inr ())
      PLLFormula.falsePLL.somehow := by
    intro hbox
    obtain ⟨d, hd, hdF⟩ := hbox _ ((adjoinAtP C p z).refl_i (.inr ()))
    rcases d with t | t
    · exact hz t hd.1 hdF
    · exact hz z (C.refl_m z) hdF
  have hA : (adjoinAtP C p z).force (.inl z)
      (((PLLFormula.prop p).ifThen PLLFormula.falsePLL.somehow).ifThen
        (.prop p)) := by
    intro b hb himp
    rcases b with y | u
    · by_cases hyz : C.Ri y z
      · exact absurd (himp (.inr ()) hyz hstar_p) hstar_nbox
      · show (Sum.inl y : (adjoinAt C z).W) ∈
          (if p = p then adjoinAtPSet C z else (adjoinAt C z).V p)
        rw [if_pos rfl]
        exact Or.inl ⟨hb, hyz⟩
    · show (Sum.inr () : (adjoinAt C z).W) ∈
        (if p = p then adjoinAtPSet C z else (adjoinAt C z).V p)
      rw [if_pos rfl]
      exact True.intro
  have hp : (Sum.inl z : (adjoinAt C z).W) ∈
      (if p = p then adjoinAtPSet C z else (adjoinAt C z).V p) :=
    hM (.inl z) ((adjoinAtP C p z).refl_i _) hA
  rw [if_pos rfl] at hp
  rcases hp with ⟨-, hns⟩ | hF
  · exact hns (C.refl_i z)
  · exact hzF hF

/-! ## Instance 3: the levelled model's core — the two-storey tower

The anchor is CONSTRAINT-RIGID (`∀ u, C.Rm z u → u = z`) with a
trivial cluster.  First storey: ⋆₁ over z with strict parameters (the
strict row is then empty).  Second storey: ⋆₂ over z again, its cone
`{⋆₁} ∪` the strict cone, its row `R = {⋆₁}` — the SIDEWAYS promise,
licensed by `mback_cover` through the accumulated pair `(z, ⋆₁)`.
Decorating `p` on ⋆₁'s upset: ⋆₂ forces `◯p` (its promise delivers a
p-world) but not `p`, so z's rigid row cannot force `◯p ⊃ p` —
`◯(◯p ⊃ p)` fails at z. -/

/-- Constraint-rigidity of the anchor. -/
def RigidRow (C : ConstraintModel) (z : C.W) : Prop :=
  ∀ u, C.Rm z u → u = z

/-- Second-storey cone: ⋆₁ and the strict cone. -/
def lobU (C : ConstraintModel) (z : C.W) : Set (adjoinAt C z).W :=
  fun b => match b with
    | .inl y => y ∈ strictCone C z
    | .inr _ => True

/-- Second-storey row: exactly ⋆₁ — the sideways promise. -/
def lobR (C : ConstraintModel) (z : C.W) : Set (adjoinAt C z).W :=
  fun b => match b with
    | .inl _ => False
    | .inr _ => True

theorem lobU_up {C : ConstraintModel} {z : C.W} :
    ∀ {b b'}, b ∈ lobU C z → (adjoinAt C z).Ri b b' → b' ∈ lobU C z := by
  intro b b' hb h
  rcases b with y | u <;> rcases b' with y' | u'
  · exact strictCone_up hb h
  · exact True.intro
  · exact h
  · exact True.intro

theorem lobU_above {C : ConstraintModel} {z : C.W} :
    ∀ {b}, b ∈ lobU C z → (adjoinAt C z).Ri (.inl z) b := by
  intro b hb
  rcases b with y | u
  · exact hb.1
  · exact C.refl_i z

theorem lobR_U {C : ConstraintModel} {z : C.W} :
    ∀ {b}, b ∈ lobR C z → b ∈ lobU C z := by
  intro b hb
  rcases b with y | u
  · exact hb.elim
  · exact True.intro

theorem lobR_closed {C : ConstraintModel} {z : C.W} (hrow : RigidRow C z) :
    ∀ {b b'}, b ∈ lobR C z → (adjoinAt C z).Rm b b' → b' ∈ lobR C z := by
  intro b b' hb h
  rcases b with y | u <;> rcases b' with y' | u'
  · exact hb.elim
  · exact hb.elim
  · obtain rfl := hrow y' h.1
    exact absurd (C.refl_i y') h.2
  · exact True.intro

/-- The two-storey tower (before decoration). -/
def lobTowerBase (C : ConstraintModel) (z : C.W) (hrow : RigidRow C z) :
    ConstraintModel :=
  adjoin (adjoinAt C z) (.inl z) (lobU C z) (lobR C z)
    lobU_up lobU_above lobR_U (lobR_closed hrow)

/-- The tower is a p-variant: both storeys through `adjoin_pbisim`,
the second citing the accumulated pair `(z, ⋆₁)` in its covers. -/
def lobTowerBase_pbisim (C : ConstraintModel) (p : String) (z : C.W)
    (htc : TrivialCluster C z) (hrow : RigidRow C z) :
    PBisim p C (lobTowerBase C z hrow) :=
  adjoin_pbisim (adjoinAt_pbisim C p z htc)
    (show (adjoinAt_pbisim C p z htc).Z z (.inl z) from rfl)
    (lobU C z) (lobR C z)
    lobU_up lobU_above lobR_U (lobR_closed hrow)
    (by intro c n hcn h
        rcases n with m | u
        · obtain rfl : c = m := hcn
          exact h
        · exact absurd h.1 h.2)
    (by intro v hv
        by_cases hvz : C.Ri v z
        · exact Or.inl (htc v hv hvz)
        · exact Or.inr ⟨.inl v, ⟨hv, hvz⟩, rfl⟩)
    (by intro n' hn'
        rcases n' with y | u
        · exact ⟨y, hn'.1, rfl⟩
        · exact ⟨z, C.refl_i z, rfl⟩)
    (by intro u hu
        exact Or.inl (hrow u hu))
    (by intro n' hn'
        rcases n' with y | u
        · exact hn'.elim
        · exact ⟨z, C.refl_m z, rfl⟩)

/-- The tower decoration: `p` on ⋆₁'s upset (⋆₁ and the strict cone)
plus the fallible worlds; ⋆₂ and the anchor stay undecorated. -/
def lobPSet (C : ConstraintModel) (z : C.W) (hrow : RigidRow C z) :
    Set (lobTowerBase C z hrow).W :=
  fun b => match b with
    | .inl (.inl y) => y ∈ strictCone C z ∨ y ∈ C.F
    | .inl (.inr _) => True
    | .inr _ => z ∈ C.F

theorem lobPSet_hered (C : ConstraintModel) (z : C.W)
    (hrow : RigidRow C z) :
    ∀ {a b}, (lobTowerBase C z hrow).Ri a b → a ∈ lobPSet C z hrow →
      b ∈ lobPSet C z hrow := by
  intro a b h hS
  rcases a with (y | u) | t <;> rcases b with (y' | u') | t'
  · rcases hS with hy | hF
    · exact Or.inl (strictCone_up hy h)
    · exact Or.inr (C.hered_F h hF)
  · exact True.intro
  · rcases hS with hy | hF
    · exact absurd h hy.2
    · exact C.hered_F h hF
  · exact Or.inl h
  · exact True.intro
  · exact absurd h.1 h.2
  · exact Or.inr (C.hered_F h.1 hS)
  · exact True.intro
  · exact hS

theorem lobPSet_full (C : ConstraintModel) (z : C.W)
    (hrow : RigidRow C z) :
    ∀ {a}, a ∈ (lobTowerBase C z hrow).F → a ∈ lobPSet C z hrow := by
  intro a hF
  rcases a with (y | u) | t
  · exact Or.inr hF
  · exact True.intro
  · exact hF

/-- The decorated tower. -/
def lobTower (C : ConstraintModel) (p : String) (z : C.W)
    (hrow : RigidRow C z) : ConstraintModel :=
  redecorate (lobTowerBase C z hrow) p (lobPSet C z hrow)
    (lobPSet_hered C z hrow) (lobPSet_full C z hrow)

/-- The decorated tower is a p-variant. -/
def lobTower_pbisim (C : ConstraintModel) (p : String) (z : C.W)
    (htc : TrivialCluster C z) (hrow : RigidRow C z) :
    PBisim p C (lobTower C p z hrow) :=
  (lobTowerBase_pbisim C p z htc hrow).comp
    (redecorate_pbisim (lobTowerBase C z hrow) p (lobPSet C z hrow)
      (lobPSet_hered C z hrow) (lobPSet_full C z hrow))

/-- **The levelled model's job by two points**: the tower refutes
`◯(◯p ⊃ p)` at the (non-fallible, rigid) anchor: z's rigid row must
supply a `◯p ⊃ p`-witness at z itself, but ⋆₂ above z forces `◯p`
(the sideways promise ⋆₁ carries p) without forcing `p`. -/
theorem lobTower_not_lob (C : ConstraintModel) (p : String) (z : C.W)
    (hzF : z ∉ C.F) (hrow : RigidRow C z) :
    ¬ (lobTower C p z hrow).force (.inl (.inl z))
      (((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow) := by
  intro hbox
  -- ⋆₂ does not force p …
  have hstar2_np : ¬ (lobTower C p z hrow).force (.inr ()) (.prop p) := by
    intro hp
    have hp' : (Sum.inr () : (lobTowerBase C z hrow).W) ∈
        (if p = p then lobPSet C z hrow else (lobTowerBase C z hrow).V p) := hp
    rw [if_pos rfl] at hp'
    exact hzF hp'
  -- … but ⋆₂ forces ◯p: every future has a p-forcing constraint successor
  have hstar2_boxp : (lobTower C p z hrow).force (.inr ())
      (PLLFormula.prop p).somehow := by
    intro c hc
    rcases c with (y | u) | t
    · refine ⟨.inl (.inl y), C.refl_m y, ?_⟩
      show (Sum.inl (Sum.inl y) : (lobTowerBase C z hrow).W) ∈
        (if p = p then lobPSet C z hrow else (lobTowerBase C z hrow).V p)
      rw [if_pos rfl]
      exact Or.inl hc
    · refine ⟨.inl (.inr ()), True.intro, ?_⟩
      show (Sum.inl (Sum.inr ()) : (lobTowerBase C z hrow).W) ∈
        (if p = p then lobPSet C z hrow else (lobTowerBase C z hrow).V p)
      rw [if_pos rfl]
      exact True.intro
    · refine ⟨.inl (.inr ()), True.intro, ?_⟩
      show (Sum.inl (Sum.inr ()) : (lobTowerBase C z hrow).W) ∈
        (if p = p then lobPSet C z hrow else (lobTowerBase C z hrow).V p)
      rw [if_pos rfl]
      exact True.intro
  -- z's row is rigid: its ◯(◯p⊃p)-witness must be z itself
  obtain ⟨d, hd, hθ⟩ := hbox (.inl (.inl z))
    ((lobTower C p z hrow).refl_i (.inl (.inl z)))
  rcases d with (y | u) | t
  · have hyz : y = z := hrow y hd
    exact hstar2_np (hθ (.inr ()) (by rw [hyz]; exact C.refl_i z) hstar2_boxp)
  · exact hd.elim
  · exact hd.elim

/-! ## The contrast: adjunction towers reach what split towers cannot -/

/-- **The adjunction tower reaches the levelled row over the one-world
model** — exactly where `splitTower_oneW_forces_lob` proves every
split-tower variant forces it.  The R-parameter (the promise row) is
the missing degree of freedom, isolated. -/
theorem adjoin_reaches_lob (p : String) :
    ∃ (N : ConstraintModel) (B : PBisim p oneW N) (v : N.W),
      B.Z () v ∧
      ¬ N.force v (((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow) := by
  have hrow : RigidRow oneW () := fun u _ => rfl
  have htc : TrivialCluster oneW () := fun v _ _ => rfl
  refine ⟨lobTower oneW p () hrow, lobTower_pbisim oneW p () htc hrow,
    .inl (.inl ()), ⟨.inl (.inl ()), rfl, rfl⟩, ?_⟩
  exact lobTower_not_lob oneW p () (fun h => h) hrow

/-! ## Axiom audit (pinned) -/

/-- info: 'PLLND.SemUI.adjoin_pbisim' does not depend on any axioms -/
#guard_msgs in
#print axioms adjoin_pbisim

/--
info: 'PLLND.SemUI.adjoin_reaches_lob' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms adjoin_reaches_lob

end SemUI
end PLLND
