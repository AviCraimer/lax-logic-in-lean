import wip.descent2

/-!
# The room-satisfying refutation schema, and the sharpest instances pinned

`cascade_low_pos_box` (`wip/absorb_base.lean:2273`) is the tower's only
`sorry`.  Every refutation the repository has produced so far
(`not_ambGuardAscent`, `not_roomFreeDescent`, `not_floorDescent`) refutes a
*variant* with the room hypothesis dropped or weakened, and each of them
lives at a configuration whose room the kernel's own hypothesis puts far
above the refuting budget — `not_derivable_k` certifies failure at `c = 1`
where `needProduct Sk Gk gk = 56`.  So none of them touches the kernel.

This file supplies the two things a *real* refutation needs.

**§1 The schema.**  `RoomDescent p S` is `cascade_low_pos_box`'s conclusion
universally quantified in everything but `p` and `S`, with all three of its
hypotheses (`hbox`, `hd1`, `hroom`) kept.  `not_roomDescent_of_check` turns
a `FinCM.checkB` certificate at a room-satisfying instance into
`¬ RoomDescent p S` in one application — the pattern of
`AscRefute.not_roomFreeDescent`, with the room hypothesis now an *input*
rather than something the refutation quietly violates.

**§2 The sharpest instances.**  `room = defect · (|jumpGoals S| + 2)` with
`1 ≤ defect`, so `room ≥ 3` at every instance whose budget is actually read
(a live gate needs a `(A⊃B)⊃D` or `◯A⊃B` member of `S`, hence
`|jumpGoals S| ≥ 1`, and it needs that member's consequent missing from
`Γ`, hence `defect ≥ 1`).  `room = 3` is therefore the *floor* of the
whole search space, and it is attained: the instances below have
`defect = 1`, `|jumpGoals| = 1`, one live gate and `hbox` true.  They are
where a miscalibration of the product law would have to show up first.
-/

open PLLFormula

namespace PLLND
namespace RoomPin

open PLLND.Descent2 PLLND.Search

/-! ## 1. The schema -/

/-- `boxFree` of `wip/absorb_base.lean:903`, transcribed (that file uses
root-level imports and is not a Lake target). -/
def boxFreeP : PLLFormula → Prop
  | .prop _ => True
  | .falsePLL => True
  | .and A B => boxFreeP A ∧ boxFreeP B
  | .or A B => boxFreeP A ∧ boxFreeP B
  | .ifThen A B => boxFreeP A ∧ boxFreeP B
  | .somehow _ => False

instance boxFreeP.dec : (φ : PLLFormula) → Decidable (boxFreeP φ)
  | .prop _ => .isTrue trivial
  | .falsePLL => .isTrue trivial
  | .and A B => @instDecidableAnd _ _ (boxFreeP.dec A) (boxFreeP.dec B)
  | .or A B => @instDecidableAnd _ _ (boxFreeP.dec A) (boxFreeP.dec B)
  | .ifThen A B => @instDecidableAnd _ _ (boxFreeP.dec A) (boxFreeP.dec B)
  | .somehow _ => .isFalse (fun h => h)

/-- The `hbox` hypothesis of `cascade_low_pos_box`, verbatim. -/
def HBox (S : Finset PLLFormula) (Γ : List PLLFormula) (g : PLLFormula) : Prop :=
  ¬ ((∀ F ∈ S, boxFreeP F) ∧
     (∀ A B : PLLFormula, A.and B ∈ S → A ∈ S ∧ B ∈ S) ∧
     (∀ A B : PLLFormula, A.or B ∈ S → A ∈ S ∧ B ∈ S) ∧
     (∀ A B : PLLFormula, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S) ∧
     g ∈ S ∧ (∀ F ∈ Γ, F ∈ S))

/-- **`cascade_low_pos_box`'s statement**, universally quantified in
everything but the eliminated variable and the space.  All three
hypotheses are kept: this is the kernel, not a variant. -/
def RoomDescent (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula),
    HBox S Γ g →
    1 ≤ defect S Γ →
    defect S Γ * ((jumpGoalsOf S).card + 2) ≤ c →
    G4c Δ (itpE p S fuel (c + 1) Γ) →
    G4c Δ (itpA p S fh (c + 1) Γ g) →
    fh ≤ fuel →
    G4c Δ (itpA p S fuel c Γ g)

/-- **The refutation schema.**  A `checkB` certificate on the sharpest
instance — the two tables at `c+1` as the context, the table at `c` as the
goal, `fh = fuel` — refutes the kernel outright, PROVIDED the three
hypotheses hold at that instance.  The two arithmetic ones are `decide`able
and the `hbox` one is `decide`able for a concrete space, so a refutation
reduces to producing the model.

This is `AscRefute.not_roomFreeDescent`'s pattern with the room hypothesis
promoted from something the refutation violates to something it must
verify. -/
theorem not_roomDescent_of_check {p : String} {S : Finset PLLFormula}
    {fuel c : Nat} {Γ : List PLLFormula} {g : PLLFormula}
    {M : FinCM} {w : Nat}
    (hbox : HBox S Γ g)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoalsOf S).card + 2) ≤ c)
    (hchk : FinCM.checkB M w
        [itpA p S fuel (c + 1) Γ g, itpE p S fuel (c + 1) Γ]
        (itpA p S fuel c Γ g) = true) :
    ¬ RoomDescent p S := by
  intro h
  refine FinCM.not_provable_of_check hchk (G4c.equiv_nd.mp ?_)
  exact h fuel Γ fuel c g _ hbox hd1 hroom
    (G4c.identity_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (G4c.identity_mem (List.mem_cons_self ..))
    (Nat.le_refl _)

/-! ## 2. The room floor, and the instances that attain it -/

/-- The minimum-room instance: one `⊃⊃` gate, its consequent the single
missing space member.  `S` is box-free but *not* subformula-closed
(`(p⊃r)⊃z ∈ S` while `p⊃r ∉ S`), so `hbox` holds and the holdout applies. -/
def Simp : Finset PLLFormula :=
  {((prop "p").ifThen (prop "r")).ifThen (prop "z"), prop "z"}

def Gimp : List PLLFormula :=
  [((prop "p").ifThen (prop "r")).ifThen (prop "z"),
   (prop "r").ifThen (prop "z")]

theorem Simp_defect : defect Simp Gimp = 1 := by decide
theorem Simp_jump : (jumpGoalsOf Simp).card = 1 := by decide
theorem Simp_room : needProduct Simp Gimp (prop "y") = 3 := by decide
theorem Simp_hbox (g : PLLFormula) : HBox Simp Gimp g := by
  intro h
  have := h.2.2.2.1 ((prop "p").ifThen (prop "r")) (prop "z") (by decide)
  revert this
  decide

/-- The minimum-room `◯` instance: one `◯A ⊃ B` gate.  `|jumpGoals| = 2`
(the clause contributes both `A` and `◯A`), so `room = 4` — the floor of
the `◯`-involving band. -/
def Sbox : Finset PLLFormula :=
  {((prop "p").somehow).ifThen (prop "z"), prop "z"}

def Gbox : List PLLFormula := [((prop "p").somehow).ifThen (prop "z")]

theorem Sbox_defect : defect Sbox Gbox = 1 := by decide
theorem Sbox_jump : (jumpGoalsOf Sbox).card = 2 := by decide
theorem Sbox_room : needProduct Sbox Gbox (prop "y") = 4 := by decide
theorem Sbox_hbox (g : PLLFormula) : HBox Sbox Gbox g := by
  intro h
  have := h.1 (((prop "p").somehow).ifThen (prop "z")) (by decide)
  revert this
  decide

/-! ## 2b. The fourth seal at the room floor — UNPAID GROWTH

`cascade_low_pos_box`'s own failure analysis names four sealed positions.
The fourth is *"the fresh-antecedent goal implication with the new piece
outside `S` (the impR seals; the defect does not pay)"*, and it is the one
site at which the context can grow **without the room hypothesis
noticing**: `itpA`'s goal clause for `C = C₁ ⊃ C₂` with `C₁ ∉ Γ` recurses at
`Γ' = C₁ :: Γ`, and if `C₁ ∉ S` then `defect S Γ' = defect S Γ`, while
`hroom` is stated at `Γ`.

`Sfresh`/`Gfresh` put that site at the room FLOOR and make the free growth
do all the work: the `⊃⊃` gate `(p⊃r)⊃z ∈ Γ` is *dead* at `Γ` (its guard
`r ⊃ z` is neither in `Γ` nor in `S`, so the clause emits nothing at all
and the ambient `itpE … Γ` is budget-blind), and becomes *live* at
`Γ' = (r⊃z) :: Γ`.  With the goal `(r ⊃ z) ⊃ y` the entire budget-active
content of the sequent therefore sits at a context the ambient does not
reach — the configuration whose `E`-side ascent
(`AmbGuardAscent`, `wip/ascRefute.lean`) is REFUTED — at `room = 3`
instead of the 56 the July configuration carried.

`Sfresh2` is the same construction with `S` subformula-closed, `Γ ⊆ S`,
and `◯`-involving (the gate's consequent is `◯w`), so that `hbox` holds
through `g ∉ S` alone and the instance sits inside the `◯`-band the
holdout is about.  Both are `checkB`-clean over the widened battery at
`c = room, room+1, room+2` and every fuel probed (`wip/roomhunt.lean`,
stage `fresh`) — reported as evidence, not as proof. -/

def Sfresh : Finset PLLFormula :=
  {((prop "p").ifThen (prop "r")).ifThen (prop "z"), prop "z"}

def Gfresh : List PLLFormula :=
  [((prop "p").ifThen (prop "r")).ifThen (prop "z")]

/-- The fresh antecedent that activates the dead gate; it is in neither
`Γ` nor `S`, so absorbing it costs no defect. -/
def Xfresh : PLLFormula := (prop "r").ifThen (prop "z")

theorem Sfresh_defect : defect Sfresh Gfresh = 1 := by decide
theorem Sfresh_room : needProduct Sfresh Gfresh (prop "y") = 3 := by decide

/-- **The growth is unpaid**: absorbing `Xfresh` leaves the defect where
it was, so the ledger the room hypothesis reads never moves. -/
theorem Sfresh_growth_unpaid :
    defect Sfresh (Xfresh :: Gfresh) = defect Sfresh Gfresh := by decide

theorem Sfresh_hbox (g : PLLFormula) : HBox Sfresh Gfresh g := by
  intro h
  have := h.2.2.2.1 ((prop "p").ifThen (prop "r")) (prop "z") (by decide)
  revert this
  decide

/-- The `◯`-involving, subformula-closed variant: `hbox` holds through
`g ∉ S` alone. -/
def Sfresh2 : Finset PLLFormula :=
  {((prop "p").ifThen (prop "r")).ifThen ((prop "w").somehow),
   (prop "p").ifThen (prop "r"), prop "p", prop "r",
   (prop "w").somehow, prop "w"}

def Gfresh2 : List PLLFormula :=
  [((prop "p").ifThen (prop "r")).ifThen ((prop "w").somehow),
   (prop "p").ifThen (prop "r"), prop "p", prop "r", prop "w"]

def Xfresh2 : PLLFormula := (prop "r").ifThen ((prop "w").somehow)

theorem Sfresh2_defect : defect Sfresh2 Gfresh2 = 1 := by decide
theorem Sfresh2_room : needProduct Sfresh2 Gfresh2 (prop "y") = 3 := by decide
theorem Sfresh2_growth_unpaid :
    defect Sfresh2 (Xfresh2 :: Gfresh2) = defect Sfresh2 Gfresh2 := by decide

/-- Subformula-closure of an implication member, computably. -/
def impClosedChk (S : Finset PLLFormula) (F : PLLFormula) : Bool :=
  match F with
  | .ifThen A B => decide (A ∈ S) && decide (B ∈ S)
  | _ => true

/-- `Sfresh2` really is subformula-closed and `Gfresh2 ⊆ Sfresh2`, so the
only conjunct of the `hbox` negation that can fail is `g ∈ S`. -/
theorem Sfresh2_closed :
    (∀ F ∈ Sfresh2, impClosedChk Sfresh2 F = true)
    ∧ (∀ F ∈ Gfresh2, F ∈ Sfresh2) := by decide

theorem Sfresh2_hbox : HBox Sfresh2 Gfresh2 (prop "y") := by
  intro h
  have := h.2.2.2.2.1
  revert this
  decide

/-! ## 3. How far below the room the existing refutations sit

`AscRefute.not_derivable_k` certifies the descent FALSE at `c = 1` on the
configuration `Sk`, `Gk`, `gk`.  The kernel's room hypothesis at that
configuration demands `c ≥ 56`.  So the certified failure is 55 budget
levels below the first cell the kernel claims anything about — which is
why `not_roomFreeDescent` refutes the room-free reformulation and leaves
`cascade_low_pos_box` untouched. -/

theorem ascRefute_room : needProduct AscRefute.Sk AscRefute.Gk AscRefute.gk = 56 := by
  decide

theorem ascRefute_gap : 1 + 55 = needProduct AscRefute.Sk AscRefute.Gk AscRefute.gk := by
  decide

/-! ## 4. Axiom audit -/

/-- info: 'PLLND.RoomPin.not_roomDescent_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_roomDescent_of_check

/-- info: 'PLLND.RoomPin.Simp_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Simp_room

end RoomPin
end PLLND
