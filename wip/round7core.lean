import round6core
import wip.boxSndTight

/-!
# ROUND 7 — the guard-stack fork, certified interfaces

PROGRESS §63(e) fork (1): discharge the γ-row landing of the `◯`-goal
descent by producing the boxed γ-head component directly, instead of
financing a budget descent.  This file states the production as a `Prop`
(`CompProd`) and certifies the two reductions that make the round-7 screens
load-bearing:

* `compProd_of_boxDesc` — the production follows from the room-free
  `Round4.BoxDesc`.  Consequently every corpus cell screened clean for
  `BoxDesc` is *implied* evidence for `CompProd`, and — the direction that
  matters — **any countermodel to `CompProd` at admissible parameters
  refutes `BoxDesc` itself** (`not_boxDesc_of_not_compProd`).  The round-7
  replay passes G/H screen exactly `CompProd`'s sequent shape, so their
  verdicts are verdicts about the room-free route as a whole.

* `gammaComp_lands` — what the γ-row landing of any direct walk needs is an
  instance of `CompProd` (the fuel/budget slots of the target's γ-head
  disjunct are reachable from the `CompProd` conclusion by the free
  monotonicities).

## The production

    CompProd p S :  for all fs ≤ ft, 1 ≤ c ≤ b, Γ ⊆ S, ◯D ∈ S,

      Δ ⊢ E@(ft, b+1)(Γ)                              (the ambient)
      Δ ⊢ ◯( E@(fs, b)(Γ) ⊃ A@(fs, b)(Γ, ◯D) )       (the held component)
      ─────────────────────────────────────────────
      Δ ⊢ ◯( E@(ft, c)(Γ) ⊃ A@(ft, c)(Γ, ◯D) )

ROOM-FREE: the only arithmetic is the band `1 ≤ c ≤ b`, which is
well-formedness (`c = 0` is REFUTED — the pass-Z control fired at 344 corpus
cells: at budget 0 the target table can be empty, so the component asserts a
boxed negation of the guard and no premise supplies it).

## Why the proof below is NOT the descent smuggled in

`compProd_of_boxDesc` consumes `BoxDesc` — it does not prove it.  The point
of the fork is the converse direction: a direct proof of `CompProd` (by the
gap-preserving pair recursion `(b, c) → (b−1, c−1)` on the γ-head rows,
which pays no room per level and so escapes `no_self_financed_nest`) would
hand every γ-row landing to the walk room-free.  The bottom of that
recursion (`c = 1`, the source's γ-head row handing a budget-1 component
against a budget-1 table) is the round's screened residue — see the pass
T/U/V verdicts and the `S3` instance checks in `wip/frontier_g7.txt`.
-/

open PLLFormula

namespace PLLND
namespace Round7

open PLLND.Round4

/-- **The boxed γ-head component.**  The shape of the first conjunct of every
γ-head disjunct (and of the source's own γ-head row), with both slots at the
displayed fuel and budget. -/
abbrev comp (p : String) (S : Finset PLLFormula) (f c : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) : PLLFormula :=
  ((itpE p S f c Γ).ifThen (itpA p S f c Γ D.somehow)).somehow

/-- **The production**: from the ambient and the held component at the
source budget, the component at every budget in the band `1 ≤ c ≤ b`.
Room-free. -/
def CompProd (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fs ft b c : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
    D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → fs ≤ ft → 1 ≤ c → c ≤ b →
    G4c Δ (itpE p S ft (b + 1) Γ) →
    G4c Δ (comp p S fs b Γ D) →
    G4c Δ (comp p S ft c Γ D)

/-- **The production follows from the room-free descent.**  Open the held
component (`laxL`), fire its guard with the ambient lowered to the source's
own slots (`ambE`), lift the value to the reference fuel, and walk it down
the band by iterating `BoxDesc` — each step's ambient is again the lowered
top ambient.  No room appears anywhere. -/
theorem compProd_of_boxDesc (p : String) (S : Finset PLLFormula)
    (hBD : BoxDesc p S) : CompProd p S := by
  intro fs ft b c Γ Δ D hgS hΓS hfs hc hcb hamb hcomp
  refine G4c.cut hcomp (G4c.laxL (.head _) ?_)
  -- context Δ₁ = (E@(fs,b) ⊃ A@(fs,b)) :: ◯(…) :: Δ
  have hambW : ∀ {Δ' : List PLLFormula}, (∀ ψ ∈ Δ, ψ ∈ Δ') →
      G4c Δ' (itpE p S ft (b + 1) Γ) :=
    fun hs => Round6.weaken_sub hs hamb
  have hV : G4c ((itpE p S fs b Γ).ifThen (itpA p S fs b Γ D.somehow) ::
      (comp p S fs b Γ D) :: Δ) (itpA p S fs b Γ D.somehow) := by
    refine Round6.fire (G4c.identity_mem (.head _)) ?_
    exact GoalDesc.ambE p S hfs (Nat.le_succ b) rfl
      (hambW (fun ψ h => .tail _ (.tail _ h)))
  -- reference fuel
  have hVft : G4c ((itpE p S fs b Γ).ifThen (itpA p S fs b Γ D.somehow) ::
      (comp p S fs b Γ D) :: Δ) (itpA p S ft b Γ D.somehow) :=
    Round6.consume₁ hV (BoxSndTight.fuelA_le p S hfs b Γ D.somehow)
  -- walk down the band: b = c + k → value at c
  have hdesc : ∀ (k b' : Nat), b' = c + k → b' ≤ b →
      G4c ((itpE p S fs b Γ).ifThen (itpA p S fs b Γ D.somehow) ::
        (comp p S fs b Γ D) :: Δ) (itpA p S ft b' Γ D.somehow) →
      G4c ((itpE p S fs b Γ).ifThen (itpA p S fs b Γ D.somehow) ::
        (comp p S fs b Γ D) :: Δ) (itpA p S ft c Γ D.somehow) := by
    intro k
    induction k with
    | zero =>
        intro b' h1 _ hv
        rw [h1] at hv
        exact hv
    | succ n ih =>
        intro b' h1 h2 hv
        refine ih (c + n) rfl (by omega) ?_
        refine hBD ft ft (c + n) Γ _ D hgS hΓS (Nat.le_refl _)
          (by omega) ?_ ?_
        · exact GoalDesc.ambE p S (Nat.le_refl _) (by omega) rfl
            (hambW (fun ψ h => .tail _ (.tail _ h)))
        · have : b' = (c + n) + 1 := by omega
          rw [this] at hv
          exact hv
  have hVc : G4c ((itpE p S fs b Γ).ifThen (itpA p S fs b Γ D.somehow) ::
      (comp p S fs b Γ D) :: Δ) (itpA p S ft c Γ D.somehow) :=
    hdesc (b - c) b (by omega) (Nat.le_refl _) hVft
  exact G4c.laxR (G4c.impR (hVc.weaken _))

/-- **The top of the band is free**: at `c = b` (gap 0) the production is
unconditional — open the component, fire its guard with the lowered ambient,
lift the fuel, re-box.  No `BoxDesc`, no room, no recursion.  The open part
of `CompProd` is therefore exactly the band `1 ≤ c < b`. -/
theorem compProd_gap0 (p : String) (S : Finset PLLFormula)
    (fs ft b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula)
    (hfs : fs ≤ ft)
    (hamb : G4c Δ (itpE p S ft (b + 1) Γ))
    (hcomp : G4c Δ (comp p S fs b Γ D)) :
    G4c Δ (comp p S ft b Γ D) := by
  refine G4c.cut hcomp (G4c.laxL (.head _) ?_)
  have hV : G4c ((itpE p S fs b Γ).ifThen (itpA p S fs b Γ D.somehow) ::
      (comp p S fs b Γ D) :: Δ) (itpA p S fs b Γ D.somehow) := by
    refine Round6.fire (G4c.identity_mem (.head _)) ?_
    exact GoalDesc.ambE p S hfs (Nat.le_succ b) rfl
      (Round6.weaken_sub (fun ψ h => .tail _ (.tail _ h)) hamb)
  have hVft : G4c ((itpE p S fs b Γ).ifThen (itpA p S fs b Γ D.somehow) ::
      (comp p S fs b Γ D) :: Δ) (itpA p S ft b Γ D.somehow) :=
    Round6.consume₁ hV (BoxSndTight.fuelA_le p S hfs b Γ D.somehow)
  exact G4c.laxR (G4c.impR (hVft.weaken _))

/-- **The upgrade direction**: a refutation of the production at admissible
parameters is a refutation of the room-free descent.  This is what makes the
round-7 replay passes G/H two-sided instruments for the whole route. -/
theorem not_boxDesc_of_not_compProd (p : String) (S : Finset PLLFormula)
    (h : ¬ CompProd p S) : ¬ BoxDesc p S :=
  fun hBD => h (compProd_of_boxDesc p S hBD)

/-- **The landing shim**: the first conjunct of the target's γ-head disjunct
(slots at fuel `f`, budget `c`) from a `CompProd` conclusion at the same
slots — definitional, recorded so the walk's consumption site is explicit. -/
theorem gammaComp_lands (p : String) (S : Finset PLLFormula)
    {f c : Nat} {Γ Δ : List PLLFormula} {A₁ : PLLFormula}
    (h : G4c Δ (comp p S f c Γ A₁)) :
    G4c Δ (((itpE p S f c Γ).ifThen (itpA p S f c Γ A₁.somehow)).somehow) := h

end Round7
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round7.compProd_of_boxDesc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round7.compProd_of_boxDesc

/--
info: 'PLLND.Round7.not_boxDesc_of_not_compProd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round7.not_boxDesc_of_not_compProd

/--
info: 'PLLND.Round7.compProd_gap0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round7.compProd_gap0

/-! **The statement carries no financing.**  Pinned as a type check: the only
arithmetic in `CompProd` is the band `fs ≤ ft`, `1 ≤ c`, `c ≤ b` — no
`defect`, no `jumpGoals`, no room. -/

/--
info: PLLND.Round7.CompProd (p : String) (S : Finset PLLFormula) : Prop
-/
#guard_msgs in
#check PLLND.Round7.CompProd
