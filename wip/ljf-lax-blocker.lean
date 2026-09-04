import LaxLogic.PLLFocused

/-!
# The G4iLL blocking sequent, derived in the lax-flagged focused calculus

The sequent `◯((◯p→r)→◯p), ◯p→r ⊢ r` is PLL-provable but unprovable in
Iemhoff's G4iLL — the machine-checked incompleteness counterexample
(2026-07-08).  The failure there is a resource failure: the derivation needs
`◯p→r` **twice** (once to reduce the goal `r` to `◯p`, once again inside the
opened box), and G4iLL's contraction-free `⊃`-left consumes it.

Matthew's question (2026-08-09): is this sequent still a blocker for the
focused calculus with the lax flag (`LaxLogic/PLLFocused.lean`)?  If yes, the
planned ◯-extension of LJF dies the same death and we need to know now.

**Answer: it is derivable.**  The term `blocker` below is the first genuine
exercise of the lax phase: `circR` fires twice, `circL` fires twice, and the
hypothesis `◯p→r` is left-focused twice — free of charge, because a focused
left context is *persistent*: `lfoc` selects a hypothesis by membership and
consumes nothing, so contraction is built into the judgment rather than being
a rule that termination must pay for.  The polarisation used:

    ◯p           = circ (atom p)                            (negative)
    ◯p→r         = imp (down (circ (atom p))) (up (atom r))
    (◯p→r)→◯p    = imp (down (◯p→r)) (circ (atom p))
    ◯((◯p→r)→◯p) = circ (down ((◯p→r)→◯p))

The derivation, phase by phase: focus `◯p→r`, whose argument `↓◯p` right-
releases and `circR` flips the goal to `p` **lax**; now `circL` opens the
boxed hypothesis, focus its body `(◯p→r)→◯p`, whose argument `↓(◯p→r)` is
proved by `impR` — putting a *fresh copy* of `↓◯p` in the context — and whose
body `◯p` closes by `circL` again; inside the fresh copy the goal `r` is
proved by focusing `◯p→r` a second time, its argument `↓◯p` now closed from
the context copy of `◯p`.
-/

namespace PLLND
namespace Focused

open Polar

variable (p r : String)

/-- `◯p`. -/
abbrev oP : Neg := .circ (.atom p)

/-- `◯p → r`. -/
abbrev hyp : Neg := .imp (.down (oP p)) (.up (.atom r))

/-- `(◯p→r) → ◯p`. -/
abbrev chi : Neg := .imp (.down (hyp p r)) (oP p)

/-- `◯((◯p→r)→◯p)`, as `◯(↓χ)`. -/
abbrev bchi : Neg := .circ (.down (chi p r))

/-- Continuation closing goal `r` once `↑r` is released from the focus. -/
def closeR {Γ : List Neg} {j : JD} : LFoc Γ (.up (.atom r)) j (.atom r) :=
  .rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..)))))

/-- `Γ ⊢lax p` whenever `◯p ∈ Γ`: `circL` on it, then `init`. -/
def closeOP {Γ : List Neg} (h : oP p ∈ Γ) : Stab Γ .lax (.atom p) :=
  .lfoc h (.circL (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))

/-- `Γ ⊢tru ↓◯p` whenever `◯p ∈ Γ`: right-release, `circR`, then `closeOP`. -/
def downOP {Γ : List Neg} (h : oP p ∈ Γ) : Stab Γ .tru (.down (oP p)) :=
  .rfoc (.rel (.circR (.stable (closeOP p h))))

/-- The inner sequent `◯p, χ, ◯χ', ◯p→r ⊢tru r` — the **second use** of
`◯p→r`, its argument now closed from the context copy of `◯p`. -/
def innerR : Stab [oP p, chi p r, bchi p r, hyp p r] .tru (.atom r) :=
  .lfoc
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (.impL (downOP p (List.mem_cons_self ..)) (closeR r))

/-- `χ, ◯χ', ◯p→r ⊢tru ↓(◯p→r)`: `impR` grows the context by a fresh `↓◯p`,
and `innerR` finishes. -/
def argHyp : Stab [chi p r, bchi p r, hyp p r] .tru (.down (hyp p r)) :=
  .rfoc (.rel (.impR (.downL (.stable (innerR p r)))))

/-- The lax core `◯χ', ◯p→r ⊢lax p`: `circL` opens the boxed hypothesis,
focus on `χ = (◯p→r)→◯p`, argument by `argHyp`, body `◯p` by `circL`. -/
def laxCore : Stab [bchi p r, hyp p r] .lax (.atom p) :=
  .lfoc (List.mem_cons_self ..)
    (.circL (.downL (.stable
      (.lfoc (List.mem_cons_self ..)
        (.impL (argHyp p r)
          (.circL (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..)))))))))))

/-- **The G4iLL blocker is derivable in the lax-flagged focused calculus.**
`◯((◯p→r)→◯p), ◯p→r ⊢ r`, at judgment `.tru`, by an explicit focused
derivation: first use of `◯p→r`, its argument via `circR` + `laxCore`. -/
def blocker : Stab [bchi p r, hyp p r] .tru (.atom r) :=
  .lfoc (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (.impL (.rfoc (.rel (.circR (.stable (laxCore p r))))) (closeR r))

/-- The soundness image: an unfocused `LaxND` derivation of the erasure. -/
def blockerSound :
    LaxND (eraseCtx [bchi p r, hyp p r]) (erasePos (.atom r)) :=
  soundStab (blocker p r)

end Focused
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.Focused.blocker' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.Focused.blocker
