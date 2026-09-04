import Mathlib

/-!
# The lax modality IS a normal box: every nucleus validates the K axiom

Reading `◯A` as "A is believed", a believer is a nucleus `j` on the Heyting
algebra of propositions.  On any Heyting algebra `H` every nucleus validates the
modal **distribution (K) axiom**

    j (a ⇨ b) ≤ j a ⇨ j b,     i.e.   ◯(A → B) → (◯A → ◯B),

and preserves the top, `j ⊤ = ⊤` (necessitation of `⊤`).  Together with
meet-preservation `j (a ⊓ b) = j a ⊓ j b` (built into `Nucleus`) this says `◯`
is a **normal** modality.  There is therefore **no** countermodel to K:
normality is *not* where lax belief differs from intuitionistic knowledge.

The K proof is one line: meet-preservation turns `j(a⇨b) ⊓ ja` into
`j((a⇨b) ⊓ a)`, and `(a⇨b) ⊓ a ≤ b` (modus ponens) plus monotonicity finishes.
-/

namespace BeliefLax

variable {H : Type*} [HeytingAlgebra H]

/-- **Normality / the K axiom.** Every nucleus validates `◯(A→B) → (◯A→◯B)`. -/
theorem nucleus_himp_le (j : Nucleus H) (a b : H) : j (a ⇨ b) ≤ j a ⇨ j b := by
  rw [le_himp_iff, ← j.map_inf]
  exact j.monotone himp_inf_le

/-- `◯` preserves the top: `◯⊤ ⟺ ⊤`. -/
theorem nucleus_top (j : Nucleus H) : j ⊤ = ⊤ :=
  top_le_iff.mp j.le_apply

end BeliefLax

#print axioms BeliefLax.nucleus_himp_le
#print axioms BeliefLax.nucleus_top
