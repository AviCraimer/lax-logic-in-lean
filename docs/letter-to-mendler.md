# Draft letter to Michael Mendler

Dear Michael,

It has been a long time since we spoke, but I am glad to have a reason to make contact again. 

I'm writing because I've spent the last
3 weeks doing something I hope will interest you: our 1997 I&C paper now lives, almost entirely, inside a proof assistant —
and the project grew well past the original paper while it was at it.

The repository is `github.com/fairflow/lax-logic-in-lean` (Lean 4 +
Mathlib). The state of it, briefly. Almost everything in I&C 137 is
mechanised: the Hilbert system, natural deduction, the term calculus
and the cut-free sequent calculus, all proved equivalent; cut
elimination; the disjunction property and ◯-reflection; the constraint
models with their fallible worlds; soundness; the (Γ, Δ, Θ)-triple
completeness proof of our §4; the finite model property; decidability.
Beyond the paper: strong normalisation of the full term reduction — β
together with let-associativity, freely interleaved — by Lindley–Stark
⊤⊤-lifting, which appears to be the first mechanisation of that method
with sums; Craig interpolation by Maehara; and, a small private project, the Kleene–Brouwer well-foundedness theorem that defeated
me in LEGO at the LFCS all those years ago — now proved fully constructively.

Two findings along the way may interest you.
First, the published G4-style terminating calculus for PLL (Iemhoff,
in the de Jongh volume / arXiv:2209.08976) is provably incomplete:
there is a machine-checked PLL-derivable sequent it cannot derive, and
neither cut nor contraction is admissible in it, the culprit being
that its ◯-implication rules consume formulas that a derivation can
need twice. A three-rule retention repair restores completeness, cut,
and termination, and the repaired calculus carries the mechanised
decision procedure, though the repair means it contains residues of contraction. I'm preparing a note to Rosalie Iemhoff about it, but will need to make quite sure we have correctly implemented her calculus before reporting errors in it.

Second, and this is the part I would most appreciate your feedback on, my old
"Belief in Lax Logic" plan has come back to life and turned into a
paper. ◯ is read as "is believed": as you know, on a Boolean algebra every nucleus is closed, so classical belief collapses to `◯M ≡ M ∨ ◯⊥`, i.e, belief is only worth having constructively.  The paper provides a realisability
semantics over our constraint models in which evidence for ◯M is a
*strategy* responding to presented futures, with a completeness
theorem: PLL is exactly complete when the ⊃-clause, like the ◯-clause,
is shown the future, and provably incomplete for more rigid semantics.
The countermodels come from a finitisation of our §4 construction in
which your Θ-component does its old work unchanged and Zorn's lemma is
replaced by an iterated appeal to the decision procedure, which is proved
constructively rather than through the FMP.  The
Lindenbaum step asks PLL what it is consistent to believe,
formula by formula. The whole chain, completeness theorem included,
is proved without AC.

I will admit plainly how it was done, and it is part of the story:
the formalisation and much of the drafting were carried out with large
large language models (mostly Fable 5, Opus 4.8) operating Lean under a strict regime — nothing
asserted beyond its machine-checked status, axiom audits recorded per
theorem, and my job largely to direct, to read statements, and to catch
its errors (there were several). Two useful theorems were found
by the machine failing to prove the statement we first wrote down and
the failure being provable.

Whatever you may think of the tools (and I am amazed, almost shocked by how much leverage they have given me), the Lean
kernel is indifferent to the provenance of its proofs; so I think these results at least as trustworthy, maybe more than the hand completed research you and I have done.  But it is interesting that the formalised work revealed no errors in our results.

Where to look, in order: `docs/pll-formalisation-ledger.md` is the
statement-level index of everything with its axiom audit;
`https://github.com/fairflow/lax-logic-in-lean/blob/claude/belief-lax-logic-review-8cf130/paper/belief.pdf` is the latest draft of the belief paper; the three files in `docs/annotated/` walk through the central
proofs with the Lean interleaved. I would particularly value your eye
on the consistency formula's ◯-guard in the finitised §4 — your design
carrying a new proof — and on whether the belief reading convinces you.

all best to you and the family, we're well here on the farm,

Matthew
