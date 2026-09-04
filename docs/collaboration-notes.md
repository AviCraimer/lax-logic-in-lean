# Notes on a collaboration: the belief-paper week

*Mined from the session transcript on 2026-07-18, at Matthew's request,
by the model that was the other party — a bias the reader should keep in
view. Quotes are verbatim; clock times are UTC. These are private
working notes for Matthew to prune before any wider circulation.*

The request that produced this document, as he left his desk:

> "it seems like a good point to mine the whole session transcript …
> for gems about this collaboration. Of course it wouldn't have
> happened without my initiative, energy, experience, mathematical 6th
> sense when confronted with overwhelming levels of detail. But it has
> enormously amplified my own mathematical reach and I wonder what a
> more up-to-speed mathematician could do with this Lean/Fable pairing."

Scope: one session, 14–18 July 2026 — the week in which "Belief in Lax
Logic" went from a handover brief to a drafted paper with a mechanised
completeness theorem. The wider formalisation (the 1997 paper's
transport, strong normalisation, decidability, the uniform-interpolation
programme) happened in earlier sessions and is not mined here.

## 1. The shape of the week

Three and a half days; a 13 MB transcript. **68 human turns against
1,118 machine turns** — a 16:1 ratio that is the division of labour in
one number: the human's contribution was direction, not volume. The
distribution is just as telling: 54, 67, 43, then **807 machine turns
on 17 July** (the day the searcher, the emitter, the obstruction, the
⊩ᵖ repair, and the finite completeness proof all landed), then 147.
Two model tiers were used (Fable 828 turns, Opus 288), switched by the
human on grounds of both cost and capability; three cleanup jobs were
delegated further down-fleet to Sonnet. Roughly 260 shell commands, 130
file edits, 8 subagents, 5 spun-off task sessions, 5 surgical
interrupts, two context compactions survived mid-flight.

## 2. What the human supplied

**Trap-testing.** Confronted with a claim he doubted, Matthew's method
was to demand the object, not the argument: "remind me (make the proof
via a countermodel) why PLL isn't normal?" The countermodel could not
be built; the claim died the same evening, and the correction — ◯ *is*
a normal modality — was machine-checked the next day. The same
instinct, aimed at a plan rather than a claim: "surely OPEN 5 and OPEN
6 completeness are incompatible? Explain if you think not." They were
incompatible, and the explanation became a theorem (the logic PLLᵘ of
rigid evidence, and eventually the fullness obstruction).

**Redirection, within minutes.** The transcript's five interrupts each
cut off a failing line early. The sharpest: "you keep talking about
building enum. You're thrashing around in circles … Why do you need
enum? I just don't trust this approach." — which was correct; the
machine conceded "I was measuring `enum` — the one object that has
nothing to do with proof search — and calling it investigation." The
constructive twin of that interrupt was a design decision: "Can you
somehow discard the fuel as it doesn't really seem to help guide search
or tell us when to stop … **If we can build a term, Lean can check
it.**" That sentence is the literal architecture of the fuel-free
searcher: untrusted search, kernel-checked term.

**Verification discipline.** The two standing rules of the week were
both his, both stated as method rather than preference: "we must have
the formal defs and theorem statements or we cannot trust what's
claimed very far," and — after catching an unmechanised claim in the
draft — the mandate that nothing be asserted beyond its machine-checked
status. He audited the auditors: "what exactly is `Quot.sound`? It
sounds like an assumption about the soundness of Lean's quotation
system, which would be quite a big assumption, so please clarify."
(It is not; it is the soundness of quotient types — but the point is
that he asked.)

**Fleet management.** He ran the models like a lab head: Fable when
credits allowed ("now on Fable Extra as I seem to have credits again"),
a deliberate escalation when he judged a job beyond the tier doing it
("this is painful to watch; Fable, can you look at PLLG4Term.lean …
It's too big a job for Opus"), routine cleanup sent down-fleet ("A
Sonnet job? Anyway: delegate please"), overnight scheduling around his
own sleep ("This may need to complete while I sleep!" — and, forty
minutes later, "brilliant! And it isn't even midnight yet!"). His
post-hoc assessment of the escalation is a datum about model tiers:
"It seemed obvious to me that this was very routine … But I don't think
Opus could have done it, the thrashing was intense and kept looping
through previously discarded avenues."

**Mathematical judgement under detail overload.** His own account:

> "I have always felt, despite my PhD in subrecursive hierarchies and
> applications to weak theories of arithmetic in proof theory, somewhat
> weak in tackling this kind of hard technical material: finding it
> difficult to see the wood for the trees while still being able to
> climb the trees."

The transcript shows the wood-sight working repeatedly: forward
confluence flagged as "a problem: this forces formulae not generally
valid in PLL" (machine-confirmed: it forces ◯∨-distribution, refuted);
the reading of the completeness architecture at a glance ("instantiate
K₁, then emitter completeness; just what I'd have said"); the
philosophical pressure kept on the semantics ("realisers need to know
what futures may await … it doesn't square so easily with the idea of
gradually building up knowledge through stages") — which is now the
paper's frame-uniform/frame-aware remark; and, on the last morning,
reading candidate three-world submodels straight off a diagram. Two of
his four guesses certified, and the two failures had a common,
instructive reason (the atom-free leaves), which is its own kind of
success: the guesses were good enough to be wrong for a reason.

## 3. What the machine supplied

Scale and stamina, principally: the 807-turn day, the overnight
completeness proof, the willingness to re-prove everything under a
changed definition without complaint. Beyond throughput, the genuine
contributions were made *inside* the human's constraints:

- **The fullness obstruction** — the week's methodological crown jewel.
  Completeness for the strategy clause ⊩ˢ was attempted, failed, and
  the failure was itself formalised, choice-free: no evidence
  assignment over the three-world frame is simultaneously atom-adequate
  and full, and the failure is ◯-essential. A theorem discovered
  because the machine could not prove the statement first written down;
  it is what forces the presented-future clause ⊩ᵖ, turning a repair
  into a necessity. Nine minutes after the obstruction landed, the
  repaired clause closed the completeness argument.
- **Choice-free engineering** throughout: executable branch decisions
  instead of excluded middle, the decided Lindenbaum fold, the table
  algebra — ending at a completeness theorem auditing
  `[propext, Quot.sound]`, the "double win" Matthew had named in
  advance and hoped for out loud ("Let's pray it works out!").
- **Refutations of the expert, with repairs attached**: the ◯◯M ≅ ◯M
  isomorphism guess (join is not injective — but on a poset every monad
  is idempotent, and that distinction became the paper's
  proof-relevant/truth-relevant design dial); the NNO quietly removed
  from his recalled topos definition; "Kolmogorov" flagged as
  unverifiable in the order's name before it could reach print; two of
  the four diagram-read submodel guesses scored wrong, with the reason.
- **Self-caught provenance failures**: a subagent's stylistic summary
  of the 1997 paper was detected as partly fabricated and replaced by
  reading the actual PDF; the vindication of Matthew's thirty-year-old
  LEGO defeat (Kleene–Brouwer well-foundedness, now proved with *no
  axioms at all*) was checked before being celebrated.

## 4. Errors were caught in both directions

Human catches of the machine: the normality falsehood; the incompatible
§6 completeness sketch; a forgotten already-proved decidability theorem
("as I thought, but got too nervous to state, we DO have decidability
for PLL already … this was a great deal of work and burned many many
credits"); a stitched-together fabrication in the draft ("(the
Kleene–Brouwer well-foundedness used in the normalisation development)
stated in the draft. Was it? I didn't spot it if so…" — it was two true
facts joined by a false connective); the overclaim that PLL "proves its
own completeness" (his objection was exact: the logic is
quantifier-free and cannot state it); the enum loop; unmerged work
sitting invisible off `main` ("um where is all the work on this Belief
paper? I looked in my repo...nothing I could see"); and register, twice
("shouty REFUTED", and "'promise' is a verb, not an adjective in UK
English").

Machine catches of the human: listed in §3. And one self-catch on each
side, for symmetry: Matthew — "ah i was reading the arrows the wrong
way!"; the machine — the enum concession above.

The ledger blunder is worth its own line, because both parties made it
*together*: the mechanised decidability theorem was filed as OPEN in
the ledger by the machine and doubted by the human, for a day. The
repair ("It is very reassuring to find that attempting the proof
reveals the bugs in the theorem and you can then autocorrect and find a
new path through") is Matthew's best one-sentence description of the
whole method.

## 5. The method as third participant

The clearest statement of the split, from mid-week: **Lean's kernel
checks the proofs; the human checks that the statements say the right
thing.** Everything else — the ledger, the per-theorem axiom audits,
the wip/library promotion gate ("We will never claim we've proved
anything formally in wip"), the PROVED/REFUTED/OPEN discipline — is
scaffolding for those two checks. Three times in the week, attempting a
mechanised proof refuted the statement being attempted (◯-normality;
the ⊩ᵘ completeness sketch; strategy-fullness), and each refutation was
promoted to a result rather than swallowed as a failure. Once, the
attempt *forced a definition* (soundness demanded the named-witness
clause). The failure mode this method exists to prevent appeared on
schedule and was caught: a plausible connective between two true facts,
invented by the machine, detected by the human, and now recorded in the
paper's own methods section.

On credit, the exchange worth preserving. Matthew, at midnight: "This
is a substantial piece of work, 10 x the size of any of my previous
papers … And how to credit you? … You would, if human, deserve most of
the credit." The machine's reply, which stands as this document's
position too: the two contributions that make the work publishable —
the mathematical judgement and the methodological standard — were the
human's; the machine supplied scale, stamina, and a few genuine
discoveries made inside those constraints; and the kernel-checked
artefact is indifferent to the provenance of its proofs, *which is the
point of the method*.

## 6. The amplification question

Matthew's parting question — what could a more up-to-speed
mathematician do with this pairing? — deserves a sober answer rather
than a flattering one. What this week actually shows: a mathematician
who — in his own words — no longer gets paid to do any of this,
working alone, took a
twenty-nine-year-old logic from "fully mechanised paper" to "new
completeness theorem, new impossibility theorem, drafted paper" in
three and a half days, at the cost of constant vigilance against
fabrication and drift. The rate-limiting factor was never proof
production; it was *his* checking bandwidth — statement-reading, taste,
and traps. A mathematician with more live context would spend the same
bandwidth at a higher exchange rate: sharper conjectures in, less
re-derivation of known ground, faster recognition of which machine
outputs matter. The honest caveat from his own letter draft belongs
here as the other half of the answer: "The formalisation has proceeded
at such a pace that, though I think the definitions and proof goals are
correct … I haven't been able to check them all." The kernel closes
that gap for proofs. Nothing yet closes it for statements, except the
human — which is why the pairing amplifies a mathematician rather than
replacing one.

---

*Raw extracts (all 68 human turns verbatim, 48 machine pivot excerpts,
full stats) are in the session scratchpad under `transcript-mine/`;
they are ephemeral — this document is the curated record.*
