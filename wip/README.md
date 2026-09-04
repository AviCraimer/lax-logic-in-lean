# Work in progress — scaffolds, probes, experiments

Nothing in this directory is claimed as proved.  Files here MAY
contain `sorry`, unverified definitions, or exploratory dead ends —
that is their purpose.  Nothing here is imported by the library root,
and the pinned axiom audits do not cover it.

Contents mirror the live investigation so the process is followable:

* `v3probe*.lean` — the empirical validation battery for the
  truncated (v3/v3.1) uniform-interpolation quantifiers: algebraic
  differencing over finite Heyting-algebras-with-a-nucleus (sound for
  PLL, linear-time on megaformula values), decider spot checks,
  fuel/budget stabilization controls.  Run with
  `lake env lean wip/<file>.lean` from the repo root.
* `stabprobe*.lean` — adversarial stabilization probes: families of
  contexts designed to make the interpolant approximants keep moving
  (gap-theorem towers, ◯/⊃ alternations).  A family whose
  approximant chain strictly descends without bound would be
  evidence AGAINST uniform interpolation for PLL; stabilization at
  small fuel is (falsifiable) evidence for it.

The policy stands: no `sorry` is ever committed to `LaxLogic/`; this
directory is the visible workbench.
