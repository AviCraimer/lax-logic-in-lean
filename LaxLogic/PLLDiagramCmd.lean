import LaxLogic.PLLSearchCmd
import LaxLogic.PLLDiagram

/-!
# `#draw` — a countermodel as a picture, in one command

`LaxLogic/PLLDiagram.lean` renders a `FinCM` as SVG or TikZ, and
`LaxLogic/PLLSearchCmd.lean` finds one; this module is the join.

```lean
import LaxLogic.PLLDiagramCmd
open PLLFormula PLLND PLLND.Search

#draw [] ⊢ ((prop "p").somehow).ifThen (prop "p") to "docs/figures/esc.svg"
```

searches for a countermodel exactly as `#refute` does — same staging, same
simplification, same certificate — and writes an SVG of the model it found,
printing the path and a one-line summary.  Open the file in VS Code (it
previews `.svg` on opening) and the model is a picture: worlds as circles
labelled with the atoms they force, solid arrows for `Rₘ`, dashed grey for
information-only `Rᵢ` steps, a dark disc for a fallible world, a red ring on
the refuting world.

The drawing and the text picture of `#refute` are the same data: both use
the transitive reduction of `Rᵢ` and read `Rₘ` off the model.  Use `#refute`
to read a small model, `#draw` when there are enough worlds that the text
form stops being a picture.

A configuration goes after `with`, as for the other commands; the PCLL form
is `with (PLLND.RNC.confluentConfig)`, which draws only mutually confluent
models.

**This command writes a file when the line elaborates**, like the `#eval
regen` of `PLLDiagram.lean`.  It is deterministic (same sequent, same model,
same bytes), so a drawing committed under `docs/figures/` stays clean across
rebuilds.
-/

open PLLFormula

namespace PLLND.Search

/-- Find a countermodel for `Γ ⊢ C` and write it to `path` as an SVG,
returning the line `#draw` prints.  `none` from the search is reported, not
raised: an absent countermodel is an absence of information (both negative
engines are incomplete), not an error. -/
def drawReport (cfg : Config) (Γ : List PLLFormula) (C : PLLFormula)
    (path : String) : IO String :=
  match countermodel Γ C cfg with
  | some wit => do
      Diagram.writeSvg path wit.1 (some wit.2.1)
      pure <| String.intercalate "\n"
        ([ s!"sequent  {seqStr Γ C}",
           s!"verdict  REFUTED  {summaryCM wit.1 wit.2.1}" ] ++
         scopeLines wit.1 ++
         [ s!"drawing  {path}" ])
  | none =>
      pure <| String.intercalate "\n"
        [ s!"sequent  {seqStr Γ C}",
          "verdict  NO COUNTERMODEL FOUND",
          "",
          "Nothing drawn, and nothing asserted: the battery and the closure \
emitter",
          "are both incomplete.  Widen Config.frames, or raise \
Config.emitClosureCap." ]

end PLLND.Search

/-- `#draw Γ ⊢ C to "path.svg"` — search for a countermodel as `#refute`
does, write it to `path` as an SVG, and print the verdict, the scope and the
path.  Append `with cfg` for a `Search.Config`. -/
macro (name := drawCmd) "#draw " Γ:term " ⊢ " C:term " to " path:term :
    command =>
  `(command| #eval (do
      IO.println (← PLLND.Search.drawReport PLLND.Search.budgetedConfig
        $Γ $C $path) : IO Unit))

@[inherit_doc drawCmd]
macro "#draw " Γ:term " ⊢ " C:term " to " path:term " with " cfg:term :
    command =>
  `(command| #eval (do
      IO.println (← PLLND.Search.drawReport $cfg $Γ $C $path) : IO Unit))
