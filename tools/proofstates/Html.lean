/-
# Self-contained HTML emission

The viewer lives in `viewer.html` next to this file and is embedded at compile
time with `include_str`, so the built executable needs no data files, and the
page it writes needs no server, no network and no separate JSON file.  The
template carries one marker, `"__PSTATES_DATA__"`, inside a
`<script type="application/json">` element; we substitute the record for it.

**Build gotcha.**  `include_str` reads the file during elaboration but does not
register it as a build dependency, and Lake decides what to rebuild from the
*content hash* of the `.lean` sources.  Editing `viewer.html` alone therefore
does not trigger a rebuild, and `touch`ing this file does not either.  Either
pass `--template tools/proofstates/viewer.html` at run time — which bypasses
the embedded copy and is the way to develop the viewer — or force the rebuild:

    rm -f .lake/build/lib/lean/tools/proofstates/Html.olean \
          .lake/build/lib/lean/tools/proofstates/Html.trace
    lake build pstates
-/
import tools.proofstates.Recorder

open Lean

namespace ProofStates

/-- The viewer template: inline CSS + JS, no external references. -/
def viewerTemplate : String := include_str "viewer.html"

/-- The one place a JSON payload can break out of a `<script>` element is the
literal `</`.  `\/` is a legal JSON escape, so this is safe and lossless. -/
def escapeForScript (s : String) : String :=
  s.replace "</" "<\\/"

/-- Substitute `s` for the first occurrence of `marker` in `tpl`. -/
def substituteOnce (tpl marker s : String) : String :=
  match tpl.splitOn marker with
  | []      => tpl
  | [_]     => tpl
  | a :: rest => a ++ s ++ String.intercalate marker rest

def renderHtmlWith (tpl : String) (r : Record) : String :=
  let payload := escapeForScript (Json.compress r.toJson)
  let title := s!"proof states — {r.file}" ++
    (if r.declPat.isEmpty then "" else s!" — {r.declPat}")
  substituteOnce (substituteOnce tpl "__PSTATES_DATA__" payload)
    "__PSTATES_TITLE__" (title.replace "<" "&lt;" |>.replace ">" "&gt;")

def renderHtml (r : Record) : String := renderHtmlWith viewerTemplate r

end ProofStates
