import LaxLogic.PLLCountermodelEmit

/-!
# Diagram export for finite constraint countermodels

`FinCM → TikZ` and `FinCM → SVG` rendering for the countermodels of
`PLLCountermodelEmit.lean`, replacing the Python prototype that
previously lived at `docs/figures/gen_figures.py` and keeping its
visual conventions:

* worlds are drawn Hasse-style — `Rᵢ` transitively reduced, reflexive
  edges omitted, `Rᵢ`-equivalent worlds joined by a thin plain line —
  and layered by belief-set size from the bottom up;
* an edge is **solid** if the pair is also in `Rₘ` (a constraint step)
  and **dashed** if it is `Rᵢ`-only (an information step along which
  promises lapse);
* fallible worlds are filled dark; the refuting world carries a ring
  (a red double circle in TikZ); each world is labelled with its
  beliefs, and with its standing refutation promises prefixed `⊘`.

Unlike the prototype, which reconstructed the relations from
belief/promise inclusion, everything here is read off the `FinCM` data
itself (`riB`/`rmB`/`fallB`), so a frame whose `Rₘ` is genuinely
smaller than inclusion — `obsM` below — is drawn faithfully.

This is display code, outside the trust story: nothing is proved here
and nothing downstream depends on it.  The `#eval regen` at the bottom
rewrites the committed figure files under `docs/figures/`; paths are
relative to the package root, where `lake build` elaborates, and the
output is deterministic, so rebuilds are idempotent.
-/

open PLLFormula

namespace PLLND
namespace Diagram

/-! ## The Hasse skeleton of `Rᵢ` -/

/-- The strict part of `Rᵢ`: below and not above. -/
def strictRi (M : FinCM) (i j : Nat) : Bool :=
  M.riB i j && !(M.riB j i)

/-- Transitive reduction of the strict part of `Rᵢ` on worlds `< n`:
reflexive pairs are dropped, mutual (`Rᵢ`-equivalent) pairs are left to
`riEquiv`, and a pair with a third world strictly between its endpoints
is implied by transitivity, hence not drawn. -/
def hasseRi (M : FinCM) : List (Nat × Nat) :=
  let idx := List.range M.n
  idx.flatMap fun i => idx.filterMap fun j =>
    if strictRi M i j &&
       !(idx.any fun k => k != i && k != j && strictRi M i k && strictRi M k j)
    then some (i, j) else none

/-- The `Rᵢ`-equivalent pairs (mutual, non-reflexive), each listed once
with its smaller index first. -/
def riEquiv (M : FinCM) : List (Nat × Nat) :=
  let idx := List.range M.n
  idx.flatMap fun i => idx.filterMap fun j =>
    if decide (i < j) && M.riB i j && M.riB j i then some (i, j) else none

/-- The `Rₘ`-equivalent pairs, likewise: empty exactly when `Rₘ` is
antisymmetric on the worlds `< n`. -/
def rmEquiv (M : FinCM) : List (Nat × Nat) :=
  let idx := List.range M.n
  idx.flatMap fun i => idx.filterMap fun j =>
    if decide (i < j) && M.rmB i j && M.rmB j i then some (i, j) else none

/-! ## Layout -/

/-- Hasse layer of each world: the length of the longest strictly
ascending `Rᵢ`-chain ending there, by `n` relaxation rounds (the strict
part is acyclic, so this converges).  For emitted models `Rᵢ` is
belief-set inclusion, so layers track belief-set size. -/
def riLayers (M : FinCM) : List Nat :=
  let idx := List.range M.n
  (List.range M.n).foldl
    (fun L _ => idx.map fun i =>
      idx.foldl (fun acc j =>
        if strictRi M j i then max acc (L.getD j 0 + 1) else acc) 0)
    (idx.map fun _ => 0)

/-- Default layered layout, in SVG orientation (y grows downwards):
height by Hasse layer, worlds spread within a layer in index order.
Not beautiful, just non-overlapping — pass a curated `pos` to
`toTikz`/`toSvg` for the committed figures. -/
def autoPos (M : FinCM) : Nat → Int × Int :=
  let L := riLayers M
  let top := L.foldl max 0
  fun i =>
    let li := L.getD i 0
    let xi := ((List.range i).filter fun j => L.getD j 0 == li).length
    (Int.ofNat (100 + xi * 150), Int.ofNat (60 + (top - li) * 150))

/-! ## Rendering -/

/-- Hundredths, rendered with two decimal places: `280 ↦ "2.80"`. -/
private def hundredths (c : Int) : String :=
  let a := c.natAbs
  let frac := a % 100
  s!"{if c < 0 then "-" else ""}{a / 100}.{if frac < 10 then "0" else ""}{frac}"

/-- One decimal place, rounded: `157.00317 ↦ "157.0"`. -/
private def tenths (x : Float) : String :=
  let neg := x < 0
  let n := ((if neg then -x else x) * 10).round.toUInt64.toNat
  s!"{if neg then "-" else ""}{n / 10}.{n % 10}"

/-- TikZ rendering.  `pos` gives SVG-style pixel coordinates (y grows
downwards; flipped and scaled by 1/50 here, the prototype's
`scale = 0.02`); `labels` gives each world's belief and promise label,
empty for none — the belief label is suppressed on fallible worlds,
whose belief set is everything; `refut` marks the refuting world. -/
def toTikz (M : FinCM) (pos : Nat → Int × Int) (labels : Nat → String × String)
    (refut : Option Nat) : String :=
  let idx := List.range M.n
  let ymax := idx.foldl (fun a i => max a (pos i).2) 0
  let node := fun i =>
    let (x, y) := pos i
    let (lt, lp) := labels i
    let opts :=
      (if M.fallB i then ["fill=black,text=white"] else []) ++
      (if refut == some i then ["double,double distance=1.5pt,draw=red!70!black"] else []) ++
      (if lt != "" && !M.fallB i then [s!"label=above:\{\\scriptsize ${lt}$}"] else []) ++
      (if lp != "" then [s!"label=below:\{\\scriptsize $\\oslash\\,{lp}$}"] else [])
    let optsStr := if opts.isEmpty then "" else "[" ++ String.intercalate "," opts ++ "]"
    s!"  \\node{optsStr} (w{i}) at ({hundredths (2*x)},{hundredths (2*(ymax - y))}) \{$w_\{{i}}$};"
  let edge := fun (i, j) =>
    let style := if M.rmB i j then "-{Stealth}" else "-{Stealth},dashed,gray"
    s!"  \\draw[{style}] (w{i}) -- (w{j});"
  let eqLink := fun (i, j) => s!"  \\draw[thin,gray!50] (w{i}) -- (w{j});"
  String.intercalate "\n"
    ("\\begin{tikzpicture}[every node/.style={circle,draw,minimum size=9mm,inner sep=1pt}]"
      :: idx.map node ++ (hasseRi M).map edge ++ (riEquiv M).map eqLink
      ++ ["\\end{tikzpicture}"])

/-- Minimal escaping for SVG text content. -/
private def esc (s : String) : String :=
  ((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;"

/-- SVG rendering, same conventions as `toTikz` (and the same output
shape as the prototype's `svg_model`): solid `Rₘ` arrows, dashed grey
`Rᵢ`-only arrows, thin equivalence links, dark fallible nodes, a red
ring on the refuting world, beliefs printed beneath each node and
promises (`⊘`) beneath those, with a hover `<title>` per world. -/
def toSvg (M : FinCM) (pos : Nat → Int × Int) (labels : Nat → String × String)
    (refut : Option Nat) (width height : Nat) : String :=
  let idx := List.range M.n
  let nodeR : Float := 26
  let edge := fun (i, j) =>
    let (x1, y1) := pos i
    let (x2, y2) := pos j
    let dx := Float.ofInt (x2 - x1)
    let dy := Float.ofInt (y2 - y1)
    let len := Float.sqrt (dx*dx + dy*dy)
    let ux := dx / len
    let uy := dy / len
    -- shrink toward the node borders (arrowhead clears the circle)
    let x1s := Float.ofInt x1 + ux * nodeR
    let y1s := Float.ofInt y1 + uy * nodeR
    let x2s := Float.ofInt x2 - ux * (nodeR + 6)
    let y2s := Float.ofInt y2 - uy * (nodeR + 6)
    let coords := s!"x1=\"{tenths x1s}\" y1=\"{tenths y1s}\" x2=\"{tenths x2s}\" y2=\"{tenths y2s}\""
    if M.rmB i j then
      s!"<line {coords} stroke=\"#5b7c99\" stroke-width=\"2\" marker-end=\"url(#arr)\"/>"
    else
      s!"<line {coords} stroke=\"#b0b0b0\" stroke-width=\"1.6\" stroke-dasharray=\"5 4\" marker-end=\"url(#arrg)\"/>"
  let eqLink := fun (i, j) =>
    let (x1, y1) := pos i
    let (x2, y2) := pos j
    s!"<line x1=\"{x1}\" y1=\"{y1}\" x2=\"{x2}\" y2=\"{y2}\" stroke=\"#d8c9a3\" stroke-width=\"1.2\"/>"
  let node := fun i =>
    let (x, y) := pos i
    let (lt, lp) := labels i
    let filled := M.fallB i
    let fill := if filled then "#3a3a3a" else "#f7f4ec"
    let tcol := if filled then "#f7f4ec" else "#1a1a1a"
    let title := s!"w{i}: believes \{{if lt.isEmpty then "∅" else lt}}"
      ++ (if lp.isEmpty then "" else s!", promises-false \{{lp}}")
      ++ (if filled then ", fallible" else "")
    [s!"<circle cx=\"{x}\" cy=\"{y}\" r=\"26\" fill=\"{fill}\" stroke=\"#3a3a3a\" stroke-width=\"1.5\"/>"]
    ++ (if refut == some i then
        [s!"<circle cx=\"{x}\" cy=\"{y}\" r=\"31\" fill=\"none\" stroke=\"#c0392b\" stroke-width=\"2.5\"/>"]
       else [])
    ++ [s!"<text x=\"{x}\" y=\"{y+5}\" text-anchor=\"middle\" font-size=\"15\" fill=\"{tcol}\">w{i}</text>",
        s!"<text x=\"{x}\" y=\"{y+42}\" text-anchor=\"middle\" font-size=\"11.5\" fill=\"#333\">{esc lt}</text>"]
    ++ (if lp.isEmpty then [] else
        [s!"<text x=\"{x}\" y=\"{y+56}\" text-anchor=\"middle\" font-size=\"11\" fill=\"#a03030\">⊘ {esc lp}</text>"])
    ++ [s!"<title>{esc title}</title>"]
  String.intercalate "\n"
    (s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {width} {height}\" font-family=\"Georgia, serif\">"
      :: ("<defs>"
          ++ "<marker id=\"arr\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">"
          ++ "<path d=\"M0 0 L10 5 L0 10 z\" fill=\"#5b7c99\"/></marker>"
          ++ "<marker id=\"arrg\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">"
          ++ "<path d=\"M0 0 L10 5 L0 10 z\" fill=\"#b0b0b0\"/></marker></defs>")
      :: (hasseRi M).map edge ++ (riEquiv M).map eqLink ++ idx.flatMap node
      ++ ["</svg>"])

/-! ## One-call rendering

`toTikz` and `toSvg` take a layout, a labelling and a canvas size, because
the committed figures below are curated.  A countermodel that has just come
back from a search has no curation to offer, and asking for five arguments
is the reason a search result never gets drawn.  The three functions here
take the model and nothing else: layout from `autoPos`, labels read off the
valuation, canvas size from the extent of the layout.

The picture is the same one `Search.renderCM` prints in text — same
transitive reduction, same `Rₘ` arrows, same fallible marking — so the two
never disagree; this one is legible at twenty worlds, where the text form
is a wall. -/

/-- Labels read off the model itself: the atoms a world forces, `∅` when it
forces none, `⊥ (fallible)` for a fallible world.  No promise labels — a
model that has been through the simplifier has no belief-set provenance
left, and its worlds mean whatever the valuation says they mean. -/
def labelsOfVal (M : FinCM) : Nat → String × String := fun i =>
  if M.fallB i then ("⊥ (fallible)", "")
  else
    let ats := (M.val.filterMap fun p =>
      if p.1 = i then some p.2 else none).eraseDups
    (if ats.isEmpty then "∅" else String.intercalate ", " ats, "")

/-- Canvas big enough for `autoPos`: the extent of the layout plus room for
the node radius and the label under the lowest row. -/
def autoSize (M : FinCM) : Nat × Nat :=
  let idx := List.range M.n
  let mx := idx.foldl (fun a i => max a (autoPos M i).1) 0
  let my := idx.foldl (fun a i => max a (autoPos M i).2) 0
  ((mx + 120).toNat, (my + 120).toNat)

/-- **A model as an SVG**, laid out automatically and labelled from the
valuation.  `w?` rings the refuting world. -/
def svgOf (M : FinCM) (w? : Option Nat := none) : String :=
  let (width, height) := autoSize M
  toSvg M (autoPos M) (labelsOfVal M) w? width height

/-- **A model as a TikZ picture**, laid out automatically and labelled from
the valuation — the same drawing as `svgOf`, for a paper. -/
def tikzOf (M : FinCM) (w? : Option Nat := none) : String :=
  toTikz M (autoPos M) (labelsOfVal M) w?

/-- Write `svgOf M w?` to `path`, creating the directory if need be.  VS
Code previews an `.svg` on opening it, so this is the shortest route from a
countermodel to a picture of it. -/
def writeSvg (path : System.FilePath) (M : FinCM) (w? : Option Nat := none) :
    IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (svgOf M w?)

/-! ## The committed figures

Curated positions and labels for the three paper figures.  Positions
are the prototype's SVG pixel coordinates, so the regenerated files
agree with the committed ones wherever the conventions coincide. -/

private def posOf (ps : List (Int × Int)) : Nat → Int × Int :=
  fun i => ps.getD i (0, 0)

private def labelsOf (ls : List (String × String)) : Nat → String × String :=
  fun i => ls.getD i ("", "")

/-- Layout for `demoM`, the pinned `◯p ⊬ p` countermodel: the two
`Rᵢ`-equivalent belief-empty worlds at the bottom, the chain
`w₂ → w₃ → w₄` above, the fallible ceiling on top. -/
private def demoPos : List (Int × Int) :=
  [(140, 380), (330, 380), (235, 255), (235, 130), (235, 20)]

/-- Labels for `demoM`: `w₁` differs from `w₀` only by its standing
promise to refute `p` (hence also `◯p`); `w₂` is the refuting world. -/
private def demoLabels : List (String × String) :=
  [("∅", ""), ("∅", "p, ◯p"), ("◯p", ""), ("◯p, p", ""), ("⊥ (fallible)", "")]

/-- The three-world fullness-obstruction frame of
`LaxLogic/BeliefRealisability.lean` (`obsM`: `0 ≤ 1`, `0 ≤ 2`; `Rₘ`
reflexive only; `t` at both leaves, `p` only at `1`, `q` only at `2`),
duplicated here as data (this module predates the 2026-07-18 promotion,
which made `obsM` importable).
With `Rₘ` reflexive only, both Hasse edges are information steps and
are drawn dashed — the prototype drew them solid because it derived
`Rₘ` from inclusion instead of reading the frame. -/
private def obsM : FinCM :=
  { n := 3, ri := [(0, 1), (0, 2)], rm := [], fall := [],
    val := [(1, "p"), (2, "q"), (1, "t"), (2, "t")] }

private def obsPos : List (Int × Int) := [(210, 240), (100, 90), (320, 90)]

private def obsLabels : List (String × String) :=
  [("∅", ""), ("p, t", ""), ("q, t", "")]

/-- Compact formula rendering for figure labels (no spaces, in the
prototype's style). -/
private def fmtc : PLLFormula → String
  | .prop a => a
  | .falsePLL => "⊥"
  | .and A B => s!"({fmtc A}∧{fmtc B})"
  | .or A B => s!"({fmtc A}∨{fmtc B})"
  | .ifThen A B => s!"({fmtc A}→{fmtc B})"
  | .somehow A => s!"◯{fmtc A}"

/-- `fmtc` with the outermost parentheses dropped. -/
private def fmtTop : PLLFormula → String
  | .and A B => s!"{fmtc A}∧{fmtc B}"
  | .or A B => s!"{fmtc A}∨{fmtc B}"
  | .ifThen A B => s!"{fmtc A}→{fmtc B}"
  | φ => fmtc φ

/-- Characteristic belief label for the `∨`-distribution model: the
most informative members of the belief set, in the prototype's key
order. -/
private def shortT (T : List PLLFormula) : String :=
  if decide (PLLFormula.falsePLL ∈ T) then "⊥ (fallible)"
  else
    let keys := [prop "p", prop "q", (prop "p").somehow, (prop "q").somehow,
                 ((prop "p").or (prop "q")).somehow]
    let ks := keys.filter fun k => decide (k ∈ T)
    if ks.isEmpty then "∅" else String.intercalate ", " (ks.map fmtTop)

/-- Layout for the 20-world `∨`-distribution countermodel
(`◯(p∨q) ⊬ ◯p ∨ ◯q`), indices in emission order: the belief-empty
worlds at the bottom (the all-promising `w₃` below them), the refuting
`◯(p∨q)`-world above, then the `◯`-disjunct layers, the `p`/`q` prime
layers, and the fallible ceiling. -/
private def ordistPos : List (Int × Int) :=
  [(430, 900), (240, 900), (620, 900), (430, 980),
   (430, 760), (250, 760), (610, 760),
   (260, 610), (120, 610), (600, 610), (740, 610),
   (430, 540),
   (240, 420), (100, 420), (310, 290), (620, 420), (760, 420), (550, 290),
   (430, 170), (430, 50)]

/-- Regenerate the committed figure files under `docs/figures/`:
`demoM` and `obsM` from pinned data, `ordist20` from a fresh run of the
emitter on `◯(p∨q) ⊢ ◯p ∨ ◯q`, with world labels read off the emitted
`(T, P)` states. -/
def regen : IO Unit := do
  IO.FS.createDirAll "docs/figures"
  let write (name : String) (tikz svg : String) : IO Unit := do
    IO.FS.writeFile s!"docs/figures/{name}.tikz" tikz
    IO.FS.writeFile s!"docs/figures/{name}.svg" svg
  write "demoM"
    (toTikz demoM (posOf demoPos) (labelsOf demoLabels) (some 2))
    (toSvg demoM (posOf demoPos) (labelsOf demoLabels) (some 2) 470 470)
  write "obsM"
    (toTikz obsM (posOf obsPos) (labelsOf obsLabels) none)
    (toSvg obsM (posOf obsPos) (labelsOf obsLabels) none 420 320)
  let Γ := [((prop "p").or (prop "q")).somehow]
  let C := ((prop "p").somehow).or ((prop "q").somehow)
  match CounterEmit.emit Γ C with
  | some (M, w) =>
      let (_, ws) := CounterEmit.build Γ C
      let labs := fun i => match ws[i]? with
        | some (T, P) => (shortT T, String.intercalate ", " (P.map fmtTop))
        | none => ("", "")
      write "ordist20"
        (toTikz M (posOf ordistPos) labs (some w))
        (toSvg M (posOf ordistPos) labs (some w) 880 1040)
      match CounterEmit.emitMinClean Γ C with
      | some (Mc, wc) =>
          let labsC := labelsOf [("∅", ""), ("p", ""), ("q", "")]
          write "ordist3clean"
            (toTikz Mc (posOf obsPos) labsC (some wc))
            (toSvg Mc (posOf obsPos) labsC (some wc) 420 320)
          IO.println s!"figures regenerated: demoM, obsM, ordist20 ({M.n} worlds, refuting w{w}), ordist3clean ({Mc.n} worlds, refuting w{wc})"
      | none => throw <| IO.userError "ordist3clean: emitMinClean returned none"
  | none => throw <| IO.userError "ordist20: emitter returned none"

/-! ## Pinned display invariants of the demo model -/

#guard hasseRi demoM = [(0, 2), (1, 2), (2, 3), (3, 4)]
#guard riEquiv demoM = [(0, 1)]
#guard riLayers demoM = [0, 0, 1, 2, 3]
#guard autoPos demoM 1 = (250, 510)

/-! ### The order profile: `Rᵢ` a preorder, `Rₘ` a partial order

Canonical and emitted `Rᵢ` compares beliefs only, so same-belief worlds
differing in their standing promises are mutually related: `Rᵢ` is a
genuine preorder, not a poset.  `Rₘ` carries promises along and is
antisymmetric in all the models here.  Minimisation removes the
`Rᵢ`-equivalent twins by deletion rather than quotienting, so the
minimised models are posets.  (Discussion: the paper draft, §7.) -/

#guard rmEquiv demoM = []

-- The 20-world ∨-distribution model: thirteen `Rᵢ`-equivalent pairs —
-- the refuting world w4 and its two promise-bound critical futures
-- w5, w6 form one class, so the refutation of `◯(p∨q) ⊢ ◯p ∨ ◯q` is
-- transacted entirely inside a single `Rᵢ`-equivalence class — and no
-- `Rₘ`-equivalent pair.
/-- info: some ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (4, 5), (4, 6), (5, 6), (7, 8), (9, 10), (12, 13), (15, 16)], []) -/
#guard_msgs in
#eval (CounterEmit.emit [((prop "p").or (prop "q")).somehow]
  (((prop "p").somehow).or ((prop "q").somehow))).map
    fun (M, _) => (riEquiv M, rmEquiv M)

-- …and both minimised models are partial orders: no equivalent pairs.
/-- info: (some [], some []) -/
#guard_msgs in
#eval ((CounterEmit.emitMinClean [((prop "p").or (prop "q")).somehow]
    (((prop "p").somehow).or ((prop "q").somehow))).map fun (M, _) => riEquiv M,
  (CounterEmit.emitMinClean [(prop "p").somehow] (prop "p")).map
    fun (M, _) => riEquiv M)

#eval regen

end Diagram
end PLLND
