# Challenge set

Four **proved** lemmas from the development, re-stated with `sorry`. Each has a
known human proof of 6–15 lines, so a claim of success can be checked against
something real — unlike the open UI claims, which are research problems, and
unlike `../NewClaims.lean`, whose statements were invented for the purpose.

| file | from | ground truth |
|---|---|---|
| `conservativity.lean` | `LaxLogic/PLLNDCore.lean` | 14 lines |
| `conservativity_prop.lean` | `LaxLogic/PLLNDCore.lean` | 14 lines |
| `pfree_trans.lean` | `LaxLogic/LJFComplete.lean` | 15 lines |
| `focalization.lean` | `LaxLogic/LJFComplete.lean` | 6 lines |

Two further candidates (`force_circ_transparent`, `mem_gHat_shape`, both from
`FRJ/Erase.lean`) were dropped: their prefixes do not compile standalone, which
is a limitation of prefix-truncation extraction, not of the lemmas.

Each file is self-contained and compiles with exactly one `sorry`. Do not
consult the original proof before attempting one.
