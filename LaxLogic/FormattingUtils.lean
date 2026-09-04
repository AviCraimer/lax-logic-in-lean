universe u

open Std (Format)

-- If a
def stripParens {α : Type u}
    (toStringFn : α  → String) (parenLeft: Char := '(')  (parenRight: Char := ')') :
    α  → String :=
  fun (a:α) =>
    let str  : String  := toStringFn a
    if str.length ≥ 2 && str.front == parenLeft && str.back == parenRight then
      -- drop the first and last character
      -- (Lean ≥4.31: `String.drop`/`String.Slice.dropEnd` return `String.Slice`;
      -- `.dropRight` is deprecated in favour of `.dropEnd`, and we convert back
      -- to `String` at the end since `stripParens : α → String`.)
      ((str.drop 1).dropEnd 1).toString
    else
      str

def addParens (f : String) : String :=  "(" ++ f ++  ")"

def getReprFn {α : Type u} (toStringFn : α  → String) : α -> Nat -> Std.Format :=
    fun (a:α)(_:Nat) =>
      Format.text (toStringFn a)
