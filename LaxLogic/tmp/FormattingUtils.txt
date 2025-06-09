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
      (str.drop 1).dropRight 1
    else
      str

def addParens (f : String) : String :=  "(" ++ f ++  ")"

def getReprFn {α : Type u} (toStringFn : α  → String) : α -> Nat -> Std.Format :=
    fun (a:α)(_:Nat) =>
      Format.text (toStringFn a)
