
functor catpartLrValsFun (structure Token : TOKEN
			           structure Absyn : ABSYN ) : catpart_LRVALS = 
struct
structure ParserData=
struct
structure Header = 
struct
(* catpart_val.grm : 
 This file describes the grammar of the test specification language
 for category partition testing, and defines the result
 of parsing specifications by giving an abstract value to each
 parsed terminal or non-terminal *)

(* This is what I want to do but I suspect ML won't let me:

   type Categ  = {param_name: string, choices: Choice list}
   type Choice = {ch_name: string, maybe_cond: Cond Option,
	          maybe_property: string list Option,
		  maybe_flag: Flag Option}
*)

open Absyn;
type result = result
type 'a Option = 'a Option


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\004\000\000\000\000\000\
\\001\000\003\000\006\000\000\000\
\\001\000\003\000\012\000\000\000\
\\001\000\004\000\013\000\000\000\
\\001\000\005\000\008\000\000\000\
\\001\000\005\000\014\000\000\000\
\\001\000\005\000\015\000\000\000\
\\001\000\005\000\022\000\000\000\
\\001\000\005\000\031\000\000\000\
\\001\000\006\000\007\000\000\000\
\\001\000\006\000\021\000\000\000\
\\001\000\006\000\028\000\000\000\
\\001\000\006\000\042\000\000\000\
\\001\000\006\000\042\000\014\000\041\000\019\000\040\000\000\000\
\\001\000\007\000\025\000\000\000\
\\001\000\008\000\036\000\009\000\035\000\000\000\
\\001\000\008\000\036\000\009\000\035\000\010\000\034\000\011\000\033\000\000\000\
\\001\000\008\000\036\000\009\000\035\000\010\000\056\000\000\000\
\\001\000\012\000\059\000\013\000\058\000\000\000\
\\001\000\015\000\005\000\000\000\
\\001\000\016\000\011\000\000\000\
\\001\000\019\000\047\000\000\000\
\\001\000\019\000\064\000\000\000\
\\001\000\020\000\051\000\000\000\
\\001\000\020\000\060\000\000\000\
\\001\000\020\000\069\000\000\000\
\\001\000\022\000\037\000\000\000\
\\001\000\022\000\045\000\000\000\
\\001\000\022\000\048\000\000\000\
\\001\000\022\000\062\000\000\000\
\\001\000\022\000\065\000\000\000\
\\001\000\022\000\066\000\000\000\
\\001\000\022\000\071\000\000\000\
\\073\000\000\000\
\\074\000\002\000\004\000\000\000\
\\075\000\000\000\
\\076\000\000\000\
\\077\000\017\000\010\000\000\000\
\\078\000\000\000\
\\079\000\023\000\018\000\000\000\
\\080\000\000\000\
\\081\000\000\000\
\\082\000\007\000\025\000\000\000\
\\083\000\000\000\
\\084\000\000\000\
\\085\000\000\000\
\\086\000\000\000\
\\087\000\021\000\068\000\000\000\
\\088\000\000\000\
\\089\000\021\000\050\000\000\000\
\\090\000\000\000\
\\091\000\021\000\053\000\000\000\
\\092\000\000\000\
\\093\000\021\000\030\000\000\000\
\\094\000\000\000\
\\095\000\000\000\
\\096\000\000\000\
\\097\000\000\000\
\\098\000\000\000\
\\099\000\018\000\049\000\000\000\
\\100\000\000\000\
\\101\000\000\000\
\\102\000\000\000\
\\103\000\000\000\
\"
val actionRowNumbers =
"\034\000\033\000\019\000\001\000\
\\009\000\004\000\037\000\020\000\
\\002\000\003\000\005\000\006\000\
\\039\000\035\000\039\000\036\000\
\\010\000\038\000\007\000\041\000\
\\014\000\042\000\040\000\011\000\
\\043\000\053\000\045\000\008\000\
\\016\000\044\000\026\000\013\000\
\\012\000\062\000\063\000\052\000\
\\054\000\027\000\013\000\021\000\
\\061\000\028\000\059\000\049\000\
\\023\000\013\000\051\000\012\000\
\\017\000\018\000\024\000\015\000\
\\060\000\029\000\012\000\022\000\
\\057\000\058\000\055\000\030\000\
\\048\000\031\000\013\000\050\000\
\\047\000\025\000\015\000\056\000\
\\032\000\046\000\000\000"
val gotoT =
"\
\\001\000\070\000\002\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\007\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\015\000\005\000\014\000\000\000\
\\000\000\
\\004\000\017\000\005\000\014\000\000\000\
\\000\000\
\\006\000\018\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\022\000\008\000\021\000\000\000\
\\007\000\024\000\008\000\021\000\000\000\
\\000\000\
\\009\000\025\000\000\000\
\\000\000\
\\010\000\027\000\000\000\
\\000\000\
\\000\000\
\\015\000\030\000\000\000\
\\000\000\
\\000\000\
\\011\000\037\000\012\000\036\000\000\000\
\\012\000\042\000\014\000\041\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\044\000\012\000\036\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\050\000\012\000\036\000\000\000\
\\000\000\
\\012\000\042\000\014\000\052\000\000\000\
\\015\000\053\000\000\000\
\\013\000\055\000\000\000\
\\000\000\
\\015\000\059\000\000\000\
\\000\000\
\\000\000\
\\012\000\042\000\014\000\061\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\065\000\012\000\036\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\015\000\068\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 71
val numrules = 31
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | NUMBER of  (int)
 | VAR of  (string) | CAP of  (string) | flag of  (Flag)
 | properties of  (string list) | log_op of  (Binop)
 | property of  (string) | cond of  (Cond)
 | maybe_modifiers of  (Modifiers) | ch_name of  (string)
 | choice of  (Choice) | choices of  (Choice list)
 | categ_name of  (string) | one_categ of  (Categ)
 | categs of  (Categ list) | categ_specs of  (Categ list)
 | func_spec of  (catpart) | start of  (catpart Option)
end
type svalue = MlyValue.svalue
type result = catpart Option
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "CAP"
  | (T 2) => "COLON"
  | (T 3) => "SEMICOLON"
  | (T 4) => "NEWLINE"
  | (T 5) => "VAR"
  | (T 6) => "STAR"
  | (T 7) => "SINGLE"
  | (T 8) => "ERROR"
  | (T 9) => "PROPERTY"
  | (T 10) => "IF"
  | (T 11) => "OR"
  | (T 12) => "AND"
  | (T 13) => "NOT"
  | (T 14) => "FUN"
  | (T 15) => "ENDFUN"
  | (T 16) => "CATEGORIES"
  | (T 17) => "COMMA"
  | (T 18) => "LRBR"
  | (T 19) => "RRBR"
  | (T 20) => "LSQBR"
  | (T 21) => "RSQBR"
  | (T 22) => "NUMBER"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn (T 5) => MlyValue.VAR(("a")) | 
(T 22) => MlyValue.NUMBER((0)) | 
_ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 17) $$ (T 16) $$ (T 15)
 $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8)
 $$ (T 7) $$ (T 6) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.func_spec func_spec, func_spec1left, 
func_spec1right)) :: rest671)) => let val  result = MlyValue.start (
Some func_spec)
 in ( LrTable.NT 0, ( result, func_spec1left, func_spec1right), 
rest671)
end
|  ( 1, ( rest671)) => let val  result = MlyValue.start (None)
 in ( LrTable.NT 0, ( result, defaultPos, defaultPos), rest671)
end
|  ( 2, ( ( _, ( _, _, NEWLINE2right)) :: _ :: _ :: ( _, ( 
MlyValue.categ_specs categ_specs, _, _)) :: _ :: ( _, ( MlyValue.VAR 
VAR, _, _)) :: _ :: _ :: ( _, ( MlyValue.CAP CAP, CAP1left, _)) :: 
rest671)) => let val  result = MlyValue.func_spec (
F{fun_letter=CAP, fun_name=VAR, categ_specs=categ_specs})
 in ( LrTable.NT 1, ( result, CAP1left, NEWLINE2right), rest671)
end
|  ( 3, ( ( _, ( MlyValue.categs categs, _, categs1right)) :: _ :: _
 :: ( _, ( _, CATEGORIES1left, _)) :: rest671)) => let val  result = 
MlyValue.categ_specs (categs)
 in ( LrTable.NT 2, ( result, CATEGORIES1left, categs1right), rest671)

end
|  ( 4, ( rest671)) => let val  result = MlyValue.categ_specs ([])
 in ( LrTable.NT 2, ( result, defaultPos, defaultPos), rest671)
end
|  ( 5, ( ( _, ( MlyValue.categs categs, _, categs1right)) :: ( _, ( 
MlyValue.one_categ one_categ, one_categ1left, _)) :: rest671)) => let
 val  result = MlyValue.categs (one_categ :: categs)
 in ( LrTable.NT 3, ( result, one_categ1left, categs1right), rest671)

end
|  ( 6, ( rest671)) => let val  result = MlyValue.categs ([])
 in ( LrTable.NT 3, ( result, defaultPos, defaultPos), rest671)
end
|  ( 7, ( ( _, ( MlyValue.choices choices, _, choices1right)) :: _ :: 
( _, ( MlyValue.categ_name categ_name, _, _)) :: ( _, ( 
MlyValue.NUMBER NUMBER, NUMBER1left, _)) :: rest671)) => let val  
result = MlyValue.one_categ (
Cat{categ_no=NUMBER, categ_name=categ_name, choices=choices})
 in ( LrTable.NT 4, ( result, NUMBER1left, choices1right), rest671)

end
|  ( 8, ( ( _, ( MlyValue.VAR VAR, VAR1left, VAR1right)) :: rest671))
 => let val  result = MlyValue.categ_name (VAR)
 in ( LrTable.NT 5, ( result, VAR1left, VAR1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.choice choice, choice1left, choice1right))
 :: rest671)) => let val  result = MlyValue.choices ([choice])
 in ( LrTable.NT 6, ( result, choice1left, choice1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.choices choices, _, choices1right)) :: ( _,
 ( MlyValue.choice choice, choice1left, _)) :: rest671)) => let val  
result = MlyValue.choices (choice :: choices)
 in ( LrTable.NT 6, ( result, choice1left, choices1right), rest671)

end
|  ( 11, ( ( _, ( _, _, NEWLINE1right)) :: ( _, ( 
MlyValue.maybe_modifiers maybe_modifiers, _, _)) :: ( _, ( 
MlyValue.ch_name ch_name, _, _)) :: ( _, ( _, STAR1left, _)) :: 
rest671)) => let val  result = MlyValue.choice (
Ch{ch_name=ch_name,maybe_modifiers=maybe_modifiers})
 in ( LrTable.NT 7, ( result, STAR1left, NEWLINE1right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.VAR VAR, VAR1left, VAR1right)) :: rest671))
 => let val  result = MlyValue.ch_name (VAR)
 in ( LrTable.NT 8, ( result, VAR1left, VAR1right), rest671)
end
|  ( 13, ( ( _, ( _, _, RSQBR3right)) :: ( _, ( MlyValue.flag flag, _,
 _)) :: _ :: _ :: ( _, ( MlyValue.properties properties, _, _)) :: _
 :: _ :: _ :: ( _, ( MlyValue.cond cond, _, _)) :: _ :: ( _, ( _, 
LSQBR1left, _)) :: rest671)) => let val  result = 
MlyValue.maybe_modifiers (
M{maybe_cond=Some cond,
       maybe_properties=Some properties,
       maybe_flag=Some flag}
)
 in ( LrTable.NT 9, ( result, LSQBR1left, RSQBR3right), rest671)
end
|  ( 14, ( ( _, ( _, _, RSQBR2right)) :: ( _, ( MlyValue.properties 
properties, _, _)) :: _ :: _ :: _ :: ( _, ( MlyValue.cond cond, _, _))
 :: _ :: ( _, ( _, LSQBR1left, _)) :: rest671)) => let val  result = 
MlyValue.maybe_modifiers (
M{maybe_cond=Some cond,
       maybe_properties=Some properties,
       maybe_flag=None}
)
 in ( LrTable.NT 9, ( result, LSQBR1left, RSQBR2right), rest671)
end
|  ( 15, ( ( _, ( _, _, RSQBR2right)) :: ( _, ( MlyValue.flag flag, _,
 _)) :: _ :: _ :: ( _, ( MlyValue.cond cond, _, _)) :: _ :: ( _, ( _, 
LSQBR1left, _)) :: rest671)) => let val  result = 
MlyValue.maybe_modifiers (
M{maybe_cond=Some cond,
       maybe_properties=None,
       maybe_flag=Some flag}
)
 in ( LrTable.NT 9, ( result, LSQBR1left, RSQBR2right), rest671)
end
|  ( 16, ( ( _, ( _, _, RSQBR1right)) :: ( _, ( MlyValue.cond cond, _,
 _)) :: _ :: ( _, ( _, LSQBR1left, _)) :: rest671)) => let val  result
 = MlyValue.maybe_modifiers (
M{maybe_cond=Some cond,
       maybe_properties=None,
       maybe_flag=None}
)
 in ( LrTable.NT 9, ( result, LSQBR1left, RSQBR1right), rest671)
end
|  ( 17, ( ( _, ( _, _, RSQBR2right)) :: ( _, ( MlyValue.flag flag, _,
 _)) :: _ :: _ :: ( _, ( MlyValue.properties properties, _, _)) :: _
 :: ( _, ( _, LSQBR1left, _)) :: rest671)) => let val  result = 
MlyValue.maybe_modifiers (
M{maybe_cond=None,
       maybe_properties=Some properties,
       maybe_flag=Some flag}
)
 in ( LrTable.NT 9, ( result, LSQBR1left, RSQBR2right), rest671)
end
|  ( 18, ( ( _, ( _, _, RSQBR1right)) :: ( _, ( MlyValue.properties 
properties, _, _)) :: _ :: ( _, ( _, LSQBR1left, _)) :: rest671)) =>
 let val  result = MlyValue.maybe_modifiers (
M{maybe_cond=None,
       maybe_properties=Some properties,
       maybe_flag=None}
)
 in ( LrTable.NT 9, ( result, LSQBR1left, RSQBR1right), rest671)
end
|  ( 19, ( ( _, ( _, _, RSQBR1right)) :: ( _, ( MlyValue.flag flag, _,
 _)) :: ( _, ( _, LSQBR1left, _)) :: rest671)) => let val  result = 
MlyValue.maybe_modifiers (
M{maybe_cond=None,
       maybe_properties=None,
       maybe_flag=Some flag}
)
 in ( LrTable.NT 9, ( result, LSQBR1left, RSQBR1right), rest671)
end
|  ( 20, ( rest671)) => let val  result = MlyValue.maybe_modifiers (
M{maybe_cond=None,
       maybe_properties=None,
       maybe_flag=None}
)
 in ( LrTable.NT 9, ( result, defaultPos, defaultPos), rest671)
end
|  ( 21, ( ( _, ( MlyValue.property property, property1left, 
property1right)) :: rest671)) => let val  result = MlyValue.cond (
Prop property)
 in ( LrTable.NT 10, ( result, property1left, property1right), rest671
)
end
|  ( 22, ( ( _, ( _, _, RRBR1right)) :: ( _, ( MlyValue.cond cond, _,
 _)) :: _ :: ( _, ( _, NOT1left, _)) :: rest671)) => let val  result =
 MlyValue.cond (Not cond)
 in ( LrTable.NT 10, ( result, NOT1left, RRBR1right), rest671)
end
|  ( 23, ( ( _, ( _, _, RRBR2right)) :: ( _, ( MlyValue.cond cond2, _,
 _)) :: _ :: ( _, ( MlyValue.log_op log_op, _, _)) :: _ :: ( _, ( 
MlyValue.cond cond1, _, _)) :: ( _, ( _, LRBR1left, _)) :: rest671))
 => let val  result = MlyValue.cond (Binary(log_op, cond1, cond2))
 in ( LrTable.NT 10, ( result, LRBR1left, RRBR2right), rest671)
end
|  ( 24, ( ( _, ( _, AND1left, AND1right)) :: rest671)) => let val  
result = MlyValue.log_op (And)
 in ( LrTable.NT 12, ( result, AND1left, AND1right), rest671)
end
|  ( 25, ( ( _, ( _, OR1left, OR1right)) :: rest671)) => let val  
result = MlyValue.log_op (Or)
 in ( LrTable.NT 12, ( result, OR1left, OR1right), rest671)
end
|  ( 26, ( ( _, ( MlyValue.property property, property1left, 
property1right)) :: rest671)) => let val  result = MlyValue.properties
 ([property])
 in ( LrTable.NT 13, ( result, property1left, property1right), rest671
)
end
|  ( 27, ( ( _, ( MlyValue.properties properties, _, properties1right)
) :: _ :: ( _, ( MlyValue.property property, property1left, _)) :: 
rest671)) => let val  result = MlyValue.properties (
property :: properties)
 in ( LrTable.NT 13, ( result, property1left, properties1right), 
rest671)
end
|  ( 28, ( ( _, ( MlyValue.VAR VAR, VAR1left, VAR1right)) :: rest671))
 => let val  result = MlyValue.property (VAR)
 in ( LrTable.NT 11, ( result, VAR1left, VAR1right), rest671)
end
|  ( 29, ( ( _, ( _, ERROR1left, ERROR1right)) :: rest671)) => let
 val  result = MlyValue.flag (Error)
 in ( LrTable.NT 14, ( result, ERROR1left, ERROR1right), rest671)
end
|  ( 30, ( ( _, ( _, SINGLE1left, SINGLE1right)) :: rest671)) => let
 val  result = MlyValue.flag (Single)
 in ( LrTable.NT 14, ( result, SINGLE1left, SINGLE1right), rest671)

end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.start x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : catpart_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun CAP (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.CAP i,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun SEMICOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun NEWLINE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun VAR (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VAR i,p1,p2))
fun STAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun SINGLE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun ERROR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun PROPERTY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun OR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun NOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun FUN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun ENDFUN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun CATEGORIES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun LRBR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun RRBR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun LSQBR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun RSQBR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun NUMBER (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.NUMBER i,p1,p2))
end
end
