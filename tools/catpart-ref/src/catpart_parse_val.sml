(* catpart_parse_val.sml : uses the generated lexer and parser to export
   parsing functions *)

signature PARSE =
sig

structure Absyn : ABSYN

(* parse a program in a file *)

    val file_parse : string -> Absyn.result

(* parse a program from a string *)

    val string_parse : string -> Absyn.result

(* parse a program from the standard input *)

    val top_parse : unit -> Absyn.result

(* print the result *)

    val print_result : Absyn.result -> unit
	
end  (* signature PARSE *)

functor ParseFun (structure Absyn : ABSYN
	       structure Interface : INTERFACE
	       structure Parser : PARSER
	          sharing type Parser.arg = Interface.arg
	          sharing type Parser.pos = Interface.pos
		  sharing type Parser.result = Absyn.result
	       structure Tokens : catpart_TOKENS
	          sharing type Tokens.token = Parser.Token.token
		  sharing type Tokens.svalue = Parser.svalue
               ) : PARSE =
struct

structure Absyn = Absyn

val parse = fn (lookahead,reader : int -> string) =>
    let val _ = Interface.init_line()
	val empty = !Interface.line
	val dummyEOF = Tokens.EOF(empty,empty)
	fun invoke lexer = 
	   Parser.parse(lookahead,lexer,Interface.error,
				Interface.nothing)
        fun loop lexer =
	  let val (result,lexer) = invoke lexer
	      val (nextToken,lexer) = Parser.Stream.get lexer
	  in if Parser.sameToken(nextToken,dummyEOF) then result
	     else loop lexer
	  end
     in loop (Parser.makeLexer reader)
     end

val file_parse = fn name =>
  let val dev = open_in name
   in (parse (15,fn i => input(dev,i))) before close_in dev
   end

fun string_reader s =
 let val next = ref s
 in fn _ => !next before next := ""
 end
    
val string_parse = fn s => parse (15,string_reader s)

val top_parse = 
fn () =>
      parse (0,fn i => input_line std_in)

val print_result = Absyn.print_result

end  (* functor Parse *)
