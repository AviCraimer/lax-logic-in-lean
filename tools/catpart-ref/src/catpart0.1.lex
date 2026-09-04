(* catpart0.1.lex : sample lexer for catpart *)

structure Tokens = Tokens
structure Interface = Interface
open Interface
open Tokens

type pos = Interface.pos
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val eof = fn () => Tokens.EOF(!line,!line)
val table = [("single", SINGLE),
		 ("error", ERROR),
		 ("property", PROPERTY),
		 ("if", IF),
		 ("and", AND),
		 ("or", OR),
		 ("not", NOT),
		 ("Function", FUN),
		 ("EndFunction", ENDFUN),
		 ("Categories", CATEGORIES)
		  ]

exception Nonkey of string

val find : string -> (pos * pos -> (svalue,pos) token) option
         = fn s => 
let 
    fun lkp ([], t) = NONE
      | lkp ((u,v) :: pairs, t) = if u=t then SOME v else lkp (pairs, t)
    in  lkp (table, s)
end;

%%
%header (functor catpartLexFun(structure Tokens: catpart_TOKENS
			    structure Interface: INTERFACE) : LEXER);
%s MAIN COMMENT CHOICE ;
ws=[\t\ ];
capital=[A-Z];
lower=[a-z];
digit=[0-9];
newline=\n;
space=" ";
alpha={capital}|{lower};
alphanum={alpha}|{digit};
alphanumsy={alphanum}|"_"|"'";
alphanumsyb={alphanumsy}|" ";
var={alphanum}{alphanumsy}*;
chvar={alphanum}{alphanumsyb}*;
%%
<INITIAL>{capital}{ws}
                    => (CAP(hd(explode yytext),!line,!line));
<INITIAL>Function   => (YYBEGIN MAIN; FUN(!line,!line));
<INITIAL>{ws}+	    => (lex());
<INITIAL>{newline}  => (next_line(); lex());
<INITIAL>.	    => (error ("ignoring illegal character" ^ yytext,
			   !line,!line); lex());
<MAIN>\:            => (COLON(!line,!line));
<MAIN>{newline}     => (next_line(); NEWLINE(!line,!line));
<MAIN>\;	    => (SEMICOLON(!line,!line));
<MAIN>{digit}+      => (NUMBER
			  (List.fold (fn (a,r) => ord(a)-ord("0")+10*r)
				      (rev(explode yytext)) 0,
			   !line,!line));
<MAIN>{var}         => (case find yytext of SOME v => v(!line,!line)
		        | NONE => VAR(yytext,!line,!line));
<MAIN>\*{space}*    => (YYBEGIN CHOICE; STAR(!line,!line));  
<MAIN>\,	    => (COMMA(!line,!line));
<MAIN>\(	    => (LRBR(!line,!line));
<MAIN>\)	    => (RRBR(!line,!line));
<MAIN>\[	    => (LSQBR(!line,!line));
<MAIN>\]	    => (RSQBR(!line,!line));
<MAIN>\{	    => (YYBEGIN COMMENT; lex());
<MAIN>{ws}+	    => (lex());
<MAIN>.	            => (error ("ignoring illegal character" ^ yytext,
			   !line,!line); lex());
<CHOICE>\[          => (YYBEGIN MAIN; LSQBR(!line,!line));
<CHOICE>{newline}   => (YYBEGIN MAIN; NEWLINE(!line,!line));
<CHOICE>{chvar}     => (case find yytext of SOME v => v(!line,!line)
		        | NONE => VAR(yytext,!line,!line));
<CHOICE>{ws}+	    => (lex());
<CHOICE>.	    => (error ("ignoring illegal character" ^ yytext,
			   !line,!line); lex());
<COMMENT>{newline}  => (next_line(); lex());
<COMMENT>[^}\n]	    => (lex());
<COMMENT>\{	    => (lex());
<COMMENT>\}	    => (YYBEGIN MAIN; lex());

