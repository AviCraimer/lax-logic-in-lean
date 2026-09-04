
structure Pretty : PRETTY = PrettyFun ();

structure Absyn : ABSYN = AbsynFun(structure Pretty = Pretty);

structure catpartLrVals : catpart_LRVALS =
    catpartLrValsFun(structure Token = LrParser.Token
		     structure Absyn = Absyn);

structure Interface : INTERFACE = InterfaceFun();
structure catpartLex : LEXER =
   catpartLexFun(structure Tokens = catpartLrVals.Tokens
		 structure Interface = Interface);

structure catpartParser : PARSER =
   Join(structure ParserData = catpartLrVals.ParserData
        structure Lex = catpartLex
	structure LrParser = LrParser);

structure Parse : PARSE =
   ParseFun (structure Absyn = Absyn
	     structure Interface = Interface
	     structure Parser = catpartParser
	     structure Tokens = catpartLrVals.Tokens );
