
structure Pretty : PRETTY = PrettyFun ();

structure Absyn : ABSYN = AbsynFun(structure Pretty = Pretty);

structure testgenLrVals : testgen_LRVALS =
    testgenLrValsFun(structure Token = LrParser.Token
		     structure Absyn = Absyn);

structure Interface : INTERFACE = InterfaceFun();
structure testgenLex : LEXER =
   testgenLexFun(structure Tokens = testgenLrVals.Tokens
		 structure Interface = Interface);

structure testgenParser : PARSER =
   Join(structure ParserData = testgenLrVals.ParserData
        structure Lex = testgenLex
	structure LrParser = LrParser);

structure Parse : PARSE =
   ParseFun (structure Absyn = Absyn
	     structure Interface = Interface
	     structure Parser = testgenParser
	     structure Tokens = testgenLrVals.Tokens );
