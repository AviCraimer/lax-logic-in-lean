signature catpart_TOKENS =
sig
type ('a,'b) token
type svalue
val NUMBER: (int) *  'a * 'a -> (svalue,'a) token
val RSQBR:  'a * 'a -> (svalue,'a) token
val LSQBR:  'a * 'a -> (svalue,'a) token
val RRBR:  'a * 'a -> (svalue,'a) token
val LRBR:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val CATEGORIES:  'a * 'a -> (svalue,'a) token
val ENDFUN:  'a * 'a -> (svalue,'a) token
val FUN:  'a * 'a -> (svalue,'a) token
val NOT:  'a * 'a -> (svalue,'a) token
val AND:  'a * 'a -> (svalue,'a) token
val OR:  'a * 'a -> (svalue,'a) token
val IF:  'a * 'a -> (svalue,'a) token
val PROPERTY:  'a * 'a -> (svalue,'a) token
val ERROR:  'a * 'a -> (svalue,'a) token
val SINGLE:  'a * 'a -> (svalue,'a) token
val STAR:  'a * 'a -> (svalue,'a) token
val VAR: (string) *  'a * 'a -> (svalue,'a) token
val NEWLINE:  'a * 'a -> (svalue,'a) token
val SEMICOLON:  'a * 'a -> (svalue,'a) token
val COLON:  'a * 'a -> (svalue,'a) token
val CAP: (string) *  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
end
signature catpart_LRVALS=
sig
structure Tokens : catpart_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
