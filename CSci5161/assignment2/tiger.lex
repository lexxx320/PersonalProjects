type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

fun revfold _ nil b = b (* If the second argument is nil (an empty list), return the third argument. *)
| revfold f (hd::tl) b = revfold f tl (f(hd,b)); (* Otherwise, recurse on the tail of the list and
                                                   replace b with the result of applying f to the head
                                                   of the list and the old b. *)

fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end


%% 

ws = [\ \t];

%%
\n	=> (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
"type" => (Tokens.TYPE(yypos, yypos + 4));
"var" => (Tokens.VAR(yypos, yypos + 3));
"function" => (Tokens.FUNCTION(yypos, yypos + 8));
"break" => (Tokens.BREAK(yypos, yypos+5));
"of" => (Tokens.OF(yypos, yypos + 2));
"end" => (Tokens.END(yypos, yypos+3));
"in" => (Tokens.IN(yypos, yypos+2));
"nil" => (Tokens.NIL(yypos, yypos+3));
"let" => (Tokens.LET(yypos, yypos + 3));
"do" => (Tokens.DO(yypos, yypos + 2));
"to" => (Tokens.TO(yypos, yypos + 2));
"for" => (Tokens.FOR(yypos, yypos + 3));
"while" => (Tokens.WHILE(yypos, yypos + 5));
"else" => (Tokens.ELSE(yypos, yypos + 4));
"then" => (Tokens.THEN(yypos, yypos + 4));
"if" => (Tokens.IF(yypos, yypos + 2));
"array" => (Tokens.ARRAY(yypos, yypos + 5));
"=" => (Tokens.ASSIGN(yypos, yypos+1));
"||" => (Tokens.OR(yypos, yypos+2));
"&&" => (Tokens.AND(yypos, yypos + 2));
">=" => (Tokens.GE(yypos, yypos+2));
">" => (Tokens.GT(yypos, yypos+1));
"<=" => (Tokens.LE(yypos, yypos+2));
"<" => (Tokens.LT(yypos, yypos+1));
"!=" => (Tokens.NEQ(yypos, yypos+2));
"==" => (Tokens.EQ(yypos, yypos + 2));
"/" => (Tokens.DIVIDE(yypos, yypos + 1));
"*" => (Tokens.TIMES(yypos, yypos + 1));
"-" => (Tokens.MINUS(yypos, yypos + 1));
"+" => (Tokens.PLUS(yypos, yypos + 1));
"." => (Tokens.DOT(yypos, yypos + 1));
"}" => (Tokens.RBRACE(yypos, yypos + 1));
"{" => (Tokens.LBRACE(yypos, yypos + 1));
"]" => (Tokens.RBRACK(yypos, yypos + 1));
"[" => (Tokens.LBRACK(yypos, yypos + 1));
")" => (Tokens.RPAREN(yypos, yypos + 1));
"(" => (Tokens.LPAREN(yypos, yypos + 1));
";" => (Tokens.SEMICOLON(yypos, yypos + 1));
":" => (Tokens.COLON(yypos, yypos + 1));
"," => (Tokens.COMMA(yypos, yypos + 1));
\"([^\n\"\\]|\\\"|\\\\|\\n|\\r|\\t)*\" => (Tokens.STRING(yytext, yypos, yypos + size(yytext)));

[a-z][a-zA-Z0-9_]* => (Tokens.ID(yytext, yypos, yypos+size(yytext)));
[0-9]+ => (Tokens.INT((revfold (fn(a,r)=>ord(a)-ord(#"0")+10*r) 
                                (explode yytext) 0), 
                       yypos, yypos+size(yytext)) );
\/\/.* => (lex());
{ws}+ => (lex());
\/\*([^\*]|\*+[^\*\/])* \*+\/ => (lex());
                       
.       => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());













