(*
Matthew Le
3975089
Assignment 2: Lexical Analysis
*)

type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val commentNesting = ref 0
val doneWithString = ref 1
exception StringError
fun err(p1,p2) = ErrorMsg.error p1

fun revfold _ nil b = b (* If the second argument is nil (an empty list), return the third argument. *)
| revfold f (hd::tl) b = revfold f tl (f(hd,b)); (* Otherwise, recurse on the tail of the list and
                                                   replace b with the result of applying f to the head
                                                   of the list and the old b. *)

fun eof() = let val pos = hd(!linePos) 
            in 
              if !commentNesting > 0
              then (commentNesting := 0;
                    ErrorMsg.error pos ("Unmatched block comment");
                    Tokens.EOF(pos, pos))
              else Tokens.EOF(pos,pos) 
            end


%% 
%s comment string escape controlChar;
ws = [\ \t];

%%
<INITIAL>\n	=> (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<comment>\n	=> (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>"type" => (Tokens.TYPE(yypos, yypos + 4));
<INITIAL>"var" => (Tokens.VAR(yypos, yypos + 3));
<INITIAL>"function" => (Tokens.FUNCTION(yypos, yypos + 8));
<INITIAL>"break" => (Tokens.BREAK(yypos, yypos+5));
<INITIAL>"of" => (Tokens.OF(yypos, yypos + 2));
<INITIAL>"end" => (Tokens.END(yypos, yypos+3));
<INITIAL>"in" => (Tokens.IN(yypos, yypos+2));
<INITIAL>"nil" => (Tokens.NIL(yypos, yypos+3));
<INITIAL>"let" => (Tokens.LET(yypos, yypos + 3));
<INITIAL>"do" => (Tokens.DO(yypos, yypos + 2));
<INITIAL>"to" => (Tokens.TO(yypos, yypos + 2));
<INITIAL>"for" => (Tokens.FOR(yypos, yypos + 3));
<INITIAL>"while" => (Tokens.WHILE(yypos, yypos + 5));
<INITIAL>"else" => (Tokens.ELSE(yypos, yypos + 4));
<INITIAL>"then" => (Tokens.THEN(yypos, yypos + 4));
<INITIAL>"if" => (Tokens.IF(yypos, yypos + 2));
<INITIAL>"array" => (Tokens.ARRAY(yypos, yypos + 5));
<INITIAL>":=" => (Tokens.ASSIGN(yypos, yypos+1));
<INITIAL>"|" => (Tokens.OR(yypos, yypos+2));
<INITIAL>"&" => (Tokens.AND(yypos, yypos + 2));
<INITIAL>">=" => (Tokens.GE(yypos, yypos+2));
<INITIAL>">" => (Tokens.GT(yypos, yypos+1));
<INITIAL>"<=" => (Tokens.LE(yypos, yypos+2));
<INITIAL>"<" => (Tokens.LT(yypos, yypos+1));
<INITIAL>"<>" => (Tokens.NEQ(yypos, yypos+2));
<INITIAL>"=" => (Tokens.EQ(yypos, yypos + 2));
<INITIAL>"/" => (Tokens.DIVIDE(yypos, yypos + 1));
<INITIAL>"*" => (Tokens.TIMES(yypos, yypos + 1));
<INITIAL>"-" => (Tokens.MINUS(yypos, yypos + 1));
<INITIAL>"+" => (Tokens.PLUS(yypos, yypos + 1));
<INITIAL>"." => (Tokens.DOT(yypos, yypos + 1));
<INITIAL>"}" => (Tokens.RBRACE(yypos, yypos + 1));
<INITIAL>"{" => (Tokens.LBRACE(yypos, yypos + 1));
<INITIAL>"]" => (Tokens.RBRACK(yypos, yypos + 1));
<INITIAL>"[" => (Tokens.LBRACK(yypos, yypos + 1));
<INITIAL>")" => (Tokens.RPAREN(yypos, yypos + 1));
<INITIAL>"(" => (Tokens.LPAREN(yypos, yypos + 1));
<INITIAL>";" => (Tokens.SEMICOLON(yypos, yypos + 1));
<INITIAL>":" => (Tokens.COLON(yypos, yypos + 1));
<INITIAL>"," => (Tokens.COMMA(yypos, yypos + 1));



<INITIAL> ["] => (doneWithString := 0; 
                  YYBEGIN string; let val rest = lex()
                                      val totalSize = size(yytext) + size(rest)
                                  in if !doneWithString = 0 (*Didn't mach string, go back to INITIAL start state and continue*)
                                     then (ErrorMsg.error yypos ("unmatched string");
                                           YYBEGIN INITIAL;
                                           Tokens.STRING("", yypos, yypos))
                                     else Tokens.STRING(rest, yypos, yypos + size(yytext) + size(rest))
                                  end);




                                          

<string> \\ => (YYBEGIN escape; continue());

<escape> "n" => (YYBEGIN string; "\n" ^ continue());
<escape> "t" => (YYBEGIN string; "\t" ^ continue());
<escape> [\"] => (YYBEGIN string; "\"" ^ continue());
<escape> [\\] => (YYBEGIN string; "\\" ^ continue());
<escape> [0-9][0-9][0-9] => (YYBEGIN string; case Int.fromString(yytext) of
                                              SOME t => String.str(Char.chr(t)) ^ continue()
                                             |NONE   => (ErrorMsg.error yypos ("illegal escape sequence " ^ yytext); continue()));
<escape> \^ => (YYBEGIN controlChar; continue());

<controlChar> ([@-_]) => (YYBEGIN string; case Char.fromString("\\^" ^ yytext)
                                          of SOME t => (String.str(t) ^ continue())
                                            |NONE => (ErrorMsg.error yypos ("Illegal control character \\^" ^ yytext); continue() ) );
                                             
<escape> . => (YYBEGIN string; ErrorMsg.error yypos ("illegal escape sequence \\" ^ yytext); continue());
                                             
<string> ([^\n\"\\])+ => (yytext ^ lex());

<string> \n => (lineNum := !lineNum+1; linePos := yypos :: !linePos;yytext);
                                                        
<string> \\({ws}|\n)+\\ => (lex());
<string> \" => (doneWithString := 1; YYBEGIN INITIAL; "");

<string> . => (ErrorMsg.error yypos ("Illegal character in string " ^ yytext); continue());

<INITIAL>[a-zA-Z][a-zA-Z0-9_]* => (Tokens.ID(yytext, yypos, yypos+size(yytext)));
<INITIAL>[0-9]+ => (Tokens.INT((revfold (fn(a,r)=>ord(a)-ord(#"0")+10*r) 
                                (explode yytext) 0), 
                       yypos, yypos+size(yytext)) );
<INITIAL>\/\/.* => (lex());
<INITIAL>{ws}+ => (lex());

<INITIAL>\/\* => (YYBEGIN comment; commentNesting := !commentNesting + 1 ; lex());
<comment>\/\* => (YYBEGIN comment; commentNesting := !commentNesting + 1 ; lex());
<comment> . => (continue());
<comment> \*\/ => (if !commentNesting = 1 
                   then YYBEGIN INITIAL 
                   else YYBEGIN comment; commentNesting := !commentNesting - 1; lex());


                       
<INITIAL>.       => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());













