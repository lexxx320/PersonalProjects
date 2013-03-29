
functor TigerLrValsFun(structure Token : TOKEN
                                structure A: ABSYN
                                structure Symbol: SYMBOL
                                sharing type A.symbol=Symbol.symbol) = 
struct
structure ParserData=
struct
structure Header = 
struct
type pos = int

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\001\000\169\000\005\000\169\000\007\000\169\000\009\000\169\000\
\\011\000\169\000\013\000\169\000\015\000\028\000\016\000\027\000\
\\017\000\026\000\018\000\025\000\025\000\169\000\026\000\169\000\
\\030\000\169\000\031\000\169\000\034\000\169\000\035\000\169\000\
\\037\000\169\000\038\000\169\000\042\000\169\000\043\000\169\000\
\\044\000\169\000\000\000\
\\001\000\001\000\170\000\005\000\170\000\007\000\170\000\009\000\170\000\
\\011\000\170\000\013\000\170\000\015\000\028\000\016\000\027\000\
\\017\000\026\000\018\000\025\000\025\000\170\000\026\000\170\000\
\\030\000\170\000\031\000\170\000\034\000\170\000\035\000\170\000\
\\037\000\170\000\038\000\170\000\042\000\170\000\043\000\170\000\
\\044\000\170\000\000\000\
\\001\000\001\000\171\000\005\000\171\000\007\000\171\000\009\000\171\000\
\\011\000\171\000\013\000\171\000\015\000\028\000\016\000\027\000\
\\017\000\026\000\018\000\025\000\025\000\171\000\026\000\171\000\
\\030\000\171\000\031\000\171\000\034\000\171\000\035\000\171\000\
\\037\000\171\000\038\000\171\000\042\000\171\000\043\000\171\000\
\\044\000\171\000\000\000\
\\001\000\001\000\172\000\005\000\172\000\007\000\172\000\009\000\172\000\
\\011\000\172\000\013\000\172\000\015\000\028\000\016\000\027\000\
\\017\000\026\000\018\000\025\000\025\000\172\000\026\000\172\000\
\\030\000\172\000\031\000\172\000\034\000\172\000\035\000\172\000\
\\037\000\172\000\038\000\172\000\042\000\172\000\043\000\172\000\
\\044\000\172\000\000\000\
\\001\000\001\000\173\000\005\000\173\000\007\000\173\000\009\000\173\000\
\\011\000\173\000\013\000\173\000\015\000\028\000\016\000\027\000\
\\017\000\026\000\018\000\025\000\025\000\173\000\026\000\173\000\
\\030\000\173\000\031\000\173\000\034\000\173\000\035\000\173\000\
\\037\000\173\000\038\000\173\000\042\000\173\000\043\000\173\000\
\\044\000\173\000\000\000\
\\001\000\001\000\174\000\005\000\174\000\007\000\174\000\009\000\174\000\
\\011\000\174\000\013\000\174\000\015\000\028\000\016\000\027\000\
\\017\000\026\000\018\000\025\000\025\000\174\000\026\000\174\000\
\\030\000\174\000\031\000\174\000\034\000\174\000\035\000\174\000\
\\037\000\174\000\038\000\174\000\042\000\174\000\043\000\174\000\
\\044\000\174\000\000\000\
\\001\000\002\000\015\000\003\000\014\000\004\000\013\000\008\000\012\000\
\\009\000\047\000\016\000\011\000\029\000\010\000\032\000\009\000\
\\033\000\008\000\036\000\007\000\040\000\006\000\041\000\005\000\000\000\
\\001\000\002\000\015\000\003\000\014\000\004\000\013\000\008\000\012\000\
\\016\000\011\000\029\000\010\000\032\000\009\000\033\000\008\000\
\\036\000\007\000\040\000\006\000\041\000\005\000\000\000\
\\001\000\002\000\041\000\000\000\
\\001\000\002\000\070\000\000\000\
\\001\000\002\000\071\000\000\000\
\\001\000\002\000\072\000\000\000\
\\001\000\002\000\079\000\000\000\
\\001\000\002\000\083\000\000\000\
\\001\000\002\000\112\000\012\000\111\000\028\000\110\000\000\000\
\\001\000\002\000\114\000\000\000\
\\001\000\002\000\118\000\000\000\
\\001\000\002\000\139\000\000\000\
\\001\000\002\000\145\000\000\000\
\\001\000\002\000\148\000\000\000\
\\001\000\006\000\093\000\027\000\092\000\000\000\
\\001\000\006\000\133\000\000\000\
\\001\000\006\000\143\000\019\000\142\000\000\000\
\\001\000\007\000\078\000\009\000\077\000\015\000\028\000\016\000\027\000\
\\017\000\026\000\018\000\025\000\019\000\024\000\020\000\023\000\
\\021\000\022\000\022\000\021\000\023\000\020\000\024\000\019\000\
\\025\000\018\000\026\000\017\000\000\000\
\\001\000\008\000\094\000\000\000\
\\001\000\009\000\076\000\000\000\
\\001\000\009\000\106\000\000\000\
\\001\000\009\000\131\000\000\000\
\\001\000\011\000\105\000\015\000\028\000\016\000\027\000\017\000\026\000\
\\018\000\025\000\019\000\024\000\020\000\023\000\021\000\022\000\
\\022\000\021\000\023\000\020\000\024\000\019\000\025\000\018\000\
\\026\000\017\000\000\000\
\\001\000\011\000\137\000\015\000\028\000\016\000\027\000\017\000\026\000\
\\018\000\025\000\019\000\024\000\020\000\023\000\021\000\022\000\
\\022\000\021\000\023\000\020\000\024\000\019\000\025\000\018\000\
\\026\000\017\000\000\000\
\\001\000\013\000\102\000\000\000\
\\001\000\013\000\140\000\000\000\
\\001\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\
\\030\000\075\000\000\000\
\\001\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\
\\034\000\119\000\000\000\
\\001\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\
\\035\000\074\000\000\000\
\\001\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\
\\035\000\146\000\000\000\
\\001\000\019\000\091\000\000\000\
\\001\000\019\000\104\000\000\000\
\\001\000\019\000\150\000\000\000\
\\001\000\027\000\073\000\000\000\
\\001\000\027\000\130\000\000\000\
\\001\000\037\000\068\000\000\000\
\\001\000\038\000\108\000\000\000\
\\001\000\039\000\128\000\000\000\
\\153\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\154\000\000\000\
\\155\000\000\000\
\\156\000\000\000\
\\157\000\008\000\052\000\010\000\051\000\012\000\050\000\014\000\049\000\000\000\
\\157\000\010\000\101\000\014\000\049\000\000\000\
\\157\000\010\000\101\000\014\000\049\000\039\000\126\000\000\000\
\\158\000\000\000\
\\159\000\000\000\
\\160\000\000\000\
\\161\000\027\000\016\000\000\000\
\\162\000\000\000\
\\163\000\000\000\
\\164\000\000\000\
\\165\000\017\000\026\000\018\000\025\000\000\000\
\\166\000\017\000\026\000\018\000\025\000\000\000\
\\167\000\000\000\
\\168\000\000\000\
\\175\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\000\000\
\\176\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\000\000\
\\177\000\000\000\
\\178\000\000\000\
\\179\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\180\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\181\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\182\000\000\000\
\\183\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\184\000\000\000\
\\185\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\
\\031\000\120\000\000\000\
\\186\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\187\000\000\000\
\\188\000\000\000\
\\189\000\007\000\078\000\015\000\028\000\016\000\027\000\017\000\026\000\
\\018\000\025\000\019\000\024\000\020\000\023\000\021\000\022\000\
\\022\000\021\000\023\000\020\000\024\000\019\000\025\000\018\000\
\\026\000\017\000\000\000\
\\190\000\000\000\
\\191\000\002\000\083\000\000\000\
\\192\000\000\000\
\\193\000\005\000\103\000\000\000\
\\194\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\195\000\000\000\
\\196\000\007\000\121\000\015\000\028\000\016\000\027\000\017\000\026\000\
\\018\000\025\000\019\000\024\000\020\000\023\000\021\000\022\000\
\\022\000\021\000\023\000\020\000\024\000\019\000\025\000\018\000\
\\026\000\017\000\000\000\
\\197\000\000\000\
\\198\000\000\000\
\\199\000\002\000\015\000\003\000\014\000\004\000\013\000\008\000\012\000\
\\016\000\011\000\029\000\010\000\032\000\009\000\033\000\008\000\
\\036\000\007\000\040\000\006\000\041\000\005\000\000\000\
\\200\000\000\000\
\\201\000\005\000\107\000\015\000\028\000\016\000\027\000\017\000\026\000\
\\018\000\025\000\019\000\024\000\020\000\023\000\021\000\022\000\
\\022\000\021\000\023\000\020\000\024\000\019\000\025\000\018\000\
\\026\000\017\000\000\000\
\\202\000\000\000\
\\203\000\042\000\040\000\043\000\039\000\044\000\038\000\000\000\
\\204\000\000\000\
\\205\000\000\000\
\\206\000\000\000\
\\207\000\000\000\
\\208\000\000\000\
\\209\000\044\000\038\000\000\000\
\\210\000\000\000\
\\211\000\000\000\
\\212\000\000\000\
\\213\000\000\000\
\\214\000\000\000\
\\215\000\002\000\118\000\000\000\
\\216\000\000\000\
\\217\000\005\000\132\000\000\000\
\\218\000\000\000\
\\219\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\220\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\221\000\000\000\
\\222\000\000\000\
\\223\000\042\000\040\000\000\000\
\\224\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\\225\000\015\000\028\000\016\000\027\000\017\000\026\000\018\000\025\000\
\\019\000\024\000\020\000\023\000\021\000\022\000\022\000\021\000\
\\023\000\020\000\024\000\019\000\025\000\018\000\026\000\017\000\000\000\
\"
val actionRowNumbers =
"\008\000\055\000\045\000\052\000\
\\070\000\091\000\009\000\008\000\
\\008\000\008\000\007\000\054\000\
\\053\000\049\000\008\000\008\000\
\\008\000\008\000\008\000\008\000\
\\008\000\008\000\008\000\008\000\
\\008\000\008\000\008\000\094\000\
\\109\000\111\000\093\000\097\000\
\\095\000\092\000\042\000\091\000\
\\010\000\011\000\012\000\040\000\
\\035\000\033\000\066\000\026\000\
\\024\000\075\000\046\000\013\000\
\\079\000\008\000\087\000\067\000\
\\064\000\063\000\006\000\005\000\
\\004\000\003\000\002\000\001\000\
\\062\000\061\000\060\000\059\000\
\\110\000\096\000\008\000\090\000\
\\037\000\021\000\025\000\008\000\
\\008\000\008\000\056\000\058\000\
\\008\000\050\000\031\000\081\000\
\\078\000\038\000\029\000\027\000\
\\086\000\089\000\043\000\076\000\
\\077\000\015\000\008\000\016\000\
\\103\000\034\000\068\000\073\000\
\\083\000\084\000\047\000\008\000\
\\072\000\014\000\008\000\051\000\
\\057\000\008\000\065\000\098\000\
\\044\000\103\000\099\000\107\000\
\\041\000\028\000\105\000\102\000\
\\022\000\008\000\008\000\008\000\
\\030\000\080\000\082\000\048\000\
\\008\000\088\000\018\000\032\000\
\\008\000\023\000\017\000\019\000\
\\036\000\074\000\085\000\050\000\
\\071\000\101\000\100\000\108\000\
\\008\000\020\000\104\000\106\000\
\\008\000\112\000\039\000\069\000\
\\008\000\113\000\000\000"
val gotoT =
"\
\\001\000\002\000\002\000\150\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\035\000\005\000\034\000\007\000\033\000\008\000\032\000\
\\009\000\031\000\010\000\030\000\011\000\029\000\012\000\028\000\
\\013\000\027\000\000\000\
\\000\000\
\\001\000\040\000\003\000\001\000\000\000\
\\001\000\041\000\003\000\001\000\000\000\
\\001\000\042\000\003\000\001\000\000\000\
\\001\000\044\000\003\000\001\000\006\000\043\000\000\000\
\\000\000\
\\000\000\
\\017\000\046\000\000\000\
\\001\000\051\000\003\000\001\000\000\000\
\\001\000\052\000\003\000\001\000\000\000\
\\001\000\053\000\003\000\001\000\000\000\
\\001\000\054\000\003\000\001\000\000\000\
\\001\000\055\000\003\000\001\000\000\000\
\\001\000\056\000\003\000\001\000\000\000\
\\001\000\057\000\003\000\001\000\000\000\
\\001\000\058\000\003\000\001\000\000\000\
\\001\000\059\000\003\000\001\000\000\000\
\\001\000\060\000\003\000\001\000\000\000\
\\001\000\061\000\003\000\001\000\000\000\
\\001\000\062\000\003\000\001\000\000\000\
\\001\000\063\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\011\000\029\000\012\000\064\000\000\000\
\\000\000\
\\008\000\065\000\009\000\031\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\035\000\005\000\067\000\007\000\033\000\008\000\032\000\
\\009\000\031\000\010\000\030\000\011\000\029\000\012\000\028\000\
\\013\000\027\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\016\000\080\000\020\000\079\000\021\000\078\000\000\000\
\\001\000\082\000\003\000\001\000\000\000\
\\001\000\085\000\003\000\001\000\023\000\084\000\024\000\083\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\088\000\003\000\001\000\006\000\087\000\025\000\086\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\093\000\003\000\001\000\000\000\
\\001\000\094\000\003\000\001\000\000\000\
\\001\000\095\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\001\000\097\000\003\000\001\000\022\000\096\000\000\000\
\\017\000\098\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\014\000\107\000\000\000\
\\001\000\111\000\003\000\001\000\000\000\
\\000\000\
\\015\000\115\000\018\000\114\000\019\000\113\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\120\000\003\000\001\000\000\000\
\\000\000\
\\016\000\121\000\020\000\079\000\000\000\
\\001\000\122\000\003\000\001\000\000\000\
\\017\000\123\000\000\000\
\\000\000\
\\001\000\085\000\003\000\001\000\023\000\125\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\015\000\115\000\018\000\114\000\019\000\127\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\132\000\003\000\001\000\000\000\
\\001\000\133\000\003\000\001\000\000\000\
\\001\000\097\000\003\000\001\000\022\000\134\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\136\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\139\000\003\000\001\000\000\000\
\\000\000\
\\015\000\142\000\018\000\114\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\017\000\123\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\145\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\147\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\149\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 151
val numrules = 73
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
datatype svalue = VOID | ntVOID of unit ->  unit
 | STRING of unit ->  (string) | INT of unit ->  (int)
 | ID of unit ->  (string) | optionalExps of unit ->  (A.exp)
 | optionalCommaExps of unit ->  (A.exp list)
 | commaExps of unit ->  (A.exp list)
 | expsRest of unit ->  ( ( A.exp * pos )  list)
 | optionalIdEQExpPairs of unit ->  ( ( Symbol.symbol * A.exp * pos )  list)
 | idEQExpPair of unit ->  (Symbol.symbol*A.exp*pos)
 | optionalFields of unit ->  (A.field list)
 | tyfield of unit ->  (A.field)
 | optionalLValue of unit ->  (A.var -> A.var)
 | idEQExpPairs of unit ->  ( ( Symbol.symbol * A.exp * pos )  list)
 | tyfields of unit ->  (A.field list) | ty of unit ->  (A.ty)
 | fundecList of unit ->  (A.dec)
 | fundecs of unit ->  (A.fundec list) | fundec of unit ->  (A.fundec)
 | vardec of unit ->  (A.dec)
 | tydec of unit ->  ({ name:Symbol.symbol,ty:A.ty,pos:pos } )
 | tydecs of unit ->  ({ name:Symbol.symbol,ty:A.ty,pos:pos }  list)
 | tydecList of unit ->  (A.dec)
 | exps of unit ->  ( ( A.exp * pos )  list)
 | decs of unit ->  (A.dec list) | dec of unit ->  (A.dec)
 | lvalue of unit ->  (A.var) | program of unit ->  (A.exp)
 | exp of unit ->  (A.exp)
end
type svalue = MlyValue.svalue
type result = A.exp
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn (T 31) => true | (T 32) => true | (T 33) => true | (T 39) => true
 | (T 35) => true | (T 36) => true | (T 37) => true | (T 41) => true
 | (T 42) => true | (T 43) => true | (T 27) => true | (T 28) => true
 | (T 29) => true | (T 30) => true | (T 34) => true | (T 38) => true
 | (T 40) => true | _ => false
val preferred_change : (term list * term list) list = 
(nil
 $$ (T 18),nil
 $$ (T 26))::
(nil
 $$ (T 26),nil
 $$ (T 18))::
(nil
,nil
 $$ (T 29))::
(nil
,nil
 $$ (T 30))::
(nil
,nil
 $$ (T 7))::
(nil
,nil
 $$ (T 28))::
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "ID"
  | (T 2) => "INT"
  | (T 3) => "STRING"
  | (T 4) => "COMMA"
  | (T 5) => "COLON"
  | (T 6) => "SEMICOLON"
  | (T 7) => "LPAREN"
  | (T 8) => "RPAREN"
  | (T 9) => "LBRACK"
  | (T 10) => "RBRACK"
  | (T 11) => "LBRACE"
  | (T 12) => "RBRACE"
  | (T 13) => "DOT"
  | (T 14) => "PLUS"
  | (T 15) => "MINUS"
  | (T 16) => "TIMES"
  | (T 17) => "DIVIDE"
  | (T 18) => "EQ"
  | (T 19) => "NEQ"
  | (T 20) => "LT"
  | (T 21) => "LE"
  | (T 22) => "GT"
  | (T 23) => "GE"
  | (T 24) => "AND"
  | (T 25) => "OR"
  | (T 26) => "ASSIGN"
  | (T 27) => "ARRAY"
  | (T 28) => "IF"
  | (T 29) => "THEN"
  | (T 30) => "ELSE"
  | (T 31) => "WHILE"
  | (T 32) => "FOR"
  | (T 33) => "TO"
  | (T 34) => "DO"
  | (T 35) => "LET"
  | (T 36) => "IN"
  | (T 37) => "END"
  | (T 38) => "OF"
  | (T 39) => "BREAK"
  | (T 40) => "NIL"
  | (T 41) => "FUNCTION"
  | (T 42) => "VAR"
  | (T 43) => "TYPE"
  | (T 44) => "UMINUS"
  | (T 45) => "LOWPREC"
  | (T 46) => "LVALUEPREC"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn (T 1) => MlyValue.ID(fn () => ("bogus")) | 
(T 2) => MlyValue.INT(fn () => (1)) | 
(T 3) => MlyValue.STRING(fn () => ("")) | 
_ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 46) $$ (T 45) $$ (T 44) $$ (T 43) $$ (T 42) $$ (T 41) $$ (T 40)
 $$ (T 39) $$ (T 38) $$ (T 37) $$ (T 36) $$ (T 35) $$ (T 34) $$ (T 33)
 $$ (T 32) $$ (T 31) $$ (T 30) $$ (T 29) $$ (T 28) $$ (T 27) $$ (T 26)
 $$ (T 25) $$ (T 24) $$ (T 23) $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19)
 $$ (T 18) $$ (T 17) $$ (T 16) $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12)
 $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ 
(T 4) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.exp exp1, exp1left, exp1right)) :: rest671)
) => let val  result = MlyValue.program (fn _ => let val  (exp as exp1
) = exp1 ()
 in (exp)
end)
 in ( LrTable.NT 1, ( result, exp1left, exp1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.optionalLValue optionalLValue1, _, 
optionalLValue1right)) :: ( _, ( MlyValue.ID ID1, (IDleft as ID1left),
 _)) :: rest671)) => let val  result = MlyValue.lvalue (fn _ => let
 val  (ID as ID1) = ID1 ()
 val  (optionalLValue as optionalLValue1) = optionalLValue1 ()
 in (
optionalLValue(A.SimpleVar(Symbol.symbol(ID), 
                              IDleft))
)
end)
 in ( LrTable.NT 2, ( result, ID1left, optionalLValue1right), rest671)

end
|  ( 2, ( ( _, ( MlyValue.optionalLValue optionalLValue1, _, 
optionalLValue1right)) :: ( _, ( MlyValue.ID ID1, IDleft, _)) :: ( _, 
( _, DOT1left, _)) :: rest671)) => let val  result = 
MlyValue.optionalLValue (fn _ => let val  (ID as ID1) = ID1 ()
 val  (optionalLValue as optionalLValue1) = optionalLValue1 ()
 in (
fn x => optionalLValue(A.FieldVar(
                  x, Symbol.symbol(ID), IDleft))
)
end)
 in ( LrTable.NT 16, ( result, DOT1left, optionalLValue1right), 
rest671)
end
|  ( 3, ( ( _, ( MlyValue.optionalLValue optionalLValue1, _, 
optionalLValue1right)) :: _ :: ( _, ( MlyValue.exp exp1, _, _)) :: ( _
, ( _, (LBRACKleft as LBRACK1left), _)) :: rest671)) => let val  
result = MlyValue.optionalLValue (fn _ => let val  (exp as exp1) = 
exp1 ()
 val  (optionalLValue as optionalLValue1) = optionalLValue1 ()
 in (
fn x => optionalLValue(
                    A.SubscriptVar(x, exp, LBRACKleft))
)
end)
 in ( LrTable.NT 16, ( result, LBRACK1left, optionalLValue1right), 
rest671)
end
|  ( 4, ( rest671)) => let val  result = MlyValue.optionalLValue (fn _
 => (fn x => x))
 in ( LrTable.NT 16, ( result, defaultPos, defaultPos), rest671)
end
|  ( 5, ( ( _, ( _, NIL1left, NIL1right)) :: rest671)) => let val  
result = MlyValue.exp (fn _ => (A.NilExp))
 in ( LrTable.NT 0, ( result, NIL1left, NIL1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.INT INT1, INT1left, INT1right)) :: rest671))
 => let val  result = MlyValue.exp (fn _ => let val  (INT as INT1) = 
INT1 ()
 in (A.IntExp(INT))
end)
 in ( LrTable.NT 0, ( result, INT1left, INT1right), rest671)
end
|  ( 7, ( ( _, ( MlyValue.STRING STRING1, (STRINGleft as STRING1left),
 STRING1right)) :: rest671)) => let val  result = MlyValue.exp (fn _
 => let val  (STRING as STRING1) = STRING1 ()
 in (A.StringExp(STRING, STRINGleft))
end)
 in ( LrTable.NT 0, ( result, STRING1left, STRING1right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.lvalue lvalue1, lvalue1left, lvalue1right))
 :: rest671)) => let val  result = MlyValue.exp (fn _ => let val  (
lvalue as lvalue1) = lvalue1 ()
 in (A.VarExp(lvalue))
end)
 in ( LrTable.NT 0, ( result, lvalue1left, lvalue1right), rest671)
end
|  ( 9, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.exps exps1, _
, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  (exps as exps1) = exps1 ()
 in (A.SeqExp(exps))
end)
 in ( LrTable.NT 0, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 10, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( 
MlyValue.optionalCommaExps optionalCommaExps1, _, _)) :: _ :: ( _, ( 
MlyValue.ID ID1, (IDleft as ID1left), _)) :: rest671)) => let val  
result = MlyValue.exp (fn _ => let val  (ID as ID1) = ID1 ()
 val  (optionalCommaExps as optionalCommaExps1) = optionalCommaExps1
 ()
 in (
A.CallExp({func = Symbol.symbol(ID), 
        args = optionalCommaExps, pos = IDleft})
)
end)
 in ( LrTable.NT 0, ( result, ID1left, RPAREN1right), rest671)
end
|  ( 11, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.exp exp1, _,
 _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  (exp as exp1) = exp1 ()
 in (exp)
end)
 in ( LrTable.NT 0, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
PLUSleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671))
 => let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.PlusOp,           (*12*)
        right = exp2, pos = PLUSleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
MINUSleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671))
 => let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.MinusOp,         (*13*)
        right = exp2, pos = MINUSleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
TIMESleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671))
 => let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.TimesOp,         (*14*)
        right = exp2, pos = TIMESleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
DIVIDEleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671)
) => let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.DivideOp,       (*15*)
        right = exp2, pos = DIVIDEleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 16, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
EQleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671)) =>
 let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.EqOp,               (*16*)
        right = exp2, pos = EQleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
NEQleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671))
 => let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.NeqOp,             (*17*)
        right = exp2, pos = NEQleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 18, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
LTleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671)) =>
 let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.LtOp,               (*18*)
        right = exp2, pos = LTleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 19, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
LEleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671)) =>
 let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.LeOp,               (*19*)
        right = exp2, pos = LEleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 20, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
GTleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671)) =>
 let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.GtOp,               (*20*)
        right = exp2, pos = GTleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 21, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( _, 
GEleft, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671)) =>
 let val  result = MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp({left = exp1, oper = A.GeOp,               (*21*)
        right = exp2, pos = GEleft})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 22, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: ( _, ( 
MlyValue.exp exp1, exp1left, _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.IfExp({test = exp1, then' = exp2,               (*22*)
        else' = SOME (A.IntExp(0)), pos = exp1left})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 23, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: ( _, ( 
MlyValue.exp exp1, exp1left, _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.IfExp({test = exp1, then' = A.IntExp(1),         (*23*)
        else' = SOME exp2, pos = exp1left})
)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp2right), rest671)
end
|  ( 24, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.optionalExps 
optionalExps1, _, _)) :: _ :: ( _, ( MlyValue.decs decs1, _, _)) :: (
 _, ( _, (LETleft as LET1left), _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  (decs as decs1) = decs1 ()
 val  (optionalExps as optionalExps1) = optionalExps1 ()
 in (
A.LetExp({decs = decs, body = optionalExps,
        pos = LETleft}))

end)
 in ( LrTable.NT 0, ( result, LET1left, END1right), rest671)
end
|  ( 25, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: ( _, ( _, (
MINUSleft as MINUS1left), _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  (exp as exp1) = exp1 ()
 in (
A.OpExp({left = A.IntExp(0), oper = A.MinusOp, (*25*)
          right = exp, pos = MINUSleft})
)
end)
 in ( LrTable.NT 0, ( result, MINUS1left, exp1right), rest671)
end
|  ( 26, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.lvalue lvalue1, (lvalueleft as lvalue1left), _)) :: rest671))
 => let val  result = MlyValue.exp (fn _ => let val  (lvalue as 
lvalue1) = lvalue1 ()
 val  (exp as exp1) = exp1 ()
 in (
A.AssignExp({var = lvalue, exp = exp,  (*26*)
          pos = lvalueleft})
)
end)
 in ( LrTable.NT 0, ( result, lvalue1left, exp1right), rest671)
end
|  ( 27, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: ( _, ( 
MlyValue.exp exp1, _, _)) :: ( _, ( _, (WHILEleft as WHILE1left), _))
 :: rest671)) => let val  result = MlyValue.exp (fn _ => let val  exp1
 = exp1 ()
 val  exp2 = exp2 ()
 in (A.WhileExp({test = exp1, body = exp2, pos = WHILEleft}))
end)
 in ( LrTable.NT 0, ( result, WHILE1left, exp2right), rest671)
end
|  ( 28, ( ( _, ( MlyValue.exp exp3, _, exp3right)) :: _ :: ( _, ( 
MlyValue.exp exp2, _, _)) :: _ :: ( _, ( MlyValue.exp exp1, _, _)) ::
 _ :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, (FORleft as FOR1left
), _)) :: rest671)) => let val  result = MlyValue.exp (fn _ => let
 val  (ID as ID1) = ID1 ()
 val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 val  exp3 = exp3 ()
 in (
A.ForExp({var = Symbol.symbol(ID), (*26*)
        escape = ref true, lo = exp1, hi = exp2, body = exp3, pos = FORleft})
)
end)
 in ( LrTable.NT 0, ( result, FOR1left, exp3right), rest671)
end
|  ( 29, ( ( _, ( _, (BREAKleft as BREAK1left), BREAK1right)) :: 
rest671)) => let val  result = MlyValue.exp (fn _ => (
A.BreakExp(BREAKleft)))
 in ( LrTable.NT 0, ( result, BREAK1left, BREAK1right), rest671)
end
|  ( 30, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: _ :: ( _, 
( MlyValue.exp exp1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, (IDleft
 as ID1left), _)) :: rest671)) => let val  result = MlyValue.exp (fn _
 => let val  (ID as ID1) = ID1 ()
 val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.ArrayExp({typ = Symbol.symbol(ID),  (*28*)
        size = exp1, init = exp2, pos = IDleft})
)
end)
 in ( LrTable.NT 0, ( result, ID1left, exp2right), rest671)
end
|  ( 31, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( 
MlyValue.optionalIdEQExpPairs optionalIdEQExpPairs1, _, _)) :: _ :: (
 _, ( MlyValue.ID ID1, (IDleft as ID1left), _)) :: rest671)) => let
 val  result = MlyValue.exp (fn _ => let val  (ID as ID1) = ID1 ()
 val  (optionalIdEQExpPairs as optionalIdEQExpPairs1) = 
optionalIdEQExpPairs1 ()
 in (
A.RecordExp({fields =       (*29*)
        optionalIdEQExpPairs, typ = Symbol.symbol(ID), pos = IDleft})
)
end)
 in ( LrTable.NT 0, ( result, ID1left, RBRACE1right), rest671)
end
|  ( 32, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: ( _, ( 
MlyValue.exp exp1, _, _)) :: ( _, ( _, (IFleft as IF1left), _)) :: 
rest671)) => let val  result = MlyValue.exp (fn _ => let val  exp1 = 
exp1 ()
 val  exp2 = exp2 ()
 in (
A.IfExp({test = exp1, then' = exp2, else' = NONE, (*30*)
        pos = IFleft})
)
end)
 in ( LrTable.NT 0, ( result, IF1left, exp2right), rest671)
end
|  ( 33, ( ( _, ( MlyValue.exp exp3, _, exp3right)) :: _ :: ( _, ( 
MlyValue.exp exp2, _, _)) :: _ :: ( _, ( MlyValue.exp exp1, _, _)) :: 
( _, ( _, (IFleft as IF1left), _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 val  exp3 = exp3 ()
 in (
A.IfExp({test = exp1, then' = exp2,    (*31*)
        else' = SOME exp3, pos = IFleft})
)
end)
 in ( LrTable.NT 0, ( result, IF1left, exp3right), rest671)
end
|  ( 34, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( _, LPAREN1left, _))
 :: rest671)) => let val  result = MlyValue.exp (fn _ => (A.SeqExp([])
))
 in ( LrTable.NT 0, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 35, ( ( _, ( MlyValue.exps exps1, exps1left, exps1right)) :: 
rest671)) => let val  result = MlyValue.optionalExps (fn _ => let val 
 (exps as exps1) = exps1 ()
 in (A.SeqExp(exps))
end)
 in ( LrTable.NT 24, ( result, exps1left, exps1right), rest671)
end
|  ( 36, ( ( _, ( MlyValue.exp exp1, exp1left, exp1right)) :: rest671)
) => let val  result = MlyValue.optionalExps (fn _ => let val  (exp
 as exp1) = exp1 ()
 in (exp)
end)
 in ( LrTable.NT 24, ( result, exp1left, exp1right), rest671)
end
|  ( 37, ( ( _, ( MlyValue.idEQExpPairs idEQExpPairs1, 
idEQExpPairs1left, idEQExpPairs1right)) :: rest671)) => let val  
result = MlyValue.optionalIdEQExpPairs (fn _ => let val  (idEQExpPairs
 as idEQExpPairs1) = idEQExpPairs1 ()
 in (idEQExpPairs)
end)
 in ( LrTable.NT 20, ( result, idEQExpPairs1left, idEQExpPairs1right),
 rest671)
end
|  ( 38, ( rest671)) => let val  result = 
MlyValue.optionalIdEQExpPairs (fn _ => ([]))
 in ( LrTable.NT 20, ( result, defaultPos, defaultPos), rest671)
end
|  ( 39, ( ( _, ( MlyValue.idEQExpPairs idEQExpPairs1, _, 
idEQExpPairs1right)) :: _ :: ( _, ( MlyValue.idEQExpPair idEQExpPair1,
 idEQExpPair1left, _)) :: rest671)) => let val  result = 
MlyValue.idEQExpPairs (fn _ => let val  (idEQExpPair as idEQExpPair1)
 = idEQExpPair1 ()
 val  (idEQExpPairs as idEQExpPairs1) = idEQExpPairs1 ()
 in (idEQExpPair :: idEQExpPairs)
end)
 in ( LrTable.NT 15, ( result, idEQExpPair1left, idEQExpPairs1right), 
rest671)
end
|  ( 40, ( ( _, ( MlyValue.idEQExpPair idEQExpPair1, idEQExpPair1left,
 idEQExpPair1right)) :: rest671)) => let val  result = 
MlyValue.idEQExpPairs (fn _ => let val  (idEQExpPair as idEQExpPair1)
 = idEQExpPair1 ()
 in ([idEQExpPair])
end)
 in ( LrTable.NT 15, ( result, idEQExpPair1left, idEQExpPair1right), 
rest671)
end
|  ( 41, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.ID ID1, (IDleft as ID1left), _)) :: rest671)) => let val  
result = MlyValue.idEQExpPair (fn _ => let val  (ID as ID1) = ID1 ()
 val  (exp as exp1) = exp1 ()
 in ((Symbol.symbol(ID), exp, IDleft))
end)
 in ( LrTable.NT 19, ( result, ID1left, exp1right), rest671)
end
|  ( 42, ( ( _, ( MlyValue.expsRest expsRest1, _, expsRest1right)) ::
 _ :: ( _, ( MlyValue.exp exp1, (expleft as exp1left), _)) :: rest671)
) => let val  result = MlyValue.exps (fn _ => let val  (exp as exp1) =
 exp1 ()
 val  (expsRest as expsRest1) = expsRest1 ()
 in ((exp, expleft)::expsRest)
end)
 in ( LrTable.NT 5, ( result, exp1left, expsRest1right), rest671)
end
|  ( 43, ( ( _, ( MlyValue.exp exp1, (expleft as exp1left), exp1right)
) :: rest671)) => let val  result = MlyValue.expsRest (fn _ => let
 val  (exp as exp1) = exp1 ()
 in ([(exp, expleft)])
end)
 in ( LrTable.NT 21, ( result, exp1left, exp1right), rest671)
end
|  ( 44, ( ( _, ( MlyValue.expsRest expsRest1, _, expsRest1right)) ::
 _ :: ( _, ( MlyValue.exp exp1, (expleft as exp1left), _)) :: rest671)
) => let val  result = MlyValue.expsRest (fn _ => let val  (exp as 
exp1) = exp1 ()
 val  (expsRest as expsRest1) = expsRest1 ()
 in ((exp, expleft) :: expsRest)
end)
 in ( LrTable.NT 21, ( result, exp1left, expsRest1right), rest671)
end
|  ( 45, ( ( _, ( MlyValue.commaExps commaExps1, commaExps1left, 
commaExps1right)) :: rest671)) => let val  result = 
MlyValue.optionalCommaExps (fn _ => let val  (commaExps as commaExps1)
 = commaExps1 ()
 in (commaExps)
end)
 in ( LrTable.NT 23, ( result, commaExps1left, commaExps1right), 
rest671)
end
|  ( 46, ( rest671)) => let val  result = MlyValue.optionalCommaExps
 (fn _ => ([]))
 in ( LrTable.NT 23, ( result, defaultPos, defaultPos), rest671)
end
|  ( 47, ( ( _, ( MlyValue.commaExps commaExps1, _, commaExps1right))
 :: _ :: ( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671)) => let
 val  result = MlyValue.commaExps (fn _ => let val  (exp as exp1) = 
exp1 ()
 val  (commaExps as commaExps1) = commaExps1 ()
 in (exp :: commaExps)
end)
 in ( LrTable.NT 22, ( result, exp1left, commaExps1right), rest671)

end
|  ( 48, ( ( _, ( MlyValue.exp exp1, exp1left, exp1right)) :: rest671)
) => let val  result = MlyValue.commaExps (fn _ => let val  (exp as 
exp1) = exp1 ()
 in ([exp])
end)
 in ( LrTable.NT 22, ( result, exp1left, exp1right), rest671)
end
|  ( 49, ( ( _, ( MlyValue.decs decs1, _, decs1right)) :: ( _, ( 
MlyValue.dec dec1, dec1left, _)) :: rest671)) => let val  result = 
MlyValue.decs (fn _ => let val  (dec as dec1) = dec1 ()
 val  (decs as decs1) = decs1 ()
 in (dec::decs)
end)
 in ( LrTable.NT 4, ( result, dec1left, decs1right), rest671)
end
|  ( 50, ( rest671)) => let val  result = MlyValue.decs (fn _ => ([]))
 in ( LrTable.NT 4, ( result, defaultPos, defaultPos), rest671)
end
|  ( 51, ( ( _, ( MlyValue.tydecList tydecList1, tydecList1left, 
tydecList1right)) :: rest671)) => let val  result = MlyValue.dec (fn _
 => let val  (tydecList as tydecList1) = tydecList1 ()
 in (tydecList)
end)
 in ( LrTable.NT 3, ( result, tydecList1left, tydecList1right), 
rest671)
end
|  ( 52, ( ( _, ( MlyValue.vardec vardec1, vardec1left, vardec1right))
 :: rest671)) => let val  result = MlyValue.dec (fn _ => let val  (
vardec as vardec1) = vardec1 ()
 in (vardec)
end)
 in ( LrTable.NT 3, ( result, vardec1left, vardec1right), rest671)
end
|  ( 53, ( ( _, ( MlyValue.fundecList fundecList1, fundecList1left, 
fundecList1right)) :: rest671)) => let val  result = MlyValue.dec (fn
 _ => let val  (fundecList as fundecList1) = fundecList1 ()
 in (fundecList)
end)
 in ( LrTable.NT 3, ( result, fundecList1left, fundecList1right), 
rest671)
end
|  ( 54, ( ( _, ( MlyValue.tydecs tydecs1, tydecs1left, tydecs1right))
 :: rest671)) => let val  result = MlyValue.tydecList (fn _ => let
 val  (tydecs as tydecs1) = tydecs1 ()
 in (A.TypeDec(tydecs))
end)
 in ( LrTable.NT 6, ( result, tydecs1left, tydecs1right), rest671)
end
|  ( 55, ( ( _, ( MlyValue.tydecs tydecs1, _, tydecs1right)) :: ( _, (
 MlyValue.tydec tydec1, tydec1left, _)) :: rest671)) => let val  
result = MlyValue.tydecs (fn _ => let val  (tydec as tydec1) = tydec1
 ()
 val  (tydecs as tydecs1) = tydecs1 ()
 in (tydec :: tydecs)
end)
 in ( LrTable.NT 7, ( result, tydec1left, tydecs1right), rest671)
end
|  ( 56, ( ( _, ( MlyValue.tydec tydec1, tydec1left, tydec1right)) :: 
rest671)) => let val  result = MlyValue.tydecs (fn _ => let val  (
tydec as tydec1) = tydec1 ()
 in ([tydec])
end)
 in ( LrTable.NT 7, ( result, tydec1left, tydec1right), rest671)
end
|  ( 57, ( ( _, ( MlyValue.ty ty1, _, ty1right)) :: _ :: ( _, ( 
MlyValue.ID ID1, IDleft, _)) :: ( _, ( _, TYPE1left, _)) :: rest671))
 => let val  result = MlyValue.tydec (fn _ => let val  (ID as ID1) = 
ID1 ()
 val  (ty as ty1) = ty1 ()
 in (
{name = Symbol.symbol(ID),  (*51*)
          ty = ty, pos = IDleft})

end)
 in ( LrTable.NT 8, ( result, TYPE1left, ty1right), rest671)
end
|  ( 58, ( ( _, ( MlyValue.ID ID1, (IDleft as ID1left), ID1right)) :: 
rest671)) => let val  result = MlyValue.ty (fn _ => let val  (ID as 
ID1) = ID1 ()
 in (A.NameTy(Symbol.symbol(ID), IDleft))
end)
 in ( LrTable.NT 13, ( result, ID1left, ID1right), rest671)
end
|  ( 59, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( 
MlyValue.optionalFields optionalFields1, _, _)) :: ( _, ( _, 
LBRACE1left, _)) :: rest671)) => let val  result = MlyValue.ty (fn _
 => let val  (optionalFields as optionalFields1) = optionalFields1 ()
 in (A.RecordTy(optionalFields))
end)
 in ( LrTable.NT 13, ( result, LBRACE1left, RBRACE1right), rest671)

end
|  ( 60, ( ( _, ( MlyValue.ID ID1, _, ID1right)) :: _ :: ( _, ( _, (
ARRAYleft as ARRAY1left), _)) :: rest671)) => let val  result = 
MlyValue.ty (fn _ => let val  (ID as ID1) = ID1 ()
 in (A.ArrayTy(Symbol.symbol(ID), ARRAYleft))
end)
 in ( LrTable.NT 13, ( result, ARRAY1left, ID1right), rest671)
end
|  ( 61, ( ( _, ( MlyValue.tyfields tyfields1, tyfields1left, 
tyfields1right)) :: rest671)) => let val  result = 
MlyValue.optionalFields (fn _ => let val  (tyfields as tyfields1) = 
tyfields1 ()
 in (tyfields)
end)
 in ( LrTable.NT 18, ( result, tyfields1left, tyfields1right), rest671
)
end
|  ( 62, ( rest671)) => let val  result = MlyValue.optionalFields (fn
 _ => ([]))
 in ( LrTable.NT 18, ( result, defaultPos, defaultPos), rest671)
end
|  ( 63, ( ( _, ( MlyValue.tyfields tyfields1, _, tyfields1right)) ::
 _ :: ( _, ( MlyValue.tyfield tyfield1, tyfield1left, _)) :: rest671))
 => let val  result = MlyValue.tyfields (fn _ => let val  (tyfield as 
tyfield1) = tyfield1 ()
 val  (tyfields as tyfields1) = tyfields1 ()
 in (tyfield :: tyfields)
end)
 in ( LrTable.NT 14, ( result, tyfield1left, tyfields1right), rest671)

end
|  ( 64, ( ( _, ( MlyValue.tyfield tyfield1, tyfield1left, 
tyfield1right)) :: rest671)) => let val  result = MlyValue.tyfields
 (fn _ => let val  (tyfield as tyfield1) = tyfield1 ()
 in ([tyfield])
end)
 in ( LrTable.NT 14, ( result, tyfield1left, tyfield1right), rest671)

end
|  ( 65, ( ( _, ( MlyValue.ID ID2, _, ID2right)) :: _ :: ( _, ( 
MlyValue.ID ID1, (IDleft as ID1left), _)) :: rest671)) => let val  
result = MlyValue.tyfield (fn _ => let val  ID1 = ID1 ()
 val  ID2 = ID2 ()
 in (
{name = Symbol.symbol(ID1), escape = ref true, (*59*)
                             typ = Symbol.symbol(ID2), pos = IDleft}
)
end)
 in ( LrTable.NT 17, ( result, ID1left, ID2right), rest671)
end
|  ( 66, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.ID ID1, _, _)) :: ( _, ( _, (VARleft as VAR1left), _)) :: 
rest671)) => let val  result = MlyValue.vardec (fn _ => let val  (ID
 as ID1) = ID1 ()
 val  (exp as exp1) = exp1 ()
 in (
A.VarDec({name = Symbol.symbol(ID),     (*60*)
          escape = ref true, typ = NONE, init = exp, pos = VARleft})
)
end)
 in ( LrTable.NT 9, ( result, VAR1left, exp1right), rest671)
end
|  ( 67, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.ID ID2, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, IDleft, _)) ::
 ( _, ( _, (VARleft as VAR1left), _)) :: rest671)) => let val  result
 = MlyValue.vardec (fn _ => let val  (ID as ID1) = ID1 ()
 val  ID2 = ID2 ()
 val  (exp as exp1) = exp1 ()
 in (
A.VarDec({name = Symbol.symbol(ID), (*61*)
          escape = ref true, typ = SOME (Symbol.symbol(ID2), IDleft), 
          init = exp, pos = VARleft})
)
end)
 in ( LrTable.NT 9, ( result, VAR1left, exp1right), rest671)
end
|  ( 68, ( ( _, ( MlyValue.fundecs fundecs1, fundecs1left, 
fundecs1right)) :: rest671)) => let val  result = MlyValue.fundecList
 (fn _ => let val  (fundecs as fundecs1) = fundecs1 ()
 in (A.FunctionDec(fundecs))
end)
 in ( LrTable.NT 12, ( result, fundecs1left, fundecs1right), rest671)

end
|  ( 69, ( ( _, ( MlyValue.fundecs fundecs1, _, fundecs1right)) :: ( _
, ( MlyValue.fundec fundec1, fundec1left, _)) :: rest671)) => let val 
 result = MlyValue.fundecs (fn _ => let val  (fundec as fundec1) = 
fundec1 ()
 val  (fundecs as fundecs1) = fundecs1 ()
 in (fundec :: fundecs)
end)
 in ( LrTable.NT 11, ( result, fundec1left, fundecs1right), rest671)

end
|  ( 70, ( ( _, ( MlyValue.fundec fundec1, fundec1left, fundec1right))
 :: rest671)) => let val  result = MlyValue.fundecs (fn _ => let val 
 (fundec as fundec1) = fundec1 ()
 in ([fundec])
end)
 in ( LrTable.NT 11, ( result, fundec1left, fundec1right), rest671)

end
|  ( 71, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: _ :: ( _, 
( MlyValue.optionalFields optionalFields1, _, _)) :: _ :: ( _, ( 
MlyValue.ID ID1, _, _)) :: ( _, ( _, (FUNCTIONleft as FUNCTION1left),
 _)) :: rest671)) => let val  result = MlyValue.fundec (fn _ => let
 val  (ID as ID1) = ID1 ()
 val  (optionalFields as optionalFields1) = optionalFields1 ()
 val  (exp as exp1) = exp1 ()
 in (
{  (*65*)
          name = Symbol.symbol(ID), params = optionalFields, result = NONE, 
          body = exp, pos = FUNCTIONleft}
)
end)
 in ( LrTable.NT 10, ( result, FUNCTION1left, exp1right), rest671)
end
|  ( 72, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.ID ID2, ID2left, _)) :: _ :: _ :: ( _, ( 
MlyValue.optionalFields optionalFields1, _, _)) :: _ :: ( _, ( 
MlyValue.ID ID1, _, _)) :: ( _, ( _, (FUNCTIONleft as FUNCTION1left),
 _)) :: rest671)) => let val  result = MlyValue.fundec (fn _ => let
 val  ID1 = ID1 ()
 val  (optionalFields as optionalFields1) = optionalFields1 ()
 val  ID2 = ID2 ()
 val  (exp as exp1) = exp1 ()
 in (
{name = Symbol.symbol(ID1), params = optionalFields, 
          result = SOME (Symbol.symbol(ID2), ID2left), body = exp, 
          pos = FUNCTIONleft}
)
end)
 in ( LrTable.NT 10, ( result, FUNCTION1left, exp1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.program x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : Tiger_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun INT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.INT (fn () => i),p1,p2))
fun STRING (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.STRING (fn () => i),p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun SEMICOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun DOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun TIMES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun DIVIDE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun EQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun NEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun LT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun LE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun GT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun GE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
fun OR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID,p1,p2))
fun ASSIGN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID,p1,p2))
fun ARRAY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun THEN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun ELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun WHILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID,p1,p2))
fun FOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID,p1,p2))
fun TO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
fun DO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID,p1,p2))
fun LET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID,p1,p2))
fun IN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID,p1,p2))
fun END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.VOID,p1,p2))
fun OF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.VOID,p1,p2))
fun BREAK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.VOID,p1,p2))
fun NIL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.VOID,p1,p2))
fun FUNCTION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.VOID,p1,p2))
fun VAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.VOID,p1,p2))
fun TYPE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.VOID,p1,p2))
fun UMINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.VOID,p1,p2))
fun LOWPREC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(
ParserData.MlyValue.VOID,p1,p2))
fun LVALUEPREC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 46,(
ParserData.MlyValue.VOID,p1,p2))
end
end
