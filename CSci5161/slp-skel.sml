type id = string

datatype binop = Plus | Minus | Times | Div

datatype stm = CompoundStm of stm * stm
	     | AssignStm of id * exp
	     | PrintStm of exp list

     and exp = IdExp of id
	     | NumExp of int
       | OpExp of exp * binop * exp
       | EseqExp of stm * exp

type table = (id * int) list

exception LookUp

fun lookup nil id = 
     (print "Error: undefined id "; print id; print "\n"; 
      raise LookUp)
  | lookup ((n,v)::t) id =
       if n = id then v else lookup t id

fun update nil id v = [(id,v)]
  | update ((id',v')::t) id v =
       if id = id' then (id,v) :: t
       else (id',v') :: update t id v

val prog = 
 CompoundStm(AssignStm("a",OpExp(NumExp 5, Plus, NumExp 3)),
  CompoundStm(AssignStm("b",
      EseqExp(PrintStm[IdExp"a",OpExp(IdExp"a", Minus,NumExp 1)],
           OpExp(NumExp 10, Times, IdExp"a"))),
   PrintStm[IdExp "b"]) )

(*Probelm 1 Part 1*)
fun maxargs (PrintStm (e)) = 1 + (checkEseqExp e)
  |maxargs (AssignStm (lhs, rhs)) = checkEseqExp [rhs]
  |maxargs (CompoundStm (first, rest)) = maxargs first + maxargs rest

and checkEseqExp (nil) : int = 0 
  |checkEseqExp (x::xs) = case x of
	   (IdExp(_)) => checkEseqExp xs
	  |(NumExp(_)) => checkEseqExp xs
    |(OpExp(_,_,_)) => checkEseqExp xs
    |(EseqExp(s, _)) => (maxargs s) + (checkEseqExp xs)
 
(*Problem 1 Part 2*)

fun interpStm (CompoundStm(first, rest)) env = interpStm rest (interpStm first env)
   |interpStm (AssignStm(lhs, rhs)) env = update env lhs (interpExp rhs env)
   |interpStm (PrintStm(e)) env = (interpExprs e env)

and interpExp (IdExp id) env= ((lookup env id), env)

and interpExprs (x::xs) env = interpExprs xs (interpExp x env)
   |interpExprs nil env = env

fun interp (s:stm) = interpStm s []













