(*
Name: Matthew Le
ID: 3975089
Date: 2/6/2013
Problem 1
*)

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

val prog2 = 
  CompoundStm(
    AssignStm("a",OpExp(NumExp 5, Plus, NumExp 3)),
    CompoundStm(AssignStm("b",
                EseqExp(PrintStm[IdExp"a",
                                 EseqExp(PrintStm [IdExp "a", 
                                                   IdExp "a", 
                                                   IdExp "a"],
                                         OpExp(IdExp"a", Minus,NumExp 1)),
                                 EseqExp(PrintStm[NumExp 4, 
                                                  NumExp 4, 
                                                  NumExp 4, 
                                                  NumExp 4
                                                 ],
                                         OpExp( IdExp "a", Minus, NumExp 3))],
                        OpExp(NumExp 10, Times, IdExp"a"))),
                PrintStm[IdExp "b"]))

val prog3 = 
 CompoundStm(AssignStm("a",OpExp(NumExp 5, Plus, NumExp 3)),
             CompoundStm(
                AssignStm("b",
                          EseqExp(PrintStm[IdExp"a",
                                           EseqExp(AssignStm("a",
                                                             OpExp(IdExp "a", 
                                                                   Times, 
                                                                   NumExp 5)),
                                                   OpExp(IdExp"a", 
                                                         Minus,
                                                         NumExp 1))],
                                  OpExp(NumExp 10, Times, IdExp"a"))),
             PrintStm[IdExp "b"]))

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
   |interpStm (AssignStm(lhs, rhs)) env = let val (e, env') = interpExp rhs env
                                          in update env' lhs e end
   |interpStm (PrintStm(e)) env = printExprs e env

and interpExp (IdExp id) env = ((lookup env id), env)
   |interpExp (NumExp n) env = (n, env)
   |interpExp (OpExp(l, binOp, r)) env = let val (lEvaluated, env') = interpExp l env
                                             val (rEvaluated, env'') = interpExp r env'
                                         in case binOp of
                                             Times => (lEvaluated * rEvaluated, env'')
                                            |Div => (lEvaluated div rEvaluated, env'')
                                            |Plus => (lEvaluated + rEvaluated, env'')
                                            |Minus => (lEvaluated - rEvaluated, env'')
                                         end
   |interpExp (EseqExp(s, e)) env = let val env' = interpStm s env
                                    in interpExp e env' end    
                                    
and printExprs (x::xs) env = let val (e, env') = interpExp x env
                                 val dummy = print(Int.toString(e) ^ " ")
                             in 
                                 (printExprs xs env') end
   |printExprs nil env = (print "\n"; env)
                                                                    
fun interp (s:stm) = (interpStm s [])












