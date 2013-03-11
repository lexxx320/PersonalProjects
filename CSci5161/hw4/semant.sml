signature SEMANT =
sig
  type exp
  type transty
  val transProg: exp -> transty
end


functor SemantFun(structure A: ABSYN
                  structure E: ENV
                  structure Symbol: SYMBOL
                    sharing type A.symbol = E.symbol = Symbol.symbol
                        and type E.table = Symbol.table) : SEMANT 
             where type transty = E.ty 
               and type exp = A.exp =
struct

type  exp = A.exp
type  transty = E.ty
val error = ErrorMsg.error

(*This is used as a placeholder for patterns that have not yet been implemented.  
It's primary use is to suppress non-exhaustive pattern matching warnings*)
exception NotImplemented

(*This function is used to check that a symbol exists in a list of symbol, 
ty pairs.  It is used for type checking FieldVars.  If the FieldVar member
is found in the list, we return its type*)
fun checkFieldVar([], s, pos) = (error pos ("Symbol \"" ^ Symbol.name(s) ^ 
                            "\" does is not a record member.\n"); E.ERROR)
   |checkFieldVar((xs : (Symbol.symbol * E.ty) list), s, pos) = 
                                     if #1(hd xs) = s
                                     then #2(hd xs)
                                     else checkFieldVar(xs, s, pos)                                                         

(*This function is used for type checking vars.  It's primary task is looking
things up in the environment to check that they are declared.*)
fun transVar(venv, A.SimpleVar(v, pos)) = 
                  (case Symbol.look(venv, v)
                      of SOME(E.VarEntry{ty,loopvar}) => ty
                        |_ => (error pos ("variable \"" ^ Symbol.name(v) ^ 
                          "not defined.\n"); E.ERROR))                  
   |transVar(venv, A.SubscriptVar(var, exp, pos)) = 
      (case transVar(venv, var) 
        of E.ARRAY(ty, _) => ty
          |E.ERROR => E.ERROR
          |_ => (error pos "lvalue needs to be of type Array\n"; E.ERROR))
   |transVar(venv, A.FieldVar(var, s, pos)) = 
      (case transVar(venv, var)
        of E.RECORD(symbols, _) => checkFieldVar(symbols, s, pos)
          |E.ERROR => E.ERROR
          |_ => (error pos "lvalue needs to be of type Record.\n"; E.ERROR))
                                 

(*This function resolves types for binary op AST's.  If one of the parameters
is already of type ERROR, then we do not print an error, and assume that it
has already been taken care of elsewhere.  Otherwise if there is a type error, 
we create an error*)
fun resolveBinOpType(l, r, pos) = case (l, r) of
      (E.INT, E.INT) => E.INT
     |(E.ERROR, _) => E.ERROR
     |(_, E.ERROR) => E.ERROR
     |_ => (error pos "Integer type needed.\n"; E.ERROR)

(*This function is used to check if two types are equal.  For record, and array
types, we simple check that their unique ID's match.  For NAME types, we 
recursively call equalTypes until we get "actual" type*)
fun equalTypes(E.INT, E.INT) = true
   |equalTypes(E.STRING, E.STRING) = true
   |equalTypes(E.NIL, _) = true
   |equalTypes(_, E.NIL) = true
   |equalTypes(E.UNIT, E.UNIT) = true
   |equalTypes(E.RECORD(_, u1), E.RECORD(_, u2)) = if !u1 = !u2
                                          then true else false
   |equalTypes(E.ARRAY(_, u1), E.ARRAY(_, u2)) = if !u1 = !u2
                                        then true else false
   |equalTypes(orig1 as E.NAME(s1,t1), orig2 as E.NAME(s2,t2)) = (case (!t1, !t2) 
      of (SOME(t1'), SOME(t2')) => equalTypes(t1', t2')
      |  (SOME(t1'), NONE) => equalTypes(t1', orig2)
      |  (NONE, SOME(t2')) => equalTypes(orig1, t2')
      |  (NONE, NONE) => raise NotImplemented)  (*Not sure what happens here*)
   |equalTypes(_,_) = false                                                                                                                        

(*This is the main type checking function, each pattern corresponds to 
a different type of node in the AST*)
fun transExp(venv, tenv, exp) = 
  let 
    fun trexp(A.OpExp({left, oper=A.PlusOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos)
      | trexp(A.OpExp({left, oper=A.MinusOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos)
      | trexp(A.OpExp({left, oper=A.TimesOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos)
      | trexp(A.OpExp({left, oper=A.DivideOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos) 
      | trexp(A.OpExp({left, oper=A.EqOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos) 
      | trexp(A.OpExp({left, oper=A.NeqOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos) 
      | trexp(A.OpExp({left, oper=A.LtOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos) 
      | trexp(A.OpExp({left, oper=A.LeOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos) 
      | trexp(A.OpExp({left, oper=A.GtOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos) 
      | trexp(A.OpExp({left, oper=A.GeOp, right, pos})) = 
          resolveBinOpType(trexp left, trexp right, pos)                      
      | trexp(A.VarExp(v)) = transVar(venv, v)
      | trexp(A.NilExp) = E.NIL
      | trexp(A.IntExp(_)) = E.INT
      | trexp(A.StringExp(_,_)) = E.STRING
      | trexp(A.CallExp({func, args, pos})) = raise NotImplemented
      | trexp(A.RecordExp{fields, typ, pos}) = raise NotImplemented
      | trexp(A.SeqExp(es)) = if List.null(es)
                              then E.UNIT
                              else trexp(#1(List.last(es)))
      | trexp(A.AssignExp({var, exp, pos})) = raise NotImplemented
      | trexp(A.IfExp({test, then', else'=NONE, pos})) = 
          let val testType = trexp(test)
              val check = case testType of
                             E.INT => ()
                            |_     => error pos "expected integer type.\n"
          in trexp(then') end
      | trexp(A.IfExp({test, then', else'=SOME elseBranch, pos})) = 
          let val testType = trexp(test)
              val checkCond = case testType of
                                E.INT => ()
                               |_     => error pos "expected integer type.\n"
              val thenType = trexp(then')
              val elseType = trexp(elseBranch)
          in if equalTypes(thenType, elseType)
             then thenType
             else (error pos ("then and else branch have different types\n,");
                           E.ERROR) 
          end
      | trexp(A.WhileExp({test, body, pos})) = 
          let val testType = trexp(test)
              val bodyType = trexp(body)
              val checkCond = case testType of
                                E.INT => ()
                               |_ => error pos "expected integer type.\n"
              val checkBody = case bodyType of
                                E.UNIT => ()
                               |E.ERROR => ()
                               |_ => error pos "expected unit type.\n"
          in E.UNIT end
      | trexp(A.ForExp({var, escape, lo, hi, body, pos})) = 
          let val loType = trexp(lo)
              val hiType = trexp(hi)
              val bodyType = trexp(body)    
              val check = (resolveBinOpType(trexp lo, trexp hi, pos))
          in case bodyType of
              E.UNIT => E.UNIT
             |E.ERROR => E.ERROR
             |_ => (error pos "body of for loop must be of type unit.\n";
                        E.ERROR)
          end                                            
                            

               
      | trexp(_) = raise NotImplemented    
  in
    trexp(exp)
  end

(*Used to typecheck an entire program.  This calls transExp where the 
venv is the base variable environment, and same thing for the type environment*)
fun transProg (exp) = transExp(E.base_venv, E.base_tenv, exp)


end







