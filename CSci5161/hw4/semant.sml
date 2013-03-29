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

(*Used for debugging purposes*)
fun say s =  print s
fun sayln s= (say s; say "\n") 

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

(*This exception gets raised if we encounter an erroneous member inside of 
a record in transTy.  This way we can handle the exception and give the entire
record the error type.*)
exception ErrorRecMem
exception CurrentError
(*This function is used for type checking vars.  It's primary task is looking
things up in the environment to check that they are declared.*)
fun transVar(venv, A.SimpleVar(v, pos)) = 
                  (case Symbol.look(venv, v)
                      of SOME(E.VarEntry{ty,loopvar}) => ty
                        |_ => (error pos ("variable \"" ^ Symbol.name(v) ^ 
                          "\" not defined.\n"); E.ERROR))                  
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

(*Translate Types*)
and transTy(tenv, A.NameTy(name, pos)) = (case Symbol.look(tenv, name)
            of SOME t => t
              |NONE => (error pos ("\"" ^ Symbol.name(name) ^ "\" not found " ^
                        "in type environment"); E.ERROR))
  |transTy(tenv, A.ArrayTy(name, pos)) = (case Symbol.look(tenv, name)
           of SOME t => E.ARRAY(t, ref())
             |NONE => (error pos ("\"" ^ Symbol.name(name) ^ "\" not found " ^ 
                        "in type environment"); E.ERROR))
  |transTy(tenv, A.RecordTy(fields)) = 
      let fun checkMembers({name,escape,typ,pos}::fs) = 
                   (name, transTy(tenv, A.NameTy(typ, pos))) :: checkMembers(fs)
             |checkMembers([]) = []
      in E.RECORD(checkMembers(fields), ref()) end
         
(*Translate declarations*)                                 
and transDec(venv, tenv, A.VarDec{name, escape, typ=NONE, init, pos}) = 
      let val eType = transExp(venv, tenv, init)
      in {tenv=tenv, venv=Symbol.enter(venv, name, E.VarEntry{ty=eType,
                  loopvar=false})}
      end
   |transDec(venv, tenv, A.VarDec{name, escape, typ=SOME(vName, vPos), init, pos}) =
      let val eType = transExp(venv, tenv, init)
      in if equalTypes(eType, transTy(tenv, A.NameTy(vName, vPos)))
         then {tenv=tenv, venv=Symbol.enter(venv, name, E.VarEntry{ty=eType,
                    loopvar=false})}
         else {tenv=tenv, venv=Symbol.enter(venv, name, E.VarEntry{ty=E.ERROR,
                    loopvar=false})}
      end
   |transDec(venv, tenv, A.TypeDec(args as {name, ty, pos}::rest)) = 
      let fun firstPass({name, ty, pos}::rest, env) = 
              firstPass(rest, Symbol.enter(env, name, E.NAME(name, ref(NONE))))
          val tenv' = firstPass(args, tenv)
          fun translateTypes({name, ty, pos}::rest) = 
              let val decl = Symbol.look(tenv', name)
                  val t = case decl of  (*Fix this.*)
                         
      in {venv=venv, tenv=tenv} end
          
      (*transDec(venv, Symbol.enter(tenv, name, transTy(tenv, ty)), A.TypeDec(rest))*)
   |transDec(venv, tenv, A.TypeDec([])) = {venv=venv, tenv=tenv}
   |transDec(venv, tenv, A.FunctionDec[{name,params,body,pos,
      result=SOME(rt, pos')}]) = 
      let val SOME(result_ty) = Symbol.look(tenv, rt)
          fun transparam{name, typ, pos,escape} = case Symbol.look(tenv, typ)
                of SOME t => {name=name, ty=t}
          val params' = map transparam params
          val venv' = Symbol.enter(venv, name, 
                          E.FunEntry{formals=map #ty params',result=result_ty})
          fun enterparams ({name,ty}::tys) venv = 
              enterparams tys (Symbol.enter(venv, name, E.VarEntry{loopvar=false, 
                ty=ty}))
            |enterparams [] venv = venv
          val venv'' = enterparams params' venv'
      in (transExp(venv'', tenv, body); 
         {venv=venv', tenv=tenv})
      end

and transDecs(dec::decs, venv, tenv) = 
      let val {venv=venv', tenv=tenv'} = transDec(venv, tenv, dec)
      in transDecs(decs, venv', tenv') end
   |transDecs([], venv, tenv) = (venv, tenv)
      
                                                                                                               
(*This is the main type checking function, each pattern corresponds to 
a different type of node in the AST*)
and transExp(venv, tenv, exp) = 
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
      | trexp(A.CallExp({func, args, pos})) = 
          let val SOME (E.FunEntry{formals=formals, result=result}) = 
                    Symbol.look(venv, func)
              fun checkArgs (e::es) (ty::tys) i = 
                    if equalTypes(ty, trexp(e))
                    then checkArgs es tys (i+1)
                    else (error pos ("type mismatch on argument " ^ 
                            Int.toString(i)); false)
                 |checkArgs [] [] i = true
                 |checkArgs _ _ _ =(error pos "incorrect number of arguments\n"; 
                                        false)
          in if checkArgs args formals 0
             then result 
             else E.ERROR end          
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
      | trexp(A.LetExp({decs, body, pos})) = 
          let val (venv', tenv') = transDecs(decs, venv, tenv)
          in transExp(venv', tenv', body) end   
      | trexp(A.ArrayExp{typ, size, init, pos}) = 
          let val initType = trexp(init)
              val arrayType = transTy(tenv, A.NameTy(typ, pos))
              fun getArrayType ty = case ty 
                      of E.ARRAY(ty', _) => ty'
                        |E.NAME(_, ref (SOME ty')) => getArrayType(ty')
                        |_ => E.ERROR                   
          in if equalTypes(initType, getArrayType(arrayType))
             then arrayType (*Check that init is a valid type*)
             else E.ERROR            
          end    
      | trexp(A.RecordExp{fields, typ, pos}) = (
          let exception RecordExpError
              fun trRecExp() =
                    (*Lookup declaration associated with record name*)
                let val recordDecl = (case Symbol.look(tenv, typ)
                      of SOME t => t
                        |NONE => (error pos ("record \"" ^ Symbol.name(typ) ^ 
                          "\" was not declared.\n"); raise RecordExpError))
                    val E.RECORD(recFields, _) = recordDecl (*get the fields*)
                    (*Check that a given symbol is a member of the record*)
                    fun lookup(member, (name,ty)::fields) = 
                          if member = name
                          then ty
                          else lookup(member, fields)
                       |lookup(member, []) = (error pos ("member \"" ^ 
                          Symbol.name(member) ^ "\" is not a record member \"");
                                   raise RecordExpError)
               (*Iterate through each field checking that it is a valid member*)
                    fun checkMembers((mem, e, pos)::rest) = 
                       let val eType = trexp(e)
                           val memType = lookup(mem, recFields)
                       in if equalTypes(eType, memType)
                          then checkMembers(rest)
                          else raise RecordExpError
                       end
                        |checkMembers([]) = recordDecl
                in (checkMembers(fields)) end
          in trRecExp() end handle RecordExpError => E.ERROR   )
          
      | trexp(_) = raise NotImplemented
  in
    trexp(exp)
  end


(*Used to typecheck an entire program.  This calls transExp where the 
venv is the base variable environment, and same thing for the type environment*)
fun transProg (exp) = transExp(E.base_venv, E.base_tenv, exp)


end







