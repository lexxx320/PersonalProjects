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
fun checkFieldVar([], s, pos) = (error pos ("Error: no record field with name " 
                                  ^ Symbol.name(s)); E.ERROR)
   |checkFieldVar((xs : (Symbol.symbol * E.ty) list), s, pos) = 
                                     if #1(hd xs) = s
                                     then #2(hd xs)
                                     else checkFieldVar(tl(xs), s, pos)  
(*Given a type, print out what that type is.  This is used for printing 
  errors*)                                     
fun printType t = case t 
      of E.INT => "integer"
        |E.STRING => "string"
        |E.NIL => "nil"
        |E.UNIT => "unit"
        |E.RECORD(_,_) => "record"
        |E.ARRAY(_) => "array"
        |E.NAME(_,_) => "name"
        |E.ERROR => "error"
                                                                                         
(*This function resolves types for binary op AST's.  If one of the parameters
is already of type ERROR, then we do not print an error, and assume that it
has already been taken care of elsewhere.  Otherwise if there is a type error, 
we create an error*)
fun checkArithOpTypes(l, r, pos, opUsed) = case (l, r) of
      (E.INT, E.INT) => E.INT
     |(E.ERROR, _) => E.ERROR
     |(_, E.ERROR) => E.ERROR
     |(E.INT, _) => (error pos ("Error: right argument to " ^ opUsed ^ 
                              " not of integer type"); E.ERROR)
     |(_,E.INT) => (error pos ("Error: left argument to " ^ opUsed ^ 
                              " not of integer type"); E.ERROR)                      
     |_ => (error pos "Error: neither types integer.\n"; E.ERROR)

(*Type check relational operator expressions*)
fun checkComparisonOpTypes(t1, t2, pos) = case (t1, t2) 
    of (E.INT, E.INT) => E.INT
      |(E.NIL, _) => E.INT
      |(_, E.NIL) => E.INT
      |(E.STRING, E.STRING) => E.INT
      |(E.ERROR,_) => E.ERROR
      |(_,E.ERROR) => E.ERROR
      |(a,b) => (error pos ("Error: right argument must be of " ^ printType(t1) ^ 
                  " type"); E.ERROR)

(*Get the absolute type as described in the textbook.*)
fun absType(E.NAME(s1, t1)) = (case !t1 
        of SOME(t1') => absType(t1') 
          |NONE =>  E.ERROR)
   |absType(t1) = t1


     

(*This function is used to check if two types are equal.  For record, and array
types, we simple check that their unique ID's match.  For NAME types, we 
recursively call equalTypes until we get "actual" type*)
fun equalTypes t1 t2 = let
  fun equalTypes'(E.INT, E.INT) = true
     |equalTypes'(E.STRING, E.STRING) = true
     |equalTypes'(E.NIL, _) = true
     |equalTypes'(_, E.NIL) = true
     |equalTypes'(E.UNIT, E.UNIT) = true
     |equalTypes'(E.ERROR, E.ERROR) = true
     |equalTypes'(E.RECORD(_, u1), E.RECORD(_, u2)) = if u1 = u2
                                            then true else false
     |equalTypes'(E.ARRAY(_, u1), E.ARRAY(_, u2)) = if u1 = u2
                                          then true else false
     |equalTypes'(l, r) = false
  in equalTypes'(absType(t1), absType(t2)) end



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
                        |_ => (error pos ("Error: undefined variable " ^ 
                              Symbol.name(v)); E.ERROR))                  
   |transVar(venv, A.SubscriptVar(var, exp, pos)) = 
      (case absType(transVar(venv, var))
        of E.ARRAY(ty, _) => ty
          |E.ERROR => E.ERROR
          |_ => (error pos "Error: non-array type used in indexed access"; E.ERROR))
   |transVar(venv, A.FieldVar(var, s, pos)) = 
      (case absType(transVar(venv, var))
        of E.RECORD(symbols, _) => checkFieldVar(symbols, s, pos)
          |E.ERROR => E.ERROR
          |_ => (error pos "Error: non-record type used in record selection"; E.ERROR))

(*Translate Types*)
and transTy(tenv, A.NameTy(name, pos)) = (case Symbol.look(tenv, name)
            of SOME t =>  t
              |NONE => (error pos ("Error: Undefined type symbol " ^
                        Symbol.name(name)); E.ERROR))
  |transTy(tenv, A.ArrayTy(name, pos)) = (case Symbol.look(tenv, name)
           of SOME t => E.ARRAY(t, ref())
             |NONE => (error pos ("\"" ^ Symbol.name(name) ^ "\" not found " ^ 
                        "in type environment"); E.ERROR))
  |transTy(tenv, A.RecordTy(fields)) = 
      let fun checkMembers({name,escape,typ,pos}::fs) = 
                   (name, transTy(tenv, A.NameTy(typ, pos))) :: checkMembers(fs)
             |checkMembers([]) = []
      in  E.RECORD(checkMembers(fields), ref()) end
         
(*Translate declarations*)                                 
and transDec(venv, tenv, A.VarDec{name, escape, typ=NONE, init, pos}) = 
      let val eType = transExp(venv, tenv, init)
      in case absType(eType)
         of E.NIL => (error pos ("Error: variable being declared of" ^ 
                " indeterminate record type"); {tenv=tenv, venv=Symbol.enter(
                  venv, name, E.VarEntry{ty=E.ERROR, loopvar=false})})
           |E.UNIT => (error pos ("Error: unit type not valid for " ^ 
                    "initializing expression"); {tenv=tenv, venv=Symbol.enter(
                      venv, name, E.VarEntry{ty=E.ERROR,loopvar=false})})
           |_ => {tenv=tenv, venv=Symbol.enter(venv, name, E.VarEntry{ty=eType,
                  loopvar=false})}
      end
   |transDec(venv, tenv, A.VarDec{name, escape, typ=SOME(vName, vPos), init, pos}) =
      let val eType = transExp(venv, tenv, init)
          val givenType = absType(transTy(tenv, A.NameTy(vName, vPos)))
          val noError = {tenv=tenv, venv=Symbol.enter(venv,name,
                           E.VarEntry{ty=givenType,loopvar=false})}
          val withError = {tenv=tenv, venv=Symbol.enter(venv, name, 
                          E.VarEntry{ty=E.ERROR, loopvar=false})}
      in case (absType(eType), absType(givenType))
          of (E.INT, E.INT) => noError
            |(E.STRING, E.STRING) => noError
            |(E.NIL, _) => noError
            |(_, E.NIL) => noError
            |(E.UNIT, E.UNIT) => noError
            |(E.ERROR, E.ERROR) => noError (*Questionable*)
            |(E.RECORD(_, u1), E.RECORD(_, u2)) => 
                if u1 = u2
                then noError
                else (error pos "Error: (record) type does not match definition";
                          noError) (*Questionable*)
            |(E.ARRAY(_, u1), E.ARRAY(_, u2)) => 
                if u1 = u2
                then noError
                else (error pos "Error (array) type does not match definition";
                        noError) (*Questionable*)
            |(l, r) => (error pos ("Error: " ^ printType(givenType) ^ 
                            " expression expected"); noError) (*Questionable*)
    end
   |transDec(venv, tenv, A.TypeDec(args as {name, ty, pos}::rest)) = 
                (*Add all type names to the environment*)
      let fun firstPass({name, ty, pos}::rest, env) = 
            let val check = if List.exists(fn x => x = name) (map #name rest)
                            then (error pos ("Error: type " ^ Symbol.name(name) ^
                                " multiply defined in mutually recursive block");
                                false)
                            else true
            in if check
               then firstPass(rest, Symbol.enter(env, name, 
                      E.NAME(name, ref(SOME(E.ERROR)))))
               else firstPass(rest, Symbol.enter(env, name,   
                      E.NAME(name, ref(NONE))))
            end
             |firstPass([], env) = env
          val tenv' = firstPass(args, tenv)
          fun printList (x::xs) = (Symbol.name(x) ^ printList(xs))
             |printList [] = "\n"
          fun checkForCycle(E.NAME(sym, ref(SOME(nt))), soFar) = 
                  if List.exists(fn x => x = sym) soFar
                  then true
                  else checkForCycle(nt, sym::soFar)
             |checkForCycle(_, _) =  false
          (*Translate each type now that all type names have been added*)
          fun translateTypes({name, ty, pos}::rest) = 
              let val t = case Symbol.look(tenv', name) 
                              of SOME(E.NAME(_, theType)) => theType
                                |_ => (error pos ("could not find " ^ 
                                  Symbol.name(name) ^ " in type environment\n"); 
                                  ref(SOME(E.ERROR)))
                  val translated = case !t of 
                         SOME(E.NAME(_,ref(SOME(E.ERROR)))) => E.ERROR
                        |_ => transTy(tenv', ty)
              in (t := SOME(translated); translated :: translateTypes(rest)) end   
              |translateTypes([]) = []     
          fun thirdPass(typ::tys, {name,ty,pos}::rest) = 
              let val t = case Symbol.look(tenv', name)
                            of SOME(E.NAME(_,theType)) => theType
                              |_ => ref(SOME(E.ERROR))
              in if checkForCycle(typ, [])
                 then (error pos ("Error: cyclic type definition for " ^ 
                      Symbol.name(name)); t := SOME(E.ERROR); 
                      thirdPass(tys, rest)) 
                 else thirdPass(tys, rest) end
             |thirdPass(_,_) = ()
      in (thirdPass(translateTypes(args), args); {venv=venv, tenv=tenv'}) end
   |transDec(venv, tenv, A.TypeDec([])) = {venv=venv, tenv=tenv}
   |transDec(venv, tenv, A.FunctionDec[]) = {venv=venv, tenv=tenv}
   (*Procedure/function declarations*)
   |transDec(venv, tenv, A.FunctionDec(defs as {name,params,body,pos,
      result}::rest)) = 
      let fun transparam{name, typ, pos,escape} = case Symbol.look(tenv, typ)
          of SOME t => {name=name, ty=t}
            |NONE => (error pos ("\"" ^ Symbol.name(typ) ^ "\" not declared\n"); 
                          {name=name, ty = E.ERROR})
                 (*Add functions to the variable environment*)
          fun firstPass({name, params, body, pos, result}::rest, env) = 
                let val params' = map transparam params
                    val check1 = if (List.exists(fn x => x = name)(map #name rest))
                                 then (error pos ("Error: function " ^ Symbol.name(name) ^ 
                                  " multiply defined in mutually recursive block");
                                  false)
                                 else true
                    val result_ty = case (result, check1)
                          of (SOME(rt, _), true) => (case Symbol.look(tenv, rt)
                                  of SOME(t) => t
                                    |NONE => E.ERROR)
                            |(NONE, true) => E.UNIT
                            |_ => E.ERROR
                in firstPass(rest, Symbol.enter(env, name, E.FunEntry{
                  formals = map #ty params', result=result_ty})) end
             |firstPass([], env) = env              
          val venv' = firstPass(defs, venv)
          fun enterparams ({name,ty}::tys) venv = 
              enterparams tys (Symbol.enter(venv, name, E.VarEntry{loopvar=false, 
                ty=ty}))
            |enterparams [] venv = venv
            (*Translate bodies*)
          fun transBodies({name, params, body, pos, result}::rest) = 
              let val params' = map transparam params
                  val venv'' = enterparams params' venv'
                  val bodyType = transExp(venv'', tenv, body)
                  val res_ty = case result 
                          of SOME(rt,_) => (case Symbol.look(tenv, rt) 
                                  of SOME(s) => s
                                    |NONE => E.ERROR)
                            |NONE => E.UNIT
              in if equalTypes bodyType res_ty
                 then transBodies(rest) 
                 else (error pos ("Error: function body not of " ^ 
                      printType(res_ty) ^ " type"); transBodies(rest)) end
             |transBodies([]) = ()
      in (transBodies(defs); {venv=venv', tenv=tenv})
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
          (checkArithOpTypes(trexp left, trexp right, pos, "+"); E.INT)
      | trexp(A.OpExp({left, oper=A.MinusOp, right, pos})) = 
          (checkArithOpTypes(trexp left, trexp right, pos, "-"); E.INT)
      | trexp(A.OpExp({left, oper=A.TimesOp, right, pos})) = 
          (checkArithOpTypes(trexp left, trexp right, pos, "*"); E.INT)
      | trexp(A.OpExp({left, oper=A.DivideOp, right, pos})) = 
          (checkArithOpTypes(trexp left, trexp right, pos, "/"); E.INT)
      | trexp(A.OpExp({left, oper=A.EqOp, right, pos})) = 
         ( case (trexp left, trexp right) 
              of (E.INT, E.INT) => E.INT
                |(E.STRING,E.STRING) => E.INT
                |(E.NIL, _) => E.INT
                |(_, E.NIL) => E.INT
                |(E.RECORD(_, u1), E.RECORD(_, u2)) => if u1 = u2
                   then E.INT
                   else (error pos "record types are not equal."; E.INT)
                |(E.ARRAY(_, u1), E.ARRAY(_, u2)) => if u1 = u2
                   then E.INT
                   else (error pos "array types are not equal."; E.INT)
                |(E.ERROR, _) => (E.INT)
                |(_, E.ERROR) => (E.INT)
                |(a, b) => (error pos ("Error: right argument must be of " ^ 
                    printType(a) ^ " type identical to left"); E.INT))
      | trexp(A.OpExp({left, oper=A.NeqOp, right, pos})) = 
         ( case (trexp left, trexp right) 
              of (E.INT, E.INT) => E.INT
                |(E.STRING,E.STRING) => E.INT
                |(E.NIL, _) => E.INT
                |(_, E.NIL) => E.INT
                |(E.RECORD(_, u1), E.RECORD(_, u2)) => if u1 = u2
                   then E.INT
                   else (error pos "record types are not equal."; E.INT)
                |(E.ARRAY(_, u1), E.ARRAY(_, u2)) => if u1 = u2
                   then E.INT
                   else (error pos "array types are not equal."; E.INT)
                |(E.ERROR, _) => (E.INT)
                |(_, E.ERROR) => (E.INT)
                |(a, b) => (error pos ("Error: right argument must be of " ^ 
                  printType(absType(a)) ^ " type identical to left"); E.INT))
      | trexp(A.OpExp({left, oper=A.LtOp, right, pos})) = 
          (checkComparisonOpTypes(trexp left, trexp right, pos); E.INT)
      | trexp(A.OpExp({left, oper=A.LeOp, right, pos})) = 
          (checkComparisonOpTypes(trexp left, trexp right, pos); E.INT)
      | trexp(A.OpExp({left, oper=A.GtOp, right, pos})) = 
          (checkComparisonOpTypes(trexp left, trexp right, pos); E.INT)
      | trexp(A.OpExp({left, oper=A.GeOp, right, pos})) = 
          (checkComparisonOpTypes(trexp left, trexp right, pos); E.INT)             
      | trexp(A.VarExp(v)) = transVar(venv, v)
      | trexp(A.NilExp) = E.NIL
      | trexp(A.IntExp(_)) = E.INT
      | trexp(A.StringExp(_,_)) = E.STRING
      | trexp(A.CallExp({func, args, pos})) = 
          let val (valid, {formals=formals, result=result}) = 
                case Symbol.look(venv, func)
                     of SOME(E.FunEntry(fe)) => (true, fe)
                       |NONE => (error pos ("Error: undefined function " ^ 
                             Symbol.name(func)); 
                            (false, {formals=[], result=E.ERROR}))
                       |SOME(_) => (error pos ("\"" ^ Symbol.name(func) ^ 
                            "\" is not a function\n"); 
                            (false, {formals=[], result=E.ERROR}))
              fun checkArgs (e::es) (ty::tys) i state = 
                 let val resType = absType(trexp(e))
                 in
                    if (equalTypes ty resType) orelse (equalTypes E.ERROR resType)
                    then checkArgs es tys (i+1) state
                    else (error pos ("Error: " ^ printType(ty) ^ 
                      " expression expected at argument position " ^ 
                        Int.toString(i)); checkArgs es tys (i+1) false) end
                 |checkArgs [] [] i state = state
                 |checkArgs [] (x::xs) _ _= (error pos ("Error: function " ^ 
                   Symbol.name(func) ^ " applied to too few arguments"); false)
                 |checkArgs (x::xs)[] _ _= (error pos ("Error: function" ^ 
                   Symbol.name(func) ^ " applied to too many arguments"); false)
          in if valid
             then (checkArgs args formals 1 true; result)
             else result
                end         
      | trexp(A.SeqExp((e,p)::another::rest)) = (trexp(e); 
                  trexp(A.SeqExp(another::rest)))
      | trexp(A.SeqExp((e,p)::[])) = trexp(e)
      | trexp(A.SeqExp([])) = E.UNIT
      | trexp(A.AssignExp({var, exp, pos})) = 
          let val varType = transVar(venv, var)
             (*Check that the lh is not a loop variable*)
              val loopVarCheck = case var
                    of A.SimpleVar(sym,pos) => (case Symbol.look(venv, sym)
                        of SOME(E.VarEntry{ty=_, loopvar=true}) => error pos 
                          ("Error: illegal assignment to loop control variable")
                          |_ => ())
                      |_ => ()
              val expType = trexp(exp)
          in case (absType(varType), absType(expType))
                of (E.ERROR,_) => E.UNIT
                  |(_,E.ERROR) => E.UNIT
                  |_ => if equalTypes varType expType
                        then E.UNIT
                        else (error pos ("Error: " ^ printType(varType) ^ 
                            " expression expected"); E.UNIT) end
      | trexp(A.IfExp({test, then', else'=NONE, pos})) = 
          let val testType = trexp(test)
              val check = case testType of
                             E.INT => ()
                            |E.ERROR => ()
                            |_     => error pos "expected integer type.\n"
          in case trexp(then')  
                of E.UNIT => E.UNIT
                  |E.ERROR => E.UNIT
                  |_ => (error pos 
                    "Error: unit type expected for then expression"; E.UNIT) 
          end
      | trexp(A.IfExp({test, then', else'=SOME elseBranch, pos})) = 
          let val testType = trexp(test)
              val checkCond = case testType of
                                E.INT => ()
                               |E.ERROR => ()
                               |_     => error pos "expected integer type.\n"
              val thenType = absType(trexp(then'))
              val elseType = absType(trexp(elseBranch))
          in if equalTypes thenType elseType
             then thenType
             else case (thenType, elseType)
                of (E.ERROR,_) => (E.ERROR)
                  |(_,E.ERROR) => (E.ERROR)
                  |(_,_) => (error pos 
                  ("Error: types of conditional branches do not match");E.ERROR) 
          end
      | trexp(A.WhileExp({test, body, pos})) = 
          let val testType = trexp(test)
              val bodyType = trexp(body)
              val checkCond = case testType of
                                E.INT => ()
                               |_ => error pos "Error: expected integer type.\n"
              val checkBody = case bodyType of
                                E.UNIT => ()
                               |E.ERROR => ()
                               |_ => error pos "Error: unit type expected for body of while"
          in E.UNIT end
      | trexp(A.ForExp({var, escape, lo, hi, body, pos})) = 
          let val loType = trexp(lo)
              val hiType = trexp(hi)
              val venv' = Symbol.enter(venv, var, E.VarEntry{ty=E.INT, loopvar=true})
              val bodyType = transExp(venv', tenv, body)  
              val check1 = if equalTypes loType E.INT orelse equalTypes loType E.ERROR
                           then ()
                           else (error pos "Error: low value of for must be of integer type")
              val check2 = if equalTypes hiType E.INT orelse equalTypes hiType E.ERROR
                           then ()
                           else error pos "Error: high value of for must be of integer type"
              val check3 = if equalTypes bodyType E.UNIT
                           then () 
                           else error pos "Error: body of for loop must be of type unit"
          in E.UNIT
          end                                            
      | trexp(A.LetExp({decs, body, pos})) = 
          let val (venv', tenv') = transDecs(decs, venv, tenv)
          in transExp(venv', tenv', body) end   
      | trexp(A.ArrayExp{typ, size, init, pos}) = 
          let val sizeType = absType(trexp(size))
              val initType = absType(trexp(init))
              val arrayType = absType(transTy(tenv, A.NameTy(typ, pos)))
              val dataType = case arrayType 
                              of E.ARRAY(ty, u) => ty
                                |E.ERROR => E.ERROR
                                |_ => (error pos ("expected type-id to be an array");
                                        E.ERROR)
              val check1 = if equalTypes sizeType E.INT
                           then true else (error pos 
                              "Error: integer expression expected"; false)
              val check2 = if equalTypes initType dataType
                           then true else (error pos ("Error: integer expression" ^ 
                                " expected in array initialization"); false)
          in case (check1, check2)
              of (true, true) => arrayType
                |_ => E.ERROR
          end  
      | trexp(A.RecordExp{fields, typ, pos}) = (
          let exception RecordExpError
              fun trRecExp() =
                    (*Lookup declaration associated with record name*)
                let val recordDecl = (case Symbol.look(tenv, typ)
                      of SOME t => t
                        |NONE => (error pos ("Error: undefined type symbol " ^ 
                            Symbol.name(typ)); raise RecordExpError))
                    val recFields = case absType(recordDecl)
                                   of E.RECORD(rf, _) => rf
                                     |_ => (error pos (Symbol.name(typ) ^ " is not a record\n"); [])
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
                       in if equalTypes eType memType
                          then checkMembers(rest)
                          else (error pos ("types don't match in record, the expression type is " ^ printType(eType) ^ 
                                          " and the formal type is " ^ printType(memType) ^ "\n");raise RecordExpError)
                       end
                        |checkMembers([]) = recordDecl
                in checkMembers(fields) end
          in trRecExp() end handle RecordExpError => E.ERROR)
      | trexp(_) = raise NotImplemented
  in
    trexp(exp)
  end


(*Used to typecheck an entire program.  This calls transExp where the 
venv is the base variable environment, and same thing for the type environment*)
fun transProg (exp) = transExp(E.base_venv, E.base_tenv, exp)


end







