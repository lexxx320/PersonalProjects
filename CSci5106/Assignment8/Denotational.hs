module Denotational where

{- For question 4(a) you will need to extend this algebraic data type
   with variants for the needed expression operations.  
-}

data Expr = Add Expr Expr
          | Sub Expr Expr
          | Mult Expr Expr
          | And Expr Expr 
          | Or Expr Expr 
          | Equals Expr Expr
          | Neq Expr Expr
          | Gt Expr Expr 
          | Gte Expr Expr
          | Lte Expr Expr 
          | Lt Expr Expr
          | Mod Expr Expr
          | Not Expr 
          | Const Integer
          | VarName String
          | TrueE
          | FalseE
  deriving (Show,Eq) -- disregard this for now.

data Stmt = Seq Stmt Stmt
          | Assignment String Expr
          | While Expr Stmt
          | IfThen Expr Stmt
          | IfThenElse Expr Stmt Stmt
      deriving (Show, Eq)

data Prog = Program String String Stmt String

type State = [(String, Integer)]          
          

----------Exponent Program----------------------------
s1 = Assignment "i" (Const 0)
s2 = Assignment "z" (Const 1)
s3 = While (Lt (VarName "i") (VarName "y")) (Seq s4 s5)
s4 = Assignment "z" (Mult (VarName "z") (VarName "x"))
s5 = Assignment "i" (Add (VarName "i") (Const 1))
exponentProg = Program "x" "y" (foldr Seq s3 [s1, s2]) "z"

--------------GCD Program-----------------------------
s6 = IfThenElse (Lt (VarName "m") (VarName "n")) s7 s8
s7 = Assignment "i" (VarName "n")
s8 = Assignment "i" (VarName "m") 
s9 = While (Or (Neq (Mod (VarName "n") (VarName "i")) (Const 0)) (Neq (Mod (VarName "m") (VarName "i")) (Const 0))) (Assignment "i" (Sub (VarName "i") (Const 1)))
gcdProg = Program "m" "n" (Seq s6 s9) "i"

-- Below is the sample environment.
env = [ ("x", 3), ("y", 4), ("z", 5), ("p", 1), ("q", 0) ]


t = Mod (Const 5) (Const 10)

update :: String -> Integer -> State -> State
update var val oldState = (var, val) : oldState

execStmt :: Stmt -> State -> State
execStmt (Seq s1 s2) currentState = execStmt s2 (execStmt s1 currentState)  
execStmt (Assignment lh rh) currentState = update lh (eval rh currentState) currentState
execStmt (While cond body) currentState = if eval cond currentState == 1
                                          then execStmt (While cond body) (execStmt body currentState)
                                          else currentState
                                          
execStmt (IfThen cond body) state = if eval cond state == 1
                                    then execStmt body state
                                    else state

execStmt (IfThenElse cond thenClause elseClause) state = if eval cond state == 1
                                                         then execStmt thenClause state
                                                         else execStmt elseClause state


execProg :: Prog -> Integer -> Integer -> Integer
execProg (Program arg1 arg2 stmts output)
   vArg1 vArg2 = case lookup output (execStmt stmts initialState) of
                    Just val -> val
                    Nothing -> error ("Output arg cannot be found in environment")
    where 
      initialState = [(arg1, vArg1), (arg2, vArg2)]


execProgState :: Prog -> Integer -> Integer -> State
execProgState (Program arg1 arg2 stmts output)
   vArg1 vArg2 = execStmt stmts initialState
    where 
      initialState = [(arg1, vArg1), (arg2, vArg2)]                                                        



































----------------------For Testing Purposes----------------
--Print out the expression
--pp :: a -> [(String, Integer)] -> String
pp (Add e1 e2) env = pp e1 env ++ " + " ++ pp e2 env
pp (Sub e1 e2) env = pp e1 env ++ " - " ++ pp e2 env
pp (Mult e1 e2) env = pp e1 env ++ " * " ++ pp e2 env
pp (And e1 e2) env = pp e1 env ++ " && " ++ pp e2 env
pp (Mod e1 e2) env = pp e1 env ++ " % " ++ pp e2 env
pp (Or e1 e2) env = pp e1 env ++ " || " ++ pp e2 env
pp (Equals e1 e2) env = pp e1 env ++ " == " ++ pp e2 env
pp (Gt e1 e2) env = pp e1 env ++ " > " ++ pp e2 env
pp (Gte e1 e2) env = pp e1 env ++ " >= " ++ pp e2 env
pp (Lte e1 e2) env = pp e1 env ++ " <= " ++ pp e2 env
pp (Lt e1 e2) env = pp e1 env ++ " < " ++ pp e2 env
pp (Neq e1 e2) env = pp e1 env ++ " != " ++ pp e2 env
pp (Not e) env = "!" ++ pp e env
pp (Const x) _ = show(x)
pp (VarName v) env = case lookup v env of
  Nothing -> error("Undefined variable \"" ++ v ++ "\".")
  Just _ -> v
pp TrueE _ = "True"
pp FalseE _ = "False"

------------------------------------------------------------

{- For question 4(c) complete the implementation of eval below.  You
   will need a clause for each constructor of the type Expr.
-}

eval :: Expr -> [(String, Integer)] -> Integer
eval (Add e1 e2) env = eval e1 env + eval e2 env
eval (Sub e1 e2) env = eval e1 env - eval e2 env
eval (Mult e1 e2) env = eval e1 env * eval e2 env
eval (Mod e1 e2) env = mod (eval e1 env) (eval e1 env) 
eval (Not e1) env = if (eval e1 env) == 0
                    then 1
                    else 0
eval (And e1 e2) env = if eval e1 env == 0 || eval e2 env == 0
                       then 0
                       else 1
eval (Or e1 e2) env = if eval e1 env == 0 && eval e2 env == 0
                      then 0
                      else 1
eval (Equals e1 e2) env = if eval e1 env == eval e2 env
                          then 1
                          else 0
eval (Gt e1 e2) env = if eval e1 env > eval e2 env
                      then 1
                      else 0
eval (Lte e1 e2) env = if eval e1 env <= eval e2 env
                       then 1
                       else 0
eval (Gte e1 e2) env = if eval e1 env >= eval e2 env
                       then 1
                       else 0
eval (Lt e1 e2) env = if eval e1 env < eval e2 env
                       then 1
                       else 0      
eval (Neq e1 e2) env = if eval e1 env /= eval e2 env
                       then 1
                       else 0                                        
eval (Const x) _ = x
eval (VarName v) env 
  = case lookup v env of
      Nothing -> error ("Undefined variable \"" ++ v ++ "\".")
      Just x -> x
eval TrueE _ = 1
eval FalseE _ = 0





{- For question 4(d) implement the translate function below.  It
   should return a String and take as input an Expr and an Integer.
-}

ririr1 i = "R" ++ show(i) ++ ", R" ++ show(i) ++ ", R" ++ show(i+1)

translate e  = putStr (translateHelper e 0)

translateHelper :: Expr -> Integer -> String

translateHelper (Add e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "AddOp " ++ (ririr1 i) ++ "\n"
translateHelper (Sub e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "SubOp " ++ (ririr1 i) ++ "\n"
translateHelper (Mult e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "MultOp " ++ (ririr1 i) ++ "\n"
translateHelper (Not e1) i = (translateHelper e1 i) ++ "NotOp R" ++ show(i) ++ ", R" ++ show(i+1) ++ "\n"
translateHelper (And e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "AndOp " ++ (ririr1 i) ++ "\n"
translateHelper (Or e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "OrOp " ++ (ririr1 i) ++ "\n"
translateHelper (Equals e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "EqualsOp " ++ (ririr1 i) ++ "\n"
translateHelper (Gt e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "GtOp " ++ (ririr1 i) ++ "\n"
translateHelper (Lte e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "LteOp " ++ (ririr1 i) ++ "\n"

translateHelper (Const x) i = "LoadC R" ++ show(i) ++ ", " ++ show(x) ++ "\n"
translateHelper (VarName v) i = "Load R" ++ show(i) ++ ", " ++ v ++ "\n"
translateHelper TrueE _ = "True"
translateHelper FalseE _ = "False"

















