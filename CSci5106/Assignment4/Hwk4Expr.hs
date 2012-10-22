module Hwk4Expr where

{- For question 4(a) you will need to extend this algebraic data type
   with variants for the needed expression operations.  
-}

data Expr = Add Expr Expr
          | Sub Expr Expr
          | Mult Expr Expr
          | And Expr Expr 
          | Or Expr Expr 
          | Equals Expr Expr
          | Gt Expr Expr 
          | Lte Expr Expr 
          | Not Expr 
          | Const Integer
          | VarName String
          | TrueE
          | FalseE
  deriving (Show,Eq) -- disregard this for now.

          

-- Some sample expressions that use the limited, original constructor.
e1 = Const 12
e2 = Add (Const 3) (Sub (Const 10) (Const 4))
e3 = Add (Const 1) (Mult (Const 2) (Const 3)) 


-- For question 4(b), define expr_a, expr_b, expr_c, and expr_d below.

expr_a = Mult (Add (VarName "x") (Const 3)) (VarName "y")
expr_b = Equals (Sub (VarName "x") (Const 1)) (Or (Const 4) (Lte (VarName "y") (VarName "z")))
expr_c = And (Not (VarName "p")) (Not(VarName "q")) 
expr_d = Gt (Mult (VarName "x") (Add (VarName "y") (Const 1))) (Add (VarName "z") (Const 2))
-- Below is the sample environment.
env = [ ("x", 3), ("y", 4), ("z", 5), ("p", 1), ("q", 0) ]

----------------------Testing Purposes----------------
--Print out the expression
pp :: Expr -> [(String, Integer)] -> String
pp (Add e1 e2) env = pp e1 env ++ " + " ++ pp e2 env
pp (Sub e1 e2) env = pp e1 env ++ " - " ++ pp e2 env
pp (Mult e1 e2) env = pp e1 env ++ " * " ++ pp e2 env
pp (And e1 e2) env = pp e1 env ++ " && " ++ pp e2 env
pp (Or e1 e2) env = pp e1 env ++ " || " ++ pp e2 env
pp (Equals e1 e2) env = pp e1 env ++ " == " ++ pp e2 env
pp (Gt e1 e2) env = pp e1 env ++ " > " ++ pp e2 env
pp (Lte e1 e2) env = pp e1 env ++ " <= " ++ pp e2 env
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

translate e i = putStr (translateHelper e i)

translateHelper :: Expr -> Integer -> String

translateHelper (Add e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "AddOp " ++ (ririr1 i) ++ "\n"
translateHelper (Sub e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "SubOp " ++ (ririr1 i) ++ "\n"
translateHelper (Mult e1 e2) i = (translateHelper e1 i) ++ (translateHelper e2 (i+1)) ++ 
  "MultOp " ++ (ririr1 i) ++ "\n"
translateHelper (Not e1) i = (translateHelper e1 i) ++ "NotOp R" ++ show(i) ++ ", R" ++ show(i+1)
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

















