(*id*) 
Require Import Coq.Init.Datatypes. 
Definition id := nat.

Definition tid := list (nat * nat). 

(*Syntax for speculative semantics*)
Inductive term : Type := 
  |threadId : tid -> term
  |ivar : id -> term
  |unit : term
  |pair_ : term -> term -> term
  |var : id -> term
  |lambda : id -> term -> term
  |app : term -> term -> term
  |ret : term -> term
  |bind : term -> term -> term
  |fork : term -> term
  |new : term
  |put : id -> term -> term
  |get : id -> term
  |raise : term -> term
  |handle : term -> term -> term
  |done : term -> term
  |spec : term -> term -> term
  |specReturn : term -> term -> term
  |fst : term -> term
  |snd : term -> term
.

(*Syntax for non-speculative Par Monad semantics*)
Inductive pterm : Type :=
|pivar : id -> pterm
|punit : pterm
|ppair : pterm -> pterm -> pterm
|pvar : id -> pterm
|plambda : id -> pterm -> pterm
|papp : pterm -> pterm -> pterm
|pret : pterm -> pterm
|pbind : pterm -> pterm -> pterm
|pfork : pterm -> pterm
|pnew : pterm
|pput : id -> pterm -> pterm
|pget : id -> pterm
|praise : pterm -> pterm
|phandle : pterm -> pterm -> pterm
|pdone : pterm -> pterm
|pfst : pterm -> pterm
|psnd : pterm -> pterm
.

Inductive action : Type :=
  |rAct : id -> tid -> term -> action
  |wAct : id -> tid -> term -> action
  |cAct : id -> tid -> term -> action
  |sAct : tid -> term -> action
  |fAct : tid -> tid -> term -> action  (*first tid is the thread id of the forked thread*)
  |joinAct : action
  |specAct : action.

Definition specStack := list action. 

Inductive pivar_state : Type :=
|pempty : pivar_state
|pfull : pterm -> pivar_state.

Inductive ivar_state : Type :=
  |empty : specStack -> ivar_state
  |full : specStack -> list tid -> specStack -> tid -> term -> ivar_state. 
(*first spec is who created, second is who wrote*)

