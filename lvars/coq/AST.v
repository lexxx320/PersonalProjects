(*id*) 
Definition id := nat.

Definition tid := list (nat * nat). 

(*Syntax*)
Inductive term : Type := 
  |threadId : tid -> term
  |ivar : id -> term
  |unit : term
  |pair : term -> term -> term
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


Inductive ivar_state : Type :=
  |empty : specStack -> ivar_state
  |none : ivar_state
  |full : specStack -> list tid -> specStack -> tid -> term -> ivar_state. 
(*first spec is who created, second is who wrote*)
