
Inductive id : Type := 
  |Id : nat -> id. 

(*Syntax*)
Inductive term : Type := 
  |ivar : id -> term
  |unit : term
  |var : id -> term
  |lambda : id -> term -> term
  |app : term -> term -> term
  |ret : term -> term
  |bind : term -> term -> term
  |fork : term -> term
  |new : term
  |put : id -> term
  |get : id -> term
  |done : term -> term.

Definition heap := nat.

Inductive pool : Type :=
  |thread : term -> pool
  |parComp : pool -> pool -> pool.


Inductive step : heap -> pool -> heap -> pool -> Prop :=
  |ParStep1 : forall t1 t1' t2 h h', step h t1 h' t1' -> step h (parComp t1 t2) h' (parComp t1' t2)
  |ParStep2 : forall t1 t2 t2' h h', step h t2 h' t2' -> step h (parComp t1 t2) h' (parComp t1 t2')
  |BindStep : forall t1 t1' t2 h h', step h (thread t1) h' (thread t1') ->
                                     step h (thread (bind t1 t2)) h' (thread (bind t1' t2))
  |Bind : forall t1 t2 h, step h (thread(bind (ret t1) t2)) h (thread (app t2 t1))
  |Fork : forall t1 h, step h (thread (fork t1)) h (parComp (thread (ret unit)) (thread t1))
.



