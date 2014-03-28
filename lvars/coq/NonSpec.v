
Require Export SfLib. 


Definition id := SfLib.id.

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
  |put : id -> term -> term
  |get : id -> term
  |done : term -> term.


Inductive ivar_state : Type :=
  |empty : ivar_state
  |full : term -> ivar_state.


Definition heap := partial_map ivar_state.

Inductive pool : Type :=
  |thread : term -> pool
  |parComp : pool -> pool -> pool.

Inductive step : heap -> pool -> heap -> pool -> Prop :=
  |ParStep1 : forall t1 t1' t2 h h', step h t1 h' t1' -> 
                                     step h (parComp t1 t2) h' (parComp t1' t2)
  |ParStep2 : forall t1 t2 t2' h h', step h t2 h' t2' -> 
                                     step h (parComp t1 t2) h' (parComp t1 t2')
  |BindStep : forall t1 t1' t2 h h', step h (thread t1) h' (thread t1') ->
                                     step h (thread (bind t1 t2)) h' 
                                          (thread (bind t1' t2))
  |Bind : forall t1 t2 h, step h (thread(bind (ret t1) t2)) h (thread (app t2 t1))
  |Fork : forall t1 h, step h (thread (fork t1)) h 
                            (parComp (thread (ret unit)) (thread t1))
  |Get : forall  h i M,  h i = Some(full M) -> 
                         step h (thread (get i)) h (thread (ret M))
  |Put : forall h h' i M, h i = Some empty ->
                       h' = extend h i (full M) ->
                       step h (thread (put i M)) h' (thread (ret unit))
  |New : forall h h' i, h i = None -> h' = extend h i empty ->
                        step h (thread new) h' (thread (ret (var i)))
.










