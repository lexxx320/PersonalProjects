Require Export Coq.Init.Datatypes. 
Require Export List. 
Export ListNotations. 

Open Scope type_scope. 

Inductive term : Type :=
|lambda : nat -> term -> term
|loc : nat -> term
|unit : term
|var : nat -> term
|app : term -> term -> term
|get : term -> term
|put : term -> term -> term
|alloc : term -> term
|fork : term -> term
|atomic : term -> term. 

Inductive value : term -> Prop :=
|v_lam : forall e n, value (lambda n e)
|v_loc : forall n, value (loc n)
|v_unit : value unit. 

Inductive nonTCtxt : Type :=
|ntHole : nonTCtxt
|ntApp : term -> nonTCtxt -> nonTCtxt
|ntAppVal : term -> nonTCtxt -> nonTCtxt
|ntGet : nonTCtxt -> nonTCtxt
|ntPut : term -> nonTCtxt -> nonTCtxt 
|ntPutVal : term -> nonTCtxt -> nonTCtxt
|ntAlloc : nonTCtxt -> nonTCtxt. 

Inductive TCtxt : Type :=
|tHole : TCtxt
|tApp : term -> TCtxt -> TCtxt
|tAppVal : term -> TCtxt -> TCtxt
|tGet : TCtxt -> TCtxt
|tPut : term -> TCtxt -> TCtxt 
|tPutVal : term -> TCtxt -> TCtxt
|tAlloc : TCtxt -> TCtxt
|tAtomic : TCtxt -> TCtxt. 

Definition heap := list (nat * term). 

Inductive logItem : Type := 
|readItem : nat -> term -> term -> logItem
|writeItem : nat -> term -> term -> logItem
|allocItem : nat -> term -> term -> logItem. 

Definition log := list logItem. 
Definition thread := heap * log * term. 

Inductive pool : Type := 
|Single : thread -> pool
|Par : pool -> pool -> pool. 





 