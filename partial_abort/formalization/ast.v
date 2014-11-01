Require Export Coq.Init.Datatypes. 
Require Export List. 
Export ListNotations. 

Open Scope type_scope. 

Inductive term : Type :=
|lambda : term -> term
|loc : nat -> term
|unit : term
|var : nat -> term
|app : term -> term -> term
|get : term -> term
|put : term -> term -> term
|alloc : term -> term
|fork : term -> term
|atomic : term -> term
|inatomic : term -> term. 

Inductive value : term -> Prop :=
|v_lam : forall e, value (lambda e)
|v_loc : forall n, value (loc n)
|v_unit : value unit. 

Inductive ctxt : Type :=
|hole : ctxt
|appCtxt : term -> ctxt -> ctxt
|appValCtxt : term -> ctxt -> ctxt
|getCtxt : ctxt -> ctxt
|putCtxt : term -> ctxt -> ctxt 
|putValCtxt : term -> ctxt -> ctxt
|allocCtxt : ctxt -> ctxt
|inatomicCtxt : ctxt -> ctxt. 

Definition location := nat.
Definition stamp := nat. 

Inductive logItem : Type := 
|readItem : location -> ctxt -> logItem
|writeItem : location -> term -> logItem
. 

Definition log := list logItem. 
 
Definition thread := option (nat * term) * log * term. 

Inductive pool : Type := 
|Single : thread -> pool
|Par : pool -> pool -> pool. 





 