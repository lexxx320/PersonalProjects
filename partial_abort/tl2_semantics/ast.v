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
|atomic : term -> term 
|inatomic : term -> term. 

Inductive value : term -> Prop :=
|v_lam : forall e n, value (lambda n e)
|v_loc : forall n, value (loc n)
|v_unit : value unit.

Inductive ctxt : Type := 
|holeCtxt : ctxt
|appCtxt : term -> ctxt -> ctxt
|appValCtxt : term -> ctxt -> ctxt
|getCtxt : ctxt -> ctxt
|putCtxt : term -> ctxt -> ctxt 
|putValCtxt : term -> ctxt -> ctxt
|allocCtxt : ctxt -> ctxt
|inAtomicCtxt : ctxt -> ctxt. 

Definition location := nat. 
Definition stamp := nat. 

Definition heap (A:Type) := list (nat * A). 

Definition globalHeap := heap (term * stamp). 

Inductive opType := R | W. 

Definition log := heap (term * stamp * ctxt * opType). 
Definition tid := nat. 
Definition thread := option tid * log * term. 

Inductive pool : Type := 
|Single : thread -> pool
|Par : pool -> pool -> pool. 





 