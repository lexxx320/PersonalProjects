Require Import AST. 
Require Import Heap. 

Require Import Coq.Sets.Ensembles. 

Fixpoint bump (t : tid) : tid := 
  match t with
    |(maj, min) :: t' => (maj, S min) :: t'
    |nil => nil
  end.
 
Definition sHeap := heap (ivar_state). 

Inductive ctxt : (term -> term) -> Prop :=
|bindCtxt : forall N c, ctxt c -> ctxt (fun M => bind (c M) N)
|specReturnCtxt : forall N c, ctxt c -> ctxt (fun M => specReturn M N)
|handleCtxt : forall N c, ctxt c -> ctxt (fun M => handle M N)
|hole : forall c, ctxt c -> ctxt (fun M => c M)
.
Hint Constructors ctxt. 

Definition thread := tid * specStack * specStack * term. 

Definition pool := Ensemble thread.

Definition tAdd := Add thread. 
Definition tIn := In thread. 
Inductive step : sHeap -> pool -> sHeap -> pool -> Prop :=
|Bind : forall tid t h E T N M s1 s2 ,
          ctxt E -> ~(tIn T t) -> t = (tid, s1, s2, E (bind (ret M) N)) ->
          step h (tAdd T t) h (tAdd T (bump tid, s1, s2, E(AST.app N M)))
|BindRaise : forall tid t h E T N M s1 s2,
               ctxt E -> ~(tIn T t) -> t = (tid, s1, s2, E(bind (raise M) N)) ->
               step h (tAdd T t) h (tAdd T (bump tid, s1, s2, E(raise M)))
|Handle : forall tid t h E T N M s1 s2,
            ctxt E -> ~(tIn T t) -> t = (tid, s1, s2, E(handle (raise M) N)) ->
            step h (tAdd T t) h (tAdd T (bump tid, s1, s2, E(AST.app N M)))
|HandleRet : forall tid t h E T N M s1 s2, 
               ctxt E -> ~(tIn T t) -> t = (tid, s1, s2, E(handle (ret M) N)) ->
               step h (tAdd T t) h (tAdd T (bump tid, s1, s2, E(ret M)))
|Terminate : forall tid t h T M s2,
               ~(tIn T t) -> t = (tid, nil, s2, ret M) ->
               step h (tAdd T t) h T


.






