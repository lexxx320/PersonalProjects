Require Import AST. 
Require Import Heap.
Require Import Coq.Sets.Ensembles. 
Require Import sets. 

Definition pHeap := heap pivar_state. 

Inductive pctxt : Type :=
|pbindCtxt : pctxt -> ptrm -> pctxt
|phandleCtxt : pctxt -> ptrm -> pctxt 
|pholeCtxt : pctxt.

Fixpoint pdecompose (t:ptrm) : (pctxt * ptrm) :=
  match t with
      |pbind M N => let (E, M') := pdecompose M
                    in (pbindCtxt E N, M')
      |phandle M N => let (E, M') := pdecompose M
                      in (phandleCtxt E N, M')
      |_ => (pholeCtxt, t)
  end. 

(*
Fixpoint isPVal (t:ptrm) : bool :=
  match t with
      |pret N => true
      |praise N => true
      |_ => false
  end. 

Fixpoint pdecompose (t:ptrm) : (pctxt * ptrm) :=
  match t with
      |pbind M N => if isPVal M
                    then (pholeCtxt, pbind M N)
                    else let (E, M') := pdecompose M
                         in (pbindCtxt E N, M')
      |phandle M N => if isPVal M 

                      then (pholeCtxt, phandle M N)
                      else let (E, M') := pdecompose M
                           in (phandleCtxt E N, M')
      |_ => (pholeCtxt, t)
  end. 
*)

Fixpoint pfill (c:pctxt) (t:ptrm) : ptrm :=
  match c with
      |pbindCtxt E N => pbind (pfill E t) N
      |phandleCtxt E N => phandle (pfill E t) N
      |pholeCtxt => t
  end. 

Theorem pdecomposeEq : forall M E e, pdecompose M = (E, e) -> M = pfill E e. 
Proof.
  induction M; intros; simpl in *; inversion H; try reflexivity; try solve[
  destruct (pdecompose M1); inversion H; inversion H1; subst;  
   assert((p,e)=(p,e)) by reflexivity; apply IHM1 in H0; subst; reflexivity]. 
Qed. 

Definition pPool := Ensemble ptrm. 
Definition pSingleton := Singleton ptrm. 
Definition pUnion := Union ptrm. 

Inductive pstep : pHeap -> pPool -> pPool -> pHeap -> pPool -> pPool -> Prop :=
|PBind : forall E t M N h T, 
            pdecompose t = (pbindCtxt E N, pret M) -> 
           pstep h T (pSingleton t) h T (pSingleton(pfill E(papp N M)))
|PBindRaise : forall E t M N h T,
                 pdecompose t = (pbindCtxt E N, praise M) -> 
                pstep h T (pSingleton t) h T (pSingleton (pfill E(praise M)))
|pHandle : forall E t M N h T,
              pdecompose t = (phandleCtxt E N, praise M) -> 
             pstep h T (pSingleton t) h T (pSingleton (pfill E(papp N M)))
|pHandleRet : forall E t M N h T,
                 pdecompose t = (phandleCtxt E N, pret M) -> 
                pstep h T (pSingleton t) h T (pSingleton (pfill E(pret M)))
|pFork : forall E t M h T,
            pdecompose t = (E, pfork M) -> 
           pstep h T (pSingleton t) h T (Couple ptrm (pfill E(pret punit)) M)
|PGet : forall E M t h T x,
           heap_lookup x h = Some(pfull M) -> pdecompose t = (E, pget (pfvar x)) -> 
          pstep h T (pSingleton t) h T (pSingleton (pfill E(pret M)))
|PPut : forall E t M h h' T x,
           pdecompose t = (E, pput (pfvar x) M) -> heap_lookup x h = Some pempty ->
          h' = replace x (pfull M) h ->
          pstep h T (pSingleton t) (replace x (pfull M) h) T (pSingleton (pfill E (pret punit)))
|PNew : forall E t h h' T x,
             pdecompose t = (E, pnew) -> (x, h') = extend pempty h ->
             pstep h T (pSingleton t) h' T (pSingleton (pfill E (pret (pfvar x))))
|PTerminate : forall h T M, pstep h T (pSingleton (pret M)) h T (Empty_set ptrm)
                
.

Inductive pmultistep : pHeap -> pPool -> pPool -> pHeap -> pPool -> pPool -> Prop :=
|pmulti_refl : forall h p1 p2, pmultistep h p1 p2 h p1 p2
|pmulti_step : forall T1 T2 T2' h h' h'' t t',
                 ~ In ptrm T2 t -> 
                 pstep h (pUnion T1 T2) (pSingleton t) h' (pUnion T1 T2) t' ->
                 pmultistep h' T1 (pUnion T2 t') h'' T1 T2' ->
                 pmultistep h T1 (Add ptrm T2 t) h'' T1 T2'
.

Require Import Coq.Sets.Powerset_facts. 


Theorem pSingletonMultistep : forall h h' T T' t t',
          pmultistep h T (Union ptrm (Empty_set ptrm) t) h' T' t' ->
          pmultistep h T t h' T' t'. 
Proof.
  intros. rewrite Union_commutative in H. rewrite union_empty in H. 
  assumption. Qed.   









