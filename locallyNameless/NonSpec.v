Require Import AST. 
Require Import Heap.
Require Import Coq.Sets.Ensembles. 
Require Import sets. 

Definition pHeap := heap pivar_state. 

Definition pctxt := ptrm -> ptrm.

Fixpoint pdecompose (t:ptrm) : (pctxt * ptrm) :=
  match t with
      |pbind M N => let (E, M') := pdecompose M
                    in (fun x => pbind (E x) N, M')
      |phandle M N => let (E, M') := pdecompose M
                      in (fun x => phandle (E x) N, M')
      |_ => (fun x => x, t)
  end. 


Theorem pdecomposeEq : forall M E e, pdecompose M = (E, e) -> M = E e. 
Proof.
  induction M; intros; simpl in *; inversion H; try reflexivity. 
  {destruct (pdecompose M1). inversion H; inversion H1; subst. 
   assert((p,e)=(p,e)) by reflexivity. apply IHM1 in H0. subst. 
   reflexivity. }
  {destruct (pdecompose M1). inversion H; inversion H1; subst. 
   assert((p,e)=(p,e)) by reflexivity. apply IHM1 in H0. subst. 
   reflexivity. }
Qed. 


Definition pPool := Ensemble ptrm. 
Definition pSingleton := Singleton ptrm. 
Definition pUnion := Union ptrm. 

Inductive pstep : pHeap -> pPool -> pPool -> pHeap -> pPool -> pPool -> Prop :=
|PBind : forall E t M N h T, 
           pterm t -> pdecompose t = (E, pbind (pret M) N) -> 
           pstep h T (pSingleton t) h T (pSingleton(E(papp N M)))
|PBindRaise : forall E t M N h T,
                pterm t -> pdecompose t = (E, pbind (praise M) N) -> 
                pstep h T (pSingleton t) h T (pSingleton (E(praise M)))
|pHandle : forall E t M N h T,
             pterm t -> pdecompose t = (E, phandle (praise M) N) -> 
             pstep h T (pSingleton t) h T (pSingleton (E(papp N M)))
|pHandleRet : forall E t M N h T,
                pterm t -> pdecompose t = (E, phandle (pret M) N) -> 
                pstep h T (pSingleton t) h T (pSingleton (E(pret M)))
|pFork : forall E t M h T,
           pterm t -> pdecompose t = (E, pfork M) -> 
           pstep h T (pSingleton t) h (Add ptrm T M) (pSingleton (E(pret punit)))
|PGet : forall E M t h T x,
          pterm t -> heap_lookup x h = Some(pfull M) -> pdecompose t = (E, pget (pfvar x)) -> 
          pstep h T (pSingleton t) h T (pSingleton (E(pret M)))
|PPut : forall E t M h h' T x y,
          pterm t -> pdecompose t = (E, pput (pfvar x) M) -> heap_lookup x h = Some pempty ->
          h' = replace x (pfull M) h ->
          pstep h T (pSingleton t) (replace y (pfull M) h) T (pSingleton (E (pret punit)))
|PNew : forall E t h h' T x,
             pdecompose t = (E, pnew) -> (x, h') = extend pempty h ->
             pstep h T (pSingleton t) h' T (pSingleton (E (pret (pfvar x))))
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









