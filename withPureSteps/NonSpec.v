Require Import AST. 
Require Import Heap.
Require Import Coq.Sets.Ensembles. 
Require Import sets. 

Definition pHeap := heap pivar_state. 

Inductive pctxt : Type :=
|pbindCtxt : pctxt -> ptrm -> pctxt
|phandleCtxt : pctxt -> ptrm -> pctxt
|pappCtxt : pctxt -> ptrm -> pctxt 
|pappValCtxt : pctxt -> ptrm -> pctxt 
|ppairCtxt : pctxt -> ptrm -> pctxt 
|ppairValCtxt : pctxt -> ptrm -> pctxt
|pfstCtxt : pctxt -> pctxt 
|psndCtxt : pctxt -> pctxt  
|pholeCtxt : pctxt
.

Inductive pdecompose : ptrm -> pctxt -> ptrm -> Prop :=
|pdecompBind : forall M N E M', pdecompose M E M' -> pdecompose (pbind M N) (pbindCtxt E N) M'
|pdecompHandle : forall M M' N E, pdecompose M E M' -> pdecompose (phandle M N) (phandleCtxt E N) M'
|pdecompApp : forall M N M' E, pval M = false -> pdecompose M E M' -> 
                              pdecompose (papp M N) (pappCtxt E N) M'
|pdecompAppVal : forall M N N' E, pval M = true -> pdecompose N E N' ->
                                 pdecompose (papp M N) (pappValCtxt E M) N'
|pdecompPair : forall M M' E N, pval M = false -> pdecompose M E M' ->
                               pdecompose (ppair M N) (ppairCtxt E N) M'
|pdecompValPair : forall M N N' E, pval M = true -> pval N = false -> pdecompose N E N' ->
                                  pdecompose (ppair M N) (ppairValCtxt E M) N'
|pdecompFst : forall M M' E, pdecompose M E M' -> pdecompose(pfst M) (pfstCtxt E) M'
|pdecompSnd : forall M M' E, pdecompose M E M' -> pdecompose(psnd M) (psndCtxt E) M'
|pdecompVal : forall M, pval M = true -> pdecompose M pholeCtxt M
. 

Fixpoint pfill (c:pctxt) (t:ptrm) : ptrm :=
  match c with
      |pbindCtxt E N => pbind (pfill E t) N
      |phandleCtxt E N => phandle (pfill E t) N
      |pappCtxt E N => papp (pfill E t) N
      |pappValCtxt E M => papp M (pfill E t)
      |ppairCtxt E N => ppair (pfill E t) N
      |ppairValCtxt E M => ppair M (pfill E t)
      |pfstCtxt E => pfst (pfill E t)
      |psndCtxt E => psnd (pfill E t)
      |pholeCtxt => t
  end. 

Ltac helperTac :=
  match goal with
    |H:?x=?y |- _ => inversion H; subst; clear H
    |H:forall M e, (?x,?y) = (M, e) -> ?z |- _ => assert(EQ:(x,y)=(x,y)) by auto; apply H in EQ
  end. 

Theorem pdecomposeEq : forall M E e, pdecompose M E e -> M = pfill E e. 
Proof.
  induction M; intros; try solve[inversion H; subst; auto].  
  {inversion H; subst; auto. simpl. apply IHM1 in H5. subst; auto. 
   apply IHM2 in H6; subst; auto. }
  {inversion H; subst; auto. apply IHM1 in H5; subst; auto. apply IHM2 in H5; subst; auto. }
  {inversion H; subst; auto. apply IHM1 in H4; subst; auto. }
  {inversion H; subst; auto. apply IHM1 in H4; subst; auto. }
  {inversion H; subst; auto. apply IHM in H1; subst; auto. }
  {inversion H; subst; auto. apply IHM in H1; subst; auto. }
Qed. 

Theorem pdecomposedVal : forall t E e, pdecompose t E e -> pval e = true. 
Proof.
  induction t; intros; try solve[inversion H; subst; auto]; try solve[inversion H; subst; eauto]. 
Qed. 

Definition pPool := Ensemble ptrm. 
Definition pSingleton := Singleton ptrm. 
Definition pUnion := Union ptrm. 

Inductive pconfig : Type :=
|pError : pconfig
|pOK : pHeap -> pPool -> pPool -> pconfig. 

Inductive pstep : pHeap -> pPool -> pPool -> pconfig -> Prop :=
|PBetaRed : forall t E e arg h T,
              pdecompose t (pappValCtxt E (plambda e)) arg -> pval arg = true ->
              pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E (popen 0 arg e))))
|pProjectL : forall V1 V2 h T t E,
               pdecompose t (pfstCtxt E) (ppair V1 V2) -> pval V1 = true -> pval V2 = true ->
               pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E V1)))
|pProjectR : forall V1 V2 h T t E,
               pdecompose t (psndCtxt E) (ppair V1 V2) -> pval V1 = true -> pval V2 = true ->
               pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E V2)))
|PBind : forall E t M N h T, 
            pdecompose t (pbindCtxt E N) (pret M) -> 
           pstep h T (pSingleton t) (pOK h T (pSingleton(pfill E(papp N M))))
|PBindRaise : forall E t M N h T,
                 pdecompose t (pbindCtxt E N) (praise M) -> 
                pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E(praise M))))
|pHandle : forall E t M N h T,
              pdecompose t (phandleCtxt E N) (praise M) -> 
             pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E(papp N M))))
|pHandleRet : forall E t M N h T,
                 pdecompose t (phandleCtxt E N) (pret M) -> 
                pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E(pret M))))
|pFork : forall E t M h T,
            pdecompose t E (pfork M) -> 
           pstep h T (pSingleton t) (pOK h T (Couple ptrm (pfill E(pret punit)) M))
|PGet : forall E M t h T x,
           heap_lookup x h = Some(pfull M) -> pdecompose t E (pget (pfvar x)) -> 
          pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E(pret M))))
|PPut : forall E t M h h' T x,
           pdecompose t E (pput (pfvar x) M) -> heap_lookup x h = Some pempty ->
          h' = replace x (pfull M) h ->
          pstep h T (pSingleton t) (pOK (replace x (pfull M) h) T (pSingleton (pfill E (pret punit))))
|PPutError : forall E t M h T x N,
               pdecompose t E (pput (pfvar x) M) -> heap_lookup x h = Some (pfull N) ->
               pstep h T (pSingleton t) pError
|PNew : forall E t h h' T x,
             pdecompose t E pnew -> (x, h') = extend pempty h ->
             pstep h T (pSingleton t) (pOK h' T (pSingleton (pfill E (pret (pfvar x)))))
|PTerminate : forall h T M, pstep h T (pSingleton (pret M)) (pOK h T (Empty_set ptrm))
                
.

Inductive pmultistep : pHeap -> pPool -> pPool -> pconfig -> Prop :=
|pmulti_refl : forall h p1 p2, pmultistep h p1 p2 (pOK h p1 p2)
|pmulti_step : forall T1 T2 h h' t t' c,
                 ~ In ptrm T2 t -> 
                 pstep h (pUnion T1 T2) (pSingleton t) (pOK h' (pUnion T1 T2) t') ->
                 pmultistep h' T1 (pUnion T2 t') c ->
                 pmultistep h T1 (Add ptrm T2 t) c
|pmulti_error : forall T1 T2 h t,
                  ~ In ptrm T2 t ->
                  pstep h (pUnion T1 T2) (pSingleton t) pError -> 
                  pmultistep h T1 (Add ptrm T2 t) pError.    

Require Import Coq.Sets.Powerset_facts. 


Theorem pSingletonMultistep : forall h h' T T' t t',
          pmultistep h T (Union ptrm (Empty_set ptrm) t) (pOK h' T' t') ->
          pmultistep h T t (pOK h' T' t'). 
Proof.
  intros. rewrite Union_commutative in H. rewrite union_empty in H. 
  assumption. Qed.   


(*Evaluation Context well formedness with respect to a particular term*)
Inductive pctxtWF : ptrm -> pctxt -> Prop :=
|pbindWF : forall e E N, pctxtWF e E -> pctxtWF e (pbindCtxt E N)
|phandleCtxtWF : forall e E N, pctxtWF e E -> pctxtWF e (phandleCtxt E N)
|pappCtxtWF : forall e E N, pctxtWF e E -> pval (pfill E e) = false -> pctxtWF e (pappCtxt E N)
|pappValCtxtWF : forall e E N, pctxtWF e E -> pval N = true -> pctxtWF e (pappValCtxt E N)
|ppairCtxtWF : forall e E N, pctxtWF e E -> pval (pfill E e) = false -> pctxtWF e (ppairCtxt E N)
|ppairValCtxtWF : forall e E N, pctxtWF e E -> pval N = true -> pval (pfill E e) = false -> 
                               pctxtWF e (ppairValCtxt E N)
|psndCtxtWF : forall e E, pctxtWF e E -> pctxtWF e (psndCtxt E)
|pfstCtxtWF : forall e E, pctxtWF e E -> pctxtWF e (pfstCtxt E)
|pholeCtxtWF : forall e, pval e = true -> pctxtWF e pholeCtxt
.

Theorem pdecomposeDecomposed : forall E e, pctxtWF e E ->
                                           pdecompose e pholeCtxt e -> 
                                           pdecompose (pfill E e) E e.
Proof.
  induction E; intros; auto; try solve[inversion H; subst; simpl; constructor; apply IHE; auto]; 
  try solve[inversion H; subst; simpl; constructor; auto].  
Qed.

Hint Constructors pctxtWF. 

Theorem pdecomposeWF : forall t E e, pdecompose t E e -> pctxtWF e E. 
Proof.
  intros. induction H; auto. 
  {constructor. assumption. apply pdecomposeEq in H0. rewrite <- H0. auto. }
  {constructor. assumption. apply pdecomposeEq in H0. rewrite <- H0. auto. }
  {constructor. assumption. assumption. apply pdecomposeEq in H1. rewrite <- H1. auto. }
Qed. 