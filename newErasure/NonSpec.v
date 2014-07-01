Require Import AST. 
Require Import Heap.
Require Import Coq.Sets.Ensembles. 
Require Import sets. 

Definition pHeap := heap pivar_state. 

Inductive pctxt : Type :=
|pbindCtxt : pctxt -> ptrm -> pctxt
|phandleCtxt : pctxt -> ptrm -> pctxt
|pappCtxt : pctxt -> ptrm -> pctxt 
|pfstCtxt : pctxt -> pctxt 
|psndCtxt : pctxt -> pctxt  
|pholeCtxt : pctxt
.

Inductive pval : ptrm -> Prop :=
|pretVal : forall M, pval (pret M)
|praiseVal : forall M, pval (praise M)
|plamVal : forall M, pval (plambda M)
|ppairVal : forall M N, pval (ppair M N).

Inductive pdecompose : ptrm -> pctxt -> ptrm -> Prop :=
|pdecompBind : forall M N E M', ~ pval M -> pdecompose M E M' ->
                                pdecompose (pbind M N) (pbindCtxt E N) M'
|pdecompBindVal : forall M N, pval M ->
                              pdecompose (pbind M N) pholeCtxt (pbind M N)
|pdecompHandle : forall M M' N E, ~pval M -> pdecompose M E M' -> pdecompose (phandle M N) (phandleCtxt E N) M'
|pdecompHandleVal : forall M N, pval M -> pdecompose (phandle M N) pholeCtxt (phandle M N)
|pdecompApp : forall M N M' E, ~pval M -> pdecompose M E M' -> pdecompose (papp M N) (pappCtxt E N) M'
|pdecompAppVal : forall M N, pval M -> pdecompose (papp M N) pholeCtxt (papp M N)
|pdecompFst : forall M E M', ~pval M -> pdecompose M E M' -> pdecompose (pfst M) (pfstCtxt E) M'
|pdecompFstVal : forall M, pval M -> pdecompose (pfst M) pholeCtxt (pfst M)
|pdecompSnd : forall M E M', ~pval M -> pdecompose M E M' -> pdecompose (psnd M) (psndCtxt E) M'
|pdecompSndVal : forall M, pval M -> pdecompose (psnd M) pholeCtxt (psnd M)
|pdecompNew : pdecompose pnew pholeCtxt pnew
|pdecompGet : forall i, pdecompose (pget i) pholeCtxt (pget i)
|pdecompPut : forall i M, pdecompose (pput i M) pholeCtxt (pput i M)
|pdecompFork : forall M, pdecompose (pfork M) pholeCtxt (pfork M)
.  

Fixpoint pfill (c:pctxt) (t:ptrm) : ptrm :=
  match c with
      |pbindCtxt E N => pbind (pfill E t) N
      |phandleCtxt E N => phandle (pfill E t) N
      |pappCtxt E N => papp (pfill E t) N
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
  induction M; intros; try solve[inversion H; subst; auto]; 
  try solve[inversion H; subst; auto; simpl; apply IHM1 in H5; subst; auto]. 
  {inversion H; subst; auto. apply IHM in H2; subst; auto. }
  {inversion H; subst; auto. apply IHM in H2; subst; auto. }
Qed. 

Definition pPool := Ensemble ptrm. 
Definition pSingleton := Singleton ptrm. 
Definition pUnion := Union ptrm. 

Inductive pconfig : Type :=
|pError : pconfig
|pOK : pHeap -> pPool -> pPool -> pconfig. 

Inductive pstep : pHeap -> pPool -> pPool -> pconfig -> Prop :=
|PBetaRed : forall t E e arg h T,
              pdecompose t E (papp (plambda e) arg) -> 
              pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E (popen 0 arg e))))
|pProjectL : forall V1 V2 h T t E,
               pdecompose t E (pfst (ppair V1 V2)) -> 
               pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E V1)))
|pProjectR : forall V1 V2 h T t E,
               pdecompose t E (psnd (ppair V1 V2)) -> 
               pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E V2)))
|PBind : forall E t M N h T, 
            pdecompose t E (pbind (pret M) N) -> 
           pstep h T (pSingleton t) (pOK h T (pSingleton(pfill E(papp N M))))
|PBindRaise : forall E t M N h T,
                 pdecompose t E (pbind (praise M) N) -> 
                pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E(praise M))))
|pHandle : forall E t M N h T,
              pdecompose t E (phandle (praise M) N)-> 
             pstep h T (pSingleton t) (pOK h T (pSingleton (pfill E(papp N M))))
|pHandleRet : forall E t M N h T,
                 pdecompose t E (phandle (pret M) N)  -> 
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
          pstep h T (pSingleton t) (pOK h' T (pSingleton (pfill E (pret punit))))
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


Inductive pctxtWF (e:ptrm) : pctxt -> Prop :=
|pbindWF : forall N E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (pbindCtxt E N)
|phandleWF : forall N E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (phandleCtxt E N)
|pappWF : forall N E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (pappCtxt E N)
|pfstWF : forall E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (pfstCtxt E)
|psndWF : forall E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (psndCtxt E)
|pholEWF : pctxtWF e pholeCtxt. 

Theorem pdecomposeDecomposed : forall E e, pctxtWF e E ->
                                          pdecompose e pholeCtxt e -> 
                                          pdecompose (pfill E e) E e. 
Proof.
  intros. induction H; try solve[simpl; constructor; auto]. 
  {simpl. assumption. }
Qed. 

Hint Constructors pctxtWF. 

Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 

Theorem pdecomposeWF : forall t E e, pdecompose t E e -> pctxtWF e E. 
Proof.
  induction t; intros; try solve[inversion H];
  try solve[inversion H; subst; auto; copy H5; apply IHt1 in H5; constructor; auto; 
   apply pdecomposeEq in H0; subst; auto]. 
  inversion H; subst; auto. constructor. apply IHt. auto. apply pdecomposeEq in H2; subst; auto.
  inversion H; subst; auto. constructor. apply IHt. auto. apply pdecomposeEq in H2; subst; auto.
Qed. 

