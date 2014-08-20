Require Export AST.   
Require Export Heap.
Require Export sets. 
Require Export Coq.Program.Equality.
Require Export multiset. 

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
|pspecRunCtxt : pctxt -> ptrm -> pctxt
|pspecJoinCtxt : pctxt -> ptrm ->pctxt
|pholeCtxt : pctxt
.

Inductive pval : ptrm -> Prop :=
|pretVal : forall M, pval (pret M)
|praiseVal : forall M, pval (praise M)
|plamVal : forall M, pval (plambda M)
|ppairVal : forall M N, pval M -> pval N -> pval (ppair M N).

Inductive pdecompose : ptrm -> pctxt -> ptrm -> Prop :=
|pdecompBind : forall M N E M', ~ pval M -> pdecompose M E M' ->
                                pdecompose (pbind M N) (pbindCtxt E N) M'
|pdecompBindVal : forall M N, pval M ->
                              pdecompose (pbind M N) pholeCtxt (pbind M N)
|pdecompSpecRun : forall M N E M', ~pval M -> pdecompose M E M' ->
                                   pdecompose (pspecRun M N) (pspecRunCtxt E N) M'
|pdecompSpecrunVal : forall M N, pval M ->
                                 pdecompose (pspecRun M N) pholeCtxt (pspecRun M N)
|pdecompSpecJoin : forall M N E N', pval M -> ~pval N -> pdecompose N E N' ->
                                    pdecompose (pspecJoin M N) (pspecJoinCtxt E M) N'
|pdecompSpecValJoin : forall M N, pval M -> pval N -> pdecompose (pspecJoin M N) pholeCtxt (pspecJoin M N)
|pdecompSpec : forall M N, pdecompose (pspec M N) pholeCtxt (pspec M N)
|pdecompHandle : forall M M' N E, ~pval M -> pdecompose M E M' -> pdecompose (phandle M N) (phandleCtxt E N) M'
|pdecompHandleVal : forall M N, pval M -> pdecompose (phandle M N) pholeCtxt (phandle M N)
|pdecompApp : forall M N M' E, ~pval M -> pdecompose M E M' -> pdecompose (papp M N) (pappCtxt E N) M'
|pdecompAppVal1 : forall M N N' E, pval M -> ~pval N -> pdecompose N E N' ->
                                   pdecompose (papp M N) (pappValCtxt E M) N'
|pdecompAppVal2 : forall M N, pval M -> pval N -> pdecompose (papp M N) pholeCtxt (papp M N)
|pdecompFst : forall M E M', ~pval M -> pdecompose M E M' -> pdecompose (pfst M) (pfstCtxt E) M'
|pdecompFstVal : forall M, pval M -> pdecompose (pfst M) pholeCtxt (pfst M)
|pdecompSnd : forall M E M', ~pval M -> pdecompose M E M' -> pdecompose (psnd M) (psndCtxt E) M'
|pdecompSndVal : forall M, pval M -> pdecompose (psnd M) pholeCtxt (psnd M)
|pdecompNew : pdecompose pnew pholeCtxt pnew
|pdecompGet : forall i, pdecompose (pget i) pholeCtxt (pget i)
|pdecompPut : forall i M, pdecompose (pput i M) pholeCtxt (pput i M)
|pdecompFork : forall M, pdecompose (pfork M) pholeCtxt (pfork M)
|pdecompPair : forall M M' E N, ~pval M -> pdecompose M E M' ->
                                pdecompose (ppair M N) (ppairCtxt E N) M'
|pdecompPairVal : forall M N N' E, pval M -> ~pval N -> pdecompose N E N' ->
                                   pdecompose (ppair M N) (ppairValCtxt E M) N'
.  

Fixpoint pfill (c:pctxt) (t:ptrm) : ptrm :=
  match c with
      |pbindCtxt E N => pbind (pfill E t) N
      |phandleCtxt E N => phandle (pfill E t) N
      |pspecRunCtxt E N => pspecRun (pfill E t) N
      |pspecJoinCtxt E M => pspecJoin M (pfill E t)
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
  induction M; intros; try solve[inversion H; subst; auto]; 
  try solve[inversion H; subst; auto; simpl; apply IHM1 in H5; subst; auto].
  {inversion H; subst. apply IHM1 in H5. subst. auto. apply IHM2 in H6. subst. auto. }
  {inversion H; subst. apply IHM1 in H5; subst; auto. apply IHM2 in H6; subst; auto. auto. }
  {inversion H; subst; auto. apply IHM in H2; subst; auto. }
  {inversion H; subst; auto. apply IHM in H2; subst; auto. }
  {inversion H; subst; auto. apply IHM2 in H6. subst. auto. }
Qed. 

Ltac inv H := inversion H; subst; clear H.

Theorem pctxtUnique : forall M E E' e e', pdecompose M E e -> pdecompose M E' e' ->
                                          E = E' /\ e = e'. 
Proof.
  induction M; intros; try solve[inversion H; inversion H0; subst; auto]. 
  {inv H; inv H0; try contradiction. eapply IHM1 in H6; eauto. inv H6. auto.  
   eapply IHM2 in H7; eauto. inv H7; auto. }
  {inv H; inv H0; try contradiction. eapply IHM1 in H6; eauto. inv H6; auto. 
   eapply IHM2 in H7; eauto. inv H7; auto. auto. }
  {inv H; inv H0; try contradiction. eapply IHM1 in H6; eauto. inv H6; auto. auto. }
  {inv H; inv H0; try contradiction; auto. eapply IHM1 in H6; eauto. inv H6; auto. }
  {inv H; inv H0; try contradiction; auto. eapply IHM in H3; eauto. inv H3; auto. }
  {inv H; inv H0; try contradiction; auto. eapply IHM in H3; eauto. inv H3; auto. }
  {inv H; inv H0; try contradiction; auto. eapply IHM1 in H6; eauto. inv H6; auto. }
  {inv H; inv H0; try contradiction; auto. eapply IHM2 in H7; eauto. inv H7; auto. }
Qed. 

Definition pPool := multiset ptrm. 
Definition pSingle := Single ptrm. 
Definition pUnion := Union ptrm. 
Definition pCouple := Couple ptrm. 
Inductive pconfig : Type :=
|pError : pconfig
|pOK : pHeap -> pPool -> pPool -> pconfig. 

Inductive pbasic_step : ptrm -> ptrm -> Prop :=
|pbasicBeta : forall t E e N,  pdecompose t E (papp(plambda e) N) ->
                              pbasic_step t (pfill E (popen 0 N e))
|pbasicProjL : forall t E V1 V2,
                pdecompose t E (pfst (ppair V1 V2)) -> pbasic_step t (pfill E V1)
|pbasicProjR : forall t E V1 V2,
                pdecompose t E (psnd(ppair V1 V2)) -> pbasic_step t (pfill E V2)
|pbasicBind : forall t E M N,
               pdecompose t E (pbind (pret M) N) -> pbasic_step t (pfill E (papp N M))
|pbasicBindRaise : forall t E M N,
                    pdecompose t E (pbind (praise M) N) -> pbasic_step t (pfill E (praise M))
|pbasicHandle : forall t E M N,
                 pdecompose t E (phandle (praise M) N) -> pbasic_step t (pfill E (papp N M))
|pbasicHandleRet : forall t E M N,
                    pdecompose t E (phandle (pret M) N) -> pbasic_step t (pfill E (pret M))
|pSpecJoinRaise : forall t M N E,
                    pdecompose t E (pspecJoin (pret N) (praise M)) ->
                    pbasic_step t (pfill E (praise M))
|pspecJoinDone : forall t M N E,
                   pdecompose t E (pspecJoin (pret N) (pret M)) ->
                   pbasic_step t (pfill E (pret (ppair N M))). 

Inductive pstep : pHeap -> pPool -> pPool -> pconfig -> Prop :=
|PBasicStep : forall t t' h T,
                pbasic_step t t' -> pstep h T (pSingle t) (pOK h T (pSingle t'))
|pSpec : forall t M N T h E, pdecompose t E (pspec M N) ->
                           pstep h T (pSingle t) (pOK h T (pSingle (pfill E (pspecRun M N))))
|pSpecRun : forall t M N T h E,
              pdecompose t E (pspecRun (pret N) M) -> 
              pstep h T (pSingle t) 
                    (pOK h T (pSingle (pfill E (pspecJoin (pret N) M))))
|pSpecRunRaise : forall t M N T h E,
                   pdecompose t E (pspecRun (praise N) M) -> 
                   pstep h T (pSingle t) (pOK h T (pSingle (pfill E (praise N))))
|pFork : forall E t M h T,
           pdecompose t E (pfork M) -> 
           pstep h T (pSingle t) (pOK h T (pCouple (pfill E(pret punit)) M))
|PGet : forall E M t h T x,
           heap_lookup x h = Some(pfull M) -> pdecompose t E (pget (pfvar x)) -> 
          pstep h T (pSingle t) (pOK h T (pSingle (pfill E(pret M))))
|PPut : forall E t M h h' T x,
          pdecompose t E (pput (pfvar x) M) -> heap_lookup x h = Some pempty ->
          h' = replace x (pfull M) h ->
          pstep h T (pSingle t) (pOK h' T (pSingle (pfill E (pret punit))))
|PPutError : forall E t M h T x N,
               pdecompose t E (pput (pfvar x) M) -> heap_lookup x h = Some (pfull N) ->
               pstep h T (pSingle t) pError
|PNew : forall E t h h' T x (p:heap_lookup x h = None),
          pdecompose t E pnew ->  h' = extend x pempty h p ->
          pstep h T (pSingle t) (pOK h' T (pSingle (pfill E (pret (pfvar x)))))
.

Inductive pmultistep : pHeap -> pPool -> option (pHeap * pPool) -> Prop :=
|pmulti_refl : forall H T, pmultistep H T (Some (H, T))
|pmulti_step : forall H H' T t t' c,
                 pstep H T t (pOK H' T t') -> pmultistep H' (pUnion T t') c ->
                 pmultistep H (pUnion T t) c
|pmulti_error : forall H T t,
                  pstep H T t pError -> 
                  pmultistep H (pUnion T t) None.    

Ltac depInd H := generalize_eqs_vars H; induction H; simplify_dep_elim; intros.

Theorem pmulti_trans : forall H T H' T' H'' T'',
                         pmultistep H T (Some (H', T')) -> 
                         pmultistep H' T' (Some (H'', T'')) ->
                         pmultistep H T (Some (H'', T'')).
Proof.
  intros. depInd H0. 
  {auto. }
  {econstructor; eauto. }
Qed. 

Inductive pctxtWF (e:ptrm) : pctxt -> Prop :=
|pbindWF : forall N E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (pbindCtxt E N)
|phandleWF : forall N E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (phandleCtxt E N)
|pSpecRunWF : forall N E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (pspecRunCtxt E N)
|pSpecJoinWF : forall M E, pctxtWF e E -> pval M -> ~pval (pfill E e) -> pctxtWF e (pspecJoinCtxt E M)
|pappWF : forall N E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (pappCtxt E N)
|pappValWF : forall M E, pctxtWF e E -> pval M -> ~pval (pfill E e) -> pctxtWF e (pappValCtxt E M)
|ppairWF : forall N E, pctxtWF e E -> ~pval (pfill E e) -> pctxtWF e (ppairCtxt E N)
|ppairValWF : forall M E, pctxtWF e E -> pval M -> ~pval (pfill E e) -> pctxtWF e (ppairValCtxt E M)
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
  {inversion H; subst. 
   {constructor; auto. apply pdecomposeEq in H5; subst. auto. }
   {constructor; auto. apply pdecomposeEq in H6; subst; auto. }
  }
  {inversion H; subst; auto.  
   {constructor; auto. apply pdecomposeEq in H5; subst; auto. }
   {constructor; auto. apply pdecomposeEq in H6; subst; auto. }
  }
  {inversion H; subst; auto. constructor. apply IHt. auto. apply pdecomposeEq in H2; subst; auto. }
  {inversion H; subst; auto. constructor. apply IHt. auto. apply pdecomposeEq in H2; subst; auto. }
  {inversion H; subst; auto. copy H6. apply IHt2 in H6. constructor; auto. apply pdecomposeEq in H0. 
   subst. auto. }
Qed. 

