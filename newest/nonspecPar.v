Require Export AST.   
Require Export Heap.
Require Export sets. 
Require Export Coq.Program.Equality.
Require Export multiset. 
Require Import NonSpec. 

(*Syntax for non-speculative Par Monad semantics (uses locally nameless cofinite quantification*)
Inductive ptrm' : Type :=
|pfvar' : id -> ptrm'
|pbvar' : id -> ptrm'
|punit' : ptrm'
|ppair' : ptrm' -> ptrm' -> ptrm'
|plambda' : ptrm' -> ptrm'
|papp' : ptrm' -> ptrm' -> ptrm'
|pret' : ptrm' -> ptrm'
|pbind' : ptrm' -> ptrm' -> ptrm'
|pfork' : ptrm' -> ptrm'
|pnew' : ptrm'
|pput' : ptrm' -> ptrm' -> ptrm'
|pget' : ptrm' -> ptrm'
|praise' : ptrm' -> ptrm'
|phandle' : ptrm' -> ptrm' -> ptrm'
|pfst' : ptrm' -> ptrm'
|psnd' : ptrm' -> ptrm'
|pdone' : ptrm' -> ptrm'
.

Fixpoint popen' (k:nat) (u:ptrm') (t:ptrm') : ptrm' :=
  match t with
      |pbvar' i => if beq_nat k i then u else t
      |ppair' e1 e2 => ppair' (popen' k u e1) (popen' k u e2)
      |plambda' e => plambda' (popen'  (S k) u e)
      |papp' e1 e2 => papp' (popen' k u e1) (popen' k u e2)
      |pret' e => pret' (popen' k u e)
      |pbind' e1 e2 => pbind' (popen' k u e1) (popen' k u e2)
      |pfork' e => pfork' (popen' k u e)
      |pput' i e => pput' (popen' k u i) (popen' k u e)
      |pget' i => pget' (popen' k u i)
      |praise' e => praise' (popen' k u e)
      |phandle' e1 e2 => phandle' (popen' k u e1) (popen' k u e2)
      |pfst' e => pfst' (popen' k u e)
      |psnd' e => psnd' (popen' k u e)
      |pdone' e => pdone' (popen' k u e)
      |_ => t
  end. 

Inductive pivar_state' : Type :=
|pempty' : pivar_state'
|pfull' : ptrm' -> pivar_state'.

Definition pHeap' := heap pivar_state'. 

Inductive pctxt' : Type :=
|pbindCtxt : pctxt' -> ptrm' -> pctxt'
|phandleCtxt : pctxt' -> ptrm' -> pctxt'
|pappctxt' : pctxt' -> ptrm' -> pctxt' 
|pappValCtxt : pctxt' -> ptrm' -> pctxt'
|ppairCtxt : pctxt' -> ptrm' -> pctxt'
|ppairValCtxt : pctxt' -> ptrm' -> pctxt'
|pfstCtxt : pctxt' -> pctxt' 
|psndCtxt : pctxt' -> pctxt'  
|pholeCtxt : pctxt'
.

Inductive pval' : ptrm' -> Prop :=
|pretVal' : forall M, pval' (pret' M)
|praiseVal' : forall M, pval' (praise' M)
|plamVal' : forall M, pval' (plambda' M)
|ppairVal' : forall M N, pval' M -> pval' N -> pval' (ppair' M N).

Inductive pdecompose' : ptrm' -> pctxt' -> ptrm' -> Prop :=
|pdecompBind : forall M N E M', ~ pval' M -> pdecompose' M E M' ->
                                pdecompose' (pbind' M N) (pbindCtxt E N) M'
|pdecompBindVal : forall M N, pval' M ->
                              pdecompose' (pbind' M N) pholeCtxt (pbind' M N)
|pdecompHandle : forall M M' N E, ~pval' M -> pdecompose' M E M' -> pdecompose' (phandle' M N) (phandleCtxt E N) M'
|pdecompHandleVal : forall M N, pval' M -> pdecompose' (phandle' M N) pholeCtxt (phandle' M N)
|pdecompApp : forall M N M' E, ~pval' M -> pdecompose' M E M' -> pdecompose' (papp' M N) (pappctxt' E N) M'
|pdecompAppVal1 : forall M N N' E, pval' M -> ~pval' N -> pdecompose' N E N' ->
                                   pdecompose' (papp' M N) (pappValCtxt E M) N'
|pdecompAppVal2 : forall M N, pval' M -> pval' N -> pdecompose' (papp' M N) pholeCtxt (papp' M N)
|pdecompFst : forall M E M', ~pval' M -> pdecompose' M E M' -> pdecompose' (pfst' M) (pfstCtxt E) M'
|pdecompFstVal : forall M, pval' M -> pdecompose' (pfst' M) pholeCtxt (pfst' M)
|pdecompSnd : forall M E M', ~pval' M -> pdecompose' M E M' -> pdecompose' (psnd' M) (psndCtxt E) M'
|pdecompSndVal : forall M, pval' M -> pdecompose' (psnd' M) pholeCtxt (psnd' M)
|pdecompNew : pdecompose' pnew' pholeCtxt pnew'
|pdecompGet : forall i, pdecompose' (pget' i) pholeCtxt (pget' i)
|pdecompPut : forall i M, pdecompose' (pput' i M) pholeCtxt (pput' i M)
|pdecompFork : forall M, pdecompose' (pfork' M) pholeCtxt (pfork' M)
|pdecompPair : forall M M' E N, ~pval' M -> pdecompose' M E M' ->
                                pdecompose' (ppair' M N) (ppairCtxt E N) M'
|pdecompPairVal : forall M N N' E, pval' M -> ~pval' N -> pdecompose' N E N' ->
                                   pdecompose' (ppair' M N) (ppairValCtxt E M) N'
.  

Fixpoint pfill' (c:pctxt') (t:ptrm') : ptrm' :=
  match c with
      |pbindCtxt E N => pbind' (pfill' E t) N
      |phandleCtxt E N => phandle' (pfill' E t) N
      |pappctxt' E N => papp' (pfill' E t) N
      |pappValCtxt E M => papp' M (pfill' E t)
      |ppairCtxt E N => ppair' (pfill' E t) N
      |ppairValCtxt E M => ppair' M (pfill' E t)
      |pfstCtxt E => pfst' (pfill' E t)
      |psndCtxt E => psnd' (pfill' E t)
      |pholeCtxt => t
  end. 

Ltac helperTac :=
  match goal with
    |H:?x=?y |- _ => inversion H; subst; clear H
    |H:forall M e, (?x,?y) = (M, e) -> ?z |- _ => assert(EQ:(x,y)=(x,y)) by auto; apply H in EQ
  end. 

Theorem pdecompose'Eq : forall M E e, pdecompose' M E e -> M = pfill' E e. 
Proof.
  induction M; intros; try solve[inversion H; subst; auto]; 
  try solve[inversion H; subst; auto; simpl; apply IHM1 in H5; subst; auto].
  {inversion H; subst. apply IHM1 in H5. subst. auto. apply IHM2 in H6. subst. auto. }
  {inversion H; subst. apply IHM1 in H5; subst; auto. apply IHM2 in H6; subst; auto. auto. }
  {inversion H; subst; auto. apply IHM in H2; subst; auto. }
  {inversion H; subst; auto. apply IHM in H2; subst; auto. }
Qed. 

Ltac inv H := inversion H; subst; clear H.

Theorem pctxt'Unique : forall M E E' e e', pdecompose' M E e -> pdecompose' M E' e' ->
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
Qed. 

Definition pPool' := multiset ptrm'. 
Definition pSingle' := Single ptrm'. 
Definition pUnion' := Union ptrm'. 
Definition pCouple' := Couple ptrm'. 

Inductive pconfig' : Type :=
|pError' : pconfig'
|pOK' : pHeap' -> pPool' -> pPool' -> pconfig'. 

Inductive pbasic_step : ptrm' -> ptrm' -> Prop :=
|pbasicBeta : forall t E e N,  pdecompose' t E (papp'(plambda' e) N) ->
                              pbasic_step t (pfill' E (popen' 0 N e))
|pbasicProjL : forall t E V1 V2,
                pdecompose' t E (pfst' (ppair' V1 V2)) -> pbasic_step t (pfill' E V1)
|pbasicProjR : forall t E V1 V2,
                pdecompose' t E (psnd'(ppair' V1 V2)) -> pbasic_step t (pfill' E V2)
|pbasicBind : forall t E M N,
               pdecompose' t E (pbind' (pret' M) N) -> pbasic_step t (pfill' E (papp' N M))
|pbasicBindRaise : forall t E M N,
                    pdecompose' t E (pbind' (praise' M) N) -> pbasic_step t (pfill' E (praise' M))
|pbasicHandle : forall t E M N,
                 pdecompose' t E (phandle' (praise' M) N) -> pbasic_step t (pfill' E (papp' N M))
|pbasicHandleRet : forall t E M N,
                    pdecompose' t E (phandle' (pret' M) N) -> pbasic_step t (pfill' E (pret' M)). 

Inductive pstep' : pHeap' -> pPool' -> pPool' -> pconfig' -> Prop :=
|PBasicStep : forall t t' h T,
                pbasic_step t t' -> pstep' h T (pSingle' t) (pOK' h T (pSingle' t'))
|pFork : forall E t M h T,
           pdecompose' t E (pfork' M) -> 
           pstep' h T (pSingle' t) (pOK' h T (pCouple' (pfill' E(pret' punit')) M))
|PGet : forall E M t h T x,
           heap_lookup x h = Some(pfull' M) -> pdecompose' t E (pget' (pfvar' x)) -> 
           pstep' h T (pSingle' t) (pOK' h T (pSingle' (pfill' E(pret' M))))
|PPut : forall E t M h h' T x,
          pdecompose' t E (pput' (pfvar' x) M) -> heap_lookup x h = Some pempty' ->
          h' = replace x (pfull' M) h ->
          pstep' h T (pSingle' t) (pOK' h' T (pSingle' (pfill' E (pret' punit'))))
|PPutError : forall E t M h T x N,
               pdecompose' t E (pput' (pfvar' x) M) -> heap_lookup x h = Some (pfull' N) ->
               pstep' h T (pSingle' t) pError'
|PNew : forall E t h h' T x (p:heap_lookup x h = None),
          pdecompose' t E pnew' ->  h' = extend x pempty' h p ->
          pstep' h T (pSingle' t) (pOK' h' T (pSingle' (pfill' E (pret' (pfvar' x)))))
.

Inductive pmultistep' : pHeap' -> pPool' -> option (pHeap' * pPool') -> Prop :=
|pmulti_refl' : forall H T, pmultistep' H T (Some (H, T))
|pmulti_step' : forall H H' T t t' c,
                 pstep' H T t (pOK' H' T t') -> pmultistep' H' (pUnion' T t') c ->
                 pmultistep' H (pUnion' T t) c
|pmulti_error' : forall H T t,
                  pstep' H T t pError' -> 
                  pmultistep' H (pUnion' T t) None.    

Ltac depInd H := generalize_eqs_vars H; induction H; simplify_dep_elim; intros.

Theorem pmulti_trans : forall H T H' T' H'' T'',
                         pmultistep' H T (Some (H', T')) -> 
                         pmultistep' H' T' (Some (H'', T'')) ->
                         pmultistep' H T (Some (H'', T'')).
Proof.
  intros. depInd H0. 
  {auto. }
  {econstructor; eauto. }
Qed. 

Inductive pctxt'WF (e:ptrm') : pctxt' -> Prop :=
|pbindWF : forall N E, pctxt'WF e E -> ~pval' (pfill' E e) -> pctxt'WF e (pbindCtxt E N)
|phandleWF : forall N E, pctxt'WF e E -> ~pval' (pfill' E e) -> pctxt'WF e (phandleCtxt E N)
|pappWF : forall N E, pctxt'WF e E -> ~pval' (pfill' E e) -> pctxt'WF e (pappctxt' E N)
|pappValWF : forall M E, pctxt'WF e E -> pval' M -> ~pval' (pfill' E e) -> pctxt'WF e (pappValCtxt E M)
|ppairWF : forall N E, pctxt'WF e E -> ~pval' (pfill' E e) -> pctxt'WF e (ppairCtxt E N)
|ppairValWF : forall M E, pctxt'WF e E -> pval' M -> ~pval' (pfill' E e) -> pctxt'WF e (ppairValCtxt E M)
|pfstWF : forall E, pctxt'WF e E -> ~pval' (pfill' E e) -> pctxt'WF e (pfstCtxt E)
|psndWF : forall E, pctxt'WF e E -> ~pval' (pfill' E e) -> pctxt'WF e (psndCtxt E)
|pholEWF : pctxt'WF e pholeCtxt. 

Theorem pdecompose'Decomposed : forall E e, pctxt'WF e E ->
                                          pdecompose' e pholeCtxt e -> 
                                          pdecompose' (pfill' E e) E e. 
Proof.
  intros. induction H; try solve[simpl; constructor; auto]. 
  {simpl. assumption. }
Qed. 

Hint Constructors pctxt'WF. 

Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 

Theorem pdecompose'WF : forall t E e, pdecompose' t E e -> pctxt'WF e E. 
Proof.
  induction t; intros; try solve[inversion H];
  try solve[inversion H; subst; auto; copy H5; apply IHt1 in H5; constructor; auto; 
   apply pdecompose'Eq in H0; subst; auto].
  {inversion H; subst. 
   {constructor; auto. apply pdecompose'Eq in H5; subst. auto. }
   {constructor; auto. apply pdecompose'Eq in H6; subst; auto. }
  }
  {inversion H; subst; auto.  
   {constructor; auto. apply pdecompose'Eq in H5; subst; auto. }
   {constructor; auto. apply pdecompose'Eq in H6; subst; auto. }
  }
  {inversion H; subst; auto. constructor. apply IHt. auto. apply pdecompose'Eq in H2; subst; auto. }
  {inversion H; subst; auto. constructor. apply IHt. auto. apply pdecompose'Eq in H2; subst; auto. }
Qed. 

Fixpoint pErase t :=
  match t with
    |pfvar i => pfvar' i
    |pbvar i => pbvar' i
    |punit => punit'
    |ppair e1 e2 => ppair' (pErase e1) (pErase e2)
    |plambda e => plambda' (pErase e)
    |papp e1 e2 => papp' (pErase e1) (pErase e2)
    |pret e => pret' (pErase e)
    |pbind e1 e2 => pbind' (pErase e1) (pErase e2)
    |pfork e => pfork' (pErase e)
    |pnew => pnew'
    |pput i e => pput' (pErase i) (pErase e)
    |pget i => pget' (pErase i)
    |praise e => praise' (pErase e)
    |phandle e1 e2 => phandle' (pErase e1) (pErase e2)
    |pfst e => pfst' (pErase e)
    |psnd e => psnd' (pErase e)
    |pdone e => pdone' (pErase e)
    |pspec e1 e2 => pbind' (pErase e1) (plambda' (pbind' (pErase e2) (pret' (ppair' (pbvar' 0) (pbvar' 1)))))
    |pspecRun e1 e2 => pbind' (pErase e1) (plambda' (pbind' (pErase e2) (pret' (ppair' (pbvar' 0) (pbvar' 1)))))
    |pspecJoin e1 e2 => pbind' (pErase e1) (plambda' (pbind' (pErase e2) (pret' (ppair' (pbvar' 0) (pbvar' 1)))))
  end. 

Fixpoint pErasePool T :=
  match T with
      |t::ts => pErase t::pErasePool ts
      |nil => nil
  end. 

Fixpoint raw_pEraseHeap (H: rawHeap pivar_state) :=
  match H with
      |(i, pempty)::H' => (i, pempty')::raw_pEraseHeap H'
      |(i, pfull M)::H' => (i, pfull' (pErase M))::raw_pEraseHeap H'
      |nil => nil
  end. 

Theorem pEraseHeapUnique : forall H S, 
                             unique pivar_state S H ->
                             unique pivar_state' S (raw_pEraseHeap H). 
Proof.
  induction H; intros. 
  {constructor. }
  {inv H0. simpl. destruct v; constructor; auto. }
Qed. 

Definition pEraseHeap H :=
  match H with
      |heap_ h p => heap_ pivar_state' (raw_pEraseHeap h) (pEraseHeapUnique h (Ensembles.Empty_set AST.id) p)
  end. 

Theorem ParImpliesPar' : forall H T t H' t', 
                           pstep H T t (pOK H' T t') ->
                           pstep' (pEraseHeap H) (pErasePool T) (pErasePool t)
                                 (pOK' (pEraseHeap H') (pErasePool T) (pErasePool t')). 
Admitted. 

Require Import Spec. 

Fixpoint specTerm' t :=
  match t with
    |pfvar' i => fvar i
    |pbvar' i => bvar i
    |punit' => unit
    |ppair' e1 e2 => pair_ (specTerm' e1) (specTerm' e2)
    |plambda' e => lambda (specTerm' e)
    |papp' e1 e2 => app (specTerm' e1) (specTerm' e2)
    |pret' e => ret (specTerm' e)
    |pbind' e1 e2 => bind (specTerm' e1) (specTerm' e2)
    |pfork' e => fork (specTerm' e)
    |pnew' => new
    |pput' i e => put (specTerm' i) (specTerm' e)
    |pget' i => get (specTerm' i)
    |praise' e => raise (specTerm' e)
    |phandle' e1 e2 => handle (specTerm' e1) (specTerm' e2)
    |pfst' e => fst (specTerm' e)
    |psnd' e => snd (specTerm' e)
    |pdone' e => done (specTerm' e)
  end. 

Inductive specPool' : pPool' -> pool -> Prop :=
|specPool'Cons : forall t ts tid s2 Ts, 
                   specPool' ts Ts ->
                   specPool' (t::ts) ((tid,unlocked nil,s2,specTerm' t)::Ts)
|specPoolNil' : specPool' nil nil. 

Inductive raw_specHeap' : rawHeap pivar_state' -> rawHeap ivar_state -> Prop :=
|specConsFull' : forall i tid M H H',
                  raw_specHeap' H H' -> 
                  raw_specHeap' ((i, pfull' M)::H) ((i, sfull COMMIT nil COMMIT tid (specTerm' M))::H')
|specConsEmpty' : forall i H H', raw_specHeap' H H' -> 
                                raw_specHeap'((i, pempty')::H) ((i, sempty COMMIT)::H')
|specHeapNil' : raw_specHeap' nil nil. 

Theorem spec'Unique : forall H S H',
                       unique pivar_state' S H -> raw_specHeap' H H' ->
                       unique ivar_state S H'. 
Proof.
  intros. Hint Constructors raw_specHeap'. generalize dependent S.
  induction H1; intros. inv H0. constructor; auto. inv H0. constructor; auto. 
  constructor. 
Qed. 

Inductive specHeap' : pHeap' -> sHeap -> Prop :=
|specHeap_' : forall h h' proof (p':raw_specHeap' h h'), 
               specHeap' (heap_ pivar_state' h proof)
                        (heap_ ivar_state h' (spec'Unique h (Ensembles.Empty_set AST.id) h' proof p')). 

Theorem Par'ImpliesSpec : forall H T t H' t' ST SH, 
                            pstep' H T t (pOK' H' T t') -> specHeap' H SH ->
                            specPool' (pUnion' T t) ST -> 
                            exists SH' ST', multistep SH ST (Some(SH', ST')) /\
                                            specPool' (pUnion' T t') ST' /\
                                            specHeap' H' SH'. 
Admitted. 


Theorem ParImpliesSpec : forall H T t H' t' ST SH, 
                            pstep H T t (pOK' H' T t') -> specHeap' H SH ->
                            specPool (pUnion' T t) ST -> 
                            exists SH' ST', multistep SH ST (Some(SH', ST')) /\
                                            specPool' (pUnion' T t') ST' /\
                                            specHeap' H' SH'. 
Admitted. 
