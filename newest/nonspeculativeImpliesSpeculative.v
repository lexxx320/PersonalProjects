Require Import erasure. 
Require Import IndependenceCommon. 
Require Import stepWF. 

Fixpoint specTerm (t:ptrm) := 
  match t with
      |pfvar x => fvar x
      |pbvar x => bvar x
      |punit => unit
      |ppair e1 e2 => pair_ (specTerm e1) (specTerm e2)
      |plambda e => lambda (specTerm e)
      |papp e1 e2 => AST.app (specTerm e1) (specTerm e2)
      |pret e => ret (specTerm e)
      |pbind e1 e2 => bind (specTerm e1) (specTerm e2)
      |pfork e => fork (specTerm e)
      |pnew => new
      |pput e1 e2 => put (specTerm e1) (specTerm e2)
      |pget e => get (specTerm e)
      |praise e => raise (specTerm e)
      |phandle e1 e2 => handle (specTerm e1) (specTerm e2)
      |pfst e => fst (specTerm e)
      |psnd e => snd (specTerm e)
      |pspec e1 e2 => spec (specTerm e1) (specTerm e2)
      |pspecRun e1 e2 => specRun (specTerm e1) (specTerm e2)
      |pspecJoin e1 e2 => specJoin (specTerm e1) (specTerm e2)
      |pdone e => done (specTerm e)
  end. 

Inductive gather : ptrm -> pool -> Prop :=
|gFVar : forall x, gather (pfvar x) (Empty_set thread)
|gBVar : forall x, gather (pbvar x) (Empty_set thread)
|gUnit : gather punit (Empty_set thread)
|gPair : forall e1 e2 T1 T2, gather e1 T1 -> gather e2 T2 -> 
                           gather (ppair e1 e2) (tUnion T1 T2)
|gLam : forall e T, gather e T -> gather (plambda e) T
|gApp : forall e1 e2 T1 T2, gather e1 T1 -> gather e2 T2 ->
                          gather (papp e1 e2) (tUnion T1 T2)
|gRet : forall e T, gather e T -> gather (pret e) T
|gBind : forall e1 e2 T1 T2, gather e1 T1 -> gather e2 T2 ->
                           gather (pbind e1 e2) (tUnion T1 T2)
|gFork : forall e T, gather e T -> gather (pfork e) T
|gNew : gather pnew (Empty_set thread)
|gPut : forall e1 e2 T1 T2, gather e1 T1 -> gather e2 T2 ->
                          gather (pput e1 e2) (tUnion T1 T2)
|gGet : forall e T, gather e T -> gather (pget e) T
|gRaise : forall e T, gather e T -> 
                            gather (praise e) T
|gHandle : forall e1 e2 T1 T2, gather e1 T1 -> gather e2 T2 ->
                             gather (phandle e1 e2) (tUnion T1 T2)
|gFST : forall e T, gather e T -> gather (pfst e) T
|gSND : forall e T, gather e T -> gather (psnd e) T
|gSpec : forall e1 e2 T1 T2, gather e1 T1 -> gather e2 T2 ->
                           gather (pspec e1 e2) (tUnion T1 T2)
|gSpecJoin : forall e1 e2 T1 T2, gather e1 T1 -> gather e2 T2 ->
                               gather (pspecJoin e1 e2) (tUnion T1 T2)
|gDone : forall e T, gather e T -> gather (pdone e) T
|gSpecRun : forall e1 e2 T1 T2 tid, 
            gather e1 T1 -> gather e2 T2 -> 
            gather (pspecRun e1 e2) 
                   (tUnion (tUnion T1 T2)
                           (tSingleton(tid,specStack [] (specTerm e2), nil, specTerm e2))).

Inductive speculate : pPool -> pool -> Prop :=
|specCons : forall t Ts Ts' tid s2 T,
              speculate Ts Ts' -> gather t T ->
              speculate (t::Ts) (tUnion T ((tid,unlocked nil,s2,specTerm t)::Ts'))
|specNil : speculate nil nil.

Inductive raw_specHeap : rawHeap pivar_state -> rawHeap ivar_state -> Prop :=
|specConsFull : forall i tid M H H',
                  raw_specHeap H H' -> 
                  raw_specHeap ((i, pfull M)::H) ((i, sfull COMMIT nil COMMIT tid (specTerm M))::H')
|specConsEmpty : forall i H H', raw_specHeap H H' -> 
                                raw_specHeap((i, pempty)::H) ((i, sempty COMMIT)::H')
|specHeapNil : raw_specHeap nil nil. 

Theorem specUnique : forall H S H',
                       unique pivar_state S H -> raw_specHeap H H' ->
                       unique ivar_state S H'. 
Proof.
  intros. generalize dependent S. induction H1; intros; auto; inv H0; auto. 
Qed. 

Inductive specHeap : pHeap -> sHeap -> Prop :=
|specHeap' : forall h h' proof (p':raw_specHeap h h'), 
               specHeap (heap_ pivar_state h proof)
                        (heap_ ivar_state h' (specUnique h (Ensembles.Empty_set AST.id) h' proof p')). 

Theorem raw_specHeapReplaceFull : forall x tid M H H',
              raw_specHeap H H' -> raw_heap_lookup x H = Some pempty ->
              raw_specHeap (raw_replace x (pfull M) H) (raw_replace x (sfull COMMIT nil COMMIT tid (specTerm M)) H').         
Proof.
  intros. genDeps{x; tid; M}. induction H0; intros. 
  {simpl. destruct (beq_nat x i) eqn:eq. 
   {constructor. auto. }
   {constructor. simpl in *. rewrite eq in H1. eauto. }
  }
  {simpl in *. destruct (beq_nat x i) eqn:eq. 
   {constructor. auto. }
   {constructor. auto. }
  }
  {constructor. }
Qed. 

Theorem specHeapReplaceFull : forall x tid M H H',
              specHeap H H' -> heap_lookup x H = Some pempty ->
              specHeap (replace x (pfull M) H) (replace x (sfull COMMIT nil COMMIT tid (specTerm M)) H').         
Proof.
  intros. destruct H. simpl. destruct H'. simpl. erewrite rawHeapsEq; auto. 
  erewrite (rawHeapsEq ivar_state); auto. apply specHeap'. 
  Grab Existential Variables. eapply raw_specHeapReplaceFull; auto. inv H0. auto. 
  apply replacePreservesUniqueness. auto. 
Qed. 

Theorem UnionEqR' : forall (U:Type) (T T1 T2:multiset U), T1 = T2 -> Union U T T1 = Union U T T2. 
Proof.
  intros. subst; auto. 
Qed. 

Theorem UnionEqL' : forall U (T T1 T2:multiset U), T1 = T2 -> Union U T1 T = Union U T2 T. 
Proof.
  intros. subst; auto. 
Qed. 

Theorem specUnionComm : forall T1 T2 T,
                          speculate (pUnion T1 T2) T ->
                          exists T1' T2', (speculate T1) T1' /\ (speculate T2) T2' /\
                          T = tUnion T1' T2' . 
Proof.
  induction T1; intros. 
  {simpl in *. econstructor. econstructor. split; eauto. constructor. 
   split; eauto. }
  {simpl in *. inv H.  
   {eapply IHT1 in H2. invertHyp. econstructor. econstructor. split. 
    econstructor. eauto. eauto. split; eauto. unfoldTac.
    rewrite <- Union_associative. simpl. auto. }
  }
Qed. 

Theorem singleton : forall (t:thread), [t] = tSingleton t. auto. Qed. 


Theorem specUnionL : forall T1 T2 T1' T2', 
                       speculate T1 T1' -> speculate T2 T2' ->
                       speculate (pUnion T1 T2) (tUnion T1' T2'). 
Proof.
  induction T1; intros. 
  {simpl. inv H. simpl. auto. }
  {inv H. eapply IHT1 in H0; eauto. simpl. unfoldTac. rewrite <- Union_associative.  
   eapply specCons. eassumption. auto. }
Qed. 

Fixpoint specCtxt E := 
  match E with
      |pbindCtxt E e => bindCtxt (specCtxt E) (specTerm e)
      |phandleCtxt E e => handleCtxt (specCtxt E) (specTerm e)
      |pappCtxt E e => appCtxt (specCtxt E) (specTerm e)
      |pappValCtxt E e => appValCtxt (specCtxt E) (specTerm e)
      |ppairCtxt E e => pairCtxt (specCtxt E) (specTerm e)
      |ppairValCtxt E e => pairValCtxt (specCtxt E) (specTerm e)
      |pfstCtxt E => fstCtxt (specCtxt E)
      |psndCtxt E => sndCtxt (specCtxt E)
      |pspecRunCtxt E e => specRunCtxt (specCtxt E) (specTerm e)
      |pspecJoinCtxt E e => specJoinCtxt (specCtxt E) (specTerm e)
      |pholeCtxt => holeCtxt
  end. 

Theorem consNil : forall (T:Type) (a:T), [a] = a::nil. auto. Qed. 

Theorem eSpecTerm : forall e, exists e', specTerm e' = e. 
Proof.
  induction e; intros; try invertHyp. 
  {exists (pfvar i). auto. }
  {exists (pbvar i). auto. }
  {exists punit; auto. }
  {exists (ppair x0 x). auto. }
  {exists (plambda x); auto. }
  {exists (papp x0 x); auto. }
  {exists (pret x); auto. }
  {exists (pbind x0 x); auto. }
  {exists (pfork x); auto. }
  {exists pnew; auto. }
  {exists (pput x0 x); auto. }
  {exists (pget x); auto. }
  {exists (praise x); auto. }
  {exists (phandle x0 x); auto. }
  {exists (pspec x0 x); auto. }
  {exists (pspecRun x0 x); auto. }
  {exists (pspecJoin x0 x); auto. }
  {exists (pfst x); auto. }
  {exists (psnd x); auto. }
  {exists (pdone x); auto. }
Qed.  

Theorem specFill : forall E e, specTerm (pfill E e) = fill (specCtxt E) (specTerm e). 
Proof.
  induction E; intros; try solve[simpl; erewrite IHE; eauto]. 
  simpl. auto. 
Qed. 

Theorem gatherTotal : forall e, exists T, gather e T.
Proof.
  induction e; try solve[repeat econstructor]; 
  try solve[invertHyp; econstructor; econstructor; eauto]. 
  Grab Existential Variables. constructor. 
Qed. 

Theorem UnionSwapL: forall (X : Type) (T1 T2 T3 : multiset X),
                      Union X (Union X T1 T2) T3 = Union X (Union X T3 T2) T1.
Proof.
  intros. rewrite (Union_commutative X T1). rewrite UnionSwap. 
  rewrite (Union_commutative X T2). auto. Qed. 

Theorem specOpen : forall e e' n, 
                     specTerm (popen n e e') = open n (specTerm e) (specTerm e').
Proof.
  induction e'; intros; auto; try solve[simpl;rewrite IHe'1; rewrite IHe'2; eauto];
  try solve[simpl; rewrite IHe'; eauto]. 
  {simpl. destruct (beq_nat n i); auto. }
Qed. 


Theorem specUnionComm' : forall T1 T1' T2 T2', 
                           speculate T1 T1' -> speculate T2 T2' ->
                           speculate (pUnion T1 T2) (tUnion T1' T2'). 
Proof.
  induction T1; intros. 
  {inv H. auto. }
  {inv H. simpl. unfoldTac. rewrite <- Union_associative. constructor; eauto. }
Qed. 

Inductive gatherCtxt : pctxt -> pool -> Prop :=
|gBindCtxt : forall E t T1 T2, gather t T1 -> gatherCtxt E T2 ->
                         gatherCtxt (pbindCtxt E t) (tUnion T1 T2)
|gHandleCtxt : forall E t T1 T2, gather t T1 -> gatherCtxt E T2 ->
                                 gatherCtxt(phandleCtxt E t) (tUnion T1 T2)
|gAppCtxt : forall E t T1 T2, gather t T1 -> gatherCtxt E T2 ->
                              gatherCtxt(pappCtxt E t) (tUnion T1 T2)
|gAppValCtxt : forall E t T1 T2, gather t T1 -> gatherCtxt E T2 ->
                                 gatherCtxt (pappValCtxt E t) (tUnion T1 T2)
|gFstCtxt : forall E T, gatherCtxt E T -> gatherCtxt (pfstCtxt E) T
|gSndCtxt : forall E T, gatherCtxt E T -> gatherCtxt (psndCtxt E) T
|gPairCtxt : forall E t T1 T2, gatherCtxt E T1 -> gather t T2 ->
                               gatherCtxt (ppairCtxt E t) (tUnion T1 T2)
|gPairValCtxt : forall E t T1 T2, gatherCtxt E T1 -> gather t T2 ->
                                  gatherCtxt (ppairValCtxt E t) (tUnion T1 T2)
|gSpecRunCtxt : forall E t T1 T2 tid, 
                  gatherCtxt E T1 -> gather t T2 ->
                  gatherCtxt (pspecRunCtxt E t) (tUnion (tUnion T1 T2)
                                                        (tSingleton(tid,specStack [] (specTerm t), nil, specTerm t)))
|gSpecJoinCtxt : forall E t T1 T2, gatherCtxt E T1 -> gather t T2 ->
                                   gatherCtxt (pspecJoinCtxt E t) (tUnion T1 T2)
|gHoleCtxt : gatherCtxt pholeCtxt (Empty_set thread). 

Theorem raw_specHeapLookupFull : forall x H M H',
                               raw_heap_lookup x H = Some(pfull M) -> raw_specHeap H H' -> exists tid,
                               raw_heap_lookup x H' = Some(sfull COMMIT nil COMMIT tid (specTerm M)).
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. inv H1. simpl. rewrite eq. eauto. }
   {destruct p; auto. inv H1. simpl. rewrite eq; auto. inv H1. simpl. rewrite eq; auto. }
  }
Qed. 

Theorem specHeapLookupFull : forall x H M H',
                               heap_lookup x H = Some(pfull M) -> specHeap H H' -> 
                               exists tid, heap_lookup x H' = Some(sfull COMMIT nil COMMIT tid (specTerm M)). 
Proof.
  intros. destruct H. simpl in *. inv H1. eapply raw_specHeapLookupFull in H0; eauto. 
Qed. 

Theorem appSingle : forall (T:Type) (a:T) b, a::b = [a]++b. reflexivity. Qed. 

Theorem gatherCtxtTotal : forall E, exists T, gatherCtxt E T.
Proof.
  induction E; intros; try( 
  match goal with
      |t:ptrm |- _ => assert(exists T, gather t T) by apply gatherTotal
  end); try invertHyp; econstructor; econstructor; eauto. 
  Grab Existential Variables. constructor. 
Qed. 

Ltac gatherTac e := try(assert(exists T, gather e T) by apply gatherTotal; invertHyp);
                   try(assert(exists T, gatherCtxt e T) by apply gatherCtxtTotal; invertHyp). 

Ltac gatherTac' es :=
  match es with
      |HNil => idtac
      |HCons ?e ?es' => gatherTac e; gatherTac' es'
  end. 

Hint Constructors gather gatherCtxt. 

Theorem gatherDecomp : forall E t e T, 
                           pdecompose t E e ->
                           gather t T -> exists T1 T2, gatherCtxt E T1 /\
                                                       gather e T2 /\
                                                       T = tUnion T1 T2. 
Proof.
  induction E; intros. 
  {inv H; inv H0. eapply IHE in H6; eauto. invertHyp. econstructor. econstructor. 
   split. constructor; eauto. split; eauto. unfoldTac. rewrite UnionSwap. 
   rewrite (Union_commutative thread x). auto. }
  {inv H; inv H0. eapply IHE in H6; eauto. invertHyp. econstructor. econstructor. 
   split. constructor; eauto. split; eauto. unfoldTac. rewrite UnionSwap. 
   rewrite (Union_commutative thread x). auto. }
  {inv H; inv H0. eapply IHE in H6; eauto. invertHyp. econstructor. econstructor. 
   split. constructor; eauto. split; eauto. unfoldTac. rewrite UnionSwapL. 
   rewrite UnionSwap. auto. }
  {inv H; inv H0. eapply IHE in H7; eauto. invertHyp. econstructor. econstructor. 
   split; eauto. split; eauto. unfoldTac. rewrite Union_associative. auto. }
  {inv H; inv H0. eapply IHE in H6; eauto. invertHyp. econstructor. econstructor. 
   split; eauto. split; eauto. unfoldTac. rewrite UnionSwap. auto. }
  {inv H; inv H0. eapply IHE in H7; eauto. invertHyp. econstructor. econstructor. 
   split; eauto. split; eauto. unfoldTac. rewrite Union_associative. 
   rewrite (Union_commutative thread T1). auto. }
  {inv H. inv H0. eapply IHE in H4; eauto. invertHyp. econstructor. eauto. }
  {inv H. inv H0. eapply IHE in H4; eauto. invertHyp. econstructor. eauto. }
  {inv H; inv H0. eapply IHE in H6; eauto. invertHyp. econstructor. econstructor. 
   split. constructor; eauto. split; eauto. unfoldTac. rewrite UnionSwap. 
   repeat rewrite <- Union_associative. apply UnionEqR'. rewrite Union_commutative. 
   repeat rewrite Union_associative. apply UnionEqL'. rewrite Union_commutative. auto. }
  {inv H; inv H0. eapply IHE in H7; eauto. invertHyp. econstructor. econstructor. 
   split. eauto. split; eauto. unfoldTac. rewrite Union_associative. 
   rewrite (Union_commutative thread T1). auto. }
  {inv H; econstructor; econstructor; eauto. }
Qed. 

Theorem gatherFill : forall E e T1 T2,
                       gatherCtxt E T1 -> gather e T2 ->
                       gather (pfill E e) (tUnion T1 T2). 
Proof.
  induction E; intros. 
  {inv H. eapply IHE in H5. Focus 2. eapply H0. simpl. unfoldTac. rewrite UnionSwapL.  
   constructor; auto. rewrite Union_commutative. auto. }
  {inv H. eapply IHE in H5. Focus 2. eapply H0. simpl. unfoldTac. rewrite UnionSwapL.  
   constructor; auto. rewrite Union_commutative. auto. }
  {inv H. eapply IHE in H5. Focus 2. eapply H0. simpl. unfoldTac. rewrite UnionSwapL. 
   constructor; auto. rewrite Union_commutative. auto. }
  {inv H. eapply IHE in H5. Focus 2. eapply H0. simpl. unfoldTac.
   rewrite <- Union_associative. constructor; auto. }
  {inv H. eapply IHE in H3. Focus 2. eapply H0. simpl. unfoldTac. rewrite UnionSwap. 
   constructor; auto. }
  {inv H. eapply IHE in H3. Focus 2. eapply H0. simpl. unfoldTac. 
   rewrite (Union_commutative thread T0). rewrite <- Union_associative. constructor; 
   auto. }
  {inv H. eapply IHE in H2; eauto. simpl. constructor. auto. }
  {inv H. eapply IHE in H2; eauto. simpl. constructor. auto. }
  {inv H. eapply IHE in H3. Focus 2. eapply H0. simpl. unfoldTac.
   rewrite UnionSwap. rewrite (UnionSwap thread T0). constructor; auto. }
  {inv H. eapply IHE in H3. Focus 2. eapply H0. simpl. unfoldTac. rewrite UnionSwap. 
   rewrite Union_commutative. constructor; auto. }
  {inv H. simpl. auto. }
Qed. 

Theorem listToSingle : forall (t:thread), [t] = Single thread t. auto. Qed. 
 
Theorem specVal : forall t, pval t <-> val (specTerm t).
Proof.
  induction t; intros; split; intros; try solveByInv; inv H; try solve[ 
  repeat match goal with
      |H:pval ?t <-> val ?t', H':pval ?t |- _ => apply H in H'
  end; simpl; constructor; auto]. apply IHt1 in H2. apply IHt2 in H3.
  constructor; auto. 
Qed. 

Theorem notSpecVal : forall t, ~pval t <-> ~val (specTerm t). 
Proof.
  induction t; intros; split; intros; try solve[introsInv]; introsInv; try solve[apply H; 
  repeat match goal with
           |H:val(specTerm ?t) |- _ => apply specVal in H
         end; auto].  
  {apply H. simpl. apply specVal in H3. apply specVal in H4. auto. }
  {apply H. simpl. constructor. }
  {apply H. simpl; auto.  }
  {apply H. simpl; auto. }
Qed. 

Theorem decomposeSpec : forall t E e, 
                          pdecompose t E e ->
                          decompose (specTerm t) (specCtxt E) (specTerm e). 
Proof.
  induction t; intros; try solveByInv; try solve[inv H; constructor]. 
  {inv H. eapply IHt1 in H5; eauto. simpl. constructor. apply notSpecVal; auto. 
   eauto. simpl. constructor. apply specVal; auto. apply notSpecVal; auto. 
   eapply IHt2 in H6; eauto. }
  {inv H. eapply IHt1 in H5; eauto. simpl. constructor. apply notSpecVal; auto. 
   eauto. simpl. constructor. apply specVal; auto. apply notSpecVal; auto. 
   eapply IHt2 in H6; eauto. simpl. constructor. apply specVal; auto. apply specVal; auto. }
  {inv H. eapply IHt1 in H5; eauto. simpl. constructor. apply notSpecVal; auto. 
   eauto. simpl. constructor. apply specVal; auto. }
  {inv H. eapply IHt1 in H5; eauto. simpl. constructor. apply notSpecVal; auto. 
   eauto. simpl. constructor. apply specVal; auto. }
  {inv H. eapply IHt in H2; eauto. simpl. constructor; eauto. apply notSpecVal; eauto. 
   simpl. constructor. apply specVal ;auto. }
  {inv H. eapply IHt in H2; eauto. simpl. constructor; eauto. apply notSpecVal; eauto. 
   simpl. constructor. apply specVal ;auto. }
  {inv H. eapply IHt1 in H5; eauto. simpl. constructor. apply notSpecVal; auto. 
   eauto. simpl. constructor. apply specVal; auto. }
  {inv H. eapply IHt2 in H6; eauto. simpl. constructor. apply specVal; auto. 
   apply notSpecVal; auto. eauto. simpl; constructor. apply specVal; auto. 
   apply specVal; auto. }
Qed. 

Theorem AddUnion : forall (X:Type) T e, Add X T e = Union X T (Single X e). auto. Qed. 

Fixpoint psourceProg t :=
  match t with
      |pfvar x => True
      |pbvar x => True
      |punit => True
      |ppair e1 e2 => psourceProg e1 /\ psourceProg e2
      |plambda e => psourceProg e
      |papp e1 e2 => psourceProg e1 /\ psourceProg e2
      |pret e => psourceProg e
      |pbind e1 e2 => psourceProg e1 /\ psourceProg e2
      |pfork e => psourceProg e
      |pnew => True
      |pput e1 e2 => psourceProg e1 /\ psourceProg e2
      |pget e => psourceProg e
      |praise e => psourceProg e
      |phandle e1 e2 => psourceProg e1 /\ psourceProg e2
      |pspec e1 e2 => psourceProg e1 /\ psourceProg e2
      |pspecRun e1 e2 => False
      |pspecJoin e1 e2 => False
      |pfst e => psourceProg e
      |psnd e => psourceProg e
      |pdone e => psourceProg e
  end. 

Theorem pval_dec : forall t, (pval t) + (~pval t). 
Proof.
  induction t; intros; try solve[left; auto]; try solve[right; introsInv]. 
  {inv IHt1; inv IHt2. left; auto. right. introsInv. contradiction.
   right. introsInv. contradiction. right. introsInv. contradiction. }
Qed. 

Fixpoint ptermWF t :=
  match t with
      |pfvar x => True
      |pbvar x => True
      |punit => True
      |ppair e1 e2 => if pval_dec e1
                      then if pval_dec e2
                           then psourceProg e1 /\ psourceProg e2
                           else ptermWF e1 /\ ptermWF e2
                      else ptermWF e1 /\ ptermWF e2
      |plambda e => psourceProg e
      |papp e1 e2 => ptermWF e1 /\ ptermWF e2
      |pret e => psourceProg e
      |pbind e1 e2 => ptermWF e1 /\ psourceProg e2
      |pfork e => psourceProg e
      |pnew => True
      |pput e1 e2 => ptermWF e1 /\ psourceProg e2
      |pget e => ptermWF e
      |praise e => psourceProg e
      |phandle e1 e2 => ptermWF e1 /\ psourceProg e2
      |pspec e1 e2 => psourceProg e1 /\ psourceProg e2
      |pspecRun e1 e2 => ptermWF e1 /\ psourceProg e2
      |pspecJoin e1 e2 => ptermWF e1 /\ ptermWF e2
      |pfst e => ptermWF e
      |psnd e => ptermWF e
      |pdone e => psourceProg e
  end. 

Fixpoint PoolWF (T:pPool) :=
  match T with
      |t::ts => ptermWF t /\ PoolWF ts
      |nil => True
  end. 

Theorem poolWFComm : forall T1 T2, PoolWF (pUnion T1 T2) <-> (PoolWF T1 /\ PoolWF T2). 
Proof.
  induction T1; intros; split; intros. 
  {simpl in *. auto. }
  {simpl in *. invertHyp; auto. }
  {simpl in *. invertHyp. apply IHT1 in H1. invertHyp. auto. }
  {simpl in *. invertHyp. split; auto. apply IHT1. auto. }
Qed. 

Theorem sourceProgWF : forall t, psourceProg t -> ptermWF t. 
Proof.
  induction t; intros; auto; 
  simpl in *; try invertHyp;  auto. 
  destruct (pval_dec t1). 
  {destruct (pval_dec t2). 
   {split; auto. }
   {split; eauto. }
  }
  {split; auto. }
  {contradiction. }
  {contradiction. }
Qed.  

Theorem ptrmDecomposeWF : forall t E e, pdecompose t E e -> ptermWF t -> ptermWF e. 
Proof.
  intros. induction H; eauto; try solve[ inv H0; auto]. 
  {simpl in *. destruct (pval_dec M). contradiction. invertHyp. eauto. }
  {simpl in *. Hint Resolve sourceProgWF. destruct (pval_dec M); destruct (pval_dec N); 
   invertHyp; apply IHpdecompose; auto. }
Qed. 

Hint Constructors gather. 

Theorem gatherSourceProg : forall M T, psourceProg M -> gather M T -> T = Empty_set thread. 
Proof.
  induction M; intros; try solve[inv H0; auto].
  {inv H. inv H0. eapply IHM1 in H1;[idtac|eauto]. 
   eapply IHM2 in H2;[idtac|eauto]. subst. auto. }
  {inv H. inv H0. eapply IHM1 in H1;[idtac|eauto]. 
   eapply IHM2 in H2;[idtac|eauto]. subst. auto. }
  {inv H. inv H0. eapply IHM1 in H1;[idtac|eauto]. 
   eapply IHM2 in H2;[idtac|eauto]. subst. auto. }
  {inv H. inv H0. eapply IHM1 in H1;[idtac|eauto]. 
   eapply IHM2 in H2;[idtac|eauto]. subst. auto. }
  {inv H. inv H0. eapply IHM1 in H1;[idtac|eauto]. 
   eapply IHM2 in H2;[idtac|eauto]. subst. auto. }
  {inv H. inv H0. eapply IHM1 in H1;[idtac|eauto]. 
   eapply IHM2 in H2;[idtac|eauto]. subst. auto. }
  {inv H. }
  {inv H. }
Qed.

Fixpoint raw_heapWF (H:rawHeap pivar_state) :=
  match H with
      |(_, pempty)::H' => raw_heapWF H'
      |(_, pfull M)::H' => psourceProg M /\ raw_heapWF H'
      |[] => True
  end. 

Definition heapWF H :=
  match H with
      |heap_ h p => raw_heapWF h
  end. 

Theorem raw_lookupSourceProg : forall x H M, 
                             raw_heapWF H -> raw_heap_lookup x H = Some(pfull M) ->
                             psourceProg M. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. invertHyp. auto. }
   {destruct p. apply IHlist; auto. invertHyp. apply IHlist; auto. }
  }
Qed. 

Theorem lookupSourceProg : forall x H M, 
                             heapWF H -> heap_lookup x H = Some(pfull M) ->
                             psourceProg M. 
Proof.
  intros. destruct H. eapply raw_lookupSourceProg; eauto. 
Qed. 

Theorem raw_specHeapLookupEmpty : forall x H H',
                               raw_heap_lookup x H = Some pempty -> raw_specHeap H H' -> 
                               raw_heap_lookup x H' = Some(sempty COMMIT).
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. inv H1. simpl. rewrite eq. auto. }
   {inv H1. simpl. rewrite eq. eauto. simpl. rewrite eq. eauto. }
  }
Qed. 

Theorem specHeapLookupEmpty : forall x H H',
                               heap_lookup x H = Some pempty -> specHeap H H' ->
                               heap_lookup x H' = Some(sempty COMMIT).
Proof.
  intros. destruct H. simpl. inv H1. eapply raw_specHeapLookupEmpty in H0; eauto. 
Qed. 

Theorem specHeapExtend : forall x H H' p p',
                           heap_lookup x H = None -> specHeap H H' ->
                           specHeap(Heap.extend x pempty H p) (Heap.extend x (sempty COMMIT) H' p'). 
Proof.
  intros. destruct H. simpl in *. erewrite rawHeapsEq; eauto. destruct H'. simpl. 
  erewrite (rawHeapsEq ivar_state). constructor. auto.  
  Grab Existential Variables. unfold raw_extend. constructor. inv H1. auto. 
  apply extendPreservesUniqueness with(prf := u). simpl. assumption. assumption. 
Qed. 

Theorem raw_specHeapLookupNone : forall H H' x, 
                               raw_specHeap H H' -> raw_heap_lookup x H = None ->
                               raw_heap_lookup x H' = None. 
Proof.
  induction H; intros. 
  {inv H. auto. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {solveByInv. }
   {inv H0. simpl. rewrite eq. eauto. simpl. rewrite eq. auto. }
  }
Qed. 

Theorem specHeapLookupNone : forall H H' x, 
                               specHeap H H' -> heap_lookup x H = None ->
                               heap_lookup x H' = None. 
Proof.
  intros. destruct H. simpl in *. inv H0. simpl. eapply raw_specHeapLookupNone; eauto. 
Qed. 


Theorem simBasicStep : forall t t', 
                         pbasic_step t t' ->
                         basic_step (specTerm t) (specTerm t'). 
Proof.
  intros. inv H. 
  {rewrite specFill. rewrite specOpen. eapply basicBeta. apply decomposeSpec in H0. 
   eauto. }
  {rewrite specFill. eapply basicProjL. apply decomposeSpec in H0. simpl in *; eauto. }
  {rewrite specFill. eapply basicProjR. apply decomposeSpec in H0. simpl in *; eauto. }
  {rewrite specFill. eapply basicBind. apply decomposeSpec in H0. eauto. }
  {rewrite specFill. eapply basicBindRaise. apply decomposeSpec in H0. eauto. }
  {rewrite specFill. apply basicHandle. apply decomposeSpec in H0. eauto. }
  {rewrite specFill. eapply basicHandleRet. apply decomposeSpec in H0. eauto. }
  {rewrite specFill. eapply specJoinRaise. apply decomposeSpec in H0. simpl in *. eauto. }
  {rewrite specFill. eapply specJoinRet. apply decomposeSpec in H0. simpl in *. eauto. }
Qed. 

Theorem pvalSourceProg : forall t, ptermWF t -> pval t -> psourceProg t. 
Proof.
  induction t; intros; try solveByInv; auto.  
  {inv H0. simpl in *. destruct (pval_dec t1); try contradiction. 
   destruct (pval_dec t2); try contradiction. auto. }
Qed. 

Theorem pdecomposeApp : forall E t e N, pdecompose t E (papp (plambda e) N) -> ptermWF t ->
                                     psourceProg e /\ psourceProg N.
Proof. 
  induction E; intros; try solve[inv H; eauto]. 
  {inv H. inv H0. eapply IHE. eauto. auto. }
  {inv H. inv H0. eapply IHE. eauto. auto. }
  {inv H. inv H0. eapply IHE. eauto. auto. }
  {inv H. inv H0. eapply IHE. eauto. auto. }
  {inv H. simpl in *. destruct (pval_dec M). contradiction. invertHyp. 
   eauto. }
  {inv H. simpl in *. destruct (pval_dec p). destruct (pval_dec N0). 
   contradiction. invertHyp. eauto. contradiction. }
  {inv H. inv H0. eauto. }
  {inv H. inv H0. eauto. }
  {inv H. inv H0. simpl in *. apply pvalSourceProg in H1; auto. }
Qed. 
Hint Resolve sourceProgWF.

Theorem UnionEqEmpty : forall A T1 T2, Union A T1 T2 = Empty_set A -> T1 = Empty_set A /\
                                                                      T2 = Empty_set A. 
Proof.
  intros. destruct T1; destruct T2; auto; simpl in *; inv H.  Qed. 


Theorem gatherOpen : forall e' n e, gather e (Empty_set thread) -> gather e' (Empty_set thread) ->
                                      gather (popen n e e') (Empty_set thread).
Proof.
  induction e'; intros; auto; try solve[simpl in *; inv H0; eauto];
  try solve[simpl; inv H0; apply UnionEqEmpty in H3; invertHyp; constructor; auto]. 
  {simpl. destruct (beq_nat n i); auto. }
  {inv H0. unfoldTac. rewrite Union_commutative in H3. inv H3. }
Qed. 

Theorem pdecomposeFST : forall E t e, pdecompose t E (pfst e) -> ptermWF t ->
                                      gather e (Empty_set thread). 
Proof.
  induction E; intros; try solve[inv H; inv H0; eauto]. 
  {inv H. simpl in *. destruct (pval_dec M); try contradiction. invertHyp. eauto. }
  {inv H. simpl in *. destruct (pval_dec p); try contradiction. 
   destruct (pval_dec N); try contradiction. invertHyp. eauto. }
  {inv H. simpl in *. eauto. }
  {inv H. simpl in *. eauto. }
  {inv H. apply pvalSourceProg in H3; auto. gatherTac e. copy H1.  
   eapply gatherSourceProg in H1; eauto. subst. auto. }
Qed. 

Theorem pdecomposeSND : forall E t e, pdecompose t E (psnd e) -> ptermWF t ->
                                      gather e (Empty_set thread). 
Proof.
  induction E; intros; try solve[inv H; inv H0; eauto]. 
  {inv H. simpl in *. destruct (pval_dec M); try contradiction. invertHyp. eauto. }
  {inv H. simpl in *. destruct (pval_dec p); try contradiction. 
   destruct (pval_dec N); try contradiction. invertHyp. eauto. }
  {inv H. simpl in *. eauto. }
  {inv H. simpl in *. eauto. }
  {inv H. apply pvalSourceProg in H3; auto. gatherTac e. copy H1.  
   eapply gatherSourceProg in H1; eauto. subst. auto. }
Qed. 

Theorem gatherEmptyUnique : forall t T, gather t (Empty_set thread) -> gather t T ->
                                        T = Empty_set thread. 
Proof.
  induction t; intros; try solve[inv H0; auto]; try solve[inv H; inv H0; eauto]. 
  {inv H. inv H0. apply UnionEqEmpty in H3. invertHyp. eapply IHt1 in H2; auto. 
   eapply IHt2 in H7; auto. subst. auto. }
  {inv H. inv H0. apply UnionEqEmpty in H3. invertHyp. eapply IHt1 in H2; auto. 
   eapply IHt2 in H7; auto. subst. auto. }
  {inv H. inv H0. apply UnionEqEmpty in H3. invertHyp. eapply IHt1 in H2; auto. 
   eapply IHt2 in H7; auto. subst. auto. }
  {inv H. inv H0. apply UnionEqEmpty in H3. invertHyp. eapply IHt1 in H2; auto. 
   eapply IHt2 in H7; auto. subst. auto. }
  {inv H. inv H0. apply UnionEqEmpty in H3. invertHyp. eapply IHt1 in H2; auto. 
   eapply IHt2 in H7; auto. subst. auto. }
  {inv H. inv H0. apply UnionEqEmpty in H3. invertHyp. eapply IHt1 in H2; auto. 
   eapply IHt2 in H7; auto. subst. auto. }
  {inv H. unfoldTac. rewrite Union_commutative in H3. inv H3. }
  {inv H. inv H0. apply UnionEqEmpty in H3. invertHyp. eapply IHt1 in H2; auto. 
   eapply IHt2 in H7; auto. subst. auto. }
Qed. 


Theorem decomposeSpecJoin : forall E t N M, pdecompose t E (pspecJoin N M) -> ptermWF t ->
                                            gather N (Empty_set thread). 
Proof.
  induction E; intros; try solve[inv H; eauto]; try solve[inv H; inv H0; eauto]. 
  {inv H. simpl in *. destruct (pval_dec M0); try contradiction. invertHyp. eauto. }
  {inv H. simpl in *. destruct (pval_dec p); try contradiction. 
   destruct (pval_dec N0); try contradiction. invertHyp. eauto. }
  {inv H. simpl in H0. invertHyp. eapply pvalSourceProg in H4; auto. gatherTac N.
   copy H2. eapply gatherSourceProg in H2; eauto. subst. auto. }
Qed. 

Theorem basicStepGather : forall t t' T, 
                            pbasic_step t t' -> ptermWF t -> 
                            gather t T -> gather t' T. 
Proof.
  intros. inv H. 
  {copy H2. eapply gatherDecomp in H2; eauto. invertHyp. copy H.  
   apply pdecomposeApp in H; eauto. invertHyp. inv H2.
   eapply gatherSourceProg in H6; eauto. subst. unfoldTac. apply gatherFill. 
   auto. copy H8. apply gatherSourceProg in H8; auto. subst. simpl. apply gatherOpen; auto. 
   inv H. auto. }
  {copy H2. eapply gatherDecomp in H2; eauto. invertHyp. copy H. apply gatherFill; auto. 
   apply pdecomposeFST in H4; auto. inv H4. apply UnionEqEmpty in H7. invertHyp. 
   inv H2. inv H5. eapply gatherEmptyUnique in H6; auto. subst.
   apply gatherEmptyUnique in H10; auto. subst. simpl. auto. }
  {copy H2. eapply gatherDecomp in H2; eauto. invertHyp. copy H. apply gatherFill; auto. 
   apply pdecomposeSND in H4; auto. inv H4. apply UnionEqEmpty in H7. invertHyp. 
   inv H2. inv H5. eapply gatherEmptyUnique in H6; auto. subst.
   apply gatherEmptyUnique in H10; auto. subst. simpl. auto. }
  {copy H2. eapply gatherDecomp in H2; eauto. invertHyp. copy H. apply gatherFill; auto.
   inv H2. unfoldTac. rewrite Union_commutative. constructor; auto. inv H7. auto. }
  {copy H2. eapply gatherDecomp in H2; eauto. invertHyp. copy H. apply gatherFill; auto.
   inv H2. eapply ptrmDecomposeWF in H0; eauto. inv H0. eapply gatherSourceProg in H5; eauto. 
   subst. unfoldTac. rewrite union_empty_r. auto. }
  {copy H2. eapply gatherDecomp in H2; eauto. invertHyp. copy H. apply gatherFill; auto.
   inv H2. unfoldTac. rewrite Union_commutative. constructor; auto. inv H7; auto. }
  {copy H2. eapply gatherDecomp in H2; eauto. invertHyp. copy H. apply gatherFill; auto.
   inv H2. eapply ptrmDecomposeWF in H0; eauto. inv H0. eapply gatherSourceProg in H5; eauto. 
   subst. unfoldTac. rewrite union_empty_r. auto. }
  {copy H2. apply decomposeSpecJoin in H2; auto. inv H2. eapply gatherDecomp in H; eauto. 
   invertHyp. apply gatherFill; auto. inv H. inv H6. eapply gatherEmptyUnique in H3; eauto. 
   subst. simpl. auto. }
  {copy H2. eapply gatherDecomp in H2; eauto. invertHyp. copy H. apply gatherFill; auto.
   inv H2. unfoldTac. constructor; auto. constructor. inv H7. auto. inv H9; auto. }
Qed. 
 
Theorem fillWF : forall t E e e', pdecompose t E e -> ptermWF (pfill E e) -> ptermWF e' ->
                                  ptermWF (pfill E e'). 
Proof.
  intros. generalize dependent e'. induction H; intros; try solve[
  simpl in *; invertHyp; eauto]; try solve[simpl in *; eauto]. 
  {simpl in *. destruct (pval_dec (pfill E M')). copy H1. 
   apply pdecomposeEq in H1. subst. contradiction. invertHyp.
   destruct (pval_dec (pfill E e')). 
   {destruct (pval_dec N); eauto. apply pvalSourceProg in p0; auto. split; auto. 
    apply pvalSourceProg in p; auto. }
   {destruct (pval_dec N); eauto. }
  }
  {simpl in *. destruct (pval_dec M); try contradiction. destruct (pval_dec (pfill E N')). 
   apply pdecomposeEq in H2. subst. contradiction. invertHyp.
   destruct (pval_dec(pfill E e')); eauto. apply pvalSourceProg in p0; auto. split; auto. 
   apply pvalSourceProg in H; auto. }
Qed. 

Theorem openSourceProg : forall e' n e, psourceProg e -> psourceProg e' ->
                                        psourceProg (popen n e e'). 
Proof.
  induction e'; intros; auto; try solve[simpl in *; try invertHyp; eauto]. 
  {simpl. destruct (beq_nat n i); auto. }
Qed. 

Theorem raw_replaceSourceProg : forall x H M, 
                              raw_heapWF H -> psourceProg M -> raw_heapWF (raw_replace x (pfull M) H).
Proof.
  induction H; intros. 
  {constructor. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl. split. auto. destruct p. auto. invertHyp; auto. }
   {simpl. destruct p. eauto. invertHyp.  split; eauto. }
  }
Qed. 

Theorem replaceSourceProg : forall x H M, 
                              heapWF H -> psourceProg M -> heapWF (replace x (pfull M) H).
Proof.
  intros. destruct H. simpl. eapply raw_replaceSourceProg; eauto. 
Qed. 

Theorem pstepWF : forall H T t H' t', 
                    PoolWF (pUnion T t) -> pstep H T t (pOK H' T t') -> heapWF H ->
                    PoolWF (pUnion T t') /\ heapWF H'. 
Proof.
  intros. inv H1. 
  {rewrite poolWFComm in *. invertHyp. split; auto. inv H7. 
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply sourceProgWF.
    apply pdecomposeApp in H0; auto. invertHyp. apply openSourceProg; auto. }
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply ptrmDecomposeWF in H0; auto.
    simpl in H0. destruct (pval_dec V1); destruct (pval_dec V2); invertHyp; auto. }
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply ptrmDecomposeWF in H0; auto.
    simpl in H0. destruct (pval_dec V1); destruct (pval_dec V2); invertHyp; auto. }
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply ptrmDecomposeWF in H0; auto.
    inv H0. constructor. auto. simpl in H4. auto. }
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply ptrmDecomposeWF in H0; auto.
    inv H0. simpl in *. auto. }
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply ptrmDecomposeWF in H0; auto.
    inv H0. simpl in *. auto. }
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply ptrmDecomposeWF in H0; auto.
    inv H0. simpl in *. auto. }
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply ptrmDecomposeWF in H0; auto.
    inv H0. simpl in *. auto. }
   {simpl in *. invertHyp. repeat split; auto. copy H0. eapply fillWF; eauto. 
    apply pdecomposeEq in H1. subst. auto. apply ptrmDecomposeWF in H0; auto. }
  }
  {rewrite poolWFComm in *. simpl in *. invertHyp. repeat split; auto. 
   copy H7. apply ptrmDecomposeWF in H7; auto. inv H7. eapply fillWF; eauto.
   apply pdecomposeEq in H1. subst. auto. constructor; auto.  }
  {rewrite poolWFComm in *. simpl in *. invertHyp. repeat split; auto. 
   copy H7. apply ptrmDecomposeWF in H7; auto. inv H7. eapply fillWF; eauto.
   apply pdecomposeEq in H1. subst. auto. constructor; auto.  }
  {rewrite poolWFComm in *. simpl in *. invertHyp. repeat split; auto. 
   copy H7. apply ptrmDecomposeWF in H7; auto. inv H7. eapply fillWF; eauto.
   apply pdecomposeEq in H1. subst. auto. }
  {rewrite poolWFComm in *. simpl in *. invertHyp. repeat split; auto. 
   copy H7. apply ptrmDecomposeWF in H7; auto. simpl in *. eapply fillWF; eauto. 
   apply pdecomposeEq in H1; subst; auto. apply ptrmDecomposeWF in H7; auto. }
  {rewrite poolWFComm in *. simpl in *. invertHyp. repeat split; auto. 
   copy H9. apply ptrmDecomposeWF in H9; auto. eapply fillWF; eauto.
   apply pdecomposeEq in H1. subst. auto. simpl. eapply lookupSourceProg; eauto. }
  {rewrite poolWFComm in *. simpl in *. invertHyp. repeat split; auto. 
   copy H5. apply ptrmDecomposeWF in H5; auto. inv H5. eapply fillWF; eauto.
   apply pdecomposeEq in H3. subst. auto. apply ptrmDecomposeWF in H5; eauto. 
   simpl in *. invertHyp. apply replaceSourceProg; auto. }
  {rewrite poolWFComm in *. simpl in *. invertHyp. repeat split; auto. 
   copy H8. apply ptrmDecomposeWF in H8; auto. inv H8. eapply fillWF; eauto.
   apply pdecomposeEq in H3. subst. auto. unfold Heap.extend. unfold heapWF. 
   simpl. unfold raw_extend. destruct H. simpl. auto. }
Qed. 

Theorem pmultistepWF : forall H T H' T', 
                         PoolWF T -> heapWF H -> pmultistep H T (Some(H', T')) -> 
                         PoolWF T' /\ heapWF H'. 
Proof.
  intros. remember (Some(H',T')). induction H2. 
  {inv Heqo. auto. }
  {subst. apply pstepWF in H2; auto. invertHyp. eapply IHpmultistep; eauto. }
  {inv Heqo. }
Qed. 

Inductive stepPlus : sHeap -> pool -> option (sHeap * pool) -> Prop :=
| plus_step : forall (H H' : sHeap) c (T t t' : pool),
                 step H T t (OK H' T t') ->
                 multistep H' (tUnion T t') c -> stepPlus H (tUnion T t) c
| smulti_error : forall (H : sHeap) (T t : pool),
                   step H T t Spec.Error -> stepPlus H (tUnion T t) None.

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' T H,
        pstep PH PT pt (pOK PH' PT pt') -> 
        speculate (pUnion PT pt) T -> PoolWF (pUnion PT pt) -> heapWF PH -> specHeap PH H ->
        exists T' H', stepPlus H T (Some(H', T')) /\
                   speculate (pUnion PT pt') T' /\ specHeap PH' H'. 
Proof.
  intros. inv H0. 
  {apply specUnionComm in H1. invertHyp. inv H1. inv H7. econstructor. econstructor. 
   split. unfoldTac. rewrite Union_associative. econstructor. 
   eapply simBasicStep in H9. eapply BasicStep. eauto. constructor. split; auto. 
   apply poolWFComm in H2. simpl in H2. invertHyp. eapply basicStepGather in H9; eauto. 
   unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto. 
   constructor. constructor. auto. }
  {copy H9. apply specUnionComm in H1. invertHyp. inv H1. inv H8.
   eapply gatherDecomp in H0; eauto. invertHyp. econstructor. econstructor. split. 
   unfoldTac. rewrite Union_associative. econstructor.
   eapply Spec.Spec with(M:=specTerm M)(N:=specTerm N)(E:=specCtxt E). 
   eapply multi_step. eapply PopSpec. rewrite app_nil_l. simpl. auto. constructor. 
   split. unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto.
   rewrite couple_swap. rewrite coupleUnion. repeat rewrite Union_associative. 
   replace (specRun(specTerm M)(specTerm N)) with (specTerm(pspecRun M N)); auto.  
   rewrite <- specFill. constructor. constructor. rewrite <- Union_associative. 
   apply gatherFill; auto. inv H0. constructor; auto. auto. }
  {copy H9. apply specUnionComm in H1. invertHyp. inv H1. inv H8. 
   eapply gatherDecomp in H0; eauto. invertHyp. inv H0. unfoldTac. 
   repeat rewrite <- Union_associative. rewrite listToSingle. rewrite <- coupleUnion. 
   rewrite couple_swap. repeat rewrite Union_associative. econstructor. econstructor. split.
   econstructor. eapply SpecJoin with (N0:=specTerm M)
                          (M:=specTerm M)(N1:=specTerm N)(E:=specCtxt E); eauto. 
   simpl. constructor. split. unfoldTac. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. rewrite (Union_associative thread x0).
   rewrite (Union_associative thread (Union thread x0 T1)). 
   replace (specJoin(ret(specTerm N)) (specTerm M)) with (specTerm (pspecJoin (pret N) M)); auto. 
   rewrite <- specFill. constructor. constructor. rewrite <- Union_associative. 
   apply gatherFill. auto. constructor; auto. auto. }
  {copy H9. apply specUnionComm in H1. invertHyp. inv H1. inv H8. 
   eapply gatherDecomp in H0; eauto. invertHyp. inv H0. unfoldTac. 
   repeat rewrite <- Union_associative. rewrite listToSingle. rewrite <- coupleUnion. 
   repeat rewrite Union_associative. rewrite <- Union_associative. econstructor. econstructor. split.  
   econstructor. apply decomposeSpec in H9.
   eapply SpecRB with (E:=specTerm N)(E':=specCtxt E)(N0:=specTerm M). eassumption. 
   auto. auto. eapply RBDone. unfold tAdd. unfold Add. unfoldTac. unfold In. 
   apply in_app_iff. right. simpl. left; eauto. eauto.
   constructor. split. unfoldTac. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. replace (raise (specTerm N)) with (specTerm (praise N)); auto. rewrite <- specFill.
   apply gatherSourceProg in H12. Focus 2. apply poolWFComm in H2. simpl in H2. invertHyp.
   apply ptrmDecomposeWF in H9; auto. inv H9. auto. subst. unfold Add. simpl. 
   rewrite Union_associative. constructor. constructor. apply gatherFill; auto. auto. }
  {copy H9. apply specUnionComm in H1. invertHyp. inv H1. inv H8. 
   eapply gatherDecomp in H0; eauto. invertHyp. inv H0. copy H9. rewrite poolWFComm in H2. 
   simpl in H2. invertHyp. apply ptrmDecomposeWF in H9; auto. simpl in H9. 
   unfoldTac. rewrite Union_associative. econstructor. econstructor. split. econstructor. 
   eapply Fork with (M:=specTerm M)(E:=specCtxt E). eauto. eapply multi_step. eapply PopFork. 
   rewrite app_nil_l. simpl. auto. auto. constructor. unfoldTac. rewrite <- Union_associative. 
   split. apply specUnionComm'. auto. copy H7. apply gatherSourceProg in H7; auto. rewrite H7. 
   rewrite union_empty_r. rewrite coupleUnion. unfold pCouple. unfold Couple. simpl. 
   replace (ret unit) with (specTerm (pret punit)); auto. rewrite <- specFill. constructor. 
   rewrite <- union_empty_l. constructor. constructor. subst. eauto. 
   rewrite <- union_empty_r. apply gatherFill. auto. repeat constructor. auto. }
  {copy H11. apply specUnionComm in H1. invertHyp. inv H1. inv H8. copy H10. 
   eapply specHeapLookupFull in H10; eauto. invertHyp. 
   eapply gatherDecomp in H0; eauto. invertHyp. 
   econstructor. econstructor. split. unfoldTac. rewrite Union_associative. econstructor. 
   eapply Get with (N:=specTerm M)(E:=specCtxt E). eauto. auto. eapply multi_step. eapply PopRead. 
   rewrite app_nil_l. simpl; auto. rewrite app_nil_r. rewrite app_nil_l. auto. introsInv. 
   erewrite HeapLookupReplace; eauto. auto. rewrite replaceOverwrite. rewrite replaceSame. 
   constructor. eauto. unfoldTac. rewrite Union_associative. repeat rewrite <- Union_associative. 
   split. apply specUnionComm'. auto. inv H0. inv H9. simpl. 
   replace (ret(specTerm M)) with (specTerm(pret M)); auto. rewrite <- specFill. 
   constructor. constructor. rewrite <- union_empty_r. apply gatherFill. auto. constructor.
   gatherTac M. copy H8. apply gatherSourceProg in H8; eauto. subst. auto. Focus 2. auto.
   eapply lookupSourceProg; eauto. } 
  {apply specUnionComm in H1. invertHyp. inv H1. inv H8. copy H7. 
   eapply gatherDecomp in H7; eauto. invertHyp. rewrite poolWFComm in H2. simpl in H2. 
   invertHyp. econstructor. econstructor. split. unfoldTac. rewrite Union_associative. 
   econstructor. eapply Put with (N:=specTerm M)(E:=specCtxt E).
   eapply specHeapLookupEmpty; eauto. auto. eapply multi_step. 
   eapply PopWrite. rewrite app_nil_l. simpl; auto. erewrite HeapLookupReplace; eauto. 
   eapply specHeapLookupEmpty; eauto. auto. rewrite replaceOverwrite. constructor. 
   split. unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto. 
   inv H6. inv H13. unfoldTac. simpl in *. copy H1. apply ptrmDecomposeWF in H6; auto. inv H6. 
   eapply gatherSourceProg in H15; eauto. subst. rewrite union_empty_r in *.  
   replace (ret unit) with (specTerm (pret punit)); auto. rewrite <- specFill. constructor. 
   constructor. rewrite <- union_empty_r. apply gatherFill. auto. repeat constructor. 
   apply specHeapReplaceFull; auto. }
  {apply specUnionComm in H1. invertHyp. inv H1. inv H7. copy H10. 
   eapply gatherDecomp in H10; eauto. invertHyp. rewrite poolWFComm in H2. simpl in H2. 
   invertHyp. econstructor. econstructor. split. unfoldTac. rewrite Union_associative. 
   econstructor. copy p. eapply specHeapLookupNone in H8; eauto.
   eapply New with (E:=specCtxt E)(x:=x). auto. eapply multi_step. 
   eapply PopNewEmpty.  rewrite app_nil_l. simpl; auto. rewrite lookupExtend. auto. 
   auto. erewrite replaceExtendOverwrite; eauto. constructor. unfoldTac.
   rewrite <- Union_associative. apply specUnionComm'. auto. 
   replace (ret(fvar x)) with (specTerm(pret(pfvar x))); auto. rewrite <- specFill. 
   constructor. constructor. apply gatherFill; auto. constructor. inv H6. constructor. 
   apply specHeapExtend; auto. }
  Grab Existential Variables. 
  {eapply specHeapLookupNone; eauto. }
  {apply decomposeSpec in H1. auto. }
  {eapply specHeapLookupNone; eauto. }
  {apply decomposeSpec in H1; auto. }
  {apply decomposeSpec in H11. auto. }
  {apply decomposeSpec in H0. auto. }
  {apply decomposeSpec in H9; auto. }
  {apply decomposeSpec in H9; auto. }
Qed. 

Theorem nonspecImpliesSpecStar : forall PH PH' PT H PT' T,
        pmultistep PH PT (Some(PH', PT')) -> 
        speculate PT T -> PoolWF PT -> heapWF PH -> specHeap PH H ->
        exists T' H', multistep H T (Some(H', T')) /\
                   speculate PT' T' /\ specHeap PH' H'. 
Proof.
  intros. remember (Some(PH',PT')). genDeps{H; T}. induction H0; intros.  
  {inv Heqo. eauto. }
  {intros. subst. copy H0. eapply nonspecImpliesSpec in H0; eauto. invertHyp.
   copy H7. apply pstepWF in H7; auto. invertHyp. 
   eapply IHpmultistep in H10; eauto. invertHyp. econstructor. econstructor. split.
   inv H8. eapply multi_step. eauto. eapply multi_trans; eauto. eauto. }
  {inv Heqo. }
Qed. 









