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

Fixpoint raw_specHeap (H:rawHeap pivar_state):= 
  match H with 
      |(i, pempty)::H' => (i, sempty COMMIT)::raw_specHeap H'
      |(i, pfull M)::H' => (i, sfull COMMIT nil COMMIT nil (specTerm M))::raw_specHeap H'
      |nil => nil
  end. 

Theorem specUnique : forall H S,
                       unique pivar_state S H -> 
                       unique ivar_state S (raw_specHeap H). 
Proof.
  induction H; intros. 
  {constructor. }
  {inv H0. simpl. destruct v. constructor. auto. eauto. constructor; auto. }
Qed. 

Definition specHeap H :=
  match H with
      |heap_ h p => 
       heap_ ivar_state (raw_specHeap h) (specUnique h (Ensembles.Empty_set AST.id) p)
  end. 


Theorem specHeapReplaceFull : forall x tid M H,
                                heap_lookup x H = Some pempty ->
                                replace x (sfull COMMIT nil COMMIT tid (specTerm M)) (specHeap H) = 
                                specHeap(replace x (pfull M) H). 
Proof.
  

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

Theorem simBasicStep : forall t t', 
                         pbasic_step t t' ->
                         basic_step (specTerm t) (specTerm t'). 
Proof.
  intros. inv H. 
  {rewrite specFill. rewrite specOpen. eapply basicBeta. Admitted. 

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

Theorem raw_specHeapLookupFull : forall x H M,
                               raw_heap_lookup x H = Some(pfull M) ->
                               raw_heap_lookup x (raw_specHeap H) = 
                               Some(sfull COMMIT nil COMMIT nil (specTerm M)). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq; auto. }
   {destruct p; auto. simpl. rewrite eq; auto. simpl. rewrite eq; auto. }
  }
Qed. 

Theorem specHeapLookupFull : forall x H M,
                               heap_lookup x H = Some(pfull M) ->
                               heap_lookup x (specHeap H) = 
                               Some(sfull COMMIT nil COMMIT nil (specTerm M)). 
Proof.
  intros. destruct H. simpl. eapply raw_specHeapLookupFull; eauto. 
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

Fixpoint ptermWF t :=
  match t with
      |pfvar x => True
      |pbvar x => True
      |punit => True
      |ppair e1 e2 => ptermWF e1 /\ ptermWF e2
      |plambda e => ptermWF e
      |papp e1 e2 => ptermWF e1 /\ ptermWF e2
      |pret e => ptermWF e
      |pbind e1 e2 => ptermWF e1 /\ psourceProg e2
      |pfork e => psourceProg e
      |pnew => True
      |pput e1 e2 => ptermWF e1 /\ psourceProg e2
      |pget e => ptermWF e
      |praise e => ptermWF e
      |phandle e1 e2 => ptermWF e1 /\ psourceProg e2
      |pspec e1 e2 => psourceProg e1 /\ psourceProg e2
      |pspecRun e1 e2 => ptermWF e1 /\ psourceProg e2
      |pspecJoin e1 e2 => ptermWF e1 /\ ptermWF e2
      |pfst e => ptermWF e
      |psnd e => ptermWF e
      |pdone e => ptermWF e
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

Theorem ptrmDecomposeWF : forall t E e, pdecompose t E e -> ptermWF t -> ptermWF e. 
Proof.
  intros. induction H; eauto; inv H0; auto. 
Qed. 

Theorem sourceProgWF : forall t, psourceProg t -> ptermWF t. 
Proof.
  induction t; intros; auto; 
  simpl in *; try invertHyp;  auto. 
  contradiction. contradiction. 
Qed.  

Theorem pstepWF : forall H T t H' t', 
                    PoolWF (pUnion T t) -> pstep H T t (pOK H' T t') ->
                    PoolWF (pUnion T t'). 
Proof.
  intros. inv H1. 
  {rewrite poolWFComm in *. invertHyp. split; auto. inv H6. 
   {Admitted. 

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

Theorem raw_specHeapLookupEmpty : forall x H,
                               raw_heap_lookup x H = Some pempty ->
                               raw_heap_lookup x (raw_specHeap H) = Some(sempty COMMIT).
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq; auto. }
   {destruct p; auto. simpl. rewrite eq; auto. simpl. rewrite eq; auto. }
  }
Qed. 

Theorem specHeapLookupEmpty : forall x H,
                               heap_lookup x H = Some pempty ->
                               heap_lookup x (specHeap H) = Some(sempty COMMIT).
Proof.
  intros. destruct H. simpl. eapply raw_specHeapLookupEmpty; eauto. 
Qed. 

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' T,
        pstep PH PT pt (pOK PH' PT pt') -> 
        speculate (pUnion PT pt) T -> PoolWF (pUnion PT pt) -> heapWF PH -> 
        exists T', multistep (specHeap PH) T (Some(specHeap PH', T')) /\
                   speculate (pUnion PT pt') T'. 
Proof.
  intros. inv H. 
  {apply specUnionComm in H0. invertHyp. inv H0. inv H5. admit. }
  {copy H7. apply specUnionComm in H0. invertHyp. inv H0. inv H6.
   eapply gatherDecomp in H; eauto. invertHyp. econstructor. split. 
   unfoldTac. rewrite Union_associative. eapply multi_step. 
   eapply Spec.Spec with(M:=specTerm M)(N:=specTerm N)(E:=specCtxt E). 
   eapply multi_step. eapply PopSpec. rewrite app_nil_l. simpl. auto. constructor. 
   unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto.
   rewrite couple_swap. rewrite coupleUnion. repeat rewrite Union_associative. 
   replace (specRun(specTerm M)(specTerm N)) with (specTerm(pspecRun M N)); auto.  
   rewrite <- specFill. constructor. constructor. rewrite <- Union_associative. 
   apply gatherFill; auto. inv H. constructor; auto. }
  {copy H7. apply specUnionComm in H0. invertHyp. inv H0. inv H6. 
   eapply gatherDecomp in H; eauto. invertHyp. inv H. unfoldTac. 
   repeat rewrite <- Union_associative. rewrite listToSingle. rewrite <- coupleUnion. 
   rewrite couple_swap. repeat rewrite Union_associative. econstructor. split.
   eapply multi_step. eapply SpecJoin with (N0:=specTerm M)
                          (M:=specTerm M)(N1:=specTerm N)(E:=specCtxt E); eauto. 
   simpl. constructor. unfoldTac. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. rewrite (Union_associative thread x0).
   rewrite (Union_associative thread (Union thread x0 T1)). 
   replace (specJoin(ret(specTerm N)) (specTerm M)) with (specTerm (pspecJoin (pret N) M)); auto. 
   rewrite <- specFill. constructor. constructor. rewrite <- Union_associative. 
   apply gatherFill. auto. constructor; auto. }
  {copy H7. apply specUnionComm in H0. invertHyp. inv H0. inv H6. 
   eapply gatherDecomp in H; eauto. invertHyp. inv H. unfoldTac. 
   repeat rewrite <- Union_associative. rewrite listToSingle. rewrite <- coupleUnion. 
   repeat rewrite Union_associative. rewrite <- Union_associative. econstructor. split.  
   eapply multi_step. apply decomposeSpec in H7.
   eapply SpecRB with (E:=specTerm N)(E':=specCtxt E)(N0:=specTerm M). eassumption. 
   auto. auto. eapply RBDone. unfold tAdd. unfold Add. unfoldTac. unfold In. 
   apply in_app_iff. right. simpl. left; eauto. eauto. rewrite poolWFComm in H1. 
   invertHyp. copy H6. simpl in H4. invertHyp. apply ptrmDecomposeWF in H7;[idtac|auto]. 
   inv H7. apply gatherSourceProg in H10. Focus 2. auto. subst. unfold tAdd. unfold Add. 
   simpl. constructor. unfoldTac. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. replace (raise (specTerm N)) with (specTerm (praise N)); auto. rewrite <- specFill. 
   rewrite listToSingle. rewrite Union_associative. constructor. constructor. 
   apply gatherFill; auto. }
  {copy H7. apply specUnionComm in H0. invertHyp. inv H0. inv H6. 
   eapply gatherDecomp in H; eauto. invertHyp. inv H. copy H7. rewrite poolWFComm in H1. 
   simpl in H1. invertHyp. apply ptrmDecomposeWF in H7; auto. simpl in H7. 
   unfoldTac. rewrite Union_associative. econstructor. split. eapply multi_step. 
   eapply Fork with (M:=specTerm M)(E:=specCtxt E). eauto. eapply multi_step. eapply PopFork. 
   rewrite app_nil_l. simpl. auto. auto. constructor. unfoldTac. rewrite <- Union_associative. 
   apply specUnionComm'. auto. copy H5. apply gatherSourceProg in H5; auto. rewrite H5. 
   rewrite union_empty_r. rewrite coupleUnion. unfold pCouple. unfold Couple. simpl. 
   replace (ret unit) with (specTerm (pret punit)); auto. rewrite <- specFill. constructor. 
   rewrite <- union_empty_l. constructor. constructor. subst. eauto. 
   rewrite <- union_empty_r. apply gatherFill. auto. repeat constructor. }
  {copy H9. apply specUnionComm in H0. invertHyp. inv H0. inv H6. 
   eapply gatherDecomp in H; eauto. invertHyp. copy H8. apply lookupSourceProg in H8; auto. 
   econstructor. split. unfoldTac. rewrite Union_associative. eapply multi_step. 
   eapply Get with (N:=specTerm M)(E:=specCtxt E). 
   apply specHeapLookupFull; eauto. auto. eapply multi_step. eapply PopRead. 
   rewrite app_nil_l. simpl; auto. rewrite app_nil_r. rewrite app_nil_l. auto. introsInv. 
   erewrite HeapLookupReplace; eauto. eapply specHeapLookupFull; eauto. auto.
   rewrite replaceOverwrite. rewrite replaceSame. constructor. eapply specHeapLookupFull; eauto. 
   unfoldTac. rewrite Union_associative. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. inv H. inv H6. simpl. 
   replace (ret(specTerm M)) with (specTerm(pret M)); auto. rewrite <- specFill. 
   constructor. constructor. rewrite <- union_empty_r. apply gatherFill. auto. constructor.
   gatherTac M. copy H5. apply gatherSourceProg in H5; eauto. subst. eauto. }
  {apply specUnionComm in H0. invertHyp. inv H0. inv H6. copy H5. 
   eapply gatherDecomp in H5; eauto. invertHyp. rewrite poolWFComm in H1. simpl in H1. 
   invertHyp. econstructor. split. unfoldTac. rewrite Union_associative. eapply multi_step. 
   copy H0. apply decomposeSpec in H0. eapply Put with (N:=specTerm M)(E:=specCtxt E).
   simpl in *. eauto. apply specHeapLookupEmpty; eauto. auto. eapply multi_step. 
   eapply PopWrite. rewrite app_nil_l. simpl; auto. erewrite HeapLookupReplace; eauto. 
   eapply specHeapLookupEmpty; eauto. auto. rewrite replaceOverwrite. 







Theorem nonspecImpliesSpecStar : forall PH PH' PT PT' T,
        pmultistep PH PT (Some(PH', PT')) -> 
        speculate PT T -> PoolWF PT ->
        exists T', multistep (specHeap PH) T (Some(specHeap PH', T')) /\
                   speculate PT' T'. 
Proof.
  intros. remember (Some(PH',PT')). generalize dependent T. induction H. 
  {inv Heqo. eauto. }
  {intros. subst. copy H0. eapply nonspecImpliesSpec in H0; eauto. invertHyp. 
   eapply IHpmultistep in H6; eauto. invertHyp. econstructor. split. 
   eapply multi_trans. eassumption. eassumption. auto. eapply pstepWF; eauto. }
  {inv Heqo. }
Qed. 









