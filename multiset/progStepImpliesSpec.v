Require Import erasure.  
Require Import NonSpecPureStep. 
Require Import eraseRollbackIdempotent. 

(*H; T ->+ H'; T'*)
Inductive pstepPlus : pHeap -> pPool -> pHeap -> pPool -> Prop :=
|stepPlus' : forall H H' H'' T T'' t t',
              pstep H T t (pOK H' T t') ->
              pmultistep H' (pUnion T t') (Some(H'', T'')) ->
              pstepPlus H (pUnion T t) H'' T''. 

Theorem AddUnion : forall A T t, Add A T t = Union A T (Single A t). 
reflexivity. 
Qed. 

Theorem raw_lookupEraseCommitEmpty : forall x H,
                                   raw_heap_lookup x H = Some(sempty COMMIT) ->
                                   raw_heap_lookup x (raw_eraseHeap H) = Some pempty. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct s; eauto. simpl. rewrite eq. auto. 
    destruct s; auto. destruct s0; simpl; rewrite eq; auto. }
  }
Qed. 

Theorem lookupEraseCommitEmpty : forall x H,
                                   heap_lookup x H = Some(sempty COMMIT) ->
                                   heap_lookup x (eraseHeap H) = Some pempty. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseCommitEmpty; eauto. 
Qed. 

Theorem raw_eraseCommitWrite : forall x H ds TID N, 
                             raw_heap_lookup x H = Some (sempty COMMIT) ->
                             raw_eraseHeap (raw_replace x (sfull COMMIT ds COMMIT TID N) H) = 
                             raw_replace x (pfull (eraseTerm N)) (raw_eraseHeap H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {simpl. erewrite IHlist; eauto. destruct i0. destruct s; auto. 
    simpl. rewrite eq. auto. destruct s; auto. destruct s0; simpl; rewrite eq. 
    auto. auto. }
  }
Qed.

Theorem eraseCommitWrite : forall x H ds TID N, 
                             heap_lookup x H = Some (sempty COMMIT) ->
                             eraseHeap (replace x (sfull COMMIT ds COMMIT TID N) H) = 
                             replace x (pfull (eraseTerm N)) (eraseHeap H). 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. eapply raw_eraseCommitWrite; eauto.
Qed. 

Theorem specImpliesNonSpec : forall H H' T t t', 
                               prog_step H T t (OK H' T t') -> wellFormed H (tUnion T t) ->
                               exists PH' T', pstepPlus (eraseHeap H) (erasePool (tUnion T t)) PH' T' /\
                                               eraseHeap H' = PH' /\ erasePool (tUnion T t') = T'. 
Proof.
  intros. inv H0. 
  {exists (eraseHeap H'). econstructor. split; auto. repeat rewrite eraseUnionComm. 
   simpl. apply simBasicStep in H6. econstructor. eapply PBasicStep. eauto. constructor. }
  {exists (eraseHeap H'). econstructor. split; auto. unfoldTac. rewrite coupleUnion. 
   repeat rewrite eraseUnionComm. simpl. copy d. erewrite <- decomposeErase in H; eauto.
   econstructor. eapply pFork. eauto. rewrite eraseFill. constructor. }
  {copy d. erewrite <- decomposeErase in H0; eauto. econstructor. econstructor. 
   split. rewrite eraseUnionComm. simpl. econstructor. eapply PGet; eauto.
   eapply lookupEraseCommitFull; eauto. eassumption. constructor. split.
   erewrite eraseHeapDependentRead; eauto. rewrite eraseUnionComm. simpl. 
   rewrite eraseFill. auto. }
  {erewrite <- decomposeErase in H4; eauto. econstructor. econstructor. split. 
   rewrite eraseUnionComm. simpl. econstructor. eapply PPut. simpl in *. eauto.
   eapply lookupEraseCommitEmpty; eauto. auto. constructor. split. 
   apply eraseCommitWrite; eauto. rewrite eraseUnionComm. simpl. rewrite eraseFill; auto. }
  {apply rollbackIdempotent in H7. invertHyp. copy d.
   erewrite <- decomposeErase in H3; eauto. econstructor. econstructor. split. 
   unfoldTac. rewrite AddUnion. rewrite Union_associative. rewrite eraseUnionComm.
   econstructor. eapply PPut. simpl in *. copy H3. apply pdecomposeEq in H3. 
   rewrite H3 in H7. rewrite eraseFill; eauto. eapply lookupEraseSpecFull; eauto. 
   auto. constructor. split. apply eraseHeapCommitWrite. 



inv H1. destruct s1. 
   {simpl. constructor. }
   {destructLast l. 
    {simpl. constructor. }
    {invertHyp. unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. actTermTac x. 
     erewrite eraseLastAct; eauto. rewrite eraseEmpty. unfold pUnion.
     rewrite union_empty_r. erewrite eraseTwoActs'; eauto. constructor. }
   }
   {simpl. constructor. }
  }
  {exists (eraseHeap H). destruct s1. 
   {econstructor. split. simpl. constructor. erewrite eraseHeapDependentRead; eauto. }
   {destructLast l. 
    {econstructor. split. simpl. constructor. erewrite eraseHeapDependentRead; eauto. }
    {invertHyp. econstructor. split. constructor. split. erewrite eraseHeapDependentRead; eauto. 
     inv H1. actTermTac x0. erewrite eraseTwoActs'; eauto. erewrite eraseLastAct; eauto. }
   }
   {econstructor. split. simpl. constructor. erewrite eraseHeapDependentRead; eauto. }
  }
  {exists (eraseHeap H). econstructor. split. constructor. split. erewrite eraseHeapWrite; auto.
   inv H1. destruct s1; auto. 
   {destructLast l; auto. invertHyp. actTermTac x0. erewrite eraseTwoActs'; eauto. 
    erewrite eraseLastAct; eauto. }
  }  
  {exists (eraseHeap H). eapply rollbackIdempotent in H7; eauto. 
   invertHyp. inv H1. econstructor. split. constructor. split. 
   erewrite eraseHeapWrite; auto. unfoldTac. repeat rewrite AddUnion. 
   repeat rewrite eraseUnionComm. rewrite <- H0. simpl. apply decomposeEq in d. 
   subst. auto. }
  {exists (eraseHeap H). econstructor. split. constructor. split. 
   rewrite eraseHeapNew. auto. inv H1. destruct s1; auto. 
   {destructLast l. 
    {copy d. apply decomposeEq in H0. subst. simpl. auto. }
    {invertHyp. actTermTac x0. erewrite eraseTwoActs'; eauto. erewrite eraseLastAct; eauto. }
   }
  }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1. unfoldTac. rewrite coupleUnion. 
   rewrite eraseUnionComm. destruct s1.
   {simpl. constructor. }
   {destructLast l. 
    {simpl. constructor. }
    {invertHyp. actTermTac x. erewrite eraseLastAct; eauto.
     erewrite eraseTwoActs'; eauto. simpl. constructor. }
   }
   {simpl. constructor. }
  }
  {inv H1. unfoldTac. rewrite coupleUnion in H0. 
   repeat rewrite unspecUnionComm in H0. econstructor. econstructor. split; auto. 
   rewrite coupleUnion. rewrite eraseUnionComm. rewrite eraseEmptySpec. unfold pUnion. 
   rewrite union_empty_r. repeat rewrite Union_associative in H0. econstructor. 
   eapply pSpecRun. copy p. erewrite <- decomposeErase in H; eauto. simpl. auto. 
   copy p. apply decomposeWF in H. rewrite eraseCtxtWF in H. simpl in H. copy p. 
   rewrite <- decomposeErase in H1; eauto. simpl in H1. destructLast s1. 
   {simpl. rewrite eraseFill. unfoldTac. rewrite UnionSwap in H0.
    rewrite Union_associative in H0. rewrite UnionSwap in H0.
    rewrite spec_multi_unused in H0. eapply simSpecJoinSteps; eauto. simpl in *.
    eassumption. }
   {unfoldTac. rewrite UnionSwap in H0. rewrite Union_associative in H0. rewrite UnionSwap in H0. 
    rewrite spec_multi_unused in H0. invertHyp. rewrite wrapDistributeApp. destruct x.
    {simpl (wrapActs [rAct x t E0 d] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps';[idtac|eauto|simpl in *; eauto]. constructor. }
    {simpl (wrapActs [wAct x t E0 M0 d] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps';[idtac|eauto|simpl in *; eauto]. constructor. }
    {simpl (wrapActs [nAct t E0 d i] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps'; [idtac|eauto|simpl in *; eauto]. constructor. }
    {simpl (wrapActs [fAct t E0 M0 d n] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps';[idtac|eauto|simpl in *; eauto]. constructor. }
    {simpl (wrapActs [srAct t E0 M0 N d] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps'; [idtac|eauto|simpl in *; eauto]. constructor. }
   }
  }
  {exists (eraseHeap H). eapply rollbackIdempotent in H10; eauto. 
   invertHyp. inv H1. econstructor. split. unfoldTac. rewrite coupleUnion. 
   repeat rewrite eraseUnionComm. unfold pUnion. rewrite Union_associative. eapply pmulti_step. 
   simpl. eapply pSpecRunRaise. eapply decomposeErase in H4; eauto. simpl. auto. 
   unfold pUnion.  rewrite <- Union_associative. 
   constructor. split; auto. unfoldTac. rewrite AddUnion. rewrite eraseUnionComm. 
   repeat rewrite AddUnion in H0. repeat rewrite eraseUnionComm in H0. simpl in H0. 
   unfold pUnion in H0. repeat rewrite union_empty_r in H0. rewrite <- H0.
   simpl. rewrite eraseFill; eauto. }
  {exists (eraseHeap H). econstructor. split. Focus 2. split; auto. 
   erewrite eraseHeapDependentRead. auto. eauto. inv H1. eraseTrmTac s1' M. 
   erewrite eraseLastAct; eauto. econstructor. eapply PGet; eauto. 
   eapply lookupEraseCommitFull; eauto. copy d. erewrite <- decomposeErase in H0; eauto. 
   rewrite unspecUnionComm in H2. erewrite unspecLastActPool in H2. Focus 2. constructor. 
   eapply specStepRead in H2; eauto. invertHyp. eapply simPureSteps in H0; eauto.
   rewrite eraseFill in H0. simpl in H0. erewrite eraseEraseTrm; eauto. 
   eapply unspecHeapLookupFull; eauto. }
  {exists (replace x (pfull (eraseTerm M'')) (eraseHeap H)). econstructor. split. 
   Focus 2. split; eauto. erewrite eraseHeapCommitWrite; eauto. inv H1. 
   erewrite eraseLastAct. Focus 2. constructor. rewrite unspecUnionComm in H2. 
   erewrite unspecLastActPool in H2. Focus 2. constructor. eraseTrmTac s1' M. 
   erewrite eraseEraseTrm; eauto. eapply specStepWrite in H2; eauto. invertHyp. 
   eapply simPureSteps in H0; eauto. rewrite eraseFill in H0. simpl in H0. 
   econstructor. eapply PPut; eauto. copy d. erewrite <- decomposeErase in H2; eauto.
   simpl. auto. eapply lookupEraseSpecFull; eauto. eassumption. 
   eapply lookupUnspecSpecFullEmpty; eauto. }
  {inv H1. assert(heap_lookup i (eraseHeap H) = None). 
   eapply lookupEraseSpecNone; eauto. exists (Heap.extend i pempty (eraseHeap H) H0). 
   econstructor. split. Focus 2. split; eauto. eapply eraseHeapCommitNewFull; eauto. 
   erewrite eraseLastAct. Focus 2. constructor. econstructor.
   eapply PNew with(x:=i)(p:=H0); eauto. copy d. erewrite <- decomposeErase in H1; eauto. 
   rewrite unspecUnionComm in H2. erewrite unspecLastActPool in H2. Focus 2. constructor. 
   eraseTrmTac s1' M. eapply specStepNewFull in H2; eauto. invertHyp. 
   eapply simPureSteps in H1; eauto. rewrite eraseFill in H1.
   erewrite eraseEraseTrm; eauto. eapply lookupUnspecSpecNone; eauto. }
  {inv H1. assert(heap_lookup i (eraseHeap H) = None). eapply lookupEraseSpecNoneEmpty; eauto. 
   exists (Heap.extend i pempty (eraseHeap H) H0). econstructor. split. Focus 2. split; eauto. 
   eapply eraseHeapCommitNewEmpty; eauto. erewrite eraseLastAct. Focus 2. constructor. 
   econstructor. eapply PNew with (x:=i)(p:=H0); eauto. copy d.
   erewrite <- decomposeErase in H1; eauto. eraseTrmTac s1' M. erewrite eraseEraseTrm; eauto. 
   rewrite unspecUnionComm in H2. erewrite unspecLastActPool in H2. Focus 2. constructor. 
   eapply specStepNewEmpty in H2; eauto. invertHyp. eapply simPureSteps in H1; eauto. 
   rewrite eraseFill in H1. eassumption. eapply lookupUnspecSpecEmptyNone; eauto. }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1.
   unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. rewrite eraseEmpty. 
   unfold pUnion. rewrite union_empty_r. erewrite eraseLastAct. Focus 2. constructor. 
   econstructor. eapply pFork. copy d. erewrite <- decomposeErase in H; eauto. 
   simpl. auto. rewrite coupleUnion in H0. repeat rewrite unspecUnionComm in H0. 
   rewrite unspecEmpty in H0. erewrite unspecLastActPool in H0. Focus 2. constructor. 
   unfoldTac. rewrite union_empty_r in H0. rewrite <- coupleUnion in H0. 
   eapply specStepFork in H0; eauto. invertHyp. rewrite eraseUnspecHeapIdem in H1. 
   rewrite <- H1. eraseTrmTac s1' M. eraseTrmTac s1'' N. unfoldTac.
   repeat rewrite coupleUnion in H. repeat rewrite Union_associative in H. 
   repeat rewrite coupleUnion. rewrite eraseUnionComm.
   repeat erewrite eraseEraseTrm; eauto. unfold pUnion. repeat rewrite <- coupleUnion. 
   copy H. eapply simPureStepsCouple' with(H'':=eraseHeap x)(PT:=erasePool T)
    (N:=pfill (eraseCtxt E)(pret punit)) in H; eauto. unfold pCouple. rewrite couple_swap. 
   eapply pmulti_trans. eassumption. rewrite UnionSwap in H0. rewrite <- Union_associative in H0. 
   rewrite UnionSwap in H0. rewrite Union_associative in H0.
   eapply simPureStepsCouple in H0; eauto. rewrite eraseFill in H0; eauto.
   unfold pCouple in *. rewrite couple_swap in H0. eauto. }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1. unfoldTac. 
   rewrite coupleUnion in *. repeat rewrite unspecUnionComm in H0.
   rewrite unspecEmpty in H0. unfoldTac. rewrite union_empty_r in H0. 
   repeat rewrite eraseUnionComm. rewrite eraseEmpty. erewrite eraseLastAct. Focus 2. 
   constructor. unfold pUnion. rewrite union_empty_r. econstructor. 
   eapply pSpec. copy d. rewrite <- decomposeErase in H; eauto. simpl. auto. 
   rewrite <- coupleUnion in H0. erewrite unspecLastActPool in H0. Focus 2. constructor. 
   eapply specStepSpec in H0; eauto. invertHyp. eraseTrmTac s1' M'. rewrite coupleUnion. 
   rewrite eraseUnionComm. erewrite eraseEraseTrm; eauto. simpl. unfoldTac.
   flipCouplesIn H.  repeat rewrite coupleUnion in H. repeat rewrite Union_associative in H. 
   eapply simPureSteps in H; eauto. rewrite eraseFill in H. eassumption. }
Qed. 

Theorem specImpliesNonSpecMulti : forall H H' T T', 
                multistep H T (Some(H', T')) -> wellFormed H T -> 
                exists PH' PT', pmultistep (eraseHeap H) (erasePool T) (Some(PH',PT')) /\
                                eraseHeap H' = PH' /\ erasePool T' = PT'. 
Proof.  
  intros. depInd H0; intros.  
  {econstructor. econstructor. split. constructor. auto. }
  {copy H0. eapply specImpliesNonSpec in H0; eauto. invertHyp.
   copy H3. eapply stepWF in H3; auto. eapply IHmultistep in H3; eauto. 
   invertHyp. econstructor. econstructor. split; eauto. eapply pmulti_trans.
   rewrite eraseUnionComm. eassumption. rewrite <- eraseUnionComm. auto. }
Qed. 









asdlkfjhalsdkjfh