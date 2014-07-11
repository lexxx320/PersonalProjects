Require Import SfLib.   
Require Import NonSpec.  
Require Import AST. 
Require Import Spec.  
Require Import Heap. 
Require Import Coq.Sets.Ensembles.
Require Import sets. 
Require Import Powerset_facts. 
Require Import unspec. 
Require Import erasure. 
Require Import eraseRollbackIdempotent. 


Theorem AddSingleton : forall T t, Add T (Empty_set T) t = Singleton T t. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. inv H. inv H0. auto. apply Union_intror. auto. 
Qed. 

 Ltac pZeroStep :=
   match goal with
     | |- pmultistep ?H ?T (erasePoolAux (tSingleton ?t)) (pOK ?H' ?T' (erasePoolAux(tSingleton ?t'))) =>
       assert(exists t'', eraseThread t t'') by apply eraseThreadTotal; invertHyp;
       erewrite erasePoolSingleton; eauto; erewrite erasePoolSingleton;
       [constructor|eapply eraseSpecSame; eauto]                                                                      
   end. 

Ltac pSingleStep := erewrite erasePoolSingleton; eauto; erewrite erasePoolSingleton; eauto;
                        unfold pSingleton; rewrite <- AddSingleton; econstructor; try introsInv.

 
Theorem eraseHeapDependentRead : forall H H' x sc ds s w N t,
             eraseHeap H = H' ->
             heap_lookup x H = Some(sfull sc ds s w N) ->
             eraseHeap (replace x (sfull sc (t::ds) s w N) H) = H'. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. apply beq_nat_true in eq. subst. destruct sc; auto. }
   {simpl. destruct i0. 
    {destruct a. inv H0. erewrite IHlist; eauto. erewrite IHlist; eauto. }
    {destruct a. destruct a0. erewrite IHlist; eauto. erewrite IHlist; eauto. 
     erewrite IHlist; eauto. }
   }
  }
Qed. 

Theorem eraseHeapWrite : forall x H a b tid N,
                           heap_lookup x H = Some(sempty nil) ->
                           eraseHeap (replace x (sfull nil nil (a::b) tid N) H) = (eraseHeap H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. apply beq_nat_true in eq. subst. auto. }
   {destruct i0; destruct a; simpl;  rewrite IHlist; eauto. }
  }
Qed.  


Theorem lookupEraseSpecFull : forall x H ds a b tid N, 
                                heap_lookup x H = Some(sfull nil ds (a::b) tid N) ->
                                heap_lookup x (eraseHeap H) = Some pempty. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct a. simpl; rewrite eq; eauto. eauto. 
    destruct a. destruct a1. simpl. rewrite eq. eauto. simpl. rewrite eq. 
    eauto. eauto. }
  }
Qed. 

Theorem eraseReplaceCommitFull : forall x H tid N ds S A tid' N',
                                   heap_lookup x H = Some (sfull [] ds (S :: A) tid' N') ->
                                   eraseHeap(replace x (sfull nil nil nil tid N) H) = 
                                   replace x (pfull (eraseTerm N)) (eraseHeap H). 
Proof.
  induction H; intros. 
  {auto. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct a. simpl. rewrite eq. erewrite IHlist; eauto. 
    simpl. erewrite IHlist; eauto. destruct a. destruct a0. simpl. rewrite eq. 
    erewrite IHlist; eauto. simpl. rewrite eq. erewrite IHlist; eauto. 
    simpl. erewrite IHlist; eauto. }
  }
Qed. 




Theorem specImpliesNonSpec : forall H H' T t t' PT pt, 
                               erasePool T PT -> erasePool t pt -> 
                               step H T t (OK H' T t') -> wellFormed H (tUnion T t) ->
                               exists PH' pt', pmultistep (eraseHeap H) PT pt (pOK PH' PT pt') /\
                                               eraseHeap H' = PH' /\ erasePool t' pt'. 
Proof.
  intros. inversion H2; subst. 
  {exists (eraseHeap H'). econstructor. destructLast s1. 
   {split; auto. inv H1. pSingleStep.  eapply PBetaRed. eapply decomposeErase in H8; eauto. 
    simpl; auto. unfold pUnion. rewrite union_empty_l. rewrite eraseFill.
    rewrite eraseOpenComm. constructor. }
   {invertHyp. inv H1. split. pZeroStep. auto. }
  }
  {exists (eraseHeap H'). econstructor. destructLast s1. 
   {split; auto. inv H1. pSingleStep. eapply pProjectL. eapply decomposeErase in H8; eauto. 
    simpl; auto. rewrite eraseFill. unfold pUnion. rewrite union_empty_l. constructor. }
   {invertHyp. inv H1. split. pZeroStep. auto. }
  }
  {exists (eraseHeap H'). econstructor. destructLast s1. 
   {split; auto. inv H1. pSingleStep. eapply pProjectR. eapply decomposeErase in H8; eauto. 
    simpl; auto. rewrite eraseFill. unfold pUnion. rewrite union_empty_l. constructor. }
   {invertHyp. inv H1. split. pZeroStep. auto. }
  }
  {exists (eraseHeap H'). econstructor. destructLast s1. 
   {split; auto. inv H1. pSingleStep. eapply PBind. eapply decomposeErase in H8; eauto. 
    simpl; auto. rewrite eraseFill. unfold pUnion. rewrite union_empty_l. constructor. }
   {invertHyp. inv H1. split. pZeroStep. auto. }
  }
  {exists (eraseHeap H'). econstructor. destructLast s1. 
   {split; auto. inv H1. pSingleStep. eapply PBindRaise. eapply decomposeErase in H8; eauto. 
    simpl; auto. rewrite eraseFill. unfold pUnion. rewrite union_empty_l. constructor. }
   {invertHyp. inv H1. split. pZeroStep. auto. }
  }
  {exists (eraseHeap H'). econstructor. destructLast s1. 
   {split; auto. inv H1. pSingleStep. eapply pHandle. eapply decomposeErase in H8; eauto. 
    simpl; auto. rewrite eraseFill. unfold pUnion. rewrite union_empty_l. constructor. }
   {invertHyp. inv H1. split. pZeroStep. auto. }
  }
  {exists (eraseHeap H'). econstructor. destructLast s1. 
   {split; auto. inv H1. pSingleStep. eapply pHandleRet. eapply decomposeErase in H8; eauto. 
    simpl; auto. rewrite eraseFill. unfold pUnion. rewrite union_empty_l. constructor. }
   {invertHyp. inv H1. split. pZeroStep. auto. }
  }
  {exists (eraseHeap H'). exists (Empty_set ptrm). split. inv H1. erewrite erasePoolSingleton; eauto. 
   simpl. unfold pSingleton. rewrite <- AddSingleton. econstructor. apply PTerminate. 
   unfold pUnion. rewrite union_empty_l. constructor. split; auto. 
   replace (Empty_set ptrm) with (erasePoolAux tEmptySet). constructor.
   apply Extensionality_Ensembles. constructor. intros a b. inv b. inv H. inv H6. 
   intros a b. inv b. }
  {exists (eraseHeap H'). destructLast s1.   
   {econstructor. split; auto. inv H1. unfold tCouple. rewrite coupleUnion. 
    repeat rewrite eraseUnionComm. repeat erewrite erasePoolSingleton; eauto.
    rewrite union_empty_r. constructor. }
   {econstructor. split; eauto. unfold tCouple. rewrite coupleUnion. 
    repeat rewrite eraseUnionComm. invertHyp. inv H1. 
    assert(exists t', eraseThread (tid,x0++[x],s2,t0) t'). apply eraseThreadTotal. 
    invertHyp. repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. 
    constructor. rewrite app_comm_cons. eapply eraseSpecSame; eauto. }
  }
  {exists (eraseHeap H). destructLast s1. 
   {econstructor. split. inv H1. erewrite erasePoolSingleton; eauto. constructor. split. 
    eapply eraseHeapDependentRead; eauto. erewrite <- erasePoolSingleton; eauto. }
   {invertHyp. econstructor. split. constructor. split. eapply eraseHeapDependentRead; eauto. 
    inv H1. assert(exists t', eraseThread(tid, x1 ++ [x0], s2, t0) t'). apply eraseThreadTotal. 
    invertHyp. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
    rewrite app_comm_cons. eapply eraseSpecSame; eauto. }
  }
  {exists (eraseHeap H). destructLast s1. 
   {econstructor. split. constructor. split. eapply eraseHeapWrite; eauto. inv H1. 
    erewrite <- erasePoolSingleton. econstructor. erewrite erasePoolSingleton; eauto. }
   {invertHyp. econstructor. split. constructor. split. eapply eraseHeapWrite; eauto. 
    inv H1. assert(exists t', eraseThread(tid, x1 ++ [x0], s2, t0) t'). apply eraseThreadTotal. 
    invertHyp. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
    rewrite app_comm_cons. eapply eraseSpecSame; eauto. }
  }
  {exists (replace x (pfull (eraseTerm N)) (eraseHeap H)). eapply rollbackIdempotent in H10; eauto. 
   invertHyp. inv H1. econstructor. split. unfold tAdd. unfold Add. rewrite eraseUnionComm. 
   erewrite erasePoolSingleton; eauto. eapply pmulti_step. rewrite eraseFill. 
   simpl. eapply PPut. copy d. eapply decomposeErase in H1; eauto. apply decomposeEq in H1. 
   subst. rewrite eraseFill. auto. simpl. auto. eapply lookupEraseSpecFull; eauto. 
   auto. simpl. constructor. split; eauto. rewrite <- H4. admit. unfold tAdd. unfold Add. inv H5.
   replace (pSingleton (pfill (eraseCtxt E) (pret punit))) with
   (erasePoolAux(Singleton thread (tid, [], wAct x t0 E N d :: s2, fill E (ret unit)))). 
   rewrite <- eraseUnionComm. constructor. erewrite erasePoolSingleton; eauto. 
   replace (pret punit) with (eraseTerm (ret unit)). rewrite <- eraseFill. constructor. auto. }
  {admit. }
  {exists (eraseHeap H'). destructLast s1. 
   {econstructor. split; auto. inv H1. unfold tCouple. rewrite coupleUnion. rewrite eraseUnionComm. 
    repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. constructor. }
   {econstructor. split. constructor. split; eauto. inv H1. 
    assert(exists t', eraseThread (tid,s1,s2,t0) t'). apply eraseThreadTotal. invertHyp. 
    erewrite erasePoolSingleton; eauto. unfold tCouple. rewrite coupleUnion. 
    rewrite eraseUnionComm. repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r.
    eauto. rewrite app_comm_cons. eapply eraseSpecSame; eauto. }
  }
  {exists (eraseHeap H'). destructLast s1'. 
   {econstructor. split; eauto. simpl. inv H1. unfold tCouple. rewrite coupleUnion. 
    rewrite eraseUnionComm. repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. 
    unfold pSingleton. rewrite <- AddSingleton. econstructor. eapply pSpecRun. 
    eapply decomposeErase; eauto. simpl. auto. unfold pUnion. rewrite union_empty_l. 
    rewrite eraseFill. simpl. (*Catch up*) admit. }
   {admit. }
  }
  {exists (eraseHeap H). eapply rollbackIdempotent in H15; eauto. 
   invertHyp. inv H1. econstructor. split. unfold tAdd. unfold Add. rewrite eraseUnionComm. 
   erewrite erasePoolSingleton; eauto. eapply pmulti_step. eapply pSpecRunRaise. 
   eapply decomposeErase in H6; eauto. simpl. auto. constructor. split; auto.
   unfold tAdd in *. unfold Add in *. rewrite eraseUnionComm in H5.
   erewrite erasePoolSingleton in H5; eauto. rewrite union_empty_r in H5. inv H5. 
   replace (praise (eraseTerm E)) with (eraseTerm (raise E)); auto. rewrite <- eraseFill.
   replace (pSingleton (eraseTerm (fill E' (raise E)))) with
   (erasePoolAux(Singleton thread (tid, [], s2, fill E' (raise E)))). 
   rewrite <- eraseUnionComm. constructor. erewrite erasePoolSingleton; eauto. }
  {exists (eraseHeap H'). econstructor. split; eauto. inv H1.
   repeat erewrite erasePoolSingleton; eauto. unfold pSingleton. rewrite <- AddSingleton. 
   econstructor. eapply pSpecJoinRaise. eapply decomposeErase in H9; eauto. simpl. auto. 
   unfold pUnion. rewrite union_empty_l. rewrite eraseFill. constructor. }
  {exists (replace x (pfull (eraseTerm N)) (eraseHeap H)). destructLast s1'.  
   {inv H1.  econstructor. repeat split; eauto. erewrite erasePoolSingleton; eauto. 
    erewrite erasePoolSingleton; eauto. inv H3. inv H4. rewrite unspecUnionComm in H6. 
    erewrite unspecSingleton in H6. Focus 2. unspecThreadTac. auto. simpl in H6. 
    



Theorem

    
    











asdlkjgfhadlskf