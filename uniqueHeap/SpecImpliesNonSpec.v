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
Require Import classifiedStep. 
Require Import Coq.Program.Equality. 
Require Import NonSpecPureStep. 

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


Theorem raw_lookupEraseSpecFull : forall x H ds a b tid N, 
                                raw_heap_lookup x H = Some(sfull (unlocked nil) ds (aCons a b) tid N) ->
                                raw_heap_lookup x (raw_eraseHeap H) = Some pempty. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. unfold commit. destruct b; simpl; rewrite eq; auto. }
   {destruct i0. destruct (commit a). simpl; rewrite eq; eauto. eauto. 
    destruct (commit a). destruct (commit a1). simpl. rewrite eq. eauto. simpl. rewrite eq. 
    eauto. eauto. }
  }
Qed. 

Theorem lookupEraseSpecFull : forall x H ds a b tid N, 
                                heap_lookup x H = Some(sfull (unlocked nil) ds (aCons a b) tid N) ->
                                heap_lookup x (eraseHeap H) = Some pempty. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseSpecFull. eauto. 
Qed.  

Theorem raw_lookupEraseCommitFull : forall x H ds tid N, 
       raw_heap_lookup x H = Some(sfull (unlocked nil) ds (unlocked nil) tid N) ->
       raw_heap_lookup x (raw_eraseHeap H) = Some (pfull (eraseTerm N)). 
Proof.
  induction H; intros.  
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct (commit a) eqn:eq2. simpl. rewrite eq. eauto. 
    eauto. destruct (commit a). destruct (commit a0). simpl. 
    rewrite eq. eauto. simpl. rewrite eq; eauto. eauto. }
  }
Qed. 

Theorem lookupEraseCommitFull : forall x H ds tid N, 
       heap_lookup x H = Some(sfull (unlocked nil) ds (unlocked nil) tid N) ->
       heap_lookup x (eraseHeap H) = Some (pfull (eraseTerm N)). 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseCommitFull; eauto. 
Qed. 

Hint Constructors pbasic_step. 

Theorem simBasicStep : forall t t',
                         basic_step t t' -> pbasic_step (eraseTerm t) (eraseTerm t'). 
Proof.
  intros. inv H; try solve[
    match goal with
       |H:decompose ?t ?E ?e |- _ => rewrite <- decomposeErase in H; eauto; 
                                     rewrite eraseFill; simpl; eauto
    end].      
  {rewrite <- decomposeErase in H0; eauto. rewrite eraseFill; simpl. rewrite eraseOpenComm. eauto. }
Qed. 

Ltac repEmpty :=
       match goal with
           | |- pmultistep ?H ?T ?t (pOK ?H' ?T' ?t')  => 
             replace t with (Union ptrm (Empty_set ptrm) t) by (rewrite union_empty_l; auto)
       end.

Axiom uniqueTP : forall T1 T2 t, tIn (tUnion T1 T2) t -> tIn T1 t -> tIn T2 t -> False. 
 
Theorem UnionEqTID : forall T T' tid s1 s2 M s1' s2' M',
                       tUnion T (tSingleton(tid,s1,s2,M)) = tUnion T' (tSingleton(tid,s1',s2',M')) ->
                       T = T' /\ s1 = s1' /\ s2 = s2' /\ M = M'. 
Proof. 
  intros. unfoldSetEq H. assert(tIn (tUnion T (tSingleton(tid,s1,s2,M)))(tid,s1,s2,M)). 
  apply Union_intror. constructor. copy H.  apply H0 in H. inversion H.  
  {assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1,s2,M)). 
   econstructor. econstructor. eauto. auto. 
   assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1',s2',M')). 
   econstructor. apply Union_intror. constructor. auto. eapply uniqueThreadPool in H5; eauto. 
   inv H5. repeat constructor; auto. eqSets. 
   {assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H5. apply H0 in H5. 
    inversion H5; subst. auto. inv H8. exfalso. eapply uniqueTP; eauto. constructor. }
   {assert(tIn (tUnion T' (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H5. 
    apply H1 in H5. inversion H5; subst. auto. inv H8. exfalso. eapply uniqueTP; eauto. 
    constructor. }
  }
  {subst. inv H3. repeat constructor; auto. eqSets. 
   {assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H4. apply H0 in H4. 
    inversion H4; subst. auto. inv H6. exfalso. eapply uniqueTP; eauto. constructor. }
   {assert(tIn (tUnion T' (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H4. 
    apply H1 in H4. inversion H4; subst. auto. inv H6. exfalso. eapply uniqueTP; eauto. 
    constructor. }
  }
Qed. 

Axiom UnionSingletonEq : forall T T' a b, 
                 tUnion T (tSingleton a) = tUnion T' (tSingleton b) -> 
                 tIn T' a -> T = tUnion (Subtract thread T' a) (tSingleton b).

Theorem EqJMeq : forall (T:Type) (x y:T), x = y -> JMeq x y.
Proof.
  intros. subst. auto. Qed. 
 
Ltac invertDecomp :=
  match goal with
    |H:(?a,?b,?c,?d)=(?e,?f,?g,?h) |- _ => inv H
    |H:?x = ?y |- _ => solve[inv H]
    |H:decompose ?M ?E ?e,H':decompose ?M' ?E' ?e' |- _=>
     eapply uniqueCtxtDecomp in H; eauto; invertHyp
  end. 


Ltac addEmpty := 
  match goal with
      | |-pmultistep ?H ?T ?t ?c => replace t with (pUnion (Empty_set ptrm) t)
  end. 

Theorem simPureSteps : forall H H' T T' PT s1 s2 tid M M',
                spec_multistep H (tUnion T (tSingleton(tid,s1,s2,M)))
                               H' (tUnion T' (tSingleton(tid,s1,s2,M'))) ->
                eraseHeap H = eraseHeap H' -> erasePool T PT ->
                pmultistep (eraseHeap H) PT (pSingleton (eraseTerm M))
                           (pOK (eraseHeap H) PT (pSingleton (eraseTerm M'))).
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
   apply H4 in H. inversion H; subst. 
   {eapply specSingleStepErase in H6; eauto. invertHyp. rewrite <- H8. 
    eapply IHspec_multistep. Focus 4.
    replace PT with (erasePoolAux(tUnion (Subtract thread T x) t')). constructor.
    rewrite eraseUnionComm. inv H9. rewrite H11. rewrite <- eraseUnionComm. 
    replace (tUnion (Subtract thread T x)(tSingleton x))
    with (tAdd (Subtract thread T x) x). unfold tAdd. rewrite <- add_subtract. 
    inv H2. auto. auto. unfoldTac. auto. apply UnionSingletonEq in H3. 
    rewrite H3. apply EqJMeq. unfoldTac. repeat rewrite Union_associative. 
    rewrite (Union_commutative thread _ t'). auto. auto. auto. rewrite <- H1. 
    auto. }
   {inv H7. addEmpty. copy H6. inv H7. 
    {unfoldTac; invertHyp. inv H8. apply simBasicStep in H9. econstructor. 
     eapply PBasicStep. eauto. unfold pUnion. rewrite union_empty_l. 
     eapply IHspec_multistep; auto. apply UnionEqTID in H3. invertHyp. auto. }
    {unfoldTac; invertHyp. inv H11. eapply monotonicActions in H0. 
     Focus 2. apply Union_intror. constructor. Focus 2. apply Union_intror. 
     constructor. destruct s1; simpl in *; omega. }
    {unfoldTac; invertHyp. inv H8. eapply monotonicActions in H0. 
     Focus 2. apply Union_intror. constructor. Focus 2. apply Union_intror. 
     constructor. destruct s1; simpl in *; omega. }
    {unfoldTac; invertHyp. inv H8. eapply monotonicActions in H0. 
     Focus 2. apply Union_intror. constructor. Focus 2. apply Union_intror. 
     constructor. destruct s1; simpl in *; omega. }
    {unfoldTac; invertHyp. inv H8. eapply monotonicActions in H0. 
     Focus 2. apply Union_intror. constructor. Focus 2. apply Union_intror. 
     constructor. destruct s1; simpl in *; omega. }
    {unfoldTac; invertHyp. inv H11. eapply monotonicActions in H0. 
     Focus 2. apply Union_intror. constructor. Focus 2. apply Union_intror. 
     constructor. destruct s1; simpl in *; omega. }
    {unfold pUnion. rewrite union_empty_l. auto. }
   }
  }
Qed.

Theorem specStepRead : forall H H' TID x M ds M' E d s1' N t0 T T' s2 PT,
   decompose M' E (get(fvar x)) -> erasePool T PT ->
   heap_lookup x H = Some(sfull(unlocked[])ds(unlocked[])t0 N) ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tSingleton(TID,unlocked(s1'++[rAct x M' E d]), s2, M))) ->
    exists H'' T'',
         spec_multistep H''
           (tUnion T''
              (tSingleton (TID, unlocked [rAct x M' E d], s2, fill E (ret N))))
           H' (tUnion T' (tSingleton (TID, unlocked (s1'++[rAct x M' E d]), s2, M))) /\
         eraseHeap H'' = eraseHeap H /\ erasePool T'' PT.
Proof.
  intros. generalize dependent ds. dependent induction H3; intros.
  {apply UnionEqTID in x. invertHyp. inv H3. invertListNeq. }
  {copy x. unfoldSetEq x. copy H2. apply specStepSingleton in H2. invertHyp. 
   assert(tIn (tUnion T0(tSingleton x)) x). apply Union_intror. constructor. 
   apply H6 in H2. inversion H2; subst. 
   {copy H8. eapply specSingleStepErase in H10; eauto. copy H8. 
    eapply specStepCommitFullIVar in H8; eauto. invertHyp. 
    eapply IHspec_multistep in H12. invertHyp. exists x2. exists x3. 
    split. eauto. split. rewrite <- H8. auto. auto. auto. inv H13. 
    replace PT with (erasePoolAux(tUnion (Subtract thread T x) t')). 
    constructor. inv H1. rewrite eraseUnionComm. rewrite H15. 
    rewrite <- eraseUnionComm. replace (tUnion (Subtract thread T x)(tSingleton x))
                                       with (tAdd (Subtract thread T x) x). 
    unfold tAdd. rewrite <- add_subtract. auto. auto. unfoldTac. auto. auto. auto.
    apply EqJMeq. apply UnionSingletonEq in H5.
    rewrite H5. unfoldTac. repeat rewrite Union_associative. 
    rewrite (Union_commutative thread _ t'). auto. auto. auto. }
   {inv H9. inv H8; unfoldTac; invertHyp; try solve[repeat invertDecomp]. 
    {invertDecomp. inv H10; repeat invertDecomp. }
    {invertDecomp. copy d; copy d0. invertDecomp. invertDecomp. inv H11. 
     exists(replace x0 (sfull sc (Union tid ds0 (Singleton tid TID)) s writer N0) H).
     exists T0. simpl in *. rewrite H10 in H4. inv H4. split. 
     auto. assert(d=d0). apply proof_irrelevance. subst. assumption. 
     erewrite eraseHeapDependentRead; eauto. split; auto. apply UnionEqTID in H5. 
     invertHyp. auto. }
   }
  }
Qed. 

Theorem specImpliesNonSpec : forall H H' T t t' PT pt, 
                erasePool T PT -> erasePool t pt -> 
                step H T t (OK H' T t') -> wellFormed H (tUnion T t) ->
                exists PH' pt', pmultistep (eraseHeap H) PT pt (pOK PH' PT pt') /\
                                eraseHeap H' = PH' /\ erasePool t' pt'. 
Proof.
  intros. inversion H2; subst. 
  {exists (eraseHeap H'). econstructor. split; auto. destruct s1. 
   {inv H1. repeat erewrite erasePoolSingleton; eauto. constructor. }
   {destructLast l. 
    {inv H1. repeat erewrite erasePoolSingleton; eauto. apply simBasicStep in H8. 
      repEmpty. econstructor. eapply PBasicStep; eauto. unfold pUnion. rewrite union_empty_l.
      constructor. }
    {invertHyp. inv H1. pZeroStep. }
   }
  }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1. destruct s1. 
   {simpl. unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. 
    repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. constructor. }
   {destructLast l. 
    {simpl. unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. 
     repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. constructor.
     eraseThreadTac. rewrite app_nil_l. auto. }
    {invertHyp. assert(exists t', eraseThread(tid,unlocked (x0++[x]),s2,t0) t'). 
     apply eraseThreadTotal. invertHyp. unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. 
     repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. constructor. 
     simpl. rewrite app_comm_cons. eapply eraseSpecSame; eauto. }
   }
  }
  {exists (eraseHeap H). destruct s1. 
   {econstructor. split. constructor. split. erewrite eraseHeapDependentRead; eauto.
    simpl. inv H1. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. }
   {destructLast l. 
    {econstructor. split. constructor. erewrite eraseHeapDependentRead; eauto. split; auto. 
     inv H1. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
     simpl. eraseThreadTac. rewrite app_nil_l. auto. }
    {invertHyp. econstructor. split. constructor. split. erewrite eraseHeapDependentRead; eauto. 
     inv H1. assert(exists t', eraseThread(TID,unlocked(x1++[x0]), s2, t0) t'). apply eraseThreadTotal. 
     invertHyp. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto.
     simpl. rewrite app_comm_cons. eapply eraseSpecSame; eauto. }         
   }
  }
  {exists (eraseHeap H). econstructor. split. constructor. split. erewrite eraseHeapWrite; auto.
   inv H1. destruct s1. 
   {simpl. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. }
   {destructLast l. 
    {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. simpl. 
     eraseThreadTac. rewrite app_nil_l. auto. }
    {simpl. invertHyp. assert(exists t', eraseThread(TID,unlocked(x1++[x0]), s2, t0) t'). 
     apply eraseThreadTotal. invertHyp. erewrite erasePoolSingleton; eauto. 
     erewrite erasePoolSingleton; eauto. rewrite app_comm_cons. eapply eraseSpecSame; eauto. }
   }
  }  
  {exists (eraseHeap H). eapply rollbackIdempotent in H7; eauto. 
   invertHyp. inv H1. econstructor. split. constructor. split. 
   replace (unlocked[wAct x t0 E N d]) with (aCons (wAct x t0 E N d) (unlocked nil)); auto.  
   erewrite eraseHeapWrite; auto. inv H5. unfoldTac. rewrite eraseUnionComm. rewrite <- H8. 
   erewrite erasePoolSingleton. rewrite <- eraseUnionComm. constructor. 
   erewrite erasePoolSingleton; eauto. copy d. apply decomposeEq in H1. subst. 
   eraseThreadTac. rewrite app_nil_l. auto. }
  {exists (eraseHeap H). econstructor. split. constructor. split. 
   rewrite eraseHeapNew. auto. inv H1. destruct s1. 
   {erewrite erasePoolSingleton; eauto. simpl. erewrite erasePoolSingleton; eauto. }
   {destruct l. 
    {copy d. apply decomposeEq in H1. subst. erewrite erasePoolSingleton; eauto. 
     simpl. erewrite erasePoolSingleton; eauto. eraseThreadTac. rewrite app_nil_l. 
     auto. }
    {assert(exists t', eraseThread (tid,unlocked(a::l),s2,t0)t').
     apply eraseThreadTotal. invertHyp. erewrite erasePoolSingleton; eauto. 
     erewrite erasePoolSingleton. copy d. apply decomposeEq in H1. subst; eauto.  
     uCons a l. rewrite eraseTwoActs. eauto. }
   }
  }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1. unfoldTac. rewrite coupleUnion. 
   rewrite eraseUnionComm. destruct s1; simpl.
   {repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. constructor. }
   {destructLast l. 
    {repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. constructor. 
     eraseThreadTac. rewrite app_nil_l. auto. } 
    {invertHyp. assert(exists t', eraseThread(tid,unlocked(x0++[x]), s2, t0) t'). 
     apply eraseThreadTotal. invertHyp. repeat erewrite erasePoolSingleton; eauto.
     rewrite union_empty_r. constructor. rewrite app_comm_cons. eapply eraseSpecSame. eauto. }
   }
  }
  {inv H3. inv H4. unfoldTac. rewrite coupleUnion in H5. 
   repeat rewrite unspecUnionComm in H5. erewrite unspecSingleton in H5; eauto. 
   erewrite unspecSingleton in H5; eauto. unfoldTac. rewrite union_empty_r in H5. 
   admit. }
  {exists (eraseHeap H). eapply rollbackIdempotent in H15; eauto. 
   invertHyp. inv H1. econstructor. split. unfold tAdd. unfold Add. rewrite eraseUnionComm. 
   erewrite erasePoolSingleton; eauto. eapply pmulti_step. eapply pSpecRunRaise. 
   eapply decomposeErase in H6; eauto. simpl. auto. constructor. split; auto. unfoldTac. 
   inv H5.  replace (praise (eraseTerm E)) with (eraseTerm (raise E)); auto. rewrite <- eraseFill.
   replace (pSingleton (eraseTerm (fill E' (raise E)))) with
   (erasePoolAux(Singleton thread (tid, unlocked [], s2, fill E' (raise E)))). 
   rewrite <- eraseUnionComm. constructor. erewrite erasePoolSingleton; eauto. }
  {exists (eraseHeap H'). econstructor. split; eauto. inv H1. 
   repeat erewrite erasePoolSingleton; eauto. unfold pSingleton. rewrite <- AddSingleton. 
   econstructor. eapply pSpecJoinRaise. eapply decomposeErase in H9; eauto. simpl. auto. 
   unfold pUnion. rewrite union_empty_l. rewrite eraseFill. constructor. }
  {exists (eraseHeap H). econstructor. split. Focus 2. split; auto. 
   erewrite eraseHeapDependentRead. auto. eauto. inv H1. inv H3. 
   inv H4. destructLast s1'.  
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
    rewrite unspecUnionComm in H5. simpl in *. erewrite unspecSingleton in H5. 
    Focus 2. unspecThreadTac. rewrite app_nil_l. auto. copy H11. 
    apply lookupEraseCommitFull in H11; auto. 
    replace (pSingleton(eraseTerm M'))with(Add ptrm(Empty_set ptrm)(eraseTerm M')). 
    econstructor. eapply PGet. eauto. copy d. rewrite <- decomposeErase in H3;eauto. 
    unfold pUnion. rewrite union_empty_l.
    replace ([rAct x M' E d]) with ([]++[rAct x M' E d]) in H5; auto.
    eapply specStepRead in H5; eauto. 
    invertHyp. rewrite eraseUnspecHeapIdem in H4. rewrite <- H4.
    eapply simPureSteps in H3. rewrite eraseFill in H3. eassumption. 
    auto. rewrite eraseUnspecPoolAuxEq in H6. inv H0. auto. 
    eapply unspecHeapLookupFull; eauto. unfoldTac. rewrite union_empty_l. auto. }
   {invertHyp. rewrite unspecUnionComm in H5. erewrite unspecSingleton in H5. 
    Focus 2. unspecThreadTac. auto. eapply specStepRead in H5; eauto. invertHyp. 
    rewrite eraseUnspecHeapIdem in H3. rewrite eraseUnspecPoolAuxEq in H5. 
    



}









asdlkjgfhadlskf