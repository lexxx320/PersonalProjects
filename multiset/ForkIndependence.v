Require Import erasure. 
Require Import IndependenceCommon. 

Theorem forkFastForward : forall H T H' T' tid s1' s1'' N M M' M'' n E s2 d,
  decompose M' E (fork M'') -> n = numForks' s2 ->   
  spec_multistep H (tUnion T (tSingleton(tid,unlocked nil, s2, M')))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,M)
                                       (n::tid,locked s1'',nil,N))) ->
  exists H'' T'',
    spec_multistep H (tUnion T (tSingleton(tid,unlocked nil,s2,M')))
                   H'' (tUnion T'' (tCouple(tid,unlocked[fAct M' E M'' d n],s2,fill E (ret unit))
                                          (n::tid,locked nil,nil,M''))) /\
    spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[fAct M' E M'' d n],s2,fill E (ret unit)) (n::tid,locked nil,nil,M'')))
                   H'(tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,M)
                                       (n::tid,locked s1'',nil,N))) /\
    spec_multistep H T H'' T''. 
Proof.
  intros. dependent induction H2. 
  {unfoldTac. rewrite coupleUnion in x. rewrite <- Union_associative in x. 
   rewrite UnionSwap in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq H1. copy H. apply specStepSingleton in H1. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x0)) x0). apply Union_intror. constructor. 
   apply H3 in H1. inv H1. 
   {eapply IHspec_multistep in H0. Focus 4. auto. Focus 2. auto. Focus 2. 
    apply UnionSingletonEq in x; auto.  
    rewrite x. unfoldTac. rewrite UnionSwap. auto. invertHyp. exists x1. exists x2.
    split; auto. apply pullOut in H5. unfoldTac. rewrite H5. rewrite UnionSwap. 
    econstructor. eapply specStepChangeUnused. eauto. unfoldTac. 
    rewrite <- UnionSwap. eauto. split. auto. copy H5. apply pullOut in H5. 
    rewrite H5. econstructor. eapply specStepChangeUnused. eauto. eauto. }
   {inv H5. apply UnionEqTID in x. invertHyp. clear H1 H5 H7. inversion H; subst. 
    {unfoldTac; invertHyp; invThreadEq.
     inv H5; eapply uniqueCtxtDecomp in H0; eauto; invertHyp; solveByInv. }
    {unfoldTac; invertHyp; invThreadEq. copy d0. eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H6. exists h'. exists T. split. econstructor. 
     eapply SFork; eauto. simpl. constructor. split. simpl in *. assert(d=d0). 
     apply proof_irrelevance. subst. assumption. constructor. }
    {unfoldTac; invertHyp; invThreadEq. copy d0; eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H7. }
    {unfoldTac; invertHyp; invThreadEq. copy d0; eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H7. }
    {unfoldTac; invertHyp; invThreadEq. copy d0; eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H6. }
    {unfoldTac; invertHyp; invThreadEq. copy d0; eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H6. }
   }
  }
Qed.


Theorem nonEmptyStack' : forall H H' tid s1 S' s1' a s2 M M' T S T',
                 spec_multistep H T H' T' -> tIn T (tid,s1,s2,M) ->  tIn T' (tid,s1',s2,M') ->
                 stackList s1 = S ++ [a] -> stackList s1' = S' -> 
                 exists s, S' = s ++ [a]. 
Proof.
  intros. genDeps{s1';s1;s2;a;M;M';tid;S';S}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,s1,s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,s1',s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. invThreadEq. destruct s1; simpl in *; subst; eauto. }
  {inv H1. 
   {eapply IHspec_multistep; eauto. constructor. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H5. inv H1. 
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep; eauto. apply Union_intror. constructor. }
    {unfoldTac; invertHyp. invThreadEq. eapply IHspec_multistep. apply Union_intror. 
     constructor. Focus 2. eauto. Focus 2. eauto. destruct s1; simpl in *; subst; simpl;
     rewrite app_comm_cons; eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. 
     constructor. Focus 2. eauto. Focus 2. eauto. destruct s1; simpl in *; subst; 
     rewrite app_comm_cons; eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. 
     constructor. Focus 2. eauto. Focus 2. eauto. destruct s1; simpl in *; subst; 
     rewrite app_comm_cons; eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. 
     constructor. Focus 2. eauto. Focus 2. eauto. destruct s1; simpl in *; subst; 
     rewrite app_comm_cons; eauto. }
    {unfoldTac; invertHyp. invThreadEq. eapply IHspec_multistep. apply Union_intror. 
     constructor. Focus 2. eauto. eauto. Focus 2. eauto. destruct s1; simpl in *; subst; 
     rewrite app_comm_cons; eauto. }
   }
  }
Qed.  


Ltac nonEmptyStack'Tac H :=
  eapply nonEmptyStack' in H;[idtac|apply InL;constructor|apply InL;apply Couple_r|
                                    rewrite app_nil_l;simpl;auto|auto]. 


Theorem forkCatchup : forall H T H' T' x tid' x0 tid s1' s1'' s2 e1 e1' e2 e2' a,
    eraseTrm s1' e1' x -> eraseTrm s1'' e2' x0 -> 
    spec_multistep H (tUnion T (tCouple(tid,unlocked[a], s2, e1)
                                       (tid',locked nil,nil,e2)))
                   H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (tid',locked s1'',nil,e2'))) -> 
    ((
    exists H'' T'' x0',
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,e1)
                                         (tid',locked nil,nil,e2)))
                     H'' (tUnion T'' (tCouple(tid,unlocked[a],s2,x)
                                             (tid',locked nil,nil,x0'))) /\
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[a],s2,x)
                                             (tid',locked nil,nil,x0')))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (tid',locked s1'',nil,e2'))) /\
      spec_multistep H T H'' T'') \/
     (
    exists H'' T'' x',
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,e1)
                                         (tid',locked nil,nil,e2)))
                     H'' (tUnion T'' (tCouple(tid,unlocked[a],s2,x')
                                             (tid',locked nil,nil,x0))) /\
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[a],s2,x')
                                             (tid',locked nil,nil,x0)))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (tid',locked s1'',nil,e2'))) /\
      spec_multistep H T H'' T'')). 
Proof.
  intros. genDeps{x;x0}. dependent induction H2; intros.
  {unfoldTac. repeat rewrite coupleUnion in x. 
   repeat rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. 
   inv H3. apply UnionEqTID in H. invertHyp. inv H. destruct s1'; inv H5; try invertListNeq. 
   inv H0; try invertListNeq. inv H1; try  invertListNeq. left. econstructor. 
   econstructor. econstructor. split. constructor. split. constructor. constructor. }
  {copy x. copy H. apply specStepSingleton in H4. invertHyp. copy x. unfoldSetEq x.
   assert(tIn (tUnion T0 (tSingleton x2)) x2). apply Union_intror. constructor.
   apply H5 in H7. inv H7. 
   {eapply IHspec_multistep in H0; eauto. Focus 2. apply UnionSingletonCoupleEq in H3. 
    rewrite H3. unfoldTac. rewrite UnionSwap. auto. auto. inv H0.  
    {invertHyp. left. econstructor. econstructor. econstructor. split. takeTStep. 
     eassumption. split; auto. takeTStep. eassumption. }
    {invertHyp. right. econstructor. econstructor. econstructor. split. 
     takeTStep; eauto. split; auto. takeTStep. eauto. }
   }
   {inv H8. 
    {unfoldTac. rewrite coupleUnion in H3. rewrite <- Union_associative in H3.
     rewrite UnionSwap in H3. apply UnionEqTID in H3. invertHyp. 
     inv H; unfoldTac; invertHyp; invThreadEq. 
     {eapply IHspec_multistep in H0. Focus 2. rewrite Union_associative. 
      rewrite <- coupleUnion. rewrite couple_swap. auto. Focus 2. auto. 
      Focus 2. eauto. inv H0. 
      {invertHyp. left. econstructor. econstructor. econstructor. split. 
       rewrite pullOutL. econstructor. eapply SBasicStep; eauto. unfoldTac. 
       rewrite <- pullOutL. eassumption. split; auto. }
      {invertHyp. right. econstructor. econstructor. econstructor. split. 
       rewrite pullOutL. econstructor. eapply SBasicStep; eauto. unfoldTac. 
       rewrite <- pullOutL. eassumption. split; auto. }
     }
     {copy H2. nonEmptyStackTac H2. invertHyp. apply eraseTrmApp in H0. inv H0. 
      left. econstructor. econstructor. econstructor. split. constructor. split. 
      rewrite pullOutL. econstructor. eapply SFork; eauto. eassumption. constructor. }
     {copy H2. nonEmptyStackTac H2. invertHyp. apply eraseTrmApp in H0. inv H0. 
      left. econstructor. econstructor. econstructor. split. constructor. split. 
      rewrite pullOutL. econstructor. eapply SGet; eauto. eassumption. constructor. }
     {copy H2. nonEmptyStackTac H2. invertHyp. apply eraseTrmApp in H0. inv H0. 
      left. econstructor. econstructor. econstructor. split. constructor. split. 
      rewrite pullOutL. econstructor. eapply SPut; eauto. eassumption. constructor. }
     {copy H2. nonEmptyStackTac H2. invertHyp. apply eraseTrmApp in H0. inv H0. 
      left. econstructor. econstructor. econstructor. split. constructor. split. 
      rewrite pullOutL. econstructor. eapply SNew; eauto. eassumption. constructor. }
     {copy H2. nonEmptyStackTac H2. invertHyp. apply eraseTrmApp in H0. inv H0. 
      left. econstructor. econstructor. econstructor. split. constructor. split. 
      rewrite pullOutL. econstructor. eapply SSpec; eauto. eassumption. constructor. }
    }
    {unfoldTac. rewrite coupleUnion in H3. rewrite <- Union_associative in H3.
     apply UnionEqTID in H3. invertHyp. inv H; unfoldTac; invertHyp; invThreadEq. 
     {eapply IHspec_multistep in H0. Focus 2. rewrite Union_associative. 
      rewrite <- coupleUnion. auto.  Focus 2. auto. Focus 2. eauto. inv H0. 
      {invertHyp. left. econstructor. econstructor. econstructor. split. 
       rewrite pullOutR. econstructor. eapply SBasicStep; eauto. unfoldTac. 
       rewrite <- pullOutR. eassumption. split; auto. }
      {invertHyp. right. econstructor. econstructor. econstructor. split. 
       rewrite pullOutR. econstructor. eapply SBasicStep; eauto. unfoldTac. 
       rewrite <- pullOutR. eassumption. split; auto. }
     }
     {copy H2. simpl in *. nonEmptyStack'Tac H2. invertHyp. simpl in *. subst. 
      apply eraseTrmApp in H1. inv H1. right. econstructor. econstructor. 
      econstructor. split. constructor. split; auto. rewrite pullOutR. econstructor. 
      eapply SFork; eauto. eassumption. constructor. }
     {copy H2. simpl in *. nonEmptyStack'Tac H2. invertHyp. simpl in *. subst. 
      apply eraseTrmApp in H1. inv H1. right. econstructor. econstructor. 
      econstructor. split. constructor. split; auto. rewrite pullOutR. econstructor. 
      eapply SGet; eauto. eassumption. constructor. }
     {copy H2. simpl in *. nonEmptyStack'Tac H2. invertHyp. simpl in *. subst. 
      apply eraseTrmApp in H1. inv H1. right. econstructor. econstructor. 
      econstructor. split. constructor. split; auto. rewrite pullOutR. econstructor. 
      eapply SPut; eauto. eassumption. constructor. }
     {copy H2. simpl in *. nonEmptyStack'Tac H2. invertHyp. simpl in *. subst. 
      apply eraseTrmApp in H1. inv H1. right. econstructor. econstructor. 
      econstructor. split. constructor. split; auto. rewrite pullOutR. econstructor. 
      eapply SNew; eauto. eassumption. constructor. }
     {copy H2. simpl in *. nonEmptyStack'Tac H2. invertHyp. simpl in *. subst. 
      apply eraseTrmApp in H1. inv H1. right. econstructor. econstructor. 
      econstructor. split. constructor. split; auto. rewrite pullOutR. econstructor. 
      eapply SSpec; eauto. eassumption. constructor. }
    }
   }
  }
Qed. 

Theorem pureStepsDiffHeap : forall H H' tid s1 s2 M M',
                              spec_multistep H (tSingleton(tid,s1,s2,M)) H (tSingleton(tid,s1,s2,M')) ->
                              spec_multistep H' (tSingleton(tid,s1,s2,M)) H' (tSingleton(tid,s1,s2,M')).
Proof. 
  intros. dependent induction H0; unfoldTac. 
  {invertHyp. invThreadEq. constructor. }
  {copy H. apply specStepSingleton in H1. invertHyp.  copy x. apply UnionEqSingleton in x. 
   subst. rewrite <- union_empty_l at 1. inv H; unfoldTac; invertHyp; invThreadEq. 
   {econstructor. eapply SBasicStep; eauto. unfoldTac. rewrite union_empty_l. 
    eapply IHspec_multistep; eauto. rewrite <- union_empty_l in H1. 
    apply UnionEqTID in H1. invertHyp. rewrite union_empty_l. auto. }
   {eapply monotonicActions in H0. Focus 2. apply InL. constructor. 
    Focus 2. constructor. destruct s1; simpl in *; omega. }
   {eapply monotonicActions in H0. Focus 2. apply InL. constructor. 
    Focus 2. constructor. destruct s1; simpl in *; omega. }
   {eapply monotonicActions in H0. Focus 2. apply InL. constructor. 
    Focus 2. constructor. destruct s1; simpl in *; omega. }
   {eapply monotonicActions in H0. Focus 2. apply InL. constructor. 
    Focus 2. constructor. destruct s1; simpl in *; omega. }
   {eapply monotonicActions in H0. Focus 2. apply InL. constructor. 
    Focus 2. constructor. destruct s1; simpl in *; omega. }
  }
Qed. 

Theorem ind1 : forall H H' T T' tid s1 s2 M M',
                spec_multistep H (tUnion T(tSingleton(tid,s1,s2,M))) 
                               H' (tUnion T'(tSingleton(tid,s1,s2,M'))) -> 
                spec_multistep H (tSingleton(tid,s1,s2,M))
                               H (tSingleton(tid,s1,s2,M')).
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {startIndCase. eqIn H1. inv H2. 
   {eapply pureStepsDiffHeap with (H:=h'). eapply IHspec_multistep; eauto. 
    proveUnionEq x. }
   {inv H4. rewrite <- union_empty_l at 1. inv H; unfoldTac; invertHyp; invThreadEq. 
    {econstructor. eapply SBasicStep; eauto. unfoldTac. rewrite union_empty_l. 
     eapply IHspec_multistep; eauto. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
   }
  }
Qed. 

Theorem ind2 : forall H H' T T' tid s1 s2 M M',
                spec_multistep H (tUnion T(tSingleton(tid,s1,s2,M))) 
                               H' (tUnion T'(tSingleton(tid,s1,s2,M'))) -> 
                spec_multistep H T H' T'. 
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {startIndCase. eqIn H1. inv H2. 
   {takeTStep. eapply IHspec_multistep; eauto. proveUnionEq x. rewrite H4. solveSet. }
   {inv H4. apply UnionEqTID in x. invertHyp. inv H; unfoldTac; invertHyp; invThreadEq. 
    {eauto. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. apply InL. constructor. Focus 2. 
     apply InL. constructor. destruct s1; simpl in *; omega. }
   }
  }
Qed. 

Theorem ind : forall H H' T T' tid s1 s2 M H'' T''  M' s1' M'' ,
                spec_multistep H (tUnion T(tSingleton(tid,s1,s2,M))) 
                               H' (tUnion T'(tSingleton(tid,s1,s2,M'))) -> 
                spec_multistep H' (tUnion T'(tSingleton(tid,s1,s2,M'))) 
                               H'' (tUnion T''(tSingleton(tid,s1',s2,M''))) -> 
                spec_multistep H (tUnion T(tSingleton(tid,s1,s2,M)))
                               H(tUnion T(tSingleton(tid,s1,s2,M'))) /\
                spec_multistep H(tUnion T(tSingleton(tid,s1,s2,M')))
                               H'' (tUnion T'' (tSingleton(tid,s1',s2,M''))). 
Proof.
  intros. split. 
  {unfoldTac. rewrite Union_commutative. rewrite (Union_commutative thread T). 
   rewrite spec_multi_unused. eapply ind1; eauto. }
  {eapply spec_multi_trans. rewrite spec_multi_unused. eapply ind2; eauto. assumption. }
Qed. 


Ltac nonEmptyStack'Tac2 H :=
  eapply nonEmptyStack' in H;[idtac|apply InL;constructor|apply InL;constructor|
                                    rewrite app_nil_l;simpl;auto|auto]. 

Theorem forkCatchupR : forall H T H' T' S S' tid s1 M M' M'' s2,
          stackList S = nil -> stackList S' = s1 -> eraseTrm s1 M' M'' ->
          spec_multistep H (tUnion T(tSingleton(tid,S,s2,M)))
                         H'(tUnion T'(tSingleton(tid,S',s2,M'))) -> 
          exists H'' T'', 
            spec_multistep H  (tUnion T(tSingleton(tid,S,s2,M)))
                           H'' (tUnion T''(tSingleton(tid,S,s2,M''))) /\
            spec_multistep H'' (tUnion T''(tSingleton(tid,S,s2,M''))) 
                           H'(tUnion T'(tSingleton(tid,S',s2,M'))).
Proof.
  intros. dependent induction H3. 
  {apply UnionEqTID in x. invertHyp. destruct S'; simpl in *; subst; 
   inv H2; try invertListNeq; repeat econstructor. }
  {startIndCase. eqIn H1. inv H4. 
   {eapply IHspec_multistep in H0; eauto. Focus 2. proveUnionEq x. invertHyp. 
    econstructor. econstructor. split. takeTStep. eauto. eauto. }
   {inv H6. apply UnionEqTID in x. invertHyp. inversion H; unfoldTac; invertHyp; invThreadEq. 
    {eapply IHspec_multistep in H0. Focus 2. eauto. Focus 2. auto. Focus 2. 
     auto. invertHyp. econstructor. econstructor. split. econstructor. 
     eapply SBasicStep; eauto. eauto. eauto. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H9 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SFork; eauto. eassumption. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H10 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SGet; eauto. eassumption. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H10 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SPut; eauto. eassumption. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H9 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SNew; eauto. eassumption. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H9 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SSpec; eauto. eassumption. }
   }
  }
Qed. 

Theorem forkCatchupL : forall a H T H' T' S S' tid s1 M M' M'' s2,
          stackList S = [a] -> stackList S' = s1 ++[a] -> eraseTrm s1 M' M'' ->
          spec_multistep H (tUnion T(tSingleton(tid,S,s2,M)))
                         H'(tUnion T'(tSingleton(tid,S',s2,M'))) -> 
          exists H'' T'', 
            spec_multistep H  (tUnion T(tSingleton(tid,S,s2,M)))
                           H'' (tUnion T''(tSingleton(tid,S,s2,M''))) /\
            spec_multistep H'' (tUnion T''(tSingleton(tid,S,s2,M''))) 
                           H'(tUnion T'(tSingleton(tid,S',s2,M'))).
Proof.
  intros. dependent induction H3.  
  {apply UnionEqTID in x. invertHyp. destruct S'; simpl in *; subst;  
   destruct s1; inv H0; try invertListNeq; inv H2; try invertListNeq; repeat econstructor. }
  {startIndCase. eqIn H4. inv H5. 
   {eapply IHspec_multistep in H0; eauto. Focus 2. proveUnionEq x. invertHyp. 
    econstructor. econstructor. split. takeTStep. eauto. eauto. }
   {inv H7. apply UnionEqTID in x. invertHyp. inversion H; unfoldTac; invertHyp; invThreadEq. 
    {eapply IHspec_multistep in H0. Focus 2. eauto. Focus 2. eauto. Focus 2. 
     auto. Focus 2. auto. invertHyp. econstructor. econstructor. split. econstructor. 
     eapply SBasicStep; eauto. eauto. eauto. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. apply eraseTrmApp in H2. inv H2. econstructor; econstructor. split. 
     constructor. econstructor. eapply SFork; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. apply eraseTrmApp in H2. inv H2. econstructor; econstructor. split. 
     constructor. econstructor. eapply SGet; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. apply eraseTrmApp in H2. inv H2. econstructor; econstructor. split. 
     constructor. econstructor. eapply SPut; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. apply eraseTrmApp in H2. inv H2. econstructor; econstructor. split. 
     constructor. econstructor. eapply SNew; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. apply eraseTrmApp in H2. inv H2. econstructor; econstructor. split. 
     constructor. econstructor. eapply SSpec; eauto. eassumption. }
   }
  }
Qed. 

Theorem forkCatchup' : forall H T H' T' x x0 tid s1' tid' s1'' a s2 e1 e1' e2 e2',
    eraseTrm s1' e1' x -> eraseTrm s1'' e2' x0 ->
    spec_multistep H (tUnion T (tCouple(tid,unlocked[a], s2, e1)
                                       (tid',locked nil,nil,e2)))
                   H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (tid',locked s1'',nil,e2'))) -> 
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,e1)
                                         (tid',locked nil,nil,e2)))
                     H (tUnion T (tCouple(tid,unlocked[a],s2,x)
                                             (tid',locked nil,nil,x0))) /\
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,x)
                                             (tid',locked nil,nil,x0)))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (tid',locked s1'',nil,e2'))).
Proof.
  intros. copy H2. eapply forkCatchup in H2; eauto. inv H2. 
  {invertHyp. unfoldTac. flipCouplesIn H2. flipCouplesIn H4. repeat rewrite coupleUnion in *.
   repeat rewrite <- Union_associative in *. eapply ind in H2; eauto. invertHyp. unfoldTac.
   rewrite UnionSwap in H7. rewrite Union_associative in H7. rewrite UnionSwap in H7. 
   rewrite <- Union_associative in H7. eapply forkCatchupR in H7; eauto. invertHyp. 
   eapply ind in H8; eauto. invertHyp. split. 
   {rewrite UnionSwap. eapply spec_multi_trans. eassumption. rewrite UnionSwap. 
    eapply spec_multi_trans. eassumption. constructor. }
   {eassumption. }
  }
  {invertHyp. unfoldTac. repeat rewrite coupleUnion in *. repeat rewrite <- Union_associative in *. 
   eapply ind in H2; eauto. invertHyp. unfoldTac. rewrite UnionSwap in H7. 
   rewrite Union_associative in H7. rewrite UnionSwap in H7. rewrite <- Union_associative in H7.
   eapply forkCatchupL in H7; simpl;eauto. invertHyp. eapply ind in H8; eauto. invertHyp. split. 
   {eapply spec_multi_trans. eassumption. rewrite UnionSwap. eapply spec_multi_trans. 
    eassumption. rewrite UnionSwap. constructor. }
   {rewrite UnionSwap. rewrite Union_associative. rewrite UnionSwap.
    rewrite <- Union_associative. assumption. }
  }
Qed. 

Theorem nonNilLockedStack : forall s1 s2 x M M' tid H H' T T',
        actionTerm x M' ->
        spec_multistep H (tUnion T (tSingleton(tid,locked nil,s2, M')))
                       H' (tUnion T' (tSingleton(tid,locked s1,s2,M))) ->
        M <> M' -> s1 <> nil. 
Proof. 
  intros. dependent induction H1.  
  {inv H0; apply UnionEqTID in x; invertHyp; inv H; exfalso; apply H2; auto. }
  {startIndCase. eqIn H3. inv H4. 
   {eapply IHspec_multistep; eauto. apply UnionSingletonEq in x. rewrite x. 
    unfoldTac. rewrite UnionSwap. auto. auto. }
   {inv H6. inv H0. 
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H4; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. Focus 2. 
      simpl. rewrite app_nil_l. auto. Focus 2. auto. simpl in *. subst. 
      introsInv. invertListNeq. }
    }
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H4; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. Focus 2. 
      simpl. rewrite app_nil_l. auto. Focus 2. auto. simpl in *. subst. 
      introsInv. invertListNeq. }
    }
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H4; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. Focus 2. 
      simpl. rewrite app_nil_l. auto. Focus 2. auto. simpl in *. subst. 
      introsInv. invertListNeq. }
    }
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H4; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. Focus 2. 
      simpl. rewrite app_nil_l. auto. Focus 2. auto. simpl in *. subst. 
      introsInv. invertListNeq. }
    }
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H4; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. Focus 2. 
      simpl. rewrite app_nil_l. auto. Focus 2. auto. simpl in *. subst. 
      introsInv. invertListNeq. }
    }
   }
  }
Qed. 

Inductive stackLists : actionStack -> list action -> actionStack -> list action -> Prop :=
|stacksL : forall s1 s2, stackLists(locked s1) s1 (locked s2) s2
|stacksU : forall s1 s2, stackLists(unlocked s1) s1 (unlocked s2) s2
|stacksS : forall s1 s2 N, stackLists(specStack s1 N) s1 (specStack s2 N) s2.  



Theorem forkSimActStepsLocked : forall H T H' T' H'' T'' tid s a s' x S S' M M',
      actionTerm a x -> stackLists S s' S' (s++[a]) ->    
      spec_multistep H'' (tUnion T'' (tSingleton(tid,locked nil,nil,x)))
                     H (tUnion T(tSingleton(tid,locked s',nil,M))) -> 
      spec_multistep H (tUnion T(tSingleton(tid,locked s',nil,M)))
                     H' (tUnion T'(tSingleton(tid,locked(s++[a]),nil,M'))) ->
      spec_multistep H (tUnion T(tSingleton(tid, S,nil,M)))
                     H' (tUnion T'(tSingleton(tid,S',nil,M'))). 
Proof.
  intros. genDeps{S;S'}. dependent induction H3; intros. 
  {apply UnionEqTID in x. invertHyp. inv H. inv H1; constructor. }
  {startIndCase. eqIn H4. inv H5. 
   {takeTStep. eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
    rewrite H7. rewrite UnionSwap. econstructor. eapply specStepChangeUnused. eauto. 
    unfoldTac. rewrite <- UnionSwap. rewrite subtractSingle. constructor. 
    proveUnionEq x. rewrite H7. solveSet. }
   {inv H7. apply UnionEqTID in x. invertHyp. inversion H; unfoldTac; invertHyp; invThreadEq. 
    {copy H2. eapply nonNilLockedStack in H2; eauto. destruct s'. exfalso; apply H2. 
     auto. econstructor. eapply SBasicStep; eauto. inv H1; constructor. 
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. econstructor. 
     eapply SBasicStep; eauto. constructor. intros c. inv H0; inv H10; falseDecomp. }
    {econstructor. eapply SFork with(n:=numForks(locked s')); eauto. inv H1; auto.  unfoldTac. 
     rewrite couple_swap. rewrite coupleUnion. rewrite <- Union_associative.
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
     eassumption. rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     econstructor. eapply SFork with(n:=numForks(locked s')); eauto. constructor. 
     rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     simpl in *. rewrite plus_0_r. reflexivity. inv H1; constructor. }
    {econstructor. eapply SGet; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. constructor. 
     simpl. auto. inv H1; simpl; constructor. }
    {econstructor. eapply SPut; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. constructor. 
     simpl. auto. inv H1; simpl; constructor. }
    {econstructor. eapply SNew; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. constructor. 
     simpl. auto. inv H1; simpl; constructor. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite couple_swap. rewrite coupleUnion. 
     rewrite <- Union_associative. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
     eassumption. rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     econstructor. eapply SSpec; eauto. constructor. rewrite Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. reflexivity. inv H1; constructor. }
   }
  }
Qed. 

Theorem forkSimActStepsUnlocked : forall H T H' T' H'' s2 T'' z b tid s a s' x M M',
      eraseTrm(s++[a]) z x -> 
      spec_multistep H'' (tUnion T'' (tSingleton(tid,unlocked [b],s2,x)))
                     H (tUnion T(tSingleton(tid,unlocked (s'++[b]),s2,M))) -> 
      spec_multistep H (tUnion T(tSingleton(tid,unlocked (s'++[b]),s2,M)))
                     H' (tUnion T'(tSingleton(tid,unlocked(s++[a]++[b]),s2,M'))) ->
      spec_multistep H (tUnion T(tSingleton(tid, unlocked s',b::s2,M)))
                     H' (tUnion T'(tSingleton(tid,unlocked(s++[a]),b::s2,M'))). 
Proof.
  intros. dependent induction H2; intros. 
  {apply UnionEqTID in x. invertHyp. inv H. replace [a;b] with([a]++[b]) in H4. 
   rewrite app_assoc in H4. apply app_inv_tail in H4. subst. inv H1; constructor. 
   auto. }
  {startIndCase. eqIn H3. inv H4. 
   {takeTStep. eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
    rewrite H6. rewrite UnionSwap. econstructor. eapply specStepChangeUnused. eauto. 
    unfoldTac. rewrite <- UnionSwap. rewrite subtractSingle. constructor. 
    proveUnionEq x. rewrite H6. solveSet. }
   {inv H6. apply UnionEqTID in x. invertHyp. inversion H; unfoldTac; invertHyp; invThreadEq. 
    {copy H1. eapply stackNonNil in H1; eauto. destruct s'. exfalso; apply H1. 
     auto. econstructor. eapply SBasicStep; eauto. inv H0; constructor. 
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. econstructor. 
     eapply SBasicStep; eauto. constructor. intros c. apply eraseTrmApp in H0. inv H0; inv H9; falseDecomp. }
    {econstructor. eapply SFork with(n:=plus (numForks(unlocked(s'++[b])))(numForks' s2)); eauto.
     simpl. rewrite numForksDistribute. simpl. destruct b; rewrite <- plus_assoc; simpl; auto. 
     unfoldTac. rewrite couple_swap. rewrite coupleUnion. 
     rewrite <- Union_associative. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
     eassumption. rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     econstructor. eapply SFork with(n:=plus (numForks(unlocked(s'++[b])))(numForks' s2)); eauto. 
     simpl. constructor.  rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     simpl in *. reflexivity. }
    {econstructor. eapply SGet; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. constructor. 
     simpl. auto. }
    {econstructor. eapply SPut; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. constructor. 
     simpl. auto. }
    {econstructor. eapply SNew; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. constructor. 
     simpl. auto. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite couple_swap. rewrite coupleUnion. 
     rewrite <- Union_associative. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
     eassumption. rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     econstructor. eapply SSpec; eauto. constructor. rewrite Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. reflexivity. }
   }
  }
Qed. 


Theorem forkSimActSteps : forall H T H' T' H'' a' T'' z z' tid s a s' s2 S1 S2 S S' M M' tid' b N N' x x',
      eraseTrm(S1++[a]) z x -> eraseTrm (S2++[a']) z' x' -> stackLists S s' S' (S2++[a']) ->    
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[b],s2,x)(tid',locked nil,nil,x')))
                     H (tUnion T(tCouple(tid,unlocked (s++[b]),s2,M)(tid',locked s',nil,N))) -> 
      spec_multistep H (tUnion T(tCouple(tid,unlocked (s++[b]),s2,M)(tid',locked s',nil,N)))
                     H' (tUnion T'(tCouple(tid,unlocked(S1++[a]++[b]),s2,M')(tid',locked(S2++[a']),nil,N'))) ->
      spec_multistep H (tUnion T(tCouple(tid,unlocked s,b::s2,M)(tid',S,nil,N)))
                     H' (tUnion T'(tCouple(tid,unlocked(S1++[a]),b::s2,M')(tid',S',nil,N'))).
Proof.
  intros. genDeps{S;S'}. dependent induction H4; intros. 
  {unfoldTac. repeat rewrite coupleUnion in *. repeat rewrite <- Union_associative in *. 
   apply UnionEqTID in x. invertHyp. apply UnionEqTID in H. invertHyp. 
   inv H. inv H5. replace[a;b] with([a]++[b]) in H8. rewrite app_assoc in H8. 
   apply app_inj_tail in H8. invertHyp. inv H2; constructor. auto . }
  {startIndCase. eqIn H5. inv H6. 
   {copy H8. takeTStep. eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
    clear H6. takeTStep. rewrite subtractSingle. constructor. apply UnionSingletonCoupleEq in x. 
    rewrite x. unfoldTac. rewrite UnionSwap. auto. auto. }
   {inv H8. 
    {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x.
     rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. 
     inversion H; unfoldTac; invertHyp; invThreadEq.  
     {copy H3. rewrite couple_swap in H3. rewrite coupleUnion in H3. rewrite couple_swap in H3. 
      rewrite coupleUnion in H3. repeat rewrite <- Union_associative in H3. eapply stackNonNil in H3. 
      Focus 2. eauto. destruct s. exfalso; apply H3; auto. rewrite pullOutL. econstructor. 
      eapply SBasicStep; eauto. constructor. unfoldTac. rewrite <- pullOutL.
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. rewrite pullOutL. 
      econstructor. eapply SBasicStep; eauto. unfoldTac. rewrite <- pullOutL. constructor. 
      rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. auto. intros c. 
      subst. apply eraseTrmApp in H0. inv H0; inv H11; falseDecomp. }
     {rewrite pullOutL. econstructor.
      eapply SFork with(n:=plus(numForks (unlocked (s ++ [b]))) (numForks' s2)); eauto.  
      simpl. rewrite numForksDistribute. simpl. destruct b; rewrite <- plus_assoc; auto. 
      unfoldTac. rewrite <- UnionSwapR. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutL. econstructor. eapply SFork; eauto. unfoldTac.
      rewrite <- UnionSwapR. constructor. rewrite <- UnionSwapR. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SGet; eauto. unfoldTac. rewrite <- pullOutL. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutL. econstructor. eapply SGet; eauto. unfoldTac. rewrite <- pullOutL. 
      constructor. rewrite <- pullOutL. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SPut; eauto. unfoldTac. rewrite <- pullOutL. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutL. econstructor. eapply SPut; eauto. unfoldTac. rewrite <- pullOutL. 
      constructor. rewrite <- pullOutL. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SNew; eauto. unfoldTac. rewrite <- pullOutL. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutL. econstructor. eapply SNew; eauto. unfoldTac. rewrite <- pullOutL. 
      constructor. rewrite <- pullOutL. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SSpec.  unfoldTac. rewrite <- UnionSwapR. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutL. econstructor. eapply SSpec; eauto. unfoldTac.
      rewrite <- UnionSwapR. constructor. rewrite <- UnionSwapR. reflexivity. }
    }
    {unfoldTac. rewrite coupleUnion in x. rewrite <- Union_associative in x.
     apply UnionEqTID in x. invertHyp. inversion H; unfoldTac; invertHyp; invThreadEq.  
     {copy H3. repeat rewrite coupleUnion in H3. repeat rewrite <- Union_associative in H3.
      copy H1. apply eraseTrmApp in H1. eapply nonNilLockedStack in H3; eauto. 
      destruct s'. exfalso; apply H3; auto. rewrite pullOutR. econstructor. 
      eapply SBasicStep; eauto. inv H2; constructor. unfoldTac. rewrite <- pullOutR.
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. rewrite pullOutR. 
      econstructor. eapply SBasicStep; eauto. unfoldTac. rewrite <- pullOutR. constructor. 
      rewrite Union_associative. rewrite <- coupleUnion. auto. intros c. 
      subst. inv H1; inv H11; falseDecomp. }
     {rewrite pullOutR. econstructor.
      eapply SFork with(n:=plus(numForks (locked s')) (numForks' [])); eauto.  
      simpl. inv H2; simpl; auto. unfoldTac. rewrite <- UnionSwapR. rewrite couple_swap. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SFork; eauto. unfoldTac.
      rewrite <- UnionSwapR. rewrite couple_swap. simpl. rewrite plus_0_r. constructor. 
      rewrite <- UnionSwapR. rewrite couple_swap. simpl. rewrite plus_0_r. reflexivity. 
      inv H2; simpl; rewrite plus_0_r;  constructor. }
     {rewrite pullOutR. econstructor. eapply SGet; eauto. unfoldTac. rewrite <- pullOutR. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutR. econstructor. eapply SGet; eauto. unfoldTac. rewrite <- pullOutR. 
      constructor. rewrite <- pullOutR. reflexivity. inv H2; constructor. }
     {rewrite pullOutR. econstructor. eapply SPut; eauto. unfoldTac. rewrite <- pullOutR. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutR. econstructor. eapply SPut; eauto. unfoldTac. rewrite <- pullOutR. 
      constructor. rewrite <- pullOutR. reflexivity. inv H2; constructor. }
     {rewrite pullOutR. econstructor. eapply SNew; eauto. unfoldTac. rewrite <- pullOutR. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutR. econstructor. eapply SNew; eauto. unfoldTac. rewrite <- pullOutR. 
      constructor. rewrite <- pullOutR. reflexivity. inv H2; constructor. }
     {rewrite pullOutR. econstructor. eapply SSpec.  unfoldTac. rewrite <- UnionSwapR. 
      rewrite couple_swap. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SSpec; eauto. unfoldTac.
      rewrite <- UnionSwapR. rewrite couple_swap. constructor. 
      rewrite <- UnionSwapR. rewrite couple_swap. reflexivity. inv H2; constructor. }
    }
   }
  }
Qed. 














