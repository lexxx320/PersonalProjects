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
  {unfoldTac. rewrite coupleUnion in x. rewrite Union_associative in x. 
   rewrite UnionSwap in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x0. exMid H7 tid. 
   {apply UnionEqTID in x. invertHyp. inversion H; subst; try solve[falseDecomp]. 
    {inv H12; falseDecomp. }
    {copy d0. eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H5. exists h'. exists T. split. econstructor. 
     eapply SFork; eauto. simpl. constructor. split. simpl in *. proofsEq d d0. 
     assumption. constructor. }
   }
   {copy x. apply UnionNeqTID in x. copy H. apply specStepSingleton in H9. 
    invertHyp. eapply IHspec_multistep in H0. Focus 4. auto. Focus 2. 
    auto. Focus 3. auto. invertHyp. econstructor. econstructor. split. 
    takeTStep. eauto. split; auto. takeTStep. econstructor.
    eapply specStepChangeUnused. eauto. eauto. rewrite H9. rewrite UnionSubtract. 
    unfoldTac. rewrite UnionSwap; auto. }
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
   eapply uniqueThreadPool in H; eauto. invThreadEq.
   destruct s1; simpl in *; subst; eauto. }
  {unfoldTac. unfold Union in H1. unfold In in H1. apply in_app_or in H1. inv H1. 
   {eapply IHspec_multistep; eauto. solveSet. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H5. inv H1. 
    {eapply IHspec_multistep; eauto. solveSet. }
    {eapply IHspec_multistep. solveSet. destruct s1; simpl in *; subst; auto.  
     eauto. auto. }
    {eapply IHspec_multistep. solveSet. destruct s1; simpl in *; subst; auto.  
     eauto. auto. }
    {eapply IHspec_multistep. solveSet. destruct s1; simpl in *; subst; auto.  
     eauto. auto. }
    {eapply IHspec_multistep. solveSet. destruct s1; simpl in *; subst; auto.  
     eauto. auto. }
    {eapply IHspec_multistep. solveSet. destruct s1; simpl in *; subst; auto.  
     eauto. auto. }
    {inv H. }
   }
  }
Qed.  

Ltac nonEmptyStack'Tac H :=
  eapply nonEmptyStack' in H;[idtac|solveSet|solveSet|
                                    rewrite app_nil_l;simpl;auto|auto]. 

Theorem forkCatchup : forall H T H' T' x n x0 tid s1' s1'' s2 e1 e1' e2 e2' a,
    eraseTrm s1' e1' x -> eraseTrm s1'' e2' x0 -> 
    spec_multistep H (tUnion T (tCouple(tid,unlocked[a], s2, e1)
                                       (n::tid,locked nil,nil,e2)))
                   H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) -> 
    ((
    exists H'' T'' x0',
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,e1)
                                         (n::tid,locked nil,nil,e2)))
                     H'' (tUnion T'' (tCouple(tid,unlocked[a],s2,x)
                                             (n::tid,locked nil,nil,x0'))) /\
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[a],s2,x)
                                             (n::tid,locked nil,nil,x0')))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) /\
      spec_multistep H T H'' T'') \/
     (
    exists H'' T'' x',
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,e1)
                                         (n::tid,locked nil,nil,e2)))
                     H'' (tUnion T'' (tCouple(tid,unlocked[a],s2,x')
                                             (n::tid,locked nil,nil,x0))) /\
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[a],s2,x')
                                             (n::tid,locked nil,nil,x0)))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) /\
      spec_multistep H T H'' T'')). 
Proof.
  intros. genDeps{x;x0}. dependent induction H2; intros.
  {unfoldTac. repeat rewrite coupleUnion in x. 
   repeat rewrite Union_associative in x. apply UnionEqTID in x. invertHyp. 
   inv H3. apply UnionEqTID in H. invertHyp. inv H.
   destruct s1'; inv H5; try invertListNeq. inv H0; try invertListNeq. 
   inv H1; try  invertListNeq. left. econstructor. econstructor. econstructor. 
   split. constructor. split. constructor. constructor. }
  {startIndCase. destructThread x2. exMid H8 tid.  
   {unfoldTac. rewrite coupleUnion in H4. rewrite Union_associative in H4.
     rewrite UnionSwap in H4. apply UnionEqTID in H4. invertHyp. inv H.
     {eapply IHspec_multistep in H0. Focus 2. rewrite <- Union_associative. 
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
   {exMid H8 (n::tid). 
    {unfoldTac. rewrite coupleUnion in H4. rewrite Union_associative in H4.
     apply UnionEqTID in H4. invertHyp. inv H.
     {eapply IHspec_multistep in H0. Focus 2. rewrite <- Union_associative. 
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
    {apply UnionCoupleNeqTID in H4; auto. eapply IHspec_multistep in H0; eauto. 
     inv H0. 
     {left. invertHyp. econstructor. econstructor. econstructor. split. 
      takeTStep. eassumption. split; auto. takeTStep. econstructor. 
      eapply specStepChangeUnused; eauto. unfoldTac. eassumption. }
     {right. invertHyp. econstructor. econstructor. econstructor. split. 
      takeTStep. eassumption. split; auto. takeTStep. econstructor. 
      eapply specStepChangeUnused; eauto. unfoldTac. eassumption. }
     invertHyp. rewrite H3. unfoldTac. rewrite couple_swap. rewrite coupleUnion. 
     rewrite Union_associative. repeat rewrite UnionSubtract. 
     rewrite <- Union_associative. rewrite <- Union_associative. 
     rewrite <- Union_associative. 
     rewrite (Union_associative thread (Single(n::tid,locked[],[],e2))).
     rewrite <- coupleUnion. rewrite couple_swap. rewrite Union_associative. 
     rewrite UnionSwap. rewrite <- Union_associative. reflexivity. intros c. 
     invertListNeq. 
    }
   }
  }
Qed. 

Theorem pureStepsDiffHeap : forall H H' tid s1 s2 M M',
                              spec_multistep H (tSingleton(tid,s1,s2,M)) H (tSingleton(tid,s1,s2,M')) ->
                              spec_multistep H' (tSingleton(tid,s1,s2,M)) H' (tSingleton(tid,s1,s2,M')).
Proof. 
  intros. dependent induction H0; unfoldTac. 
  {constructor. }
  {copy H. apply specStepSingleton in H1. invertHyp. copy x. 
   apply UnionEqSingleton in x. invertHyp. 
   rewrite <- union_empty_l at 1. inv H. 
   {econstructor. eapply SBasicStep; eauto. unfoldTac. rewrite union_empty_l. 
    eapply IHspec_multistep; eauto. }
   {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
    destruct s1; simpl in *; omega. }
   {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
    destruct s1; simpl in *; omega. }
   {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
    destruct s1; simpl in *; omega. }
   {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
    destruct s1; simpl in *; omega. }
   {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
    destruct s1; simpl in *; omega. }
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
  {startIndCase. destructThread x0. exMid H6 tid. 
   {apply UnionEqTID in H2. invertHyp. rewrite <- union_empty_l at 1. inv H. 
    {econstructor. eapply SBasicStep; eauto. unfoldTac. rewrite union_empty_l. 
     eapply IHspec_multistep; eauto. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
   }
   {eapply pureStepsDiffHeap with (H:=h'). eapply IHspec_multistep; eauto. 
    apply UnionNeqTID in x; auto. invertHyp. rewrite H1. unfoldTac. 
    rewrite UnionSwap. eauto. }
  }
Qed. 

Theorem ind2 : forall H H' T T' tid s1 s2 M M',
                spec_multistep H (tUnion T(tSingleton(tid,s1,s2,M))) 
                               H' (tUnion T'(tSingleton(tid,s1,s2,M'))) -> 
                spec_multistep H T H' T'. 
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {startIndCase. destructThread x0. exMid tid H6. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {eauto. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0. Focus 2. solveSet. Focus 2. solveSet. 
     destruct s1; simpl in *; omega. }
   }
   {apply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. 
    eapply specStepChangeUnused; eauto. eapply IHspec_multistep; eauto. 
    rewrite H1. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap. eauto. }
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
  eapply nonEmptyStack' in H;[idtac|solveSet|solveSet|
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
  {startIndCase. destructThread x0. exMid tid H8. 
   {apply UnionEqTID in H4. invertHyp. inv H. 
    {eapply IHspec_multistep in H0. Focus 2. eauto. Focus 2. auto. Focus 2. 
     auto. invertHyp. econstructor. econstructor. split. econstructor. 
     eapply SBasicStep; eauto. eauto. eauto. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H1 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SFork; eauto. eassumption. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H1 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SGet; eauto. eassumption. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H1 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SPut; eauto. eassumption. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H1 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SNew; eauto. eassumption. }
    {copy H3. nonEmptyStack'Tac2 H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. rewrite H1 in H2. apply eraseTrmApp in H2. 
     inv H2. econstructor; econstructor. split. constructor. econstructor. 
     eapply SSpec; eauto. eassumption. }
   }
   {apply UnionNeqTID in x. eapply IHspec_multistep in H0; eauto. invertHyp. 
    econstructor. econstructor. split. takeTStep. eauto. eauto. invertHyp. 
    rewrite H1. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap; eauto. auto. }
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
   destruct s1; inv H0; try invertListNeq; inv H2; 
   try invertListNeq; repeat econstructor. }
  {startIndCase. destructThread x0. exMid H9 tid. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {eapply IHspec_multistep in H0. Focus 2. eauto. Focus 2. eauto. Focus 2. 
     auto. Focus 2. auto. invertHyp. econstructor. econstructor. split. econstructor. 
     eapply SBasicStep; eauto. eauto. eauto. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto.
     Focus 2. eauto. invertHyp. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor. 
     eapply SFork; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto.
     Focus 2. eauto. invertHyp. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor. 
     eapply SGet; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto.
     Focus 2. eauto. invertHyp. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor. 
     eapply SPut; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto.
     Focus 2. eauto. invertHyp. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor. 
     eapply SNew; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto.
     Focus 2. eauto. invertHyp. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor. 
     eapply SSpec; eauto. eassumption. }
   }
   {apply UnionNeqTID in x; auto. eapply IHspec_multistep in H0; eauto.
    invertHyp. econstructor. econstructor. split. takeTStep. eauto. eauto. 
    invertHyp. rewrite H4. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap; auto. 
   }
  }
Qed. 

Theorem forkCatchup' : forall H T H' T' x x0 tid s1' n s1'' a s2 e1 e1' e2 e2',
    eraseTrm s1' e1' x -> eraseTrm s1'' e2' x0 ->
    spec_multistep H (tUnion T (tCouple(tid,unlocked[a], s2, e1)
                                       (n::tid,locked nil,nil,e2)))
                   H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) -> 
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,e1)
                                         (n::tid,locked nil,nil,e2)))
                     H (tUnion T (tCouple(tid,unlocked[a],s2,x)
                                             (n::tid,locked nil,nil,x0))) /\
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,x)
                                             (n::tid,locked nil,nil,x0)))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))).
Proof.
  intros. copy H2. eapply forkCatchup in H2; eauto. inv H2. 
  {invertHyp. unfoldTac. flipCouplesIn H2. flipCouplesIn H4. 
   repeat rewrite coupleUnion in *. repeat rewrite Union_associative in *. 
   eapply ind in H2; eauto. invertHyp. unfoldTac.
   rewrite UnionSwap in H7. rewrite <- Union_associative in H7. 
   rewrite UnionSwap in H7. rewrite Union_associative in H7. 
   eapply forkCatchupR in H7; eauto. invertHyp. eapply ind in H8; eauto. invertHyp. 
   split. 
   {rewrite UnionSwap. eapply spec_multi_trans. eassumption. rewrite UnionSwap. 
    eapply spec_multi_trans. eassumption. constructor. }
   {eassumption. }
  }
  {invertHyp. unfoldTac. repeat rewrite coupleUnion in *.
   repeat rewrite Union_associative in *. eapply ind in H2; eauto. invertHyp. 
   unfoldTac. rewrite UnionSwap in H7. rewrite <- Union_associative in H7. 
   rewrite UnionSwap in H7. rewrite Union_associative in H7.
   eapply forkCatchupL in H7; simpl;eauto. invertHyp. eapply ind in H8; eauto. 
   invertHyp. split. 
   {eapply spec_multi_trans. eassumption. rewrite UnionSwap. eapply spec_multi_trans. 
    eassumption. rewrite UnionSwap. constructor. }
   {rewrite UnionSwap. rewrite <- Union_associative. rewrite UnionSwap.
    rewrite Union_associative. assumption. }
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
  {startIndCase. destructThread x1. exMid tid H8. 
   {apply UnionEqTID in x. invertHyp. inv H0. 
    {inv H; try solve[falseDecomp]. 
     {inv H13; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. solveSet. Focus 2. solveSet. 
      Focus 2. simpl. rewrite app_nil_l. auto. Focus 2. auto. invertHyp. simpl in *. 
      subst. introsInv. invertListNeq. }
    }
    {inv H; try solve[falseDecomp]. 
     {inv H13; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. solveSet. Focus 2. solveSet. 
      Focus 2. simpl. rewrite app_nil_l. auto. Focus 2. auto. invertHyp. simpl in *. 
      subst. introsInv. invertListNeq. }
    }
    {inv H; try solve[falseDecomp]. 
     {inv H13; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. solveSet. Focus 2. solveSet. 
      Focus 2. simpl. rewrite app_nil_l. auto. Focus 2. auto. invertHyp. simpl in *. 
      subst. introsInv. invertListNeq. }
    }
    {inv H; try solve[falseDecomp]. 
     {inv H13; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. solveSet. Focus 2. solveSet. 
      Focus 2. simpl. rewrite app_nil_l. auto. Focus 2. auto. invertHyp. simpl in *. 
      subst. introsInv. invertListNeq. }
    }
    {inv H; try solve[falseDecomp]. 
     {inv H13; falseDecomp. }
     {simpl in *. eapply nonEmptyStack' in H1. Focus 2. solveSet. Focus 2. solveSet. 
      Focus 2. simpl. rewrite app_nil_l. auto. Focus 2. auto. invertHyp. simpl in *. 
      subst. introsInv. invertListNeq. }
    }
   }
   {eapply IHspec_multistep; eauto. apply UnionNeqTID in x; auto. invertHyp. 
    rewrite H3. unfoldTac. rewrite UnionSwap; auto. }
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
  {startIndCase. destructThread x1. exMid H9 tid. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {copy H2. eapply nonNilLockedStack in H2; eauto. destruct s'. exfalso; apply H2. 
     auto. econstructor. eapply SBasicStep; eauto. inv H1; constructor. 
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SBasicStep; eauto. constructor. intros c. 
     inv H0; inv H14; falseDecomp. }
    {econstructor. eapply SFork with(n:=numForks(locked s')); eauto. inv H1; auto.  
     unfoldTac. rewrite couple_swap. rewrite coupleUnion. rewrite Union_associative.
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
     eassumption. rewrite <- Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. econstructor. 
     eapply SFork with(n:=numForks(locked s')); eauto. constructor. 
     rewrite <- Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     simpl in *. rewrite plus_0_r. reflexivity. inv H1; constructor. }
    {econstructor. eapply SGet; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. 
     constructor. simpl. auto. inv H1; simpl; constructor. }
    {econstructor. eapply SPut; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. 
     constructor. simpl. auto. inv H1; simpl; constructor. }
    {econstructor. eapply SNew; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. 
     constructor. simpl. auto. inv H1; simpl; constructor. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite couple_swap. 
     rewrite coupleUnion. rewrite Union_associative. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. econstructor. eapply SSpec; eauto. 
     constructor. rewrite <- Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. reflexivity. inv H1; constructor. }
   }
   {apply UnionNeqTID in x. invertHyp. takeTStep. eapply IHspec_multistep; eauto. 
    eapply spec_multi_trans. eassumption. takeTStep. constructor. rewrite H4. 
    rewrite UnionSubtract. rewrite UnionSwap. auto. auto. }
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
  {startIndCase. destructThread x1. exMid tid H8. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {copy H1. eapply stackNonNil in H1; eauto. destruct s'. exfalso; apply H1. 
     auto. econstructor. eapply SBasicStep; eauto. inv H0; constructor. 
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SBasicStep; eauto. constructor. intros c. 
     apply eraseTrmApp in H0. inv H0; inv H14; falseDecomp. }
    {econstructor.
     eapply SFork with(n:=plus (numForks(unlocked(s'++[b])))(numForks' s2)); eauto.
     simpl. rewrite numForksDistribute. simpl.
     destruct b; rewrite <- plus_assoc; simpl; auto. unfoldTac. rewrite couple_swap. 
     rewrite coupleUnion. rewrite Union_associative. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. econstructor. 
     eapply SFork with(n:=plus (numForks(unlocked(s'++[b])))(numForks' s2)); eauto. 
     simpl. constructor.  rewrite <- Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. simpl in *. reflexivity. }
    {econstructor. eapply SGet; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. 
     constructor. simpl. auto. }
    {econstructor. eapply SPut; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. 
     constructor. simpl. auto. }
    {econstructor. eapply SNew; eauto. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. 
     constructor. simpl. auto. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite couple_swap. 
     rewrite coupleUnion. rewrite Union_associative. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. econstructor. eapply SSpec; eauto. 
     constructor. rewrite <- Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. reflexivity. }
   }
   {apply UnionNeqTID in x. invertHyp. takeTStep. eapply IHspec_multistep; eauto. 
    eapply spec_multi_trans. eassumption. takeTStep. constructor. rewrite H3. 
    rewrite UnionSubtract. rewrite UnionSwap; auto. auto. }
  }
Qed. 

Theorem forkSimActSteps : forall H T H' T' H'' a' T'' z z' tid s a s' s2 S1 S2 S S' M M' n b N N' x x',
      eraseTrm(S1++[a]) z x -> eraseTrm (S2++[a']) z' x' -> stackLists S s' S' (S2++[a']) ->    
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[b],s2,x)(n::tid,locked nil,nil,x')))
                     H (tUnion T(tCouple(tid,unlocked (s++[b]),s2,M)(n::tid,locked s',nil,N))) -> 
      spec_multistep H (tUnion T(tCouple(tid,unlocked (s++[b]),s2,M)(n::tid,locked s',nil,N)))
                     H' (tUnion T'(tCouple(tid,unlocked(S1++[a]++[b]),s2,M')(n::tid,locked(S2++[a']),nil,N'))) ->
      spec_multistep H (tUnion T(tCouple(tid,unlocked s,b::s2,M)(n::tid,S,nil,N)))
                     H' (tUnion T'(tCouple(tid,unlocked(S1++[a]),b::s2,M')(n::tid,S',nil,N'))).
Proof.
  intros. genDeps{S;S'}. dependent induction H4; intros. 
  {unfoldTac. repeat rewrite coupleUnion in *. repeat rewrite Union_associative in x. 
   apply UnionEqTID in x. invertHyp. apply UnionEqTID in H. invertHyp. 
   inv H. apply app_inj_tail in H8. invertHyp. inv H5. inv H2; constructor. }
  {startIndCase. destructThread x1. exMid tid H10. 
   {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x.
    rewrite Union_associative in x. apply UnionEqTID in x. invertHyp. inv H. 
    {copy H3. rewrite couple_swap in H3. rewrite coupleUnion in H3. 
     rewrite couple_swap in H3. rewrite coupleUnion in H3. 
     repeat rewrite Union_associative in H3. eapply stackNonNil in H3. 
     Focus 2. eauto. destruct s. exfalso; apply H3; auto. rewrite pullOutL. 
     econstructor. eapply SBasicStep; eauto. constructor. unfoldTac. 
     rewrite <- pullOutL. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
     eassumption. rewrite pullOutL. econstructor. eapply SBasicStep; eauto. 
     unfoldTac. rewrite <- pullOutL. constructor. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. auto. intros c. subst. 
     apply eraseTrmApp in H0. inv H0; inv H15; falseDecomp. }
    {rewrite pullOutL. econstructor.
     eapply SFork with(n:=plus(numForks (unlocked (s ++ [b]))) (numForks' s2));eauto.
     simpl. rewrite numForksDistribute. simpl. destruct b;rewrite <- plus_assoc;auto. 
     unfoldTac. rewrite <- UnionSwapR. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. rewrite pullOutL. econstructor. 
     eapply SFork; eauto. unfoldTac. rewrite <- UnionSwapR. constructor. 
     rewrite <- UnionSwapR. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SGet; eauto. unfoldTac. 
      rewrite <- pullOutL. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutL. econstructor. eapply SGet; eauto. unfoldTac. 
      rewrite <- pullOutL. constructor. rewrite <- pullOutL. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SPut; eauto. unfoldTac. 
      rewrite <- pullOutL. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutL. econstructor. eapply SPut; eauto. unfoldTac. 
      rewrite <- pullOutL. constructor. rewrite <- pullOutL. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SNew; eauto. unfoldTac. 
      rewrite <- pullOutL. eapply IHspec_multistep; eauto. eapply spec_multi_trans.
      eassumption. rewrite pullOutL. econstructor. eapply SNew; eauto. unfoldTac. 
      rewrite <- pullOutL. constructor. rewrite <- pullOutL. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SSpec.  unfoldTac. 
      rewrite <- UnionSwapR. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutL. econstructor. eapply SSpec; eauto. unfoldTac.
      rewrite <- UnionSwapR. constructor. rewrite <- UnionSwapR. reflexivity. }
    }
    {exMid H10 (n::tid). unfoldTac. rewrite coupleUnion in x. 
     rewrite Union_associative in x. apply UnionEqTID in x. invertHyp. inv H.
     {copy H3. repeat rewrite coupleUnion in H3. 
      repeat rewrite Union_associative in H3. copy H1. apply eraseTrmApp in H1. 
      eapply nonNilLockedStack in H3; eauto. destruct s'. exfalso; apply H3; auto. 
      rewrite pullOutR. econstructor. eapply SBasicStep; eauto. inv H2; constructor. 
      unfoldTac. rewrite <- pullOutR. eapply IHspec_multistep; eauto. 
      eapply spec_multi_trans. eassumption. rewrite pullOutR. econstructor. 
      eapply SBasicStep; eauto. unfoldTac. rewrite <- pullOutR. constructor. 
      rewrite <- Union_associative. rewrite <- coupleUnion. auto. intros c. 
      subst. inv H1; inv H15; falseDecomp. }
     {rewrite pullOutR. econstructor.
      eapply SFork with(n:=plus(numForks (locked s')) (numForks' [])); eauto.  
      simpl. inv H2; simpl; auto. unfoldTac. rewrite <- UnionSwapR. 
      rewrite couple_swap. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SFork; eauto. unfoldTac.
      rewrite <- UnionSwapR. rewrite couple_swap. simpl. rewrite plus_0_r. 
      constructor. rewrite <- UnionSwapR. rewrite couple_swap. simpl. 
      rewrite plus_0_r. reflexivity. inv H2; simpl; rewrite plus_0_r;  constructor. }
     {rewrite pullOutR. econstructor. eapply SGet; eauto. unfoldTac. 
      rewrite <- pullOutR. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SGet; eauto. unfoldTac. 
      rewrite <- pullOutR. constructor. rewrite <- pullOutR. reflexivity.
      inv H2; constructor. }
     {rewrite pullOutR. econstructor. eapply SPut; eauto. unfoldTac. 
      rewrite <- pullOutR. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SPut; eauto. unfoldTac. 
      rewrite <- pullOutR. constructor. rewrite <- pullOutR. reflexivity. 
      inv H2; constructor. }
     {rewrite pullOutR. econstructor. eapply SNew; eauto. unfoldTac. 
      rewrite <- pullOutR. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SNew; eauto. unfoldTac. 
      rewrite <- pullOutR. constructor. rewrite <- pullOutR. reflexivity.
      inv H2; constructor. }
     {rewrite pullOutR. econstructor. eapply SSpec. unfoldTac. rewrite <- UnionSwapR. 
      rewrite couple_swap. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SSpec; eauto. unfoldTac.
      rewrite <- UnionSwapR. rewrite couple_swap. constructor. 
      rewrite <- UnionSwapR. rewrite couple_swap. reflexivity. inv H2; constructor. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      takeTStep. constructor.  rewrite H5. unfoldTac. rewrite couple_swap. 
      rewrite coupleUnion.  rewrite Union_associative. repeat rewrite UnionSubtract. 
      rewrite <- Union_associative. rewrite <- Union_associative. 
      rewrite <- Union_associative. 
      rewrite (Union_associative thread (Single(n::tid,locked s',[],N))).
      rewrite <- coupleUnion. rewrite couple_swap. rewrite Union_associative. 
      rewrite UnionSwap. rewrite <- Union_associative. reflexivity. intros c. 
      invertListNeq. }
    }
  }
Qed. 

















