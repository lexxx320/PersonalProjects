Require Import erasure. 
Require Import IndependenceCommon. 
  
Ltac solveSet := 
  unfoldTac; simpl;
  match goal with
      | |- In ?X (Union ?X ?T1 ?T2) ?x => invUnion;try solve[left; solveSet|right;solveSet]
      | |- List.In ?x (Union ?X ?T1 ?T2) => invUnion;try solve[left; solveSet|right;solveSet]
      | |- ?a \/ ?b => try solve[left; solveSet|right; solveSet]
      |_ => eauto
  end. 

Theorem nonEmptyStack' : forall H H' tid s1 S' s1' a s2 M M' T S T',
                 spec_multistep H T H' T' -> tIn T (tid,s1,s2,M) -> 
                 tIn T' (tid,s1',s2,M') ->
                 stackList s1 = S ++ [a] -> stackList s1' = S' -> 
                 exists s, S' = s ++ [a]. 
Proof.
  intros. genDeps{s1';s1;s2;a;M;M';tid;S';S}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,s1,s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,s1',s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. invThreadEq.
   destruct s1; simpl in *; subst; eauto. }
  {unfoldTac. invUnion. inv H1. 
   {eapply IHspec_multistep; eauto. solveSet. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H5. inv H1. 
    {eapply IHspec_multistep; eauto. solveSet. }
    {eapply IHspec_multistep in H2. Focus 2. solveSet. Focus 3. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons;  auto. }
    {eapply IHspec_multistep in H2. Focus 2. solveSet. Focus 3. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons;  auto. }
    {eapply IHspec_multistep in H2. Focus 2. solveSet. Focus 3. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons;  auto. }
    {eapply IHspec_multistep in H2. Focus 2. solveSet. Focus 3. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons;  auto. }
    {eapply IHspec_multistep in H2. Focus 2. solveSet. Focus 3. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons;  auto. }
    {inv H. }
   }
  }
Qed. 

Ltac nonEmptyStack'Tac H :=
  eapply nonEmptyStack' in H;[idtac|solveSet|solveSet|
                                    rewrite app_nil_l;simpl;auto|auto]. 

Theorem pureStepsDiffHeap : forall H H' tid s1 s2 M M',
                              spec_multistep H (tSingleton(tid,s1,s2,M)) H (tSingleton(tid,s1,s2,M')) ->
                              spec_multistep H' (tSingleton(tid,s1,s2,M)) H' (tSingleton(tid,s1,s2,M')).
Proof. 
  intros. dependent induction H0; unfoldTac. 
  {constructor. }
  {copy H. apply specStepSingleton in H1. invertHyp. copy x. 
   apply UnionEqSingleton in x. invertHyp. rewrite <- union_empty_l at 1. inv H. 
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
   {apply UnionEqTID in x. invertHyp. rewrite <- union_empty_l at 1. inv H.
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
    apply UnionNeqTID in x. invertHyp. rewrite H1. unfoldTac. rewrite UnionSwap. 
    eauto. auto. }
  }
Qed. 

Theorem ind2 : forall H H' T T' tid s1 s2 M M',
                spec_multistep H (tUnion T(tSingleton(tid,s1,s2,M))) 
                               H' (tUnion T'(tSingleton(tid,s1,s2,M'))) -> 
                spec_multistep H T H' T'. 
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {startIndCase. destructThread x0. exMid H6 tid. 
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
   {apply UnionNeqTID in x. invertHyp. takeTStep. econstructor. 
    eapply specStepChangeUnused. eauto. eapply IHspec_multistep; eauto. 
    rewrite H1. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap; eauto. auto. }
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

Theorem specCatchupL : forall a H T H' T' S S' tid s1 M M' M'' s2,
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
   destruct s1; inv H0; try invertListNeq; inv H2; try invertListNeq;
   repeat econstructor. }
  {startIndCase. destructThread x0. exMid tid H9. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {eapply IHspec_multistep in H0. Focus 2. eauto. Focus 2. eauto. Focus 2. 
     auto. Focus 2. auto. invertHyp. econstructor. econstructor. split. econstructor. 
     eapply SBasicStep; eauto. eauto. eauto. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. Focus 2. eauto. subst. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor.
     eapply SFork; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. Focus 2. eauto. subst. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor.
     eapply SGet; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. Focus 2. eauto. subst. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor.
     eapply SPut; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. Focus 2. eauto. subst. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor.
     eapply SNew; eauto. eassumption. }
    {copy H3. nonEmptyStackTac H3. Focus 2. destruct S; simpl in *; subst; auto. 
     invertHyp. Focus 2. eauto. subst. apply eraseTrmApp in H2. inv H2. 
     econstructor; econstructor. split. constructor. econstructor.
     eapply SSpec; eauto. eassumption. }
   }
   {apply UnionNeqTID in x. invertHyp. eapply IHspec_multistep in H0; eauto. 
    invertHyp. econstructor. econstructor. split. takeTStep. eauto. eauto. 
    rewrite H4. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap; eauto. auto. }
  }
Qed. 

Theorem specCatchup' : forall H T H' T' x tid s1' tid' s1'' a s2 e1 e1' e2 e2',
    eraseTrm s1' e1' x -> 
    spec_multistep H (tUnion T (tCouple(tid,unlocked[a], s2, e1)
                                       (tid',locked nil,nil,e2)))
                   H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (tid',locked s1'',nil,e2'))) -> 
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,e1)
                                         (tid',locked nil,nil,e2)))
                     H (tUnion T (tCouple(tid,unlocked[a],s2,x)
                                             (tid',locked nil,nil,e2))) /\
      spec_multistep H (tUnion T (tCouple(tid,unlocked[a],s2,x)
                                             (tid',locked nil,nil,e2)))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[a]),s2,e1')
                                         (tid',locked s1'',nil,e2'))).
Proof.
  intros. unfoldTac. flipCouplesIn H1. repeat rewrite coupleUnion in H1. 
  repeat rewrite Union_associative in H1.
  eapply specCatchupL in H1; eauto; simpl; auto.
  invertHyp. eapply ind in H3; eauto. invertHyp. unfoldTac.
  repeat rewrite <- Union_associative in *. repeat rewrite <- coupleUnion in *. 
  flipCouplesIn H1. flipCouplesIn H4. split. eauto. eauto. 
Qed. 

Inductive stackLists : actionStack -> list action -> actionStack -> list action -> Prop :=
|stacksL : forall s1 s2, stackLists(locked s1) s1 (locked s2) s2
|stacksU : forall s1 s2, stackLists(unlocked s1) s1 (unlocked s2) s2
|stacksS : forall s1 s2 N, stackLists(specStack s1 N) s1 (specStack s2 N) s2.  

Theorem simSpecStackSteps : forall H T H' T' tid s s' M M' N,
      spec_multistep H (tUnion T(tSingleton(tid,locked s,nil,M)))
                     H' (tUnion T'(tSingleton(tid,locked(s'),nil,M'))) ->
      spec_multistep H (tUnion T(tSingleton(tid, specStack s N,nil,M)))
                     H' (tUnion T'(tSingleton(tid,specStack (s') N,nil,M'))). 
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. inv H. constructor. }
  {startIndCase. destructThread x0. exMid H6 tid. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {econstructor. eapply SBasicStep; eauto. constructor. 
     eapply IHspec_multistep; eauto. }
    {econstructor. eapply SFork; eauto. unfoldTac. rewrite couple_swap. 
     rewrite coupleUnion. rewrite Union_associative. eapply IHspec_multistep; eauto. 
     rewrite <- Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     simpl. rewrite plus_0_r. reflexivity. }
    {econstructor. eapply SGet; eauto. eapply IHspec_multistep; eauto. reflexivity. }
    {econstructor. eapply SPut; eauto. eapply IHspec_multistep; eauto. reflexivity. }
    {econstructor. eapply SNew; eauto. eapply IHspec_multistep; eauto. reflexivity. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite couple_swap. 
     rewrite coupleUnion. rewrite Union_associative. eapply IHspec_multistep; eauto. 
     rewrite <- Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     reflexivity. }
   }
   {apply UnionNeqTID in x. invertHyp. takeTStep; eauto. 
    eapply IHspec_multistep; eauto. rewrite H1. rewrite UnionSubtract. 
    unfoldTac. rewrite UnionSwap. eauto. auto. }
  }
Qed. 

Theorem specSimActSteps : forall H T H' T' H'' T'' z tid s a s' s2 S1 S2 y M M' n b N N' x x',
      eraseTrm(S1++[a]) z x -> 
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[b],s2,x)(n::tid,locked nil,nil,x')))
                     H (tUnion T(tCouple(tid,unlocked (s++[b]),s2,M)(n::tid,locked s',nil,N))) -> 
      spec_multistep H (tUnion T(tCouple(tid,unlocked (s++[b]),s2,M)(n::tid,locked s',nil,N)))
                     H' (tUnion T'(tCouple(tid,unlocked(S1++[a]++[b]),s2,M')(n::tid,locked(S2),nil,N'))) ->
      spec_multistep H (tUnion T(tCouple(tid,unlocked s,b::s2,M)(n::tid,specStack s' y,nil,N)))
                     H' (tUnion T'(tCouple(tid,unlocked(S1++[a]),b::s2,M')(n::tid,specStack (S2) y,nil,N'))).
Proof.
  intros. dependent induction H2; intros. 
  {unfoldTac. repeat rewrite coupleUnion in *.
   repeat rewrite Union_associative in *. 
   apply UnionEqTID in x. invertHyp. apply UnionEqTID in H. invertHyp. 
   inv H. apply app_inj_tail in H6. invertHyp. inv H3. apply eraseTrmApp in H0. 
   inv H0; constructor. }
  {startIndCase. destructThread x1. exMid H8 tid. 
   {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x.
    rewrite Union_associative in x. apply UnionEqTID in x. invertHyp. inv H. 
    {copy H1. rewrite couple_swap in H1. rewrite coupleUnion in H1. 
     rewrite couple_swap in H1. rewrite coupleUnion in H1. 
     repeat rewrite Union_associative in H1. eapply stackNonNil in H1. 
     Focus 2. eauto. destruct s. exfalso; apply H1; auto. rewrite pullOutL. 
     econstructor. eapply SBasicStep; eauto. constructor. unfoldTac. 
     rewrite <- pullOutL. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
     eassumption. rewrite pullOutL. econstructor. eapply SBasicStep; eauto. unfoldTac.
     rewrite <- pullOutL. constructor. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. auto. intros c. subst. 
     apply eraseTrmApp in H0. inv H0; inv H12; falseDecomp. }
    {rewrite pullOutL. econstructor.
     eapply SFork with(n:=plus(numForks (unlocked (s ++ [b]))) (numForks' s2)); eauto.
     simpl. rewrite numForksDistribute. simpl.
     destruct b; rewrite <- plus_assoc; auto. unfoldTac. rewrite <- UnionSwapR. 
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
     rewrite pullOutL. econstructor. eapply SFork; eauto. unfoldTac.
      rewrite <- UnionSwapR. constructor. rewrite <- UnionSwapR. reflexivity. }
     {rewrite pullOutL. econstructor. eapply SGet; eauto. unfoldTac. 
      rewrite <- pullOutL. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutL. econstructor. eapply SGet; eauto. unfoldTac. 
      rewrite <- pullOutL.  constructor. rewrite <- pullOutL. reflexivity. }
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
    {exMid (n::tid) H8. 
     {unfoldTac. rewrite coupleUnion in x. rewrite Union_associative in x.
      apply UnionEqTID in x. invertHyp. inv H. 
      {rewrite pullOutR. econstructor. eapply SBasicStep; eauto. constructor. 
       unfoldTac. rewrite <- pullOutR. eapply IHspec_multistep; eauto.
       eapply spec_multi_trans. eassumption. rewrite pullOutR. econstructor. 
       eapply SBasicStep; eauto. unfoldTac. rewrite <- pullOutR. constructor. 
       rewrite <- Union_associative. rewrite <- coupleUnion. auto. }
      {rewrite pullOutR. econstructor.
       eapply SFork with(n:=plus(numForks (locked s')) (numForks' [])); eauto.  
       simpl. unfoldTac. rewrite <- UnionSwapR. rewrite couple_swap. 
       eapply IHspec_multistep; eauto. eapply spec_multi_trans.  eassumption. 
       rewrite pullOutR. econstructor. eapply SFork; eauto. unfoldTac. 
       rewrite <- UnionSwapR. rewrite couple_swap. simpl. rewrite plus_0_r. 
       constructor. rewrite <- UnionSwapR. rewrite couple_swap. simpl. 
       rewrite plus_0_r. reflexivity. }
     {rewrite pullOutR. econstructor. eapply SGet; eauto. unfoldTac. 
      rewrite <- pullOutR. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SGet; eauto. unfoldTac. 
      rewrite <- pullOutR. constructor. rewrite <- pullOutR. reflexivity. }
     {rewrite pullOutR. econstructor. eapply SPut; eauto. unfoldTac. 
      rewrite <- pullOutR. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SPut; eauto. unfoldTac. 
      rewrite <- pullOutR. constructor. rewrite <- pullOutR. reflexivity. }
     {rewrite pullOutR. econstructor. eapply SNew; eauto. unfoldTac. 
      rewrite <- pullOutR. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SNew; eauto. unfoldTac. 
      rewrite <- pullOutR. constructor. rewrite <- pullOutR. reflexivity. }
     {rewrite pullOutR. econstructor. eapply SSpec. unfoldTac. rewrite <- UnionSwapR. 
      rewrite couple_swap. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SSpec; eauto. unfoldTac.
      rewrite <- UnionSwapR. rewrite couple_swap. constructor. 
      rewrite <- UnionSwapR. rewrite couple_swap. reflexivity. }
     }
     {apply UnionCoupleNeqTID in x. invertHyp. takeTStep. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      takeTStep. constructor. rewrite H3. unfoldTac. rewrite couple_swap. 
      rewrite coupleUnion.  rewrite Union_associative. repeat rewrite UnionSubtract. 
      rewrite <- Union_associative. rewrite <- Union_associative. 
      rewrite <- Union_associative. 
      rewrite (Union_associative thread (tSingleton(n::tid,locked s',[],N))).
      rewrite <- coupleUnion. rewrite couple_swap. rewrite Union_associative. 
      rewrite UnionSwap. rewrite <- Union_associative. reflexivity. auto. auto.
      intros c. invertListNeq. }
    }
  }
Qed. 

Theorem smultiWithoutPure : forall H T H' T' tid s1 s2 M M', 
                              spec_multistep H (tUnion T(tSingleton(tid,s1,s2,M)))
                                             H' (tUnion T'(tSingleton(tid,s1,s2,M'))) ->
                              spec_multistep H T H' T'. 
Proof.
  intros.  
  {dependent induction H0. 
   {apply UnionEqTID in x. invertHyp. constructor. }
   {startIndCase. destructThread x0. exMid tid H6. 
    {apply UnionEqTID in x. invertHyp. inv H. 
     {eapply IHspec_multistep; eauto. }
     {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
     {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
     {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
     {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
     {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
    }
    {apply UnionNeqTID in x. invertHyp. takeTStep. econstructor. 
     eapply specStepChangeUnused. eauto. eapply IHspec_multistep; eauto. 
     rewrite H1. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap. eauto. auto. }
   }
  }
Qed. 



