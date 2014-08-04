Require Import SfLib.            
Require Import NonSpec.   
Require Import Spec.  
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import hetList. 
Require Import Coq.Program.Equality. 
Require Import unspec. 
Require Import sets. 
Require Import classifiedStep. 
Require Import Coq.Sets.Powerset_facts.  
Require Import Heap.    
Require Import IndependenceCommon. 

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
  intros. copy H2. unfoldTac. flipCouplesIn H1. repeat rewrite coupleUnion in H1. 
  repeat rewrite <- Union_associative in H1. eapply specCatchupL in H1; eauto; simpl; auto.
  invertHyp. eapply ind in H3; eauto. invertHyp. unfoldTac.
  repeat rewrite Union_associative in *. repeat rewrite <- coupleUnion in *. flipCouplesIn H1. 
  flipCouplesIn H4. split. eauto. eauto. 
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
  {startIndCase. eqIn H1. inv H2. 
   {copy H4. takeTStep; eauto. eapply IHspec_multistep; eauto. clear H2. proveUnionEq x. }
   {inv H4. apply UnionEqTID in x. invertHyp. inv H; unfoldTac; invertHyp; invThreadEq. 
    {econstructor. eapply SBasicStep; eauto. constructor. eapply IHspec_multistep; eauto. }
    {econstructor. eapply SFork; eauto. unfoldTac. rewrite couple_swap. 
     rewrite coupleUnion. rewrite <- Union_associative. eapply IHspec_multistep; eauto. 
     rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     simpl. rewrite plus_0_r. reflexivity. }
    {econstructor. eapply SGet; eauto. eapply IHspec_multistep; eauto. reflexivity. }
    {econstructor. eapply SPut; eauto. eapply IHspec_multistep; eauto. reflexivity. }
    {econstructor. eapply SNew; eauto. eapply IHspec_multistep; eauto. reflexivity. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite couple_swap. 
     rewrite coupleUnion. rewrite <- Union_associative. eapply IHspec_multistep; eauto. 
     rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. reflexivity. }
   }
  }
Qed. 

Theorem specSimActSteps : forall H T H' T' H'' T'' z tid s a s' s2 S1 S2 y M M' tid' b N N' x x',
      eraseTrm(S1++[a]) z x -> 
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[b],s2,x)(tid',locked nil,nil,x')))
                     H (tUnion T(tCouple(tid,unlocked (s++[b]),s2,M)(tid',locked s',nil,N))) -> 
      spec_multistep H (tUnion T(tCouple(tid,unlocked (s++[b]),s2,M)(tid',locked s',nil,N)))
                     H' (tUnion T'(tCouple(tid,unlocked(S1++[a]++[b]),s2,M')(tid',locked(S2),nil,N'))) ->
      spec_multistep H (tUnion T(tCouple(tid,unlocked s,b::s2,M)(tid',specStack s' y,nil,N)))
                     H' (tUnion T'(tCouple(tid,unlocked(S1++[a]),b::s2,M')(tid',specStack (S2) y,nil,N'))).
Proof.
  intros. dependent induction H2; intros. 
  {unfoldTac. repeat rewrite coupleUnion in *. repeat rewrite <- Union_associative in *. 
   apply UnionEqTID in x. invertHyp. apply UnionEqTID in H. invertHyp. 
   inv H. inv H3. replace[a;b] with([a]++[b]) in H6. rewrite app_assoc in H6. 
   apply app_inj_tail in H6. invertHyp. inv H0; constructor. auto . }
  {startIndCase. eqIn H3. inv H4. 
   {copy H6. takeTStep. eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
    clear H4. takeTStep. rewrite subtractSingle. constructor. apply UnionSingletonCoupleEq in x. 
    rewrite x. unfoldTac. rewrite UnionSwap. auto. auto. }
   {inv H6. 
    {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x.
     rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. 
     inversion H; unfoldTac; invertHyp; invThreadEq.  
     {copy H1. rewrite couple_swap in H1. rewrite coupleUnion in H1. rewrite couple_swap in H1. 
      rewrite coupleUnion in H1. repeat rewrite <- Union_associative in H1. eapply stackNonNil in H1. 
      Focus 2. eauto. destruct s. exfalso; apply H1; auto. rewrite pullOutL. econstructor. 
      eapply SBasicStep; eauto. constructor. unfoldTac. rewrite <- pullOutL.
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. rewrite pullOutL. 
      econstructor. eapply SBasicStep; eauto. unfoldTac. rewrite <- pullOutL. constructor. 
      rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. auto. intros c. 
      subst. apply eraseTrmApp in H0. inv H0; inv H9; falseDecomp. }
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
     {rewrite pullOutR. econstructor. eapply SBasicStep; eauto. constructor. 
      unfoldTac. rewrite <- pullOutR. eapply IHspec_multistep; eauto.
      eapply spec_multi_trans. eassumption. rewrite pullOutR. econstructor. 
      eapply SBasicStep; eauto. unfoldTac. rewrite <- pullOutR. constructor. 
      rewrite Union_associative. rewrite <- coupleUnion. auto. }
     {rewrite pullOutR. econstructor.
      eapply SFork with(n:=plus(numForks (locked s')) (numForks' [])); eauto.  
      simpl. unfoldTac. rewrite <- UnionSwapR. rewrite couple_swap. eapply IHspec_multistep; eauto. 
      eapply spec_multi_trans.  eassumption. rewrite pullOutR. econstructor. eapply SFork; eauto. 
      unfoldTac. rewrite <- UnionSwapR. rewrite couple_swap. simpl. rewrite plus_0_r. constructor. 
      rewrite <- UnionSwapR. rewrite couple_swap. simpl. rewrite plus_0_r. reflexivity. }
     {rewrite pullOutR. econstructor. eapply SGet; eauto. unfoldTac. rewrite <- pullOutR. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutR. econstructor. eapply SGet; eauto. unfoldTac. rewrite <- pullOutR. 
      constructor. rewrite <- pullOutR. reflexivity. }
     {rewrite pullOutR. econstructor. eapply SPut; eauto. unfoldTac. rewrite <- pullOutR. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutR. econstructor. eapply SPut; eauto. unfoldTac. rewrite <- pullOutR. 
      constructor. rewrite <- pullOutR. reflexivity. }
     {rewrite pullOutR. econstructor. eapply SNew; eauto. unfoldTac. rewrite <- pullOutR. 
      eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
      rewrite pullOutR. econstructor. eapply SNew; eauto. unfoldTac. rewrite <- pullOutR. 
      constructor. rewrite <- pullOutR. reflexivity. }
     {rewrite pullOutR. econstructor. eapply SSpec.  unfoldTac. rewrite <- UnionSwapR. 
      rewrite couple_swap. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
      eassumption. rewrite pullOutR. econstructor. eapply SSpec; eauto. unfoldTac.
      rewrite <- UnionSwapR. rewrite couple_swap. constructor. 
      rewrite <- UnionSwapR. rewrite couple_swap. reflexivity. }
    }
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
   {startIndCase. eqIn H1. inv H2. 
    {takeTStep. eapply IHspec_multistep; eauto. proveUnionEq x. 
     rewrite H4. solveSet. }
    {inv H4. apply UnionEqTID in x. invertHyp. inv H; unfoldTac; invertHyp; invThreadEq. 
     {eapply IHspec_multistep; eauto. }
     {eapply monotonicActions in H0. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply InL. constructor. destruct s1; simpl in *; omega. }
     {eapply monotonicActions in H0. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply InL. constructor. destruct s1; simpl in *; omega. }
     {eapply monotonicActions in H0. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply InL. constructor. destruct s1; simpl in *; omega. }
     {eapply monotonicActions in H0. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply InL. constructor. destruct s1; simpl in *; omega. }
     {eapply monotonicActions in H0. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply InL. constructor. destruct s1; simpl in *; omega. }
    }
   }
  }
Qed. 




