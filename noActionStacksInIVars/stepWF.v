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
Require Import specIndependence. 
Require Import writeIndependence. 
Require Import IndependenceCommon. 
Require Import ReadIndependence. 
Require Import newIndependence. 

Ltac eUnspec :=
  match goal with
    | |-spec_multistep ?H ?t ?H' (tUnion ?T' (tSingleton ?t')) =>
        assert(exists t'', unspecThread t' t'') by apply unspecThreadTotal; invertHyp
    | H:spec_multistep ?H ?t ?H' (tUnion ?T' (tSingleton ?t')) |- _ =>
        assert(exists t'', unspecThread t' t'') by apply unspecThreadTotal; invertHyp
  end. 

Ltac rewriteEmpty xs := 
      match xs with
          |HNil => unfold tUnion; try rewrite union_empty_l; try rewrite union_empty_r
          |HCons ?x ?xs' => unfold tUnion in x; try rewrite union_empty_l in x; 
                          try rewrite union_empty_r in x; rewriteEmpty xs'
      end. 

Theorem rollbackWF : forall H H' T TR TR' tidR acts,
                       wellFormed H (tUnion T TR) ->
                       rollback tidR acts H TR H' TR' ->
                       wellFormed H' (tUnion T TR'). 
Admitted. 

Ltac foldTac := fold Add in *; fold tAdd in *; fold tUnion in *; fold tSingleton in *; fold tCouple in *.

Ltac rUnspec := erewrite unspecSingleton; eauto.
Ltac rUnspecIn H := erewrite unspecSingleton in H; eauto.
Ltac rUnspecAll := erewrite unspecSingleton in *; eauto. 

Ltac invertDecomp :=
  match goal with
    |H:(?a,?b,?c,?d)=(?e,?f,?g,?h) |- _ => inv H
    |H:?x = ?y |- _ => solve[inv H]
    |H:decompose ?M ?E ?e,H':decompose ?M' ?E' ?e' |- _=>
     eapply uniqueCtxtDecomp in H; eauto; invertHyp
  end. 

Axiom UnionSingletonCoupleEq : forall T T' a b c, 
                 tUnion T (tSingleton a) = tUnion T' (tCouple b c) -> 
                 tIn T' a -> T = tUnion (Subtract thread T' a) (tCouple b c).

Axiom CoupleUnionAx : forall T T' t1 t2,
                        tUnion T (tSingleton t1) = tUnion T' (tCouple t1 t2) -> 
                        T = tUnion T' (tSingleton t2).

Ltac actEqTac H :=
  eapply firstActEq in H;[idtac|apply Union_intror; rewrite app_nil_l; constructor|
                          apply Union_intror; constructor]. 

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

Theorem appCons : forall (T:Type) x (y:T) z,
                    x ++ [y;z] = (x ++ [y]) ++ [z]. 
Proof. 
  intros. rewrite <- app_assoc. simpl. auto. Qed. 


Theorem forkCatchupOneDone : forall H T H' T' s1 x0 tid s1''' s1' s1'' s2 e1 e1' e2 e2' n,
    stackList s1' = nil -> eraseTrm (stackList s1''') e2' x0 -> n = numForks' s2 -> 
    spec_multistep H (tUnion T (tCouple(tid,s1, s2, e1)(n::tid,s1',nil,e2)))
                   H' (tUnion T' (tCouple(tid,s1'',s2,e1')(n::tid,s1''',nil,e2'))) -> 
    exists H'' T'',
      spec_multistep H (tUnion T (tCouple(tid,s1,s2,e1)(n::tid,s1',nil,e2)))
                     H'' (tUnion T'' (tCouple(tid,s1,s2,e1)(n::tid,s1',nil,x0))) /\
      spec_multistep H'' (tUnion T'' (tCouple(tid,s1,s2,e1)(n::tid,s1',nil,x0)))
                   H' (tUnion T' (tCouple(tid,s1'',s2,e1')(n::tid,s1''',nil,e2'))) /\
      spec_multistep H T H'' T''. 
Proof.
  intros. dependent induction H3. 
  {unfoldTac. repeat rewrite coupleUnion in x. 
   repeat rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. 
   apply UnionEqTID in H. invertHyp. destruct s1'''; 
   simpl in *; subst; inv H1; try invertListNeq; do 5 econstructor. }
  {startIndCase. eqIn H2. inv H4. 
   {eapply IHspec_multistep in H1; eauto. Focus 2. apply UnionSingletonCoupleEq in x.
    rewrite x. unfoldTac. rewrite UnionSwap. auto. auto. invertHyp. 
    econstructor. econstructor. split. takeTStep. eassumption. split; auto. 
    takeTStep. eauto. }
   {inv H6. 
    {unfoldTac. rewrite coupleUnion in x. rewrite <- Union_associative in x. 
     rewrite UnionSwap in x. apply UnionEqTID in x. invertHyp. 
     inversion H; unfoldTac; invertHyp; invThreadEq. 
     {eapply IHspec_multistep in H1;[idtac|eauto|eauto|idtac|auto]. Focus 2. 
      rewrite UnionSwap. rewrite Union_associative. rewrite <- coupleUnion. 
      auto. invertHyp. econstructor. econstructor. split. 
      repeat rewrite pullOutL in *. rewrite spec_multi_unused. 
      rewrite spec_multi_unused in H7. eassumption. split. rewrite pullOutL. 
      econstructor. eapply SBasicStep; eauto. unfoldTac. rewrite <- pullOutL. 
      eassumption. eauto. }
     {eapply IHspec_multistep in H1;[idtac|eauto|eauto|idtac|auto]. Focus 2.
      rewrite UnionSwap. rewrite pullOutL. rewrite Union_associative. 
      rewrite <- coupleUnion. auto. invertHyp. econstructor; econstructor;
      split. Admitted. 



Ltac flipCouples :=
  rewrite couple_swap; rewrite coupleUnion; try flipCouples; rewrite <- coupleUnion. 

Ltac flipCouplesIn H :=
  rewrite couple_swap in H; rewrite coupleUnion in H; try flipCouplesIn H; rewrite <- coupleUnion in H. 


Theorem forkCatchup : forall H T H' T' x x0 tid s1' s1'' s2 e1 e1' e2 e2' M' M'' n E d,
    eraseTrm s1' e1' x -> eraseTrm s1'' e2' x0 -> n = numForks' s2 -> 
    spec_multistep H (tUnion T (tCouple(tid,unlocked[fAct M' E M'' d n], s2, e1)
                                       (n::tid,locked nil,nil,e2)))
                   H' (tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) -> 
    exists H'' T'',
      spec_multistep H (tUnion T (tCouple(tid,unlocked[fAct M' E M'' d n],s2,e1)
                                         (n::tid,locked nil,nil,e2)))
                     H'' (tUnion T'' (tCouple(tid,unlocked[fAct M' E M'' d n],s2,x)
                                             (n::tid,locked nil,nil,x0))) /\
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[fAct M' E M'' d n],s2,x)
                                             (n::tid,locked nil,nil,x0)))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) /\
      spec_multistep H T H'' T''. 
Proof.
  intros. genDeps{x;x0}. dependent induction H3; intros.
  {unfoldTac. repeat rewrite coupleUnion in x. 
   repeat rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. 
   inv H3. apply UnionEqTID in H. invertHyp. inv H. destruct s1'; inv H5. 
   inv H0; try invertListNeq. inv H1; try  invertListNeq. exists h. exists T'. 
   split. constructor. split. constructor. constructor. invertListNeq. }
  {copy x. copy H. apply specStepSingleton in H4. invertHyp. copy x. unfoldSetEq x.
   assert(tIn (tUnion T0 (tSingleton x2)) x2). apply Union_intror. constructor.
   apply H5 in H7. inv H7. 
   {eapply IHspec_multistep in H0; eauto. invertHyp. exists x. exists x3. 
    split. copy H8. apply pullOut in H9. rewrite H9. unfoldTac. rewrite UnionSwap. 
    econstructor. eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap.
    eauto. split. auto. copy H8. apply pullOut in H9. rewrite H9. econstructor. 
    eapply specStepChangeUnused. eauto. auto. apply UnionSingletonCoupleEq in H2. 
    rewrite H2. unfoldTac. rewrite UnionSwap. auto. auto. }
   {inv H8. 
    {unfoldTac. rewrite coupleUnion in H2. rewrite <- Union_associative in H2.
     rewrite UnionSwap in H2. apply UnionEqTID in H2. invertHyp. 
     inv H; unfoldTac; invertHyp; invThreadEq. 
     {eapply IHspec_multistep in H0. invertHyp. exists x. exists x2. 
      split. rewrite coupleUnion. rewrite <- Union_associative. rewrite UnionSwap. 
      econstructor. eapply SBasicStep. eauto. constructor. unfoldTac. 
      rewrite <- UnionSwap. rewrite Union_associative. rewrite <- coupleUnion. 
      eauto. split. eassumption. assumption.  auto. rewrite Union_associative. 
      rewrite <- coupleUnion. rewrite couple_swap. auto. auto. auto. }
     {simpl in *. copy H3. nonEmptyStackTac H3. invertHyp. copy H0. apply eraseTrmApp in H0. 
      inv H0. rewrite UnionSwapR in H. eapply forkCatchupOneDone; eauto. unfoldTac. 
      rewrite pullOutL. econstructor. eapply SFork; eauto. unfoldTac. rewrite UnionSwapR. eassumption. }
     {simpl in *. copy H3. nonEmptyStackTac H3. invertHyp. copy H0. apply eraseTrmApp in H0. 
      inv H0. eapply forkCatchupOneDone; eauto. unfoldTac. rewrite pullOutL. econstructor. 
      eapply SGet; eauto. unfoldTac. eassumption. }
     {simpl in *. copy H3. nonEmptyStackTac H3. invertHyp. copy H0. apply eraseTrmApp in H0. 
      inv H0. eapply forkCatchupOneDone; eauto. unfoldTac. rewrite pullOutL. econstructor. 
      eapply SPut; eauto. unfoldTac. eassumption. }
     {simpl in *. copy H3. nonEmptyStackTac H3. invertHyp. copy H0. apply eraseTrmApp in H0. 
      inv H0. eapply forkCatchupOneDone; eauto. unfoldTac. rewrite pullOutL. econstructor. 
      eapply SNew; eauto. unfoldTac. eassumption. }
     {simpl in *. copy H3. nonEmptyStackTac H3. invertHyp. copy H0. apply eraseTrmApp in H0. 
      inv H0. eapply forkCatchupOneDone; eauto. unfoldTac. rewrite pullOutL. econstructor. 
      eapply SSpec; eauto. unfoldTac. eassumption. }
    } 
    {unfoldTac. rewrite coupleUnion in H2. rewrite <- Union_associative in H2. 
     apply UnionEqTID in H2. invertHyp. inv H; unfoldTac; invertHyp; invThreadEq. 
     {eapply IHspec_multistep in H0;[idtac|eauto|eauto|eauto|eauto]. Focus 2. 
      rewrite Union_associative. rewrite <- coupleUnion. auto. invertHyp. econstructor. 
      econstructor. split. rewrite pullOutR. econstructor. eapply SBasicStep; eauto. 
      unfoldTac. rewrite <- pullOutR. eauto. split. eauto. eauto. }
     {simpl in *. copy H3. rewrite couple_swap in H. eapply monotonicActions in H. 
      Focus 2. apply InL. apply Couple_r. Focus 2. apply InL. apply Couple_r. simpl in *. 
      destructLast s1''. simpl in *. omega. invertHyp. apply eraseTrmApp in H1. 
      inv H1. 

Ltac nonEmptyStackTac H :=
  try(eapply nonEmptyStack in H;[ idtac
                                | apply InL; constructor
                                | solve[solveSet]
                                | simpl; try rewrite app_nil_l; eauto   
                                | simpl; eauto]);
  try(eapply nonEmptyStack in H;[ idtac
                                | apply InL; apply Couple_r
                                | solve[solveSet]
                                | simpl; try rewrite app_nil_l; eauto   
                                | simpl; eauto]); fail. 


Theorem listTailEq : forall (T:Type) a (b:T) c d e,
                       ~List.In b c -> ~List.In b e -> a ++ [b] ++ c = d ++ b::e -> c = e. 
Proof.
  induction a; intros. 
  {simpl in *. destruct d. simpl in *. inv H1. auto. inv H1. exfalso. apply  H. 
   apply in_or_app. right. simpl. left. auto. }
  {destruct d. inv H1. exfalso. apply H0. apply in_or_app. right. 
   simpl. auto. inv H1. eapply IHa; eauto. }
Qed.   

Theorem raw_unspecHeapCommitNewFull : forall x ds t N H S,
                                   unique ivar_state S H -> 
                                   raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                   raw_unspecHeap (raw_replace x (sfull COMMIT ds SPEC t N) H) =
                                   raw_extend x (sempty COMMIT) (raw_unspecHeap H).
Proof.
  intros. apply heapExtensionality. genDeps{S; N; t; ds; x; H}. induction H; intros. 
  {inv H1. } 
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. simpl. destruct (beq_nat x0 x) eqn:eq2; auto. }
   {simpl. destruct (beq_nat x0 x) eqn:eq2; eauto.
    {destruct i0. destruct s. erewrite IHlist. rewrite eq2. auto. 
     auto. inv H0;  eauto. apply beq_nat_true in eq2. subst. simpl. rewrite eq. inv H0.
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. eauto. 
     destruct s. inv H0. eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. 
     eauto. destruct s0. apply beq_nat_true in eq2. subst. simpl. rewrite eq. inv H0. 
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. eauto. 
     simpl. apply beq_nat_true in eq2. subst. rewrite eq. inv H0. 
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. auto. }
    {destruct i0. destruct s. inv H0. eapply IHlist with(x0:=x0)in H1; eauto. 
     rewrite eq2 in H1. auto. simpl. destruct (beq_nat x0 i)eqn:eq3; auto. 
     inv H0. eapply IHlist with(x0:=x0)in H1. rewrite eq2 in H1. auto. eauto.
     destruct s. inv H0. eapply IHlist with(x0:=x0) in H1. rewrite eq2 in H1. auto. 
     eauto. destruct s0. simpl. destruct (beq_nat x0 i) eqn:eq3; auto. 
     eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. auto. inv H0; eauto. 
     simpl. destruct (beq_nat x0 i); auto. eapply IHlist with(x0:=x0) in H1. 
     rewrite eq2 in H1. auto. inv H0; eauto. }
   }
  }
Qed.
 
Theorem unspecHeapCommitNewFull : forall x ds t N H p,
                                   heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                   unspecHeap (replace x (sfull COMMIT ds SPEC t N) H) =
                                   extend x (sempty COMMIT) (unspecHeap H) p.
Proof.
  intros. destruct H. simpl in *. apply rawHeapsEq. eapply raw_unspecHeapCommitNewFull; eauto. 
Qed.
 
Theorem raw_eraseHeapCommitNewEmpty : forall x S H,
                                   unique ivar_state S H -> 
                                   raw_heap_lookup x H = Some(sempty SPEC) ->
                                   raw_unspecHeap (raw_replace x (sempty COMMIT) H) =
                                   raw_extend x (sempty COMMIT) (raw_unspecHeap H).
Proof.
  intros. apply heapExtensionality. genDeps{S; x; H}. induction H; intros. 
  {inv H1. }
  {simpl in H1. simpl. destruct a. destruct (beq_nat x i)eqn:eq. 
   {inv H1. destruct (beq_nat x0 x) eqn:eq2. simpl. rewrite eq2. auto. simpl. rewrite eq2. 
    auto. }
   {simpl. destruct i0. 
    {destruct s. 
     {destruct (beq_nat x0 x) eqn:eq2. 
      {simpl in *. inv H0. eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. 
       auto. }
      {erewrite IHlist. simpl. rewrite eq2. auto. eauto. inv H0; eauto. }
     }
     {simpl. destruct(beq_nat x0 i)eqn:eq2. 
      {apply beq_nat_true in eq2. subst. rewrite beq_nat_sym in eq. rewrite eq. auto. }
      {destruct(beq_nat x0 x) eqn:eq3.
       {eapply IHlist with(x0:=x0) in H1. simpl in *. rewrite eq3 in H1. auto. inv H0; eauto. }
       {erewrite IHlist; eauto. simpl. rewrite eq3. auto. inv H0; eauto. }
      }
     }
    }
    {destruct s. 
     {destruct (beq_nat x0 x)eqn:eq2. 
      {eapply IHlist with(x0:=x0) in H1. simpl in *. rewrite eq2 in H1. auto. inv H0; eauto. }
      {erewrite IHlist; eauto. simpl. rewrite eq2. auto. inv H0; eauto. }
     }
     {destruct s0. 
      {destruct (beq_nat x0 x) eqn:eq2. 
       {simpl. apply beq_nat_true in eq2. subst. rewrite eq.
        eapply IHlist with(x0:=x) in H1; eauto. simpl in *. rewrite <- beq_nat_refl in H1. auto. 
        inv H0; eauto. }
       {simpl. destruct (beq_nat x0 i); auto. erewrite IHlist; eauto. simpl. rewrite eq2. auto. 
        inv H0; eauto. }
      }
      {simpl. destruct (beq_nat x0 i) eqn:eq2. 
       {apply beq_nat_true in eq2. subst. rewrite beq_nat_sym in eq. rewrite eq. auto. }
       {destruct (beq_nat x0 x) eqn:eq3. 
        {simpl in *. eapply IHlist with(x0:=x0) in H1. rewrite eq3 in H1. eauto. inv H0; eauto. }
        {erewrite IHlist; eauto. simpl. rewrite eq3. auto. inv H0; eauto. }
       }
      }
     }
    }
   }
  }
Qed. 

Theorem eraseHeapCommitNewEmpty : forall x H p,
                                   heap_lookup x H = Some(sempty SPEC) ->
                                   unspecHeap (replace x (sempty COMMIT) H) =
                                   extend x (sempty COMMIT) (unspecHeap H) p.
Proof.
  intros. destruct H. simpl in *. apply rawHeapsEq. eapply raw_eraseHeapCommitNewEmpty; eauto. 
Qed.

Theorem uniqueLookupNone : forall (T:Type) x H S, 
                            unique T S H -> In (AST.id) S x ->
                            raw_heap_lookup x H = None. 
Proof.
  induction H; intros. 
  {auto. }
  {inv H0. simpl. assert(x <> m). intros c. subst. contradiction.
   apply beq_nat_false_iff in H0. rewrite H0. eapply IHlist; eauto.
   constructor. auto. }
Qed. 

Theorem raw_lookupCreatedSpec : forall x H ds t0 N s S,
                                  unique ivar_state S H -> 
                                  (raw_heap_lookup x H = Some(sempty SPEC) \/
                                  raw_heap_lookup x H = Some(sfull SPEC ds s t0 N)) ->
                                  raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof. 
  induction H; intros. 
  {inv H0; inv H1. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. inv H1; inv H0; apply unspecUnique in H7; eapply uniqueLookupNone; eauto;
    apply beq_nat_true in eq; subst; apply Union_intror; constructor. }
   {inv H0. destruct i0. destruct s0. eauto. simpl. rewrite eq. eauto. 
    destruct s0; eauto. destruct s1; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupCreatedSpec : forall x H ds t0 N s,
                                  (heap_lookup x H = Some(sempty SPEC) \/
                                  heap_lookup x H = Some(sfull SPEC ds s t0 N)) ->
                                  heap_lookup x (unspecHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupCreatedSpec; eauto. 
Qed. 

Theorem stepWF : forall H T t H' t', 
                   wellFormed H (tUnion T t) -> step H T t (OK H' T t') ->
                   wellFormed H' (tUnion T t'). 
Proof.
  intros. inversion H1; subst.      
  {destruct s1.  
   {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. 
    rUnspecAll. unfoldTac. rewrite union_empty_r in *. eapply spec_multi_trans; eauto. 
    econstructor. eapply SBasicStep. eauto. constructor. constructor. } 
   {destruct l. 
    {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. rUnspecAll. 
     apply spec_multi_unused in H3. rewrite spec_multi_unused. auto. }
    {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SBasicStep; eauto. constructor. constructor. 
    uCons a l. eapply unspecTwoActs. eauto. }
   }
   {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. rUnspecAll. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SBasicStep; eauto.
    constructor. constructor. }
  }
  {inv H0. inv H2. econstructor; eauto. destruct s1.
   {simpl. unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans.
    eassumption. econstructor. eapply SFork. auto. rewrite <- coupleUnion. simpl. constructor. }
   {destruct l. 
    {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
     erewrite unspecSingleton;try unspecThreadTac; auto. erewrite unspecSingleton; eauto. 
     unfold tUnion. rewrite union_empty_r. eapply spec_multi_trans. copy d. apply decomposeEq in H. subst. 
     erewrite unspecSingleton in H3; eauto. copy d. apply decomposeEq in H. rewrite <- H.  
     econstructor. auto. unfold tUnion. eapply SFork; eauto. rewrite <- coupleUnion. unfoldTac. 
     constructor. simpl. copy d. apply decomposeEq in H; subst. eapply unspecFork.
     rewrite app_nil_l. auto. }
   {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    assert(exists t', unspecThread (tid, unlocked(a :: l), s2, t0) t'). 
    apply unspecThreadTotal. invertHyp. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton; eauto. unfold tUnion. rewrite union_empty_r. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. 
    econstructor. eapply SFork. auto. rewrite <- coupleUnion. constructor. uCons a l.
    rewrite unspecTwoActs'. eauto. }
   }
   {simpl. unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans.
    eassumption. econstructor. eapply SFork. auto. rewrite <- coupleUnion. constructor. }
  }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapRBRead; eauto. destruct s1.  
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. unfoldTac. rewrite union_empty_r in *. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. constructor. }
   {destruct l.
    {unfoldTac. rewrite unspecUnionComm in *. simpl. rUnspecAll. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SGet; eauto. constructor. eapply unspecRead. 
     rewrite app_nil_l. auto. }
   {rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4. Focus 2. uCons a l. rewrite <- unspecTwoActs'. eauto. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. constructor. }
   }
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. constructor. }
  }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapAddWrite; eauto. destruct s1.  
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. unfoldTac. rewrite union_empty_r in *. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. constructor. }
   {destruct l. 
    {unfold tUnion in *. rewrite unspecUnionComm in *. simpl. rUnspecAll. Focus 2. 
     unspecThreadTac. rewrite app_nil_l; auto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SPut; eauto. constructor. }
    {rewrite unspecUnionComm in *. eUnspec. rUnspecAll. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SPut; eauto. constructor. uCons a l.
     rewrite <- unspecTwoActs'. eauto. uCons a l. rewrite <- unspecTwoActs'; eauto. }
   }
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SPut; eauto. constructor. }
  }   
  {copy H5. unfoldTac. rewrite <- Union_associative in H0. rewrite wfFrame in H0. 
   eapply rollbackWF in H7; eauto. Focus 2. unfold commitPool. intros. inv H3; auto.
   econstructor; eauto. uCons (wAct x t0 E N d) (@nil action). rewrite unspecHeapAddWrite; auto.
   inv H7. inv H8. rewrite unspecUnionComm in H9. repeat rewrite unspecUnionComm. simpl. 
   erewrite unspecSingleton. Focus 2. unspecThreadTac. rewrite app_nil_l. auto. 
   unfoldTac. rewrite <- Union_associative. rewrite <- spec_multi_unused in H9. 
   eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. 
   simpl. rewrite <- Union_associative. constructor. }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapExtend; eauto. destruct s1. 
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. unfoldTac. rewrite union_empty_r in *. 
    eapply spec_multi_trans. eassumption. copy d. apply decomposeEq in H0; subst. 
    econstructor. eapply SNew; eauto. constructor. }
   {destruct l. 
    {unfold tUnion in *. rewrite unspecUnionComm in *. simpl. rUnspecAll. Focus 2. 
     unspecThreadTac. rewrite app_nil_l; auto. copy d. apply decomposeEq in H0; subst. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. constructor. }
    {copy d. apply decomposeEq in H0; subst. rewrite unspecUnionComm in *. eUnspec. 
     rUnspecAll. eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. 
     constructor. uCons a l. rewrite <- unspecTwoActs'. eauto. uCons a l. 
     rewrite <- unspecTwoActs'; eauto. }
   }
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. 
    eapply spec_multi_trans. eassumption. copy d. apply decomposeEq in H0; subst. 
    econstructor. eapply SNew; eauto. constructor. }
  }   
  {inv H0. inv H2. econstructor; eauto. destruct s1.  
   {unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. simpl. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SSpec; eauto. rewrite <- coupleUnion. constructor. }
   {destruct l.
    {unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
     erewrite unspecSingleton. Focus 2. eapply unspecSpecret. rewrite app_nil_l. simpl. auto. 
     copy d. apply decomposeEq in H. subst. auto. erewrite unspecSingleton; eauto. unfoldTac. 
     rewrite union_empty_r.  erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SSpec; eauto. unfold tUnion. rewrite <- coupleUnion. 
     constructor. }
    {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. foldTac. eUnspec. 
     erewrite unspecSingleton in H3; eauto. repeat erewrite unspecSingleton; eauto. unfoldTac. 
     rewrite union_empty_r. eapply spec_multi_trans. eassumption. econstructor. eapply SSpec. 
     rewrite <- coupleUnion. constructor. uCons a l. rewrite unspecTwoActs'. eauto. }
   }
   {unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. simpl. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SSpec; eauto. rewrite <- coupleUnion. constructor. }
  }  
  {inv H0. inv H2. econstructor; eauto. unfoldTac. rewrite couple_swap in H3. 
   rewrite coupleUnion in H3. repeat rewrite unspecUnionComm in *. 
   erewrite unspecSingleton in H3; eauto. erewrite unspecSingleton in H3; eauto. 
   unfoldTac. repeat rewrite <- Union_associative in H3. rewrite spec_multi_unused in H3. 
   destructLast s1. 
   {simpl. erewrite unspecSingleton; eauto. rewrite spec_multi_unused. unfoldTac. 
    eapply simSpecJoin in H3. eauto. }
   {invertHyp. eraseTrmTac (x0++[x]) M. copy H0. 
    eapply wrapEraseTrm with(N:=N1)(E:=E)(N':=(specRun(ret N1) N0))in H0.
    erewrite unspecSingleton. Focus 2. apply unspecEraseTrm; eauto.
    eapply specFastForward in H3; eauto. invertHyp. eapply spec_multi_trans. 
    eapply simTSteps in H2. eassumption. eapply simSpecJoin' in H4. simpl in *.
    eauto. eauto. constructor. introsInv. }
  }
  {copy H13. unfoldTac. rewrite <- Union_associative. rewrite wfFrame. Focus 2. 
   unfold commitPool. intros. inv H3. auto. rewrite <- Union_associative in H0. 
   rewrite wfFrame in H0. Focus 2. unfold commitPool; intros. inv H3. auto.
   eapply rollbackWF; eauto. }
  {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. rUnspecAll. 
   rewrite spec_multi_unused in H3. rewrite spec_multi_unused. auto. }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapRBRead; eauto. 
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. unspecThreadTac. 
   auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2. apply unspecEraseTrm; eauto. 
   eapply readFastForward in H4. Focus 2. eapply unspecHeapLookupFull; eauto. Focus 2. eauto. 
   Focus 2. intros c. inv c. invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. 
   eassumption. copy H3. eapply monotonicReaders in H3; eauto. invertHyp.
   apply listTailEq in H9; auto. subst.  eapply readSimPureSteps in H7; eauto. Focus 2. 
   rewrite app_nil_l. simpl. eassumption. invertHyp. eapply spec_multi_trans.
   rewrite spec_multi_unused. eassumption. destructLast s1'. 
   {inv H2; try solve[invertListNeq]. rewrite spec_multi_unused. rewrite spec_multi_unused in H7. 
    eapply stepWithoutReader; eauto. }
   {invertHyp. eapply readSimActionSteps; eauto. constructor. simpl. rewrite <- app_assoc in H7. 
    simpl in *. auto. }
  }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapCommitCreateFull; eauto.
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. unspecThreadTac. 
   auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2.  apply unspecEraseTrm; eauto.
   eapply writeFastForward in H4; eauto. Focus 2. eapply lookupUnspecEmpty; eauto.
   invertHyp. eapply spec_multi_trans. eapply spec_multi_unused. eassumption. 
   eapply writeSimPureSteps in H3; eauto. invertHyp. eapply spec_multi_trans. 
   rewrite spec_multi_unused. eassumption. destructLast s1'. 
   {simpl in *. inv H2; try solve[invertListNeq]. eapply helper; eauto. rewrite spec_multi_unused. 
    rewrite spec_multi_unused in H3. assumption. }
   {invertHyp. eapply writeSimActionSteps; eauto. eauto. constructor. simpl. rewrite <- app_assoc in H3. 
    simpl in *. assumption. }
  }                   
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapCommitNewFull; eauto. 
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. 
   unspecThreadTac. auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2. 
   apply unspecEraseTrm; eauto. eapply newFastForward in H4; eauto. Focus 2. 
   eapply lookupCreatedSpec; eauto. invertHyp. eapply spec_multi_trans.
   rewrite spec_multi_unused. eassumption. eapply newSimPureStepsFull in H3; eauto. 
   inv H3.  
   {invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. eassumption. 
    destructLast s1'. 
    {inv H2; try invertListNeq. simpl in *. rewrite spec_multi_unused. 
     rewrite spec_multi_unused in H5. clear H4. eapply smultiReplaceEmptyFull; eauto. }
    {invertHyp. eapply newSimActionStepsEmptyFull; eauto.  constructor. 
     rewrite <- app_assoc in H5. simpl in *. assumption. }
   }
   {invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. eassumption. 
    destructLast s1'. 
    {inv H2; try invertListNeq. rewrite spec_multi_unused. rewrite spec_multi_unused in H3. 
     clear H4. eapply smultiReplaceSpecFull; eauto. }
    {invertHyp. eapply newSimActionStepsFullFull; eauto. constructor.  rewrite <- app_assoc in H3.
     simpl in *. eassumption. }
   }
  }
  {inv H0. inv H3. econstructor; eauto. erewrite eraseHeapCommitNewEmpty; eauto. 
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. 
   unspecThreadTac. auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2. 
   apply unspecEraseTrm; eauto. eapply newFastForward in H4; eauto. Focus 2. 
   eapply lookupCreatedSpec; eauto. invertHyp. eapply spec_multi_trans.
   rewrite spec_multi_unused. eassumption. eapply newSimPureStepsEmpty in H3; eauto. 
   invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. eassumption. 
   destructLast s1'. 
   {simpl in *. inv H2; try invertListNeq. rewrite spec_multi_unused.
    rewrite spec_multi_unused in H3. eapply smultiReplaceEmpty; eauto. }
   {invertHyp. eapply newSimActionStepsEmpty; eauto. constructor. rewrite <- app_assoc in H3. 
    simpl in *. assumption. }
  }
  {inv H0. inv H2. econstructor; eauto. unfoldTac. rewrite coupleUnion in *. 
   repeat rewrite unspecUnionComm in *. eraseTrmTac s1' M. rUnspecAll. 
   Focus 2. unspecThreadTac; eauto. Focus 3. unspecThreadTac; eauto. 
   Focus 2. apply unspecEraseTrm; eauto. eraseTrmTac s1'' N. rUnspecAll. Focus 2. 
   apply unspecEraseTrm. eauto. unfoldTac. rewrite union_empty_r in H3. 
   rewrite <- coupleUnion in H3. eapply forkFastForward in H3; eauto. invertHyp.
   eapply spec_multi_trans. erewrite spec_multi_unused. eassumption. 
   repeat rewrite <- coupleUnion. eapply forkCatchup in H3; eauto. 
   invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. eassumption. 
   
   




  




aldsfhlasdkjhfasd