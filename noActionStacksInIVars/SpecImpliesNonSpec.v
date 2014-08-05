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
Require Import hetList. 

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


Theorem raw_lookupEraseSpecFull : forall x H ds tid N, 
                                raw_heap_lookup x H = Some(sfull COMMIT ds SPEC tid N) ->
                                raw_heap_lookup x (raw_eraseHeap H) = Some pempty. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct s. erewrite IHlist; eauto. simpl. rewrite eq. 
    erewrite IHlist; eauto. destruct s. eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupEraseSpecFull : forall x H ds tid N, 
                                heap_lookup x H = Some(sfull COMMIT ds SPEC tid N) ->
                                heap_lookup x (eraseHeap H) = Some pempty. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseSpecFull. eauto. 
Qed.  

Theorem raw_eraseHeapCommitWrite : forall H x ds t N,
                                 raw_heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                                 raw_eraseHeap(raw_replace x (sfull COMMIT ds COMMIT t N) H) = 
                                 raw_replace x (pfull (eraseTerm N)) (raw_eraseHeap H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {simpl. erewrite IHlist; eauto. destruct i0. destruct s; auto.  simpl. rewrite eq. 
    auto. destruct s;auto. destruct s0; simpl; rewrite eq; auto. }
  }
Qed. 

Theorem eraseHeapCommitWrite : forall H x ds t N,
                                 heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                                 eraseHeap(replace x (sfull COMMIT ds COMMIT t N) H) = 
                                 replace x (pfull (eraseTerm N)) (eraseHeap H). 
Proof.
  intros. destruct H; simpl. apply rawHeapsEq. eapply raw_eraseHeapCommitWrite; eauto. 
Qed. 

Theorem raw_lookupEraseCommitFull : forall x H ds tid N, 
       raw_heap_lookup x H = Some(sfull COMMIT ds COMMIT tid N) ->
       raw_heap_lookup x (raw_eraseHeap H) = Some (pfull (eraseTerm N)). 
Proof.
  induction H; intros.  
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct s. eauto. simpl. rewrite eq. eauto. destruct s. 
    eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupEraseCommitFull : forall x H ds tid N, 
       heap_lookup x H = Some(sfull COMMIT ds COMMIT tid N) ->
       heap_lookup x (eraseHeap H) = Some (pfull (eraseTerm N)). 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseCommitFull; eauto. 
Qed. 

Theorem raw_lookupUnspecSpecFullEmpty : forall x H ds t N,
                                          raw_heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                                          raw_heap_lookup x (raw_unspecHeap H) = Some(sempty COMMIT). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq; auto. }
   {destruct i0. destruct s; eauto. simpl. rewrite eq; eauto. 
    destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupUnspecSpecFullEmpty : forall x H ds t N,
                                          heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                                          heap_lookup x (unspecHeap H) = Some(sempty COMMIT). 
Proof.
  intros. destruct H; simpl. eapply raw_lookupUnspecSpecFullEmpty; eauto. 
Qed. 



Theorem raw_eraseHeapCommitNewFull : forall x ds t N H S,
                                   unique ivar_state S H -> 
                                   raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                   raw_eraseHeap (raw_replace x (sfull COMMIT ds SPEC t N) H) =
                                   raw_extend x pempty (raw_eraseHeap H).
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

Theorem eraseHeapCommitNewFull : forall x ds t N H p,
                                   heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                   eraseHeap (replace x (sfull COMMIT ds SPEC t N) H) =
                                   extend x pempty (eraseHeap H) p.
Proof.
  intros. destruct H. simpl in *. apply rawHeapsEq. eapply raw_eraseHeapCommitNewFull; eauto. 
Qed.

Theorem raw_eraseHeapCommitNewEmpty : forall x S H,
                                   unique ivar_state S H -> 
                                   raw_heap_lookup x H = Some(sempty SPEC) ->
                                   raw_eraseHeap (raw_replace x (sempty COMMIT) H) =
                                   raw_extend x pempty (raw_eraseHeap H).
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
                                   eraseHeap (replace x (sempty COMMIT) H) =
                                   extend x pempty (eraseHeap H) p.
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

Theorem raw_lookupNoneBoth : forall x H,
                           raw_heap_lookup x H = None ->
                           raw_heap_lookup x (raw_eraseHeap H) = None. 
Proof.
  induction H; intros; auto. simpl in *. 
  destruct a. destruct (beq_nat x i) eqn:eq. 
  {inv H0. }
  {destruct i0. destruct s; auto. simpl. rewrite eq. auto. destruct s; auto. 
   destruct s0; simpl; rewrite eq; auto. }
Qed. 
 
Theorem raw_lookupEraseSpecNone : forall x H t S N ds,
                                    unique ivar_state S H ->
                                    raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                    raw_heap_lookup x (raw_eraseHeap H) = None. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. inv H0. eapply uniqueLookupNone in H6. Focus 2. 
    apply Union_intror. constructor. apply raw_lookupNoneBoth. apply beq_nat_true in eq. 
    subst. auto. }
   {destruct i0. 
    {destruct s. inv H0. eauto. simpl. rewrite eq. inv H0. eauto. }
    {destruct s; auto. inv H0; eauto. inv H0. destruct s0; simpl; rewrite eq; eauto. }
   }
  }
Qed.

Theorem lookupEraseSpecNone : forall x H t N ds,
                                heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                heap_lookup x (eraseHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseSpecNone; eauto. 
Qed.

Theorem raw_lookupEraseSpecNoneEmpty : forall x H S,
                                    unique ivar_state S H ->
                                    raw_heap_lookup x H = Some(sempty SPEC) ->
                                    raw_heap_lookup x (raw_eraseHeap H) = None. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. inv H0. eapply uniqueLookupNone in H6. Focus 2. 
    apply Union_intror. constructor. apply raw_lookupNoneBoth. apply beq_nat_true in eq. 
    subst. auto. }
   {destruct i0.  
    {destruct s. inv H0; eauto. simpl. rewrite eq. inv H0; eauto. }
    {inv H0. destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
   }
  }
Qed.

Theorem lookupEraseSpecNoneEmpty : forall x H,
                                heap_lookup x H = Some(sempty SPEC) ->
                                heap_lookup x (eraseHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseSpecNoneEmpty; eauto. 
Qed.  

Theorem raw_lookupUnspecNoneBoth : forall x H,
                           raw_heap_lookup x H = None ->
                           raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof.
  induction H; intros; auto. simpl in *. 
  destruct a. destruct (beq_nat x i) eqn:eq. 
  {inv H0. }
  {destruct i0. destruct s; eauto. simpl. rewrite eq; eauto. destruct s. eauto. 
   destruct s0; simpl; rewrite eq; eauto. }
Qed. 

Theorem raw_lookupUnspecSpecNone : forall x H t S N ds,
                                    unique ivar_state S H ->
                                    raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                    raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1.  inv H0. eapply uniqueLookupNone in H6. Focus 2. 
    apply Union_intror. constructor. apply raw_lookupUnspecNoneBoth. apply beq_nat_true in eq. 
    subst. auto. }
   {destruct i0. 
    {inv H0. destruct s; eauto. simpl. rewrite eq. eauto. }
    {inv H0. destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
   }
  }
Qed. 

Theorem lookupUnspecSpecNone : forall x H t N ds,
                                heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                heap_lookup x (unspecHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupUnspecSpecNone; eauto. 
Qed. 

Theorem raw_lookupUnspecSpecEmptyNone : forall x H S,
                                    unique ivar_state S H ->
                                    raw_heap_lookup x H = Some(sempty SPEC) ->
                                    raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. inv H0. eapply uniqueLookupNone in H6. Focus 2. 
    apply Union_intror. constructor. apply raw_lookupUnspecNoneBoth. apply beq_nat_true in eq. 
    subst. auto. }
   {destruct i0. 
    {inv H0. destruct s; eauto. simpl. rewrite eq. eauto. }
    {inv H0. destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
   }
  }
Qed. 

Theorem lookupUnspecSpecEmptyNone : forall x H,
                                heap_lookup x H = Some(sempty SPEC) ->
                                heap_lookup x (unspecHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupUnspecSpecEmptyNone; eauto. 
Qed. 

Hint Constructors pbasic_step. 
 
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

Inductive eraseTrm : list action -> trm -> trm -> Prop :=
|eraseTrmNil : forall M, eraseTrm nil M M
|eraseTrmRead : forall x t E d s M, eraseTrm (s++[rAct x t E d]) M t
|eraseTrmWrite : forall x t E M d N s, eraseTrm (s++[wAct x t E M d]) N t
|eraseTrmNew : forall x t E d s M, eraseTrm (s++[nAct t E d x]) M t
|eraseTrmFork : forall t E M d N n s, eraseTrm (s++[fAct t E M d n]) N t
|eraseTrmSR : forall t E M N d M' s, eraseTrm (s++[srAct t E M N d]) M' t. 

Theorem eraseEraseTrm : forall tid s1 s2 M M', 
                          eraseTrm s1 M M' ->
                          eraseThread(tid,unlocked s1,s2,M) (pSingleton (eraseTerm M')). 
Proof.
  intros. destructLast s1. 
  {inv H; try invertListNeq. auto. }
  {invertHyp. destruct x; inv H; try solve[invertListNeq]; apply lastElementEq in H1; 
   inv H1; eraseThreadTac; auto. }
Qed. 

Theorem eEraseTrm : forall s1 M, exists M', eraseTrm s1 M M'. 
  intros. destructLast s1. 
  {econstructor. econstructor. }
  {invertHyp. destruct x; econstructor; econstructor. }
Qed. 

Ltac eraseTrmTac s1 M := assert(exists M', eraseTrm s1 M M') by apply eEraseTrm; invertHyp.             

Ltac consedActTac H :=
  eapply consedActEq in H;[idtac|apply InL; constructor|apply InL; constructor|rewrite app_nil_l; simpl;auto|
                           simpl; auto]. 

Theorem eraseTrmApp : forall x y M M',
                        eraseTrm(x++[y]) M M' -> actionTerm y M'. 
Proof.
  intros. inv H; try solve[invertListNeq]; 
  apply lastElementEq in H1; subst; constructor. 
Qed. 

Theorem simPureSteps : forall H H' H'' T T' PT s1 s2 tid M M' M'' a,
                eraseTrm s1 M' M'' ->
                spec_multistep H (tUnion T (tSingleton(tid,unlocked[a],s2,M)))
                               H' (tUnion T' (tSingleton(tid,unlocked(s1++[a]),s2,M'))) ->
                pmultistep H'' PT (pSingleton (eraseTerm M))
                           (pOK H'' PT (pSingleton (eraseTerm M''))).
Proof.
  intros. dependent induction H1. 
  {apply UnionEqTID in x. invertHyp. inv H. destruct s1; inv H3. inv H0; try invertListNeq. 
   constructor. invertListNeq. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
   apply H3 in H. inversion H; subst. 
   {eapply specSingleStepErase in H5; eauto. invertHyp.
    eapply IHspec_multistep. Focus 2. auto. apply UnionSingletonEq in H2; auto. 
    rewrite H2. apply EqJMeq. unfoldTac. rewrite Union_associative. 
    rewrite (Union_commutative thread _ t'). rewrite <- Union_associative.
    auto. eauto. auto. }
   {inv H6. addEmpty. copy H5. inv H6. 
    {unfoldTac; invertHyp. inv H7. apply simBasicStep in H8. econstructor. 
     eapply PBasicStep. eauto. unfold pUnion. rewrite union_empty_l. 
     eapply IHspec_multistep; auto. eauto. }
    {unfoldTac; invertHyp; invThreadEq. destructLast s1. 
     {simpl in *. eapply monotonicActions in H1. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply Union_intror. constructor. simpl in *. omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      inv H0; try solve[invertListNeq]. apply lastElementEq in H6. 
      inv H6. unfold pUnion. rewrite union_empty_l. constructor. }
    }
    {unfoldTac; invertHyp. inv H7. destructLast s1. 
     {simpl in *. eapply monotonicActions in H1. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply Union_intror. constructor. simpl in *. omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      inv H0; try solve[invertListNeq]. apply lastElementEq in H6. 
      inv H6. unfold pUnion. rewrite union_empty_l. constructor. }
    }
    {unfoldTac; invertHyp. inv H7. destructLast s1. 
     {simpl in *. eapply monotonicActions in H1. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply Union_intror. constructor. simpl in *. omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      inv H0; try solve[invertListNeq]. apply lastElementEq in H6. 
      inv H6. unfold pUnion. rewrite union_empty_l. constructor. }
    }
    {unfoldTac; invertHyp. inv H7. destructLast s1. 
     {simpl in *. eapply monotonicActions in H1. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply Union_intror. constructor. simpl in *. omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst.
      inv H0; try solve[invertListNeq]. apply lastElementEq in H6. 
      inv H6. unfold pUnion. rewrite union_empty_l. constructor. }
    }
    {unfoldTac; invertHyp. inv H10. destructLast s1. 
     {simpl in *. eapply monotonicActions in H1. Focus 2. apply Union_intror. constructor. 
      Focus 2. apply Union_intror. constructor. simpl in *. omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      inv H0; try solve[invertListNeq]. apply lastElementEq in H6. 
      inv H6. unfold pUnion. rewrite union_empty_l. constructor. }
    }
    {unfold pUnion. rewrite union_empty_l. auto. }
   }
  }
Qed. 

Theorem specStepRead : forall H H' TID x M ds M' E d s1' N t0 T T' s2 PT,
   decompose M' E (get(fvar x)) -> erasePool T PT ->
   heap_lookup x H = Some(sfull COMMIT ds COMMIT t0 N) ->
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
    eapply specStepFullIVar in H8; eauto. invertHyp. 
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
     exists(replace x0 (sfull sc (TID::ds0) s writer N0) H).
     exists T0. simpl in *. rewrite H10 in H4. inv H4. split. 
     auto. assert(d=d0). apply proof_irrelevance. subst. assumption. 
     erewrite eraseHeapDependentRead; eauto. split; auto. apply UnionEqTID in H5. 
     invertHyp. auto. }
   }
  }
Qed. 

Theorem specStepWrite : forall H H' TID x M M' E ds s1' N T T' s2 t PT d,
   decompose M' E (put(fvar x) N) -> erasePool T PT ->
   heap_lookup x H = Some(sempty COMMIT) ->
   heap_lookup x H' = Some(sfull COMMIT ds SPEC t N) ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tSingleton(TID,unlocked(s1'++[wAct x M' E N d]), s2, M))) ->
    exists H'' T'',
         spec_multistep H''
           (tUnion T''
              (tSingleton (TID, unlocked [wAct x M' E N d], s2, fill E (ret unit))))
           H' (tUnion T' (tSingleton (TID, unlocked (s1'++[wAct x M' E N d]), s2, M))) /\
         eraseHeap H'' = eraseHeap H /\ erasePool T'' PT.
Proof.
  intros. dependent induction H4; intros.
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq x. copy H5. apply specStepSingleton in H5. invertHyp. 
   assert(tIn (tUnion T0(tSingleton x)) x). apply Union_intror. constructor. 
   apply H7 in H5. inversion H5; subst.  
   {assert(tIn (tUnion T (tSingleton(TID,unlocked nil,s2,M')))(TID,unlocked nil, s2, M')). 
    apply Union_intror. constructor. apply H8 in H11. inversion H11; subst. 
    {copy H9. eapply specSingleStepErase in H13; eauto. copy H9. 
     eapply specStepEmptyIVar in H9; eauto. Focus 3. apply Union_intror. constructor. 
     Focus 2. constructor. eauto. eapply IHspec_multistep in H3. invertHyp. exists x1. exists x2.  
     split. eauto. split. rewrite <- H16. rewrite <- H3. auto. auto.
     replace PT with (erasePoolAux(tUnion (Subtract thread T x) t')).  
     constructor. inv H1. rewrite eraseUnionComm. invertHyp. inv H15. rewrite H17. 
     rewrite <- eraseUnionComm. replace (tUnion (Subtract thread T x)(tSingleton x))
                                with (tAdd (Subtract thread T x) x). 
     unfold tAdd. rewrite <- add_subtract. auto. auto. unfoldTac. auto. auto. auto. auto.
     apply EqJMeq. apply UnionSingletonEq in H6.
     rewrite H6. unfoldTac. repeat rewrite Union_associative. 
     rewrite (Union_commutative thread _ t'). auto. auto. auto. auto. }
    {inv H12. inv H9; unfoldTac; invertHyp; try solve[repeat invertDecomp]. 
    {invertDecomp. inv H13; repeat invertDecomp. }
    {invertDecomp. copy d; copy d0. invertDecomp. invertDecomp. inv H14. 
     exists(replace x0(sfull sc nil SPEC TID N)H).
     exists T0. simpl in *. split. assert(d=d0). apply proof_irrelevance. subst. eassumption. 
     split. rewrite eraseHeapWrite; auto. simpl. auto. apply UnionEqTID in H6. invertHyp. auto. }
    }
   }
   {inv H10. inv H9; unfoldTac; invertHyp; try solve[repeat invertDecomp]. 
    {invertDecomp. inv H11; repeat invertDecomp. }
    {invertDecomp. copy d; copy d0. invertDecomp. invertDecomp. inv H12. 
     exists(replace x0(sfull sc nil SPEC TID N)H). exists T0. simpl in *. split. assert(d=d0). 
     apply proof_irrelevance. subst. eassumption. split. 
     rewrite eraseHeapWrite; auto. simpl. auto. apply UnionEqTID in H6. invertHyp. auto. }
   }
  }
Qed. 

Ltac firstActTac H :=
       eapply firstActEq in H;[idtac|apply InL; constructor|apply InL; constructor
                               |rewrite app_nil_l; simpl; auto|simpl; auto]. 

Theorem specStepNewFull : forall H H' TID x M M' E ds s1' N T T' s2 t PT d,
   decompose M' E new -> erasePool T PT ->
   heap_lookup x H = None ->
   heap_lookup x H' = Some(sfull SPEC ds SPEC t N) ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]), s2, M))) ->
    exists H'' T'',
         spec_multistep H''
           (tUnion T''
              (tSingleton (TID, unlocked [nAct M' E d x], s2, fill E (ret (fvar x)))))
           H' (tUnion T' (tSingleton (TID, unlocked (s1'++[nAct M' E d x]), s2, M))) /\
         eraseHeap H'' = eraseHeap H /\ erasePool T'' PT.
Proof.
  intros. dependent induction H4; intros.
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq x. copy H5. apply specStepSingleton in H5. invertHyp. 
   assert(tIn (tUnion T0(tSingleton x)) x). apply Union_intror. constructor. 
   apply H7 in H5. inversion H5; subst.  
   {assert(tIn (tUnion T (tSingleton(TID,unlocked nil,s2,M')))(TID,unlocked nil, s2, M')). 
    apply Union_intror. constructor. apply H8 in H11. inversion H11; subst. 
    {copy H9. eapply specSingleStepErase in H13; eauto. copy H9. 
     eapply specStepNoneIVar in H9; eauto. Focus 3. apply Union_intror. constructor. 
     Focus 2. constructor. eauto. eapply IHspec_multistep in H3. invertHyp. exists x1. exists x2.  
     split. eauto. split. rewrite <- H16. rewrite <- H3. auto. auto.
     replace PT with (erasePoolAux(tUnion (Subtract thread T x) t')).  
     constructor. inv H1. rewrite eraseUnionComm. invertHyp. inv H15. rewrite H17. 
     rewrite <- eraseUnionComm. replace (tUnion (Subtract thread T x)(tSingleton x))
                                with (tAdd (Subtract thread T x) x). 
     unfold tAdd. rewrite <- add_subtract. auto. auto. unfoldTac. auto. auto. auto. auto.
     apply EqJMeq. apply UnionSingletonEq in H6.
     rewrite H6. unfoldTac. repeat rewrite Union_associative. 
     rewrite (Union_commutative thread _ t'). auto. auto. auto. auto. }
    {inv H12. exfalso. eapply uniqueTP with (T1:=T)(T2:=tSingleton(TID,unlocked nil,s2,M')). 
     assert(tIn(tUnion T (tSingleton(TID,unlocked nil, s2, M')))(TID,unlocked nil,s2,M')). 
     apply Union_intror. constructor. eapply H12. eauto. constructor. }
   } 
   {inv H10. inv H9; unfoldTac; invertHyp; try solve[repeat invertDecomp]. 
    {invertDecomp. inv H11; repeat invertDecomp. }
    {invertDecomp. copy d; copy d0. invertDecomp. invertDecomp. inv H12. 
     exists (extend x (sempty SPEC) H p).
     exists T0. simpl in *. split. assert(d=d0). apply proof_irrelevance. subst. 
     copy H4. firstActTac H4. inv H4. eassumption. split. rewrite eraseHeapNew; auto. 
     simpl. auto. apply UnionEqTID in H6. invertHyp. auto. }
   }
  }
Qed. 

Theorem specStepNewEmpty : forall H H' TID x M M' E s1' T T' s2 PT d,
   decompose M' E new -> erasePool T PT ->
   heap_lookup x H = None ->
   heap_lookup x H' = Some(sempty SPEC) ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]), s2, M))) ->
    exists H'' T'',
         spec_multistep H''
           (tUnion T''
              (tSingleton (TID, unlocked [nAct M' E d x], s2, fill E (ret (fvar x)))))
           H' (tUnion T' (tSingleton (TID, unlocked (s1'++[nAct M' E d x]), s2, M))) /\
         eraseHeap H'' = eraseHeap H /\ erasePool T'' PT.
Proof.
  intros. dependent induction H4; intros.
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq x. copy H5. apply specStepSingleton in H5. invertHyp. 
   assert(tIn (tUnion T0(tSingleton x)) x). apply Union_intror. constructor. 
   apply H7 in H5. inversion H5; subst.  
   {assert(tIn (tUnion T (tSingleton(TID,unlocked nil,s2,M')))(TID,unlocked nil, s2, M')). 
    apply Union_intror. constructor. apply H8 in H11. inversion H11; subst. 
    {copy H9. eapply specSingleStepErase in H13; eauto. copy H9. 
     eapply specStepNoneIVar in H9; eauto. Focus 3. apply Union_intror. constructor. 
     Focus 2. constructor. eauto. eapply IHspec_multistep in H3. invertHyp. exists x1. exists x2.  
     split. eauto. split. rewrite <- H16. rewrite <- H3. auto. auto.
     replace PT with (erasePoolAux(tUnion (Subtract thread T x) t')).  
     constructor. inv H1. rewrite eraseUnionComm. invertHyp. inv H15. rewrite H17. 
     rewrite <- eraseUnionComm. replace (tUnion (Subtract thread T x)(tSingleton x))
                                with (tAdd (Subtract thread T x) x). 
     unfold tAdd. rewrite <- add_subtract. auto. auto. unfoldTac. auto. auto. auto. auto.
     apply EqJMeq. apply UnionSingletonEq in H6.
     rewrite H6. unfoldTac. repeat rewrite Union_associative. 
     rewrite (Union_commutative thread _ t'). auto. auto. auto. auto. }
    {inv H12. exfalso. eapply uniqueTP with (T1:=T)(T2:=tSingleton(TID,unlocked nil,s2,M')). 
     assert(tIn(tUnion T (tSingleton(TID,unlocked nil, s2, M')))(TID,unlocked nil,s2,M')). 
     apply Union_intror. constructor. eapply H12. eauto. constructor. }
   } 
   {inv H10. inv H9; unfoldTac; invertHyp; try solve[repeat invertDecomp]. 
    {invertDecomp. inv H11; repeat invertDecomp. }
    {invertDecomp. copy d; copy d0. invertDecomp. invertDecomp. inv H12. 
     exists (extend x (sempty SPEC) H p). exists T0. simpl in *. split. assert(d=d0). 
     apply proof_irrelevance. subst. copy H4. firstActTac H4. inv H4. eassumption. split. 
     rewrite eraseHeapNew; auto. simpl. auto. apply UnionEqTID in H6. invertHyp. auto. }
   }
  }
Qed. 

Theorem eActTerm : forall a, exists M, actionTerm a M. 
Proof.
  intros. destruct a; repeat econstructor. 
Qed. 

Theorem eraseActTerm : forall tid s x s2 M M', 
                         actionTerm x M' ->
                         eraseThread(tid,unlocked(s++[x]),s2,M) (pSingleton(eraseTerm M')).
Proof.
  intros. inv H; eraseThreadTac; eauto.
Qed. 

Fixpoint joinCtxts E1 E2 :=
  match E1 with
      |pbindCtxt E M => pbindCtxt (joinCtxts E E2) M
      | phandleCtxt E M => phandleCtxt (joinCtxts E E2) M
      | pappCtxt E M => pappCtxt (joinCtxts E E2) M
      | pappValCtxt E M => pappValCtxt (joinCtxts E E2) M
      | ppairCtxt E M => ppairCtxt (joinCtxts E E2) M
      | ppairValCtxt E M => ppairValCtxt (joinCtxts E E2) M
      | pfstCtxt E => pfstCtxt (joinCtxts E E2)
      | psndCtxt E => psndCtxt (joinCtxts E E2)
      | pspecRunCtxt E M => pspecRunCtxt (joinCtxts E E2) M
      | pspecJoinCtxt E M => pspecJoinCtxt (joinCtxts E E2) M
      | pholeCtxt => E2
  end. 

Theorem notPValPFill : forall E e, ~ pval e -> ~pval (pfill E e). 
Proof.
  induction E; intros; simpl; try solve[introsInv].
  {intros c. inv c. apply IHE in H. contradiction. }
  {intros c. inv c. apply IHE in H. contradiction. }
  {auto. }
Qed. 

Theorem pdecomposeNotPVal : forall t E e, pdecompose t E e -> E <> pholeCtxt -> ~pval t. 
Proof.
  intros. induction H; try solve[introsInv].
  {intros c. inv c. contradiction. }
  {introsInv. contradiction. }
Qed. 

Theorem pdecomposeFurther : forall E E' e e' e'',
                                  pctxtWF e E -> pdecompose e' E' e'' -> ~ pval e' ->
                                  pdecompose (pfill E e') (joinCtxts E E') e''.
Proof.
  induction E; intros. 
  {simpl. constructor. inv H. eapply notPValPFill. auto. inv H. eapply IHE; eauto. }
  {simpl. constructor. apply notPValPFill; auto. inv H. eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {simpl. auto. }
Qed. 


Theorem joinFill : forall E1 E2 e, pfill (joinCtxts E1 E2) e = pfill E1 (pfill E2 e). 
Proof.
  induction E1; intros; try solve[simpl; rewrite IHE1; eauto]. 
  simpl. auto. 
Qed. 

Ltac monoActs H :=
           eapply monotonicActions in H;[idtac|apply InL; constructor|apply InL;constructor]; eauto. 

Theorem simSpecJoinSteps : forall H H' e T T' N N0 N1 PT H'' M E s2 tid,
                             pctxtWF e E ->
                             spec_multistep H (tUnion T (tSingleton(tid,specStack nil N0, s2, N)))
                                            H' (tUnion T' (tSingleton(tid,specStack nil N0, s2, M))) ->
                             pmultistep H'' PT (pSingleton(pfill E (pspecJoin (pret N1) (eraseTerm N))))
                                        (pOK H'' PT (pSingleton(pfill E (pspecJoin (pret N1) (eraseTerm M))))).
Proof.
  intros. genDeps{E; e}. dependent induction H1; intros. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
   apply H3 in H. inversion H; subst. 
   {eapply specSingleStepErase in H5; eauto. invertHyp.
    eapply IHspec_multistep; eauto. apply UnionSingletonEq in H2. rewrite H2. 
    apply EqJMeq. unfoldTac. rewrite Union_associative. rewrite (Union_commutative thread _ t'). 
    rewrite <- Union_associative. auto. auto. }
   {inv H6. addEmpty. copy H5. inv H5. 
    {unfoldTac; invertHyp. inv H7. apply simBasicStep in H8. inv H8. 
     {econstructor. eapply PBasicStep. eapply pbasicBeta. eapply pdecomposeFurther. 
      eauto. econstructor. constructor. Focus 2. eauto. Focus 2. introsInv.  
      apply pdecomposeEq in H9; subst. rewrite H9. apply notPValPFill. introsInv. 
      unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H5. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicProjL. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H9. rewrite H9. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H5. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicProjR. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H9. rewrite H9. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H5. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicBind. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H9. rewrite H9. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H5. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicBindRaise. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H9. rewrite H9. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H5. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicHandle. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H9. rewrite H9. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H5. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicHandleRet. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H9. rewrite H9. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H5. eapply IHspec_multistep; eauto. }
    }
    {unfoldTac; invertHyp; invThreadEq. monoActs H1; simpl in *; omega. }
    {unfoldTac; invertHyp; invThreadEq. monoActs H1; simpl in *; omega. }
    {unfoldTac; invertHyp; invThreadEq. monoActs H1; simpl in *; omega. }
    {unfoldTac; invertHyp; invThreadEq. monoActs H1; simpl in *; omega. }
    {unfoldTac; invertHyp; invThreadEq. monoActs H1; simpl in *; omega. }
    {unfold pUnion. rewrite union_empty_l. auto. }
   }
  }
Qed.

Theorem simSpecJoinSteps' : forall H H' H'' e T T' PT s2 tid M M' s b M'' N1 E X,
                actionTerm b M'' -> pctxtWF e E -> 
                spec_multistep H (tUnion T (tSingleton(tid,specStack nil X,s2,M)))
                               H' (tUnion T' (tSingleton(tid,specStack(s++[b]) X,s2,M'))) ->
                pmultistep H'' PT (pSingleton (pfill E (pspecJoin (pret N1) (eraseTerm M))))
                           (pOK H'' PT (pSingleton (pfill E (pspecJoin (pret N1)(eraseTerm M''))))).
Proof. 
  intros. genDeps{E; e}. dependent induction H2; intros. 
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
   apply H4 in H. inversion H; subst. 
   {eapply specSingleStepErase in H6; eauto. invertHyp.
    eapply IHspec_multistep; eauto. apply UnionSingletonEq in H3. rewrite H3. 
    apply EqJMeq. unfoldTac. rewrite Union_associative. rewrite (Union_commutative thread _ t'). 
    rewrite <- Union_associative. auto. auto. }
   {inv H7.  addEmpty. copy H6. inv H6. 
    {unfoldTac; invertHyp. inv H8. apply simBasicStep in H9. inv H9. 
     {econstructor. eapply PBasicStep. eapply pbasicBeta. eapply pdecomposeFurther. 
      eauto. econstructor. constructor. Focus 2. eauto. Focus 2. introsInv.  
      apply pdecomposeEq in H10; subst. rewrite H10. apply notPValPFill. introsInv. 
      unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H6. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicProjL. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H10. rewrite H10. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H6. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicProjR. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H10. rewrite H10. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H6. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicBind. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H10. rewrite H10. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H6. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicBindRaise. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H10. rewrite H10. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H6. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicHandle. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H10. rewrite H10. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H6. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicHandleRet. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H10. rewrite H10. apply notPValPFill. 
      introsInv. eauto. introsInv. unfold pUnion. rewrite union_empty_l. rewrite joinFill. simpl. 
      rewrite H6. eapply IHspec_multistep; eauto. }
    }
    {unfoldTac; invertHyp; invThreadEq. simpl in *. firstActTac H2. subst. subst. inv H0. 
     unfold pUnion. rewrite union_empty_l. constructor. }
    {unfoldTac; invertHyp; invThreadEq. simpl in *. firstActTac H2. subst. subst. inv H0. 
     unfold pUnion. rewrite union_empty_l. constructor. }
    {unfoldTac; invertHyp; invThreadEq. simpl in *. firstActTac H2. subst. subst. inv H0. 
     unfold pUnion. rewrite union_empty_l. constructor. }
    {unfoldTac; invertHyp; invThreadEq. simpl in *. firstActTac H2. subst. subst. inv H0. 
     unfold pUnion. rewrite union_empty_l. constructor. }
    {unfoldTac; invertHyp; invThreadEq. simpl in *. firstActTac H2. subst. subst. inv H0. 
     unfold pUnion. rewrite union_empty_l. constructor. }
    {unfold pUnion. rewrite union_empty_l. auto. }
   }
  }
Qed. 

Theorem wrapDistributeApp : forall s a N E e p, 
                              wrapActs(s++[a]) N E e p = wrapActs(s) N E e p++ wrapActs[a] N E e p.
Proof.
  induction s; intros. 
  {simpl. destruct a; auto. }
  {simpl. destruct a; auto; destruct a0; auto; rewrite IHs; auto. }
Qed. 

Theorem specStepFork : forall H H' TID M M' E s1' s1'' N T T' s2 PT n M'' d,
   decompose M' E (fork M'') -> erasePool T PT ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tCouple(TID,unlocked(s1'++[fAct M' E M'' d n]), s2, M)
                                 (n::TID, locked s1'',nil, N))) ->
   exists H'' T'',
     spec_multistep H'' (tUnion T'' 
                                (tCouple (TID, unlocked[fAct M' E M'' d n], s2, fill E (ret unit))
                                         (n::TID, locked nil, nil, M'')))
                    H' (tUnion T' (tCouple(TID,unlocked(s1'++[fAct M' E M'' d n]), s2, M)
                                 (n::TID, locked s1'',nil, N))) /\ 
     eraseHeap H'' = eraseHeap H /\ erasePool T'' PT.
Proof.
  intros. dependent induction H2. 
  {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x.
   rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H. invertHyp. 
   assert(tIn (tUnion T0(tSingleton x)) x). apply Union_intror. constructor. 
   apply H4 in H. inversion H; subst.  
   {assert(tIn (tUnion T (tSingleton(TID,unlocked nil,s2,M')))(TID,unlocked nil, s2, M')). 
    apply Union_intror. constructor. apply H5 in H8. inversion H8; subst. 
    {copy H6. eapply specSingleStepErase in H10; eauto. invertHyp. rewrite <- H11. 
     eapply IHspec_multistep.
     replace PT with (erasePoolAux(tUnion (Subtract thread T x) t')). eauto. inv H1. 
     rewrite eraseUnionComm. inv H12. rewrite H13.
     rewrite <- eraseUnionComm. replace (tUnion (Subtract thread T x)(tSingleton x))
                                with (tAdd (Subtract thread T x) x). unfold tAdd. 
     rewrite <- add_subtract. auto. auto. auto. auto. apply EqJMeq. apply UnionSingletonEq in H3.
     rewrite H3. unfoldTac. repeat rewrite Union_associative. 
     rewrite (Union_commutative thread _ t'). auto. auto. auto. }
    {inv H9. exfalso. eapply uniqueTP with (T1:=T)(T2:=tSingleton(TID,unlocked nil,s2,M')). 
     assert(tIn(tUnion T (tSingleton(TID,unlocked nil, s2, M')))(TID,unlocked nil,s2,M')). 
     apply Union_intror. constructor. eassumption. eauto. constructor. }
   }
   {inv H7. inv H6; unfoldTac; invertHyp; try solve[repeat invertDecomp]. 
    {invertDecomp. inv H8; repeat invertDecomp. }
    {invertDecomp. copy d; copy d0. invertDecomp. invertDecomp. inv H9. 
     exists h'. exists T0. simpl in *. split. assert(d=d0). apply proof_irrelevance. subst.
     copy H2. firstActTac H2. inv H2. assumption. 
     split. auto. apply UnionEqTID in H3. invertHyp; auto. }
   }
  }
Qed. 


Axiom UnionSingletonCoupleEq : forall T T' a b c, 
                 tUnion T (tSingleton a) = tUnion T' (tCouple b c) -> 
                 tIn T' a -> T = tUnion (Subtract thread T' a) (tCouple b c).


Theorem simPureStepsCouple' : forall T' H H' H'' T PT s2 tid s1 M M' M'' N,
        eraseTrm s1 M' M'' -> 
        spec_multistep H (tUnion T (tSingleton(tid,locked[],s2,M)))
                       H' (tUnion T' (tSingleton(tid,locked(s1),s2,M'))) ->
        pmultistep H'' PT (pUnion (pSingleton (eraseTerm M)) (pSingleton N))
                   (pOK H'' PT (pUnion (pSingleton (eraseTerm M'')) (pSingleton N))).
Proof.
  intros. dependent induction H1. 
  {apply UnionEqTID in x. invertHyp. inv H. inv H0; try invertListNeq. constructor. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
   apply H3 in H. inversion H; subst. 
   {eapply IHspec_multistep; eauto. apply UnionSingletonEq in H2. rewrite H2. 
    apply EqJMeq. unfoldTac. rewrite Union_associative. rewrite (Union_commutative thread _ t'). 
    rewrite <- Union_associative. auto. auto. }
   {inv H6. unfold pUnion. inv H5. 
    {unfoldTac; invertHyp; invThreadEq. apply simBasicStep in H7. rewrite Union_commutative. 
     econstructor. eapply PBasicStep. 
     eauto. unfold pUnion. rewrite Union_commutative. eapply IHspec_multistep; eauto. }
    {unfoldTac; invertHyp; invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
    {unfoldTac; invertHyp; invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
    {unfoldTac; invertHyp; invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
    {unfoldTac; invertHyp; invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
    {unfoldTac; invertHyp; invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
   }
  }
Qed. 

Theorem simPureStepsCouple : forall T' H H' H'' T PT s2 tid s1 M M' a M'' N,
        eraseTrm s1 M' M'' -> 
        spec_multistep H (tUnion T (tSingleton(tid,unlocked[a],s2,M)))
                       H' (tUnion T' (tSingleton(tid,unlocked(s1++[a]),s2,M'))) ->
        pmultistep H'' PT (pUnion (pSingleton (eraseTerm M)) (pSingleton N))
                   (pOK H'' PT (pUnion (pSingleton (eraseTerm M'')) (pSingleton N))).
Proof.
  intros. dependent induction H1. 
  {apply UnionEqTID in x. invertHyp. inv H. destruct s1. inv H3. inv H0; try invertListNeq. 
   constructor. simpl in *. inversion H3. invertListNeq. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
   apply H3 in H. inversion H; subst. 
   {eapply IHspec_multistep; eauto. apply UnionSingletonEq in H2. rewrite H2. 
    apply EqJMeq. unfoldTac. rewrite Union_associative. rewrite (Union_commutative thread _ t'). 
    rewrite <- Union_associative. auto. auto. }
   {inv H6. unfold pUnion. rewrite Union_commutative. inv H5. 
    {unfoldTac; invertHyp. inv H6. apply simBasicStep in H7. econstructor. eapply PBasicStep. 
     eauto. unfold pUnion. rewrite Union_commutative. eapply IHspec_multistep; eauto. }
    {unfoldTac; invertHyp. invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. rewrite Union_commutative. constructor. }
    }
    {unfoldTac; invertHyp. invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. rewrite Union_commutative. constructor. }
    }
    {unfoldTac; invertHyp. invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. rewrite Union_commutative. constructor. }
    }
    {unfoldTac; invertHyp. invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. rewrite Union_commutative. constructor. }
    }
    {unfoldTac; invertHyp. invThreadEq. destructLast s1. 
     {inv H0; try invertListNeq. eapply monotonicActions in H1. Focus 2. apply Union_intror. 
      constructor. Focus 2. apply Union_intror. constructor. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. rewrite Union_commutative. constructor. }
    }
   }
  }
Qed. 

Theorem specStepSpec : forall H H' TID M M' E t s1' s1'' N T T' s2 s2' PT d M'',
   decompose t E (spec M N) -> erasePool T PT ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,t)))
           H' (tUnion T' (tCouple(TID,unlocked(s1'++[srAct t E M N d]), s2, M')
                                 (2::TID, locked s1'',s2', M''))) ->
   exists H'' T'',
     spec_multistep H'' (tUnion T'' 
                                (tCouple (TID, unlocked[srAct t E M N d], s2, fill E (specRun M N))
                                         (2::TID, locked nil, nil, N)))
                    H' (tUnion T' (tCouple(TID,unlocked(s1'++[srAct t E M N d]), s2, M')
                                 (2::TID, locked s1'',s2', M''))) /\ 
     eraseHeap H'' = eraseHeap H /\ erasePool T'' PT.
Proof.
  intros. dependent induction H2. 
  {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x.
   rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H. invertHyp. 
   assert(tIn (tUnion T0(tSingleton x)) x). apply Union_intror. constructor. 
   apply H4 in H. inversion H; subst.  
   {assert(tIn (tUnion T (tSingleton(TID,unlocked nil,s2,t)))(TID,unlocked nil, s2, t)). 
    apply Union_intror. constructor. apply H5 in H8. inversion H8; subst. 
    {copy H6. eapply specSingleStepErase in H10; eauto. invertHyp. rewrite <- H11. 
     eapply IHspec_multistep.
     replace PT with (erasePoolAux(tUnion (Subtract thread T x) t')). eauto. inv H1. 
     rewrite eraseUnionComm. inv H12. rewrite H13.
     rewrite <- eraseUnionComm. replace (tUnion (Subtract thread T x)(tSingleton x))
                                with (tAdd (Subtract thread T x) x). unfold tAdd. 
     rewrite <- add_subtract. auto. auto. auto. auto. apply EqJMeq. apply UnionSingletonEq in H3.
     rewrite H3. unfoldTac. repeat rewrite Union_associative. 
     rewrite (Union_commutative thread _ t'). auto. auto. auto. }
    {inv H9. exfalso. eapply uniqueTP with (T1:=T)(T2:=tSingleton(TID,unlocked nil,s2,t)). 
     assert(tIn(tUnion T (tSingleton(TID,unlocked nil, s2, t)))(TID,unlocked nil,s2,t)). 
     apply Union_intror. constructor. eassumption. eauto. constructor. }
   }
   {inv H7. inversion H6; subst; unfoldTac; invertHyp; try solve[repeat invertDecomp]. 
    {invertDecomp. inv H8; repeat invertDecomp. }
    {invertDecomp. copy d; copy d0. invertDecomp. invertDecomp. inv H9. 
     exists h'. exists T0. simpl in *. split. assert(d=d0). apply proof_irrelevance. subst. 
     eassumption. split. auto. apply UnionEqTID in H3. invertHyp; auto. }
   }
  }
Qed. 

Theorem pmultistep_trans : forall H T t H' T' t' c,
                             pmultistep H T t (pOK H' T' t') ->
                             pmultistep H' T' t' c ->
                             pmultistep H T t c. 
Proof.
  intros. remember (pOK H' T' t'). induction H0. 
  {inv Heqp. auto. }
  {subst. econstructor. eauto. eauto. }
  {inv Heqp. }
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
   {inv H1. repeat erewrite erasePoolSingleton; eauto. constructor. }
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
   {simpl. unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. 
    repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. constructor. }
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
   {econstructor. split. constructor. split. erewrite eraseHeapDependentRead; eauto.
    simpl. inv H1. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. }
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
   {simpl. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. }
  }  
  {exists (eraseHeap H). eapply rollbackIdempotent in H9; eauto. 
   invertHyp. inv H1. econstructor. split. constructor. split. 
   erewrite eraseHeapWrite; auto. inv H5. unfoldTac. rewrite eraseUnionComm. rewrite <- H10. 
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
   {erewrite erasePoolSingleton; eauto. simpl. erewrite erasePoolSingleton; eauto. }
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
   {repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. constructor. }
  }
  {inv H3. inv H4. unfoldTac. rewrite coupleUnion in H5. 
   repeat rewrite unspecUnionComm in H5. erewrite unspecSingleton in H5; eauto. 
   erewrite unspecSingleton in H5; eauto. exists (eraseHeap H'). econstructor. 
   split; auto. inv H1. rewrite coupleUnion. rewrite eraseUnionComm. 
   erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto.
   rewrite union_empty_r. unfoldTac. repeat rewrite <- Union_associative in H5. 
   addEmpty. econstructor. eapply pSpecRun. copy p. erewrite <- decomposeErase in H; eauto. 
   simpl. auto. unfold pUnion. rewrite union_empty_l. Focus 2. unfold pUnion. 
   rewrite union_empty_l. auto. copy p. apply decomposeWF in H. rewrite eraseCtxtWF in H.
   simpl in *. copy p. rewrite <- decomposeErase in H1; eauto. simpl in *. destructLast s1. 
   {simpl. erewrite erasePoolSingleton; eauto. rewrite eraseFill. 
    eapply simSpecJoinSteps. eauto. eauto. }
   {invertHyp. rewrite wrapDistributeApp. destruct x. 
    {erewrite erasePoolSingleton. Focus 2. eapply eraseSpecSame; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps' with (b:=rAct x t E0 d); eauto. constructor. }
    {erewrite erasePoolSingleton. Focus 2. eapply eraseSpecSame; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps' with (b:=wAct x t E0 M0 d); eauto. constructor. }
    {erewrite erasePoolSingleton. Focus 2. eapply eraseSpecSame; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps' with (b:=nAct t E0 d i); eauto. constructor. }
    {erewrite erasePoolSingleton. Focus 2. eapply eraseSpecSame; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps' with (b:=fAct t E0 M0 d n); eauto. constructor. }
    {erewrite erasePoolSingleton. Focus 2. eapply eraseSpecSame; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps' with (b:=srAct t E0 M0 N d); eauto. constructor. }
   }
  }
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
   inv H4. erewrite erasePoolSingleton; eauto. eraseTrmTac s1' M. erewrite erasePoolSingleton. 
   Focus 2. apply eraseEraseTrm; eauto. rewrite unspecUnionComm in H5. 
   erewrite unspecSingleton in H5. Focus 2. unspecThreadTac; auto. addEmpty. 
   econstructor. eapply PGet. eapply lookupEraseCommitFull; eauto. copy d. 
   erewrite <- decomposeErase in H1; eauto. unfold pUnion. rewrite union_empty_l. 
   eapply specStepRead in H5; eauto. Focus 2. eapply unspecHeapLookupFull; eauto.
   invertHyp. eapply simPureSteps in H1; eauto. rewrite eraseFill in H1. eassumption. 
   unfold pUnion. rewrite union_empty_l; auto. }
  {exists (replace x (pfull (eraseTerm M'')) (eraseHeap H)). econstructor. split. 
   Focus 2. split; eauto. erewrite eraseHeapCommitWrite; eauto. inv H1. 
   erewrite erasePoolSingleton; eauto. addEmpty. Focus 2. unfold pUnion. rewrite union_empty_l. 
   auto. econstructor. eapply PPut. copy d. rewrite <- decomposeErase in H1; eauto. simpl. 
   auto. eapply lookupEraseSpecFull; eauto. auto. inv H3. inv H4. rewrite unspecUnionComm in H5. 
   erewrite unspecSingleton in H5. Focus 2. unspecThreadTac. eauto.
   eapply specStepWrite in H5; eauto. invertHyp. eraseTrmTac s1' M. erewrite erasePoolSingleton. 
   Focus 2. apply eraseEraseTrm; eauto. eapply simPureSteps in H1; eauto. rewrite eraseFill in H1. 
   simpl in *. unfold pUnion. rewrite union_empty_l. eassumption. eapply lookupUnspecSpecFullEmpty; eauto. }
  {inv H1. inv H3. inv H4. assert(heap_lookup i (eraseHeap H) = None). 
   eapply lookupEraseSpecNone; eauto. exists (extend i pempty (eraseHeap H) H1). 
   econstructor. split. Focus 2. split; eauto. eapply eraseHeapCommitNewFull; eauto. 
   erewrite erasePoolSingleton; eauto. addEmpty. econstructor. eapply PNew with(x:=i)(p:=H1). 
   copy d. rewrite <- decomposeErase in H3; eauto. auto. Focus 2. unfold pUnion. 
   rewrite union_empty_l. auto. rewrite unspecUnionComm in H5. erewrite unspecSingleton in H5. 
   Focus 2. unspecThreadTac. auto. eapply specStepNewFull in H5; eauto. invertHyp. 
   unfold pUnion. rewrite union_empty_l. Focus 2. eapply lookupUnspecSpecNone; eauto. 
   eraseTrmTac s1' M. erewrite erasePoolSingleton. Focus 2. apply eraseEraseTrm; eauto. 
   eapply simPureSteps in H3; eauto. rewrite eraseFill in H3. simpl in *. eassumption. }
  {inv H1. inv H3. inv H4. assert(heap_lookup i (eraseHeap H) = None). 
   eapply lookupEraseSpecNoneEmpty; eauto. exists (extend i pempty (eraseHeap H) H1). 
   econstructor. split. Focus 2. split; eauto. eapply eraseHeapCommitNewEmpty; eauto. 
   erewrite erasePoolSingleton; eauto. addEmpty. econstructor. eapply PNew with(x:=i)(p:=H1). 
   copy d. rewrite <- decomposeErase in H3; eauto. auto. Focus 2. unfold pUnion. 
   rewrite union_empty_l. auto. rewrite unspecUnionComm in H5. erewrite unspecSingleton in H5. 
   Focus 2. unspecThreadTac. auto. eapply specStepNewEmpty in H5; eauto. invertHyp. 
   unfold pUnion. rewrite union_empty_l. Focus 2. eapply lookupUnspecSpecEmptyNone; eauto. 
   eraseTrmTac s1' M. erewrite erasePoolSingleton. Focus 2. apply eraseEraseTrm; eauto. 
   eapply simPureSteps in H3; eauto. rewrite eraseFill in H3. simpl in *. eassumption. }
  {exists (eraseHeap H'). econstructor. split; auto. inv H3. inv H4. inv H1. 
   unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto.
   erewrite erasePoolSingleton; eauto. rewrite union_empty_r. addEmpty. econstructor. 
   eapply pFork. copy d. rewrite <- decomposeErase in H; eauto. simpl. auto. Focus 2. 
   unfold pUnion. rewrite union_empty_l. auto. unfold pUnion. rewrite union_empty_l. 
   rewrite coupleUnion in H5. repeat rewrite unspecUnionComm in H5. 
   erewrite unspecSingleton in H5. Focus 2. unspecThreadTac; auto. 
   erewrite unspecSingleton in H5; eauto. unfoldTac. rewrite union_empty_r in H5. 
   rewrite <- coupleUnion in H5. eapply specStepFork in H5; eauto. invertHyp. 
   rewrite eraseUnspecHeapIdem in H1. rewrite <- H1. inv H4. inv H0. 
   rewrite eraseUnspecPoolAuxEq in H6. rewrite <- H6. eraseTrmTac s1' M. eraseTrmTac s1'' N. 
   unfoldTac. repeat rewrite coupleUnion in H. repeat rewrite <- Union_associative in H. 
   repeat rewrite coupleUnion. rewrite eraseUnionComm. erewrite erasePoolSingleton. 
   Focus 2. apply eraseEraseTrm; eauto. erewrite erasePoolSingleton. Focus 2. 
   apply eraseEraseTrm; eauto. repeat rewrite <- coupleUnion. 
   copy H. eapply simPureStepsCouple' with(H'':=eraseHeap x)(PT:=erasePoolAux x0)
    (N:=pfill (eraseCtxt E)(pret punit)) in H; eauto. rewrite couple_swap. rewrite coupleUnion. 
   rewrite couple_swap. rewrite coupleUnion. eapply pmultistep_trans. eassumption. unfold pUnion. 
   repeat rewrite <- coupleUnion. rewrite couple_swap. rewrite coupleUnion. rewrite couple_swap. 
   rewrite coupleUnion. repeat rewrite Union_associative in H0. rewrite <- coupleUnion in H0.
   rewrite couple_swap in H0. rewrite coupleUnion in H0. rewrite <- Union_associative in H0.
   rewrite <- coupleUnion in H0. rewrite couple_swap in H0. rewrite coupleUnion in H0. 
   rewrite <- Union_associative in H0. eapply simPureStepsCouple in H0; eauto.
   rewrite eraseFill in H0. eauto. }
  {exists (eraseHeap H'). econstructor. split; auto. inv H3. inv H4. inv H1.
   unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in H5. 
   erewrite unspecSingleton in H5. Focus 2. unspecThreadTac. auto. 
   erewrite unspecSingleton in H5; eauto. unfoldTac. rewrite union_empty_r in H5. 
   repeat rewrite eraseUnionComm. 
   repeat erewrite erasePoolSingleton; eauto. rewrite Union_commutative. econstructor. 
   eapply pSpec. copy d. rewrite <- decomposeErase in H; eauto. simpl. auto. 
   unfold pUnion. rewrite union_empty_l. rewrite <- coupleUnion in H5.
   eapply specStepSpec in H5; eauto. invertHyp. 
   eraseTrmTac s1' M'. rewrite coupleUnion. rewrite eraseUnionComm. 
   repeat erewrite erasePoolSingleton; eauto. Focus 2. apply eraseEraseTrm. eauto. 
   rewrite union_empty_r. unfoldTac. rewrite couple_swap in H. 
   rewrite (couple_swap thread _ (2::tid,locked s1'',nil,M'')) in H. 
   repeat rewrite coupleUnion in H. repeat rewrite <- Union_associative in H. 
   eapply simPureSteps in H; eauto. rewrite eraseFill in H. eassumption. 
  }
  Grab Existential Variables. repeat econstructor. repeat econstructor. repeat econstructor. 
  repeat econstructor. repeat econstructor. repeat econstructor. repeat econstructor. 
  repeat econstructor. repeat econstructor. repeat econstructor. repeat econstructor. 
  repeat econstructor. repeat econstructor. repeat econstructor. repeat econstructor. 
  repeat econstructor. repeat econstructor. repeat econstructor. repeat econstructor. 
  repeat econstructor. 
Qed. 



