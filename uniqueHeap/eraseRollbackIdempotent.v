Require Import NonSpec.       
Require Import Spec.
Require Import erasure. 
Require Import AST. 
Require Import SfLib. 
Require Import Heap. 
Require Import hetList.    
Require Import sets. 
Require Import Coq.Sets.Ensembles. 

(*Helper theorems for reasoning about the erasure of heaps being rolled back*)
Theorem raw_eraseHeapRBNew : forall H x S A,
                           raw_heap_lookup x H = Some(sempty (S::A)) ->
                           raw_eraseHeap H = raw_eraseHeap (raw_remove H x). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0; auto. }
   {simpl in *. erewrite IHlist; eauto. }
  }
Qed. 

Theorem eraseHeapRBNew : forall H x S A,
                           heap_lookup x H = Some(sempty (S::A)) ->
                           eraseHeap H = eraseHeap (remove H x). 
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq. eapply raw_eraseHeapRBNew; eauto. 
Qed. 

Theorem raw_eraseHeapRBWrite : forall H x sc S A TID N,
                      raw_heap_lookup x H = Some(sfull sc (Empty_set tid) (S::A) TID N) ->
                      raw_eraseHeap H = raw_eraseHeap (raw_replace x (sempty sc) H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0; auto. apply beq_nat_true in eq. subst. destruct sc; auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed. 

Theorem eraseHeapRBWrite : forall H x sc S A TID N,
                      heap_lookup x H = Some(sfull sc (Empty_set tid) (S::A) TID N) ->
                      eraseHeap H = eraseHeap (replace x (sempty sc) H). 
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq. eapply raw_eraseHeapRBWrite; eauto. 
Qed. 

Ltac rollbackIdemHelper :=
  match goal with
    | |-erasePool (Union ?x ?T ?t) (Union ?p (erasePoolAux ?T) (erasePoolAux ?t')) => 
      assert(erasePoolAux t' = erasePoolAux t)
  end.  
 
Theorem eraseExists : forall T t T', 
                        erasePool (tAdd T t) T' -> exists t', eraseThread t t'. 
Proof.
  intros. eapply erasePoolEraseThread. eassumption. apply Union_intror. constructor. Qed. 

Require Import Coq.Sets.Powerset_facts.  
Theorem rollbackIdempotent : forall tid stack H T H' H'' T' T'', 
                               rollback tid stack H T H' T' ->  erasePool T T'' ->
                               eraseHeap H = H'' ->
                               eraseHeap H' = H'' /\ erasePool T' T''. 
Proof.
  intros. genDeps{H''; T''}. induction H0; intros; subst.  
  {split; auto. }
  {eapply IHrollback. inversion H6. unfold tAdd. unfold Add. rewrite eraseUnionComm. 
   rollbackIdemHelper. destruct s1'. 
   {repeat erewrite erasePoolSingleton. reflexivity. eauto. eauto. }
   {apply eraseExists in H6. inv H6. repeat erewrite erasePoolSingleton. reflexivity. 
    Focus 2. eauto. rewrite <- eraseTwoActs. eauto. }
   rewrite H4. rewrite <- eraseUnionComm. constructor. symmetry.
   erewrite <- eraseHeapDependentRead; eauto. }
  {assert(exists t', eraseThread (TID', fAct M' E N' d::s1', s2, M) t'). eapply erasePoolEraseThread. 
   eauto. apply Union_intror. constructor. inv H. eapply IHrollback. inv H5. 
   unfold tAdd. unfold Add.  unfold tCouple. rewrite couple_swap. rewrite coupleUnion. 
   repeat rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto. rewrite union_empty_l. 
   rollbackIdemHelper. repeat erewrite erasePoolSingleton. auto. Focus 2. eauto. 
   destruct s1'. inversion H2; try invertListNeq. inv H8. destruct s1'; inv H10. auto. 
   invertListNeq. rewrite <- eraseTwoActs. eauto. rewrite H. rewrite <- eraseUnionComm. 
   constructor. auto. }
  {inversion H5; subst. apply eraseExists in H5. inv H5. eapply IHrollback. unfold tAdd. 
   unfold Add. rewrite eraseUnionComm. rollbackIdemHelper. repeat erewrite erasePoolSingleton; eauto. 
   destruct s1'. inversion H; try invertListNeq. destruct s1'; inv H8. auto. invertListNeq. 
   rewrite <- eraseTwoActs. eauto. rewrite H1. rewrite <- eraseUnionComm. constructor. 
   symmetry. eapply eraseHeapRBWrite; eauto. }
  {inversion H6; subst. apply eraseExists in H6. inv H6. eapply IHrollback. unfold tAdd. 
   unfold Add. rewrite eraseUnionComm. rollbackIdemHelper. repeat erewrite erasePoolSingleton; eauto. 
   destruct s1'. inversion H; try invertListNeq. destruct s1'; inv H9. auto. invertListNeq. 
   rewrite <- eraseTwoActs. eauto. rewrite H2. rewrite <- eraseUnionComm. constructor. 
   symmetry. eapply eraseHeapRBNew; eauto. }
  {assert(exists t', eraseThread (TID', srAct M' E M'' N'' d::s1', s2, M) t'). eapply erasePoolEraseThread. 
   eauto. constructor. apply Union_intror. constructor. inv H. eapply IHrollback. inv H5. 
   unfold tAdd. unfold Add. repeat rewrite eraseUnionComm.
   replace(erasePoolAux (Singleton thread (2 :: TID', [specAct; specAct], s2', N))) with (Empty_set ptrm).
   Focus 2. erewrite erasePoolSingleton; eauto. eapply tEraseCreatedSpec with(s1':=[specAct]); auto. 
   rewrite union_empty_r. rollbackIdemHelper. 
   repeat erewrite erasePoolSingleton; eauto. destruct s1'. 
   inv H2; try invertListNeq. destruct s1'; inv H8. auto. invertListNeq. rewrite <- eraseTwoActs. 
   eauto. rewrite H. rewrite <- eraseUnionComm. constructor. auto. }
Qed. 
 