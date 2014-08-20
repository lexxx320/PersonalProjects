Require Import erasure. 

(*Helper theorems for reasoning about the erasure of heaps being rolled back*)
Theorem raw_eraseHeapRBNew : forall H x,
                           raw_heap_lookup x H = Some(sempty SPEC) ->
                           raw_eraseHeap H = raw_eraseHeap (raw_remove H x). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0; auto. }
   {simpl in *. erewrite IHlist; eauto. }
  }
Qed. 

Theorem eraseHeapRBNew : forall H x,
                           heap_lookup x H = Some(sempty SPEC) ->
                           eraseHeap H = eraseHeap (Heap.remove H x). 
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq. eapply raw_eraseHeapRBNew; eauto. 
Qed. 

Theorem raw_eraseHeapRBWrite : forall H x sc TID N,
                      raw_heap_lookup x H = Some(sfull sc nil SPEC TID N) ->
                      raw_eraseHeap H = raw_eraseHeap (raw_replace x (sempty sc) H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {apply beq_nat_true in eq. subst. inv H0. destruct sc; auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed. 

Theorem eraseHeapRBWrite : forall H x sc TID N,
                      heap_lookup x H = Some(sfull sc nil SPEC TID N) ->
                      eraseHeap H = eraseHeap (replace x (sempty sc) H). 
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq. eapply raw_eraseHeapRBWrite; eauto. 
Qed. 
 
Theorem erasePoolApp : forall T1 T2, 
                          erasePool(T1++T2) = erasePool T1++erasePool T2. 
Proof.
  induction T1; intros. 
  {simpl. auto. }
  {simpl. rewrite IHT1. unfold tUnion. unfold Union. rewrite <- app_assoc. auto. }
Qed. 

Theorem eraseAdd : forall T t1 t2,
                      eraseThread t1 = eraseThread t2 ->
                      erasePool (tAdd T t1) = erasePool (tAdd T t2).
Proof.
  induction T; intros. 
  {simpl. rewrite H. auto. }
  {simpl. repeat rewrite erasePoolApp. simpl. rewrite H. auto. }
Qed. 

Theorem eraseAddCouple : forall T t1 t2,
                            erasePool t1 = eraseThread t2 ->
                            erasePool (tUnion T t1) = erasePool (tAdd T t2).
Proof.
  induction T; intros. 
  {simpl. rewrite H. unfold tUnion. rewrite union_empty_r. auto. }
  {simpl. unfold tUnion. unfold Union. repeat rewrite erasePoolApp.
   rewrite H. simpl. unfoldTac. rewrite union_empty_r. auto. }
Qed. 

Theorem eraseThreadActTerm : forall tid a s1 s2 M M',
              actionTerm a M' ->
              eraseThread(tid,aCons a s1,s2,M) = 
              eraseThread(tid, s1,s2,M'). 
Proof.
  intros. destruct s1; auto. 
  {destruct l. simpl. inv H; auto. uCons a0 l. erewrite eraseTwoActs.  
   eauto. }
Qed. 


Theorem rollbackIdempotent : forall tid stack H T H' T', 
                               rollback tid stack H T H' T' ->  
                               erasePool T = erasePool T' /\
                               eraseHeap H = eraseHeap H'.
Proof.
  intros. induction H0; subst.  
  {split; auto. }
  {invertHyp. split. rewrite <- H. apply eraseAdd. erewrite eraseThreadActTerm. 
   eauto. constructor. rewrite <- H0. erewrite eraseHeapDependentRead; eauto. }
  {invertHyp. split. rewrite <- H. apply eraseAddCouple. unfoldTac. rewrite couple_swap. 
   erewrite <- eraseThreadActTerm; simpl; eauto. rewrite app_nil_r. auto. constructor. 
   auto. }
  {invertHyp. split. rewrite <- H. apply eraseAdd. erewrite eraseThreadActTerm. 
   eauto. constructor. rewrite <- H1. erewrite eraseHeapRBWrite; eauto. }
  {invertHyp. rewrite <- H. split. apply eraseAdd. erewrite eraseThreadActTerm. 
   eauto. constructor. rewrite <- H2. erewrite eraseHeapRBNew; eauto. }
  {invertHyp. split. rewrite <- H. apply eraseAddCouple.
   erewrite <- eraseThreadActTerm. simpl. rewrite app_nil_r; eauto. constructor. 
   auto. }
Qed. 
