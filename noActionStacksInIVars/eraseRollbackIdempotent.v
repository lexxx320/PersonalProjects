Require Import NonSpec.       
Require Import Spec.
Require Import erasure. 
Require Import AST. 
Require Import SfLib. 
Require Import Heap. 
Require Import hetList.    
Require Import sets. 
Require Import Coq.Sets.Ensembles. 
Require Import unspec. 
Require Import classifiedStep. 
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
                           eraseHeap H = eraseHeap (remove H x). 
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
  {eapply IHrollback. inv H7. unfoldTac. rewrite eraseUnionComm. rollbackIdemHelper. destruct s1'. 
   {repeat erewrite erasePoolSingleton. reflexivity. eauto. simpl. eauto. }
   {destruct l. 
    {erewrite erasePoolSingleton; eauto. simpl. erewrite erasePoolSingleton; eauto.
     eraseThreadTac. rewrite app_nil_l. auto. }
    {erewrite erasePoolSingleton; eauto. 
     assert(exists t, eraseThread(TID',unlocked (a::l),s2,M') t). apply eraseThreadTotal. 
     invertHyp. erewrite erasePoolSingleton; eauto. uCons a l. rewrite eraseTwoActs. eauto. }
   }
   {erewrite erasePoolSingleton; eauto. simpl; erewrite erasePoolSingleton; eauto. }
   rewrite H. rewrite <- eraseUnionComm. constructor. eapply eraseHeapDependentRead. 
   eauto.
  }
  {eapply IHrollback. inv H5. unfoldTac. rewrite coupleUnion. destruct s1'. 
   {repeat rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto. 
    erewrite erasePoolSingleton; eauto. rewrite union_empty_r. rewrite <- eraseUnionComm. 
    constructor. erewrite erasePoolSingleton; eauto. simpl. auto. }
   {destruct l. 
    {repeat rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto. 
     erewrite erasePoolSingleton; eauto. rewrite union_empty_r. rewrite <- eraseUnionComm. 
     constructor. erewrite erasePoolSingleton; eauto. simpl. eraseThreadTac. 
     rewrite app_nil_l. auto. }
    {repeat rewrite eraseUnionComm. assert(exists t, eraseThread(TID',unlocked(a::l),s2,M') t). 
     apply eraseThreadTotal. invertHyp. erewrite erasePoolSingleton; eauto.
     erewrite erasePoolSingleton; eauto. rewrite union_empty_r. rewrite <- eraseUnionComm. 
     constructor. erewrite erasePoolSingleton; eauto. uCons a l. rewrite eraseTwoActs. 
     eauto. }
   } 
   {repeat rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto. 
    erewrite erasePoolSingleton; eauto. rewrite union_empty_r. rewrite <- eraseUnionComm. 
    auto. erewrite erasePoolSingleton; eauto. simpl; auto. } auto. 
  }
  {eapply IHrollback. inversion H5. unfold tAdd. unfold Add. rewrite eraseUnionComm. 
   rollbackIdemHelper. destruct s1'. 
   {repeat erewrite erasePoolSingleton. reflexivity. eauto. simpl. eauto. }
   {destruct l. 
    {erewrite erasePoolSingleton; eauto. simpl. erewrite erasePoolSingleton; eauto.
     eraseThreadTac. rewrite app_nil_l. auto. }
    {apply eraseExists in H5. invertHyp. erewrite erasePoolSingleton; eauto. 
     erewrite erasePoolSingleton; eauto. uCons a l; auto.
     rewrite <- eraseTwoActs. eauto. }
   }
   {erewrite erasePoolSingleton; eauto. simpl; erewrite erasePoolSingleton; eauto. }
   rewrite H3. rewrite <- eraseUnionComm. constructor. symmetry. eapply eraseHeapRBWrite; eauto. }
  {eapply IHrollback. inversion H6. unfold tAdd. unfold Add. rewrite eraseUnionComm. 
   rollbackIdemHelper. destruct s1'. 
   {repeat erewrite erasePoolSingleton. reflexivity. eauto. simpl. eauto. }
   {destruct l. 
    {erewrite erasePoolSingleton; eauto. simpl. erewrite erasePoolSingleton; eauto.
     eraseThreadTac. rewrite app_nil_l. auto. }
    {apply eraseExists in H6. invertHyp. erewrite erasePoolSingleton; eauto. 
     erewrite erasePoolSingleton; eauto. uCons a l; auto.
     rewrite <- eraseTwoActs. eauto. }
   }
   {erewrite erasePoolSingleton; eauto. simpl; erewrite erasePoolSingleton; eauto. }
   rewrite H4. rewrite <- eraseUnionComm. constructor. symmetry. 
   eapply eraseHeapRBNew; eauto. 
  }
  {eapply IHrollback. inv H5. unfoldTac. destruct s1'. 
   {repeat rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto. 
    erewrite erasePoolSingleton; eauto. rewrite union_empty_r. rewrite <- eraseUnionComm. 
    constructor. erewrite erasePoolSingleton; eauto. simpl. auto. }
   {destruct l. 
    {repeat rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto. 
     erewrite erasePoolSingleton; eauto. rewrite union_empty_r. rewrite <- eraseUnionComm. 
     constructor. erewrite erasePoolSingleton; eauto. simpl. eraseThreadTac. 
     rewrite app_nil_l. auto. }
    {repeat rewrite eraseUnionComm. assert(exists t, eraseThread(TID',unlocked(a::l),s2,M') t). 
     apply eraseThreadTotal. invertHyp. erewrite erasePoolSingleton; eauto.
     erewrite erasePoolSingleton; eauto. rewrite union_empty_r. rewrite <- eraseUnionComm. 
     constructor. erewrite erasePoolSingleton; eauto. uCons a l. rewrite eraseTwoActs. 
     eauto. }
   }
   {repeat rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto.
    erewrite erasePoolSingleton; eauto. rewrite union_empty_r. rewrite <- eraseUnionComm. 
    auto. simpl; erewrite erasePoolSingleton; eauto. }
   auto.
  }
Qed. 