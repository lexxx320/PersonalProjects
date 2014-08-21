Require Import erasure.   
Require Import SpecImpliesNonSpec.
Require Import stepWF. 
Require Import IndependenceCommon.
Require Import nonspeculativeImpliesSpeculative. 

Theorem raw_eraseFull : forall H x N tid ds,
                          raw_heap_lookup x H = Some(sfull COMMIT ds COMMIT tid N) ->
                          raw_heap_lookup x (raw_eraseHeap H) = Some(pfull (eraseTerm N)). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {apply IHlist in H0. destruct i0. destruct s; eauto. simpl. rewrite eq. eauto. 
    destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem eraseFull : forall H x N tid ds,
                      heap_lookup x H = Some(sfull COMMIT ds COMMIT tid N) ->
                      heap_lookup x (eraseHeap H) = Some(pfull (eraseTerm N)). 
Proof.
  intros. destruct H. simpl in *. eapply raw_eraseFull; eauto. 
Qed. 
  

Ltac existTac e := let n := fresh in
                   try(assert(n:exists e', eraseTerm e' = e) by apply eTerm; inv n);
                   try(assert(n:exists e', eraseCtxt e' = e) by apply eCtxt; inv n). 

Theorem specErrorParError : forall H T t, 
                       step H T t Error -> 
                       pstep (eraseHeap H) (erasePool T) (erasePool t) pError. 
Proof.
  intros. inv H0. eapply eraseFull in H2. simpl. eapply PPutError.
  erewrite <- decomposeErase in H1; eauto. simpl. auto. eauto. 
Qed. 

Theorem ParErrorSpecError : forall H T t H' T' t',
                              pstep H T t pError -> specHeap H H' -> speculate T T' ->
                              speculate t t' -> multistep H' (tUnion T' t') None.  
Proof.
  intros. inv H0. inv H3. inv H7. copy H4. apply decomposeSpec in H4. 
  unfoldTac. eapply specHeapLookupFull in H5; eauto. invertHyp. 
  rewrite Union_associative. eapply Spec.smulti_error. eapply ErrorWrite. 
  simpl in *. eauto. eauto. 
Qed.                          
 
Theorem pmulti_trans : forall H T H' T' c, 
                         pmultistep H T (Some(H', T')) ->
                         pmultistep H' T' c -> 
                         pmultistep H T c. 
Proof.
  intros. dependent induction H0; eauto. 
  {econstructor. eauto. eauto. }
Qed. 

Theorem specErrorParErrorStar : forall H T, 
                              wellFormed H T -> 
                              multistep H T None -> 
                              pmultistep (eraseHeap H) (erasePool T) None. 
Proof.
  intros. remember (@None (sHeap * pool)). induction H1; intros. 
  {inv Heqo. }
  {subst. copy H1. eapply specImpliesNonSpec in H1; eauto. invertHyp.  
   rewrite eraseUnionComm. eapply pmulti_trans. eassumption.
   eapply stepWF in H3; eauto. rewrite <- eraseUnionComm. eapply IHmultistep; eauto. }
  {eapply specErrorParError in H1; eauto. rewrite eraseUnionComm. 
   eapply pmulti_error. eauto. }
Qed. 

Theorem multi_trans : forall H T H' T' c, multistep H T (Some(H', T')) ->  
                                          multistep H' T' c ->
                                          multistep H T c. 
Proof.
  intros. remember (Some(H',T')). induction H0. 
  {inv Heqo. auto. }
  {subst. econstructor. eauto. eauto. }
  {inv Heqo. }
Qed. 

Theorem ParErrorSpecErrorStar : forall H T H' T',
                                  pmultistep H T None -> specHeap H H' -> heapWF H -> PoolWF T ->
                                  speculate T T' -> multistep H' T' None. 
Proof.
  intros. genDeps{H'; T'}. dependent induction H0; intros. 
  {copy H0. eapply nonspecImpliesSpec in H0; eauto. invertHyp. 
   eapply pstepWF in H6; eauto. invertHyp. inv H7. econstructor. 
   eauto. eapply multi_trans. eassumption. eapply IHpmultistep; eauto. }
  {apply specUnionComm in H4. invertHyp. eapply ParErrorSpecError in H0; eauto. }
Qed. 




