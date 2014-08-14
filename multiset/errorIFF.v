Require Import erasure.   
Require Import SpecImpliesNonSpec.
Require Import stepWF. 
Require Import IndependenceCommon.

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

Theorem lookupSomeUnique : forall T H x v S,
                             unique T S H -> Ensembles.In AST.id S x ->
                             raw_heap_lookup x H = Some v -> False. 
Proof.
  induction H; intros. 
  {inv H1. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H2. inv H0. apply beq_nat_true in eq. subst. contradiction. }
   {inv H0. eapply IHlist; eauto. constructor. auto. }
  }
Qed. 

Theorem raw_eraseFull' : forall H x N S, 
          unique ivar_state S H ->
          raw_heap_lookup x (raw_eraseHeap H) = Some(pfull (eraseTerm N)) ->
          exists tid ds, raw_heap_lookup x H = 
                         Some(sfull COMMIT ds COMMIT tid N). 
Proof.
  induction H; intros. 
  {inv H0. } 
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {destruct i0. destruct s. inv H0. eapply IHlist in H1; eauto. 
    invertHyp. eapply lookupSomeUnique in H1; eauto. inv H1. apply beq_nat_true in eq. 
    subst. apply Ensembles.Union_intror. constructor. simpl in *. rewrite eq in H1. inv H1. 
    destruct s. eapply IHlist in H1. invertHyp. inv H0. eapply lookupSomeUnique in H1; eauto. 
    contradiction. apply beq_nat_true in eq. subst. apply Ensembles.Union_intror. constructor. 
    inv H0. eauto. destruct s0. simpl in H1. rewrite eq in H1. inv H1. simpl in *. 
    rewrite eq in H1. inv H1. apply eraseTermUnique in H3. subst. eauto. }
   {destruct i0. destruct s; inv H0; eauto. simpl in H1. rewrite eq in H1. 
    eauto. destruct s. inv H0; eauto. destruct s0. simpl in *. rewrite eq in H1.
    inv H0; eauto. simpl in *. rewrite eq in H1. inv H0. eauto. }
  }
Qed. 


Theorem eraseFull' : forall H x N, 
                       heap_lookup x (eraseHeap H) = Some(pfull (eraseTerm N)) ->
                       exists tid ds, heap_lookup x H = Some(sfull COMMIT ds COMMIT tid N). 
Proof.
  intros. destruct H. simpl in *. eapply raw_eraseFull' in H0; eauto. 
Qed. 

Ltac invertActList :=
  match goal with
      |H:aCons ?A ?b = locked nil |- _ => destruct b; inv H
      |H:aCons ?A ?b = unlocked nil |- _ => destruct b; inv H
  end. 

Theorem spec_multi_false : forall T T' tid s1 x M' E N d s2 M H H' a b c,
                             spec_multistep H (tUnion T (tSingleton(tid,unlocked nil,s2,M'))) H'
                                            (tUnion T' (tSingleton(tid,unlocked(s1++[wAct x M' E N d]),s2,M))) ->
                             heap_lookup x H = Some(sfull COMMIT a COMMIT b c) ->
                             False. 
Proof.
  intros. genDeps{a; b; c}. dependent induction H0; intros.
  {subst. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x1. exMid tid H7. 
   {apply UnionEqTID in x. invertHyp. inv H; try solve[falseDecomp]. 
    {inv H13; falseDecomp. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H; eauto. invertHyp. inv H5. 
     heapsDisagree. }
   }
   {apply UnionNeqTID in x. invertHyp. eapply specStepFullIVar in H; eauto. 
    invertHyp. eapply IHspec_multistep; eauto. rewrite H2. unfoldTac. 
    rewrite UnionSwap. eauto. auto. }
  }
Qed. 

Theorem wfDoubleWrite : forall H T tid s1' x M' E N d s2 M a b c,
                          wellFormed H (tAdd T (tid,unlocked(s1'++[wAct x M' E N d]),s2,M)) ->
                          heap_lookup x H = Some(sfull COMMIT a COMMIT b c) -> False. 
Proof.
  intros. inv H0. unfoldTac. rewrite AddUnion in H3. rewrite unspecUnionComm in H3. 
  erewrite unspecLastActPool in H3. Focus 2. constructor. eapply spec_multi_false in H3. 
  auto. eapply unspecHeapLookupFull; eauto. 
Qed. 


Theorem commitPoolUnionComm : forall T1 T2, 
                                commitPool (tUnion T1 T2) -> 
                                commitPool T1 /\ commitPool T2. 
Proof.
  induction T2; intros. 
  {simpl in *. unfoldTac. rewrite union_empty_r in H. auto. }
  {destructThread a. destruct H5. 
   {unfoldTac. rewrite Union_commutative in H. simpl in *. contradiction. }
   {destruct l. 
    {simpl. apply IHT2. unfoldTac. rewrite Union_commutative in H. simpl in H. 
     rewrite Union_commutative. auto. }
    {unfoldTac. rewrite Union_commutative in H. simpl in *. contradiction. }
   }
   {unfoldTac. rewrite Union_commutative in H. simpl in *. contradiction. }
  }
Qed. 

Theorem commitEraseSingle : forall t t',
                              commitPool t -> erasePool t = pSingle t' ->
                              exists tid s2 M, t = tSingleton(tid,unlocked nil, s2, M) /\
                                               eraseTerm M = t'. 
Proof.
  intros. destruct t. 
  {inv H0. }
  {destructThread t. destruct H6; try contradiction.  
   destruct l; try contradiction. simpl in *. destruct t0. 
   {inv H0. econstructor. econstructor. econstructor. split; eauto. unfold tSingleton.
    unfold Single. reflexivity. }
   {inv H0. destructThread t. destruct H9; try contradiction. destruct l; try contradiction. 
    simpl in *. inv H6. }
  }
Qed. 

Theorem ParErrorSpecError : forall H T t,
                               wellFormed H (tUnion T t) -> commitPool (tUnion T t) ->
                               pstep (eraseHeap H) (erasePool T) (erasePool t) pError ->
                               multistep H (tUnion T t) None. 
Proof.
  intros. inv H2. 
  {existTac E. existTac N. existTac M. apply commitPoolUnionComm in H1. invertHyp.
   eapply commitEraseSingle in H5; eauto. invertHyp. simpl in *. 
   rewrite decomposeErase with(e:=put (fvar x) x2)in H4; eauto. apply eraseFull' in H7.
   invertHyp. eapply smulti_error. econstructor; eauto. }
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


Theorem ParErrorSpecErrorStar : forall H T,
                                  wellFormed H T -> commitPool T -> 
                                  pmultistep (eraseHeap H) (erasePool T) None -> 
                                  multistep H T None. 
Proof.
  Admitted. (*This needs ParImpliesSpec first*)





