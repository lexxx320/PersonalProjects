Require Import NonSpec.          
Require Import Spec.
Require Import Coq.Sets.Ensembles.
Require Import SfLib.  
Require Import erasure.  
Require Import sets. 
Require Import hetList. 
Require Import Heap. 
Require Import AST. 
Require Import Coq.Program.Equality.
Require Import unspec. 
Require Import classifiedStep. 
Require Import SpecLib.

Theorem raw_eraseFull : forall H x N tid ds,
                          raw_heap_lookup x H = Some(sfull (unlocked nil) ds (unlocked nil) tid N) ->
                          raw_heap_lookup x (raw_eraseHeap H) = Some(pfull (eraseTerm N)). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {apply IHlist in H0. destruct i0. destruct (commit a). simpl. rewrite eq. auto. 
    auto. destruct (commit a). destruct (commit a0). simpl. rewrite eq. auto. simpl. 
    rewrite eq. auto. auto. }
  }
Qed. 

Theorem eraseFull : forall H x N tid ds,
                      heap_lookup x H = Some(sfull (unlocked nil) ds (unlocked nil) tid N) ->
                      heap_lookup x (eraseHeap H) = Some(pfull (eraseTerm N)). 
Proof.
  intros. destruct H. simpl in *. eapply raw_eraseFull; eauto. 
Qed. 
  
Ltac eqSets := apply Extensionality_Ensembles; unfold Same_set; unfold Included; split; intros.
Ltac unfoldSetEq H := apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H; inv H.

Ltac existTac e := let n := fresh in
                   try(assert(n:exists e', eraseTerm e' = e) by apply eTerm; inv n);
                   try(assert(n:exists e', eraseCtxt e' = e) by apply eCtxt; inv n). 

Ltac clean :=
  repeat match goal with
           |H:exists c, ?a |- _ => inv H
           |H:?a /\ ?b |- _ => inv H
         end. 


Theorem specErrorParError : forall H T t PH PT pt, 
                              eraseHeap H = PH -> erasePool T PT -> eraseThread t pt ->
                              step H T (tSingleton t) Error -> pstep PH PT pt pError. 
Proof.
  intros. inversion H3; subst. eapply eraseFull in H8; eauto. apply SingletonEq in H4. 
  subst. inv H2; try invertListNeq. econstructor. eapply decomposeErase in H5. eauto. 
  apply decomposeEq in H5. subst. auto. auto. simpl. auto. eauto.  
Qed.  


Theorem lookupSomeUnique : forall T H x v S,
                             unique T S H -> Ensembles.In id S x ->
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
                         Some(sfull (unlocked nil) ds (unlocked nil) tid N). 
Proof.
  induction H; intros. 
  {inv H0. } 
  {simpl in *. destruct a eqn:eq1. destruct i0 eqn:eq2. 
   {destruct (commit a0). 
    {simpl in *. destruct (beq_nat x i). inv H1. eapply IHlist in H1. invertHyp. 
     eauto.     inversion H0; subst. eauto. }
    {eapply IHlist in H1. invertHyp. simpl in *. destruct (beq_nat x i) eqn:eq4. 
     {inversion H0; subst. apply beq_nat_true in eq4. subst. 
      eapply lookupSomeUnique in H1; eauto. inv H1. apply Union_intror. constructor. }
     {eauto. }
     {subst. inversion H0; subst. eauto. }
    }
   }
   {destruct (commit a0) eqn:eq5. 
    {destruct (commit a1)eqn:eq6. 
     {simpl in *. destruct (beq_nat x i) eqn:eq4. inv H1.
      apply eraseTermUnique in H3. subst. destruct a0; inv eq5.
      destruct a1; inv eq6. destruct l; inv H2. destruct l0; inv H3.
      eauto. eapply IHlist in H1; eauto. inv H0. eauto. }
     {simpl in *. destruct (beq_nat x i). inv H1. eapply IHlist in H1. auto. 
      inversion H0; subst. eauto. }
    }
    {simpl in *. destruct (beq_nat x i) eqn:eq. 
     {subst. eapply IHlist in H1; eauto. invertHyp. inversion H0; subst. 
      eapply lookupSomeUnique in H1; eauto. inv H1. apply beq_nat_true in eq. 
      subst. apply Union_intror. constructor. inv H0. eauto. }
     {subst. eapply IHlist; eauto. inversion H0; subst. eauto. }
    }
   }
  }
Qed. 

Theorem eraseFull' : forall H x N, 
                       heap_lookup x (eraseHeap H) = Some(pfull (eraseTerm N)) ->
                       exists tid ds, heap_lookup x H = Some(sfull (unlocked nil) ds (unlocked nil) tid N). 
Proof.
  intros. destruct H. simpl in *. eapply raw_eraseFull' in H0; eauto. 
Qed. 

Ltac eqIn H := unfoldTac; 
  match type of H with
      |forall x, Ensembles.In ?X (Union ?X ?T (Singleton ?X ?t)) x -> ?y =>
       assert(Ensembles.In X(Union X T (Singleton X t)) t) by (apply Union_intror; constructor)
  end.

Theorem EqJMeq : forall (T:Type) (x y:T), x = y -> JMeq x y.
Proof.
  intros. subst. auto. Qed. 

Axiom UnionSingletonEq : forall T T' a b, 
                 tUnion T (tSingleton a) = tUnion T' (tSingleton b) -> 
                 tIn T' a -> T = tUnion (Subtract thread T' a) (tSingleton b).

Ltac invertActList :=
  match goal with
      |H:aCons ?A ?b = locked nil |- _ => destruct b; inv H
      |H:aCons ?A ?b = unlocked nil |- _ => destruct b; inv H
  end. 

Theorem spec_multi_false : forall T T' tid s1 x M' E N d s2 M H H' a b c,
                             spec_multistep H (tUnion T (tSingleton(tid,unlocked nil,s2,M'))) H'
                                            (tUnion T' (tSingleton(tid,unlocked(s1++[wAct x M' E N d]),s2,M))) ->
                             heap_lookup x H = Some(sfull (unlocked nil) a (unlocked nil) b c) ->
                             False. 
Proof.
  intros. genDeps{a; b; c}. dependent induction H0; intros.
  {subst. unfoldSetEq x. eqIn H. apply H in H2. inversion H2; subst. 
   {assert(thread_lookup(tAdd T'(tid,unlocked(s1++[wAct x0 M' E N d]),s2,M)) tid (tid,unlocked nil,s2,M')). 
    econstructor. econstructor;eauto. eauto. 
    assert(thread_lookup(tAdd T'(tid,unlocked(s1++[wAct x0 M' E N d]),s2,M)) tid 
                        (tid,unlocked(s1++[wAct x0 M' E N d]),s2,M)). 
    econstructor. apply Union_intror. auto. auto. eapply uniqueThreadPool in H4; eauto.
    inv H4. invertListNeq. }
   {inv H3. invertListNeq. }
  }
  {copy x. copy H. apply specStepSingleton in H. invertHyp. unfoldSetEq x. eqIn H. apply H in H5. 
   inversion H5; subst. eapply specStepFullIVar in H1; eauto. invertHyp.
   {copy H2. eapply UnionSingletonEq in H2; auto. subst. 
    eapply IHspec_multistep with (T0 := (tUnion (Subtract thread T x1) (tAdd t' (tid,unlocked nil,s2,M')))); eauto. 
    apply EqJMeq. eqSets. 
    {inversion H2; subst. inversion H8; subst. constructor. constructor. auto. 
     inv H9. constructor. apply Union_intror. apply Union_intror. auto. constructor. 
     apply Union_intror. constructor. auto. }
    {inversion H2; subst. inversion H8; subst. constructor. constructor. auto. inversion H9; subst.
     apply Union_intror. auto. inv H10. constructor. apply Union_intror. constructor. 
     inv H8. constructor. apply Union_intror. constructor. }
   }
   {inv H6. inversion H3;try solve[ unfoldTac; invertHyp; 
    match goal with
        |H:?a = ?b |- _ => solve[inv H; invertActList]
    end];
    try solve[unfoldTac; invertHyp; 
     match goal with 
         |H:(_,_,_,_) = (_,_,_,_) |- _ => inv H
     end; copy d; copy d0; 
     match goal with
         |H:decompose ?M ?E ?e, H' : decompose ?M' ?E' ?e' |- _ => eapply uniqueCtxtDecomp in H; eauto
     end; invertHyp; cleanup].
    {unfoldTac; invertHyp. inv H6; inv H7; copy d; eapply uniqueCtxtDecomp in H6; 
                           eauto; invertHyp; solveByInv. }
    {{unfoldTac; invertHyp. inv H6. copy d; copy d0.
      eapply uniqueCtxtDecomp in H6; eauto. 
     invertHyp. inv H10. rewrite H1 in H7. inv H7. }
    }
   }
  }
Qed. 

Theorem wfDoubleWrite : forall H T tid s1' x M' E N d s2 M a b c,
                          wellFormed H (tAdd T (tid,unlocked(s1'++[wAct x M' E N d]),s2,M)) ->
                          heap_lookup x H = Some(sfull (unlocked nil) a (unlocked nil) b c) -> False. 
Proof.
  intros. inv H0. inv H3. unfoldTac. rewrite unspecUnionComm in H4. erewrite unspecSingleton in H4.
  Focus 2. eapply unspecWrite. auto. eapply unspecHeapLookupFull in H1; eauto. 
  eapply spec_multi_false in H4; eauto. 
Qed. 

Theorem ParErrorSpecError : forall H T t PT pt,
                               wellFormed H (tAdd T t) -> erasePool T PT -> eraseThread t pt ->
                               pstep (eraseHeap H) PT pt pError -> multistep H T (tSingleton t) Error. 
Proof.
  intros. inversion H3; subst. inversion H2; subst. 
  {apply SingletonEq in H8; subst. existTac E. existTac N. existTac M. 
   rewrite decomposeErase with(e:=put (fvar x) x2)in H4; eauto. apply eraseFull' in H5. 
   invertHyp. eapply multi_error1. rewrite <- union_empty_l at 1. auto. eapply ErrorWrite. 
   eauto. eauto. }
  {apply SingletonEq in H6. subst. copy d. apply decomposeEq in H6. subst. 
   rewrite eraseFill in H4. copy d. rewrite <- decomposeErase in H6; eauto. 
   rewrite eraseFill in H6. simpl in *. eapply pctxtUnique in H4; eauto. inv H4. inv H8. }
  {apply SingletonEq in H6; subst. existTac N. existTac E. existTac M. copy d.
   eapply decomposeErase in H6; eauto. eapply pctxtUnique in H4; eauto. inv H4. inv H7. 
   apply eraseFull' in H5. invertHyp.  simpl in H8. inv H8. eapply wfDoubleWrite in H0; eauto. 
   inv H0. }
  {apply SingletonEq in H6. subst. copy d. apply decomposeEq in H6. subst. 
   rewrite eraseFill in H4. copy d. rewrite <- decomposeErase in H6; eauto. 
   rewrite eraseFill in H6. simpl in *. eapply pctxtUnique in H4; eauto. inv H4. inv H8. }
  {apply SingletonEq in H6. subst. copy d. apply decomposeEq in H6. subst. 
   rewrite eraseFill in H4. copy d. rewrite <- decomposeErase in H6; eauto. 
   rewrite eraseFill in H6. simpl in *. eapply pctxtUnique in H4; eauto. inv H4. inv H8. }
  {apply SingletonEq in H6. subst. copy d. apply decomposeEq in H6. subst. 
   rewrite eraseFill in H4. copy d. rewrite <- decomposeErase in H6; eauto. 
   rewrite eraseFill in H6. simpl in *. eapply pctxtUnique in H4; eauto. inv H4. inv H8. }
  {symmetry in H8. apply SingletonNeqEmpty in H8. contradiction. }
  {symmetry in H8. apply SingletonNeqEmpty in H8. contradiction. }
Qed. 





