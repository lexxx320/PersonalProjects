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

Theorem eraseFull : forall H x N tid ds,
                      heap_lookup x H = Some(sfull nil ds nil tid N) ->
                      heap_lookup x (eraseHeap H) = Some(pfull (eraseTerm N)). 
Proof.
  induction H; intros. 
  {simpl in *. inversion H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq.  
   {inv H0. simpl. rewrite eq. auto. }
   {apply IHlist in H0. destruct i0. destruct a. simpl. rewrite eq. auto. auto. 
    destruct a. destruct a0. simpl. rewrite eq. auto. simpl. rewrite eq. auto. 
    auto. }
  }
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

Axiom heapUnique : forall (T:Type)x H (v v':T), 
                     heap_lookup x H = Some v ->
                     heap_lookup x ((x, v')::H) = Some v' -> False. 

Theorem eraseFull' : forall H x N, 
                       heap_lookup x (eraseHeap H) = Some(pfull (eraseTerm N)) ->
                       exists tid ds, heap_lookup x H = Some(sfull nil ds nil tid N). 
Proof.
  induction H; intros. 
  {simpl in H. inversion H. }
  {simpl in H0. destruct a eqn:eq1. destruct i0 eqn:eq2. 
   {destruct a0. 
    {simpl in *. destruct (beq_nat x i). inv H0. apply IHlist in H0. invertHyp. eauto. }
    {apply IHlist in H0. invertHyp. destruct (beq_nat x i) eqn:eq4. 
     {assert(heap_lookup x ((i, sempty (a0 :: a1)) :: H) = Some (sempty(a0::a1))). 
      simpl. rewrite eq4. auto. eapply heapUnique in H1. inversion H1. simpl.
      rewrite <-beq_nat_refl. eauto. }
     {simpl. rewrite eq4. eauto. }
    }
   }
   {destruct a0. 
    {destruct a1. 
     {simpl in *. destruct (beq_nat x i) eqn:eq4. inv H0. apply eraseTermUnique in H2.
      subst; eauto. apply IHlist in H0. auto. }
     {simpl in *. destruct (beq_nat x i). inv H0. apply IHlist in H0. auto. }
    }
    {apply IHlist in H0. invertHyp. simpl. destruct (beq_nat x i) eqn:eq. 
     {assert(heap_lookup x ((i, sfull (a0 :: a2) l a1 t t0) :: H) = Some ( sfull (a0 :: a2) l a1 t t0)). 
      simpl. rewrite eq. auto. eapply heapUnique in H1; eauto. inversion H1. simpl. 
     rewrite <- beq_nat_refl. eauto. }
     {eauto. }
    }
   }
  }
  Grab Existential Variables. repeat constructor. repeat constructor.
Qed. 

Ltac eqIn H := unfoldTac; 
  match type of H with
      |forall x, Ensembles.In ?X (Union ?X ?T (Singleton ?X ?t)) x -> ?y =>
       assert(Ensembles.In X(Union X T (Singleton X t)) t) by (apply Union_intror; constructor)
  end.
 
Theorem unspecHeapTrans : forall H H' H'', unspecHeap H H'' -> unspecHeap H' H'' -> 
                                           unspecHeap H H''.
Proof.
  intros. generalize dependent H'. induction H0; intros; eauto. 
Qed. 


Theorem EqJMeq : forall (T:Type) (x y:T), x = y -> JMeq x y.
Proof.
  intros. subst. auto. Qed. 

Axiom UnionSingletonEq : forall T T' a b, tUnion T (tSingleton a) = tUnion T' (tSingleton b) -> 
                                          tIn T' a -> T = tUnion (Subtract thread T' a) (tSingleton b).

Theorem xNeqSx : forall x, x <> S x. induction x; intros c; try solve[inv c]. 
                                     inversion c. auto. 
Qed. 
Theorem specStepCommitFullIVar:  forall x H H' ds tid M T t t',
                                   spec_step H T t H' T t' ->
                                   heap_lookup x H = Some(sfull nil ds nil tid M) ->
                                  exists ds', heap_lookup x H' = Some(sfull nil ds' nil tid M). 
Proof. 
  intros. inv H0; try solve[econstructor; eauto]. 
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. eapply lookupDeterministic in H2; eauto. inv H2. 
    exists (tid0::ds0). erewrite HeapLookupReplace; eauto. }
   {eapply lookupReplaceNeq in H1; eauto. intros c. apply beq_nat_false in eq. contradiction. }
  }
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. eapply lookupDeterministic in H2; eauto. inv H2. }
   {eapply lookupReplaceNeq in H1; eauto. apply beq_nat_false in eq. auto. }
  }
  {destruct H; simpl in *. 
   {inv H1. }
   {destruct p. inv H2. destruct (beq_nat x i) eqn:eq. 
    {inv H1. simpl. apply beq_nat_true in eq. subst. assert(i <> S i). apply xNeqSx. 
     apply beq_nat_false_iff in H0. rewrite H0. rewrite <- beq_nat_refl. eauto. }
    {admit. }
   }
  }
Qed. 

Theorem spec_multi_false : forall T T' tid s1 x M' E N d s2 M H H' a b c,
                             spec_multistep H (tUnion T (tSingleton(tid,nil,s2,M'))) H'
                                            (tUnion T' (tSingleton(tid,s1++[wAct x M' E N d],s2,M))) ->
                             heap_lookup x H = Some(sfull nil a nil b c) ->
                             False. 
Proof.
  intros. genDeps{a; b; c}. dependent induction H0; intros.
  {subst. unfoldSetEq x. eqIn H. apply H in H2. inversion H2; subst. 
   {assert(thread_lookup(tAdd T'(tid,s1++[wAct x0 M' E N d],s2,M)) tid (tid,nil,s2,M')). 
    econstructor. econstructor;eauto. eauto. 
    assert(thread_lookup(tAdd T'(tid,s1++[wAct x0 M' E N d],s2,M)) tid (tid,s1++[wAct x0 M' E N d],s2,M)). 
    econstructor. apply Union_intror. auto. auto. eapply uniqueThreadPool in H4; eauto.
    inv H4. invertListNeq. }
   {inv H3. invertListNeq. }
  }
  {copy x. copy H. apply specStepSingleton in H. invertHyp. unfoldSetEq x. eqIn H. apply H in H5. 
   inversion H5; subst. eapply specStepCommitFullIVar in H1; eauto. invertHyp.
   {copy H2. eapply UnionSingletonEq in H2; auto. subst. 
    eapply IHspec_multistep with (T0 := (tUnion (Subtract thread T x1) (tAdd t' (tid,nil,s2,M')))); eauto. 
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
        |H:?a = ?b |- _ => solve[inv H]
    end]. 
    {unfoldTac; invertHyp. inv H9. copy d. copy d0. eapply uniqueCtxtDecomp in H6; eauto. 
     inv H6. inv H9. }
    {unfoldTac; invertHyp. inv H6. copy d; copy d0. eapply uniqueCtxtDecomp in H6; eauto. 
     inv H6. inv H10. }
    {unfoldTac; invertHyp. inv H6. copy d; copy d0. eapply uniqueCtxtDecomp in H6; eauto. 
     inv H6. inv H10. eapply lookupDeterministic in H1; eauto. inv H1. }
    {unfoldTac; invertHyp. inv H6. copy d; copy d0. eapply uniqueCtxtDecomp in H6; eauto. 
     inv H6. inv H10. }
    {unfoldTac; invertHyp. inv H9. copy d; copy d0. eapply uniqueCtxtDecomp in H6; eauto. 
     inv H6. inv H9. }
   }
  }
Qed. 

Theorem unspecHeapLookupFull : forall H H' x a b c,
                                 heap_lookup x H = Some(sfull nil a nil b c) ->
                                 unspecHeap H H' ->
                                 heap_lookup x H' = Some(sfull nil nil nil b c).
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. inv H1. simpl. rewrite eq. auto. }
   {inv H1; eauto; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem wfDoubleWrite : forall H T tid s1' x M' E N d s2 M a b c,
                          wellFormed H (tAdd T (tid,s1'++[wAct x M' E N d],s2,M)) ->
                          heap_lookup x H = Some(sfull nil a nil b c) -> False. 
Proof.
  intros. inv H0. inv H3. unfoldTac. rewrite unspecUnionComm in H5. erewrite unspecSingleton in H5.
  Focus 2. eapply unspecWrite. auto. eapply unspecHeapLookupFull in H1; eauto. 
  eapply spec_multi_false in H5; eauto. 
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
  {symmetry in H6. apply SingletonNeqEmpty in H6. inversion H6. }
Qed. 
