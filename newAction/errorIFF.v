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

Theorem ParErrorSpecError : forall H T t PT pt,
                               erasePool T PT -> eraseThread t pt ->
                               pstep (eraseHeap H) PT pt pError -> multistep H T (tSingleton t) Error. 
Proof.
  intros. inversion H2; subst. inversion H1; subst. 
  {apply SingletonEq in H7; subst. existTac E. existTac N. existTac M. 
   rewrite decomposeErase with(e:=put (fvar x) x2)in H3; eauto. apply eraseFull' in H4. 
   invertHyp. eapply multi_error1. rewrite <- union_empty_l at 1. auto. eapply ErrorWrite. 
   eauto. eauto. }
  {apply SingletonEq in H5. subst. copy d. apply decomposeEq in H5. subst. 
   rewrite eraseFill in H3. copy d. rewrite <- decomposeErase in H5; eauto. 
   rewrite eraseFill in H5. simpl in *. eapply pctxtUnique in H3; eauto. inv H3. inv H7. }
  {apply SingletonEq in H5; subst. existTac N. existTac E. existTac M. copy d.
   eapply decomposeErase in H5; eauto. eapply pctxtUnique in H3; eauto. inv H3. inv H6. 
   apply eraseFull' in H4. invertHyp.  
  (* rewrite <- decomposeErase in H8; eauto. eapply pctxtUnique in H3; eauto. invertHyp. 
   simpl in *. inv H6. econstructor. rewrite <- union_empty_l at 1. auto. eapply PopWrite. 
   auto. eauto. auto. *) admit. }
  {apply SingletonEq in H5. subst. copy d. apply decomposeEq in H5. subst. 
   rewrite eraseFill in H3. copy d. rewrite <- decomposeErase in H5; eauto. 
   rewrite eraseFill in H5. simpl in *. eapply pctxtUnique in H3; eauto. inv H3. inv H7. }
  {apply SingletonEq in H5. subst. copy d. apply decomposeEq in H5. subst. 
   rewrite eraseFill in H3. copy d. rewrite <- decomposeErase in H5; eauto. 
   rewrite eraseFill in H5. simpl in *. eapply pctxtUnique in H3; eauto. inv H3. inv H7. }
  {apply SingletonEq in H5. subst. copy d. apply decomposeEq in H5. subst. 
   rewrite eraseFill in H3. copy d. rewrite <- decomposeErase in H5; eauto. 
   rewrite eraseFill in H5. simpl in *. eapply pctxtUnique in H3; eauto. inv H3. inv H7. }
  {symmetry in H5. apply SingletonNeqEmpty in H5. inversion H5. }
Qed. 
