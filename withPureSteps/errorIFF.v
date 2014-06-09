Require Import NonSpec.   
Require Import Spec.
Require Import Coq.Sets.Ensembles.
Require Import SfLib.  
Require Import erasure.  
Require Import sets. 

Theorem eraseFull : forall H H' x N tid ds N',
                      eraseHeap H H' -> eraseTerm N tEmptySet N' ->
                      Heap.heap_lookup x H = Some(AST.sfull nil ds nil tid N) ->
                      Heap.heap_lookup x H' = Some(AST.pfull N'). 
Proof.
  induction H; intros. 
  {simpl in *. inversion H1. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq.  
   {inversion H2; subst. clear H2. inversion H0; subst. simpl. rewrite eq. 
    eapply termErasureDeterminism in H1. rewrite <- H1. reflexivity. assumption. }
   {inversion H0; subst; eauto; solve[simpl; rewrite eq; eauto]. }
  }
Qed. 

Theorem z : forall H T tid s2 M sigma,
              step H T (tSingleton (tid, [], s2, M)) sigma ->
              exists M', eraseTerm M T M'. 
Admitted. 

Axiom eraseSameThread : forall t t', eraseThread t (tSingleton t) t' <->
                                     eraseThread t tEmptySet t'. 

Ltac eraseDetHelper :=
  match goal with
      |H:forall M, eraseTerm ?t1 ?T M -> ?x = M, H':eraseTerm ?t1 ?T ?y |- _ =>
       apply H in H'; subst
  end. 

Theorem eraseTermEmptyDet : forall M M' M'' T,
                              eraseTerm M T M' -> eraseTerm M tEmptySet M'' ->
                              M' = M''. 
Proof.
  intros. generalize dependent M''. induction H; intros;
  try solve[inversion H0; subst; auto]; try solve[
  match goal with
      |H:eraseTerm ?t tEmptySet ?M |- _ => inversion H; repeat eraseDetHelper; eauto
  end]. 
  {inversion H3; subst. inversion H13; subst. inversion H9. }
Qed. 

Ltac cleanup :=
  match goal with
      |H:?x = ?y |- _ => inversion H; subst
  end. 

Ltac eraseThreadHelper :=
  match goal with
      |H:eraseTerm ?M ?T ?M', H':eraseTerm ?M tEmptySet ?M'' |- _ =>
      eapply eraseTermEmptyDet in H; eauto; subst; auto
      |H:?x++[?a]=nil |- _ => symmetry in H; invertListNeq
      |H:?s1++[?a]=?s2++[?b] |- _ => apply lastElementEq in H; inversion H; subst;
                                     eraseThreadHelper
      |_ => try solve[auto|invertListNeq]
  end. 

Theorem emptyEraseDeterminism : forall t t' t'' T,
                        eraseThread t T t' -> eraseThread t tEmptySet t'' ->
                        t' = t''. 
Proof. 
  intros. inversion H; inversion H0; subst; cleanup; try solve[eraseThreadHelper]. 
  Qed. 


  
Theorem eraseSingleton : forall t t' T,
                           eraseThread t T t' ->
                           erasePoolAux(tSingleton t) = t'. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H5; subst; clear H5. 
   inversion H4; subst; clear H4. apply eraseSameThread in H2.
   eapply emptyEraseDeterminism in H; eauto; subst. assumption. }
  {destruct t. destruct p. destruct p. destruct t0. destruct p. 
   econstructor. econstructor. econstructor. reflexivity. rewrite eraseSameThread. 
   Admitted. 



Theorem errorIffSingleStep : forall H T t PH PT pt,
                               eraseHeap H PH -> erasePool T PT -> erasePool t pt ->
                               (step H T t Error <-> pstep PH PT pt pError). 
Proof.
  intros. split; intros.  
  {inversion H3. subst. eapply eraseFull in H0. inversion H2; subst. 
   apply z in H3. invertExists. 
   
