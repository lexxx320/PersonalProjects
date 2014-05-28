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

Theorem errorIffSingleStep : forall H T t PH PT pt,
                               eraseHeap H PH -> erasePool T PT -> erasePool t pt ->
                               (step H T t Error <-> pstep PH PT pt pError). 
Proof.
  intros. split; intros.  
  {inversion H3. subst. eapply eraseFull in H0. 


 admit. 
  }
  {inversion H3; subst. inversion H2; subst. apply eqImpliesSameSet in H8. unfold Same_set in H8. 
   unfold Included in H8. inversion H8; clear H8. assert(Ensembles.In AST.ptrm (pSingleton t0) t0). 
   constructor. apply H7 in H8. inversion H8.  inversion H8; subst. inversion H10; subst. 
   {