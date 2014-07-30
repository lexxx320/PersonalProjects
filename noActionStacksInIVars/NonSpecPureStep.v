Require Import Spec.     
Require Import NonSpec.  
Require Import AST.
Require Import Coq.Sets.Ensembles.   
Require Import sets. 
Require Import SfLib. 
Require Import Coq.Program.Equality. 
Require Import erasure. 
Require Import hetList. 
Require Import SpecLib. 
Require Import Heap. 
Require Import unspec. 
Require Import classifiedStep. 

Axiom uniqueThreadPool : forall T tid t t', 
                           thread_lookup T tid t -> thread_lookup T tid t' -> t = t'. 

Ltac cleanup := unfold tSingleton in *; unfold tCouple in *; unfold tAdd in *;
  repeat(match goal with
           |H : ?x = ?x |- _ => clear H; try subst
           |H : Singleton ?T ?x = Singleton ?T ?y |- _ => apply SingletonEq in H; inversion H; try subst
           |H : Singleton ?T ?x = Couple ?T ?y ?z |- _ => apply SingleEqCouple in H; inversion H; try subst
           |H : Couple ?T ?y ?z = Singleton ?t ?x |- _ => symmetry in H
         end). 

Theorem raw_heapLookupSomeReplace : forall T x H (v v' : T),
                                  raw_heap_lookup x (raw_replace x v H) = Some v' -> v = v'.
Proof.
  induction H; intros. 
  {inversion H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl in *. rewrite <- beq_nat_refl in H0. inv H0; auto. }
   {simpl in *. rewrite eq in H0. apply IHlist in H0; auto. }
  }
Qed. 

Theorem heapLookupSomeReplace : forall T x H (v v' : T),
                                  heap_lookup x (replace x v H) = Some v' -> v = v'.
Proof.
  intros. destruct H; simpl in *. eapply raw_heapLookupSomeReplace; eauto. 
Qed. 

Hint Constructors pbasic_step. 

Theorem simBasicStep : forall t t',
                         basic_step t t' -> pbasic_step (eraseTerm t) (eraseTerm t'). 
Proof.
  intros. inv H; try solve[
    match goal with
       |H:decompose ?t ?E ?e |- _ => rewrite <- decomposeErase in H; eauto; 
                                     rewrite eraseFill; simpl; eauto
    end].      
  {rewrite <- decomposeErase in H0; eauto. rewrite eraseFill; simpl. rewrite eraseOpenComm. eauto. }
  {rewrite <- decomposeErase in H0; eauto. rewrite eraseFill; simpl.
   econstructor. simpl in *. eauto. }
  {rewrite <- decomposeErase in H0; eauto. rewrite eraseFill; simpl.
   eapply pbasicProjR. simpl in *. eauto. }
Qed. 

(*
Theorem NonSpecPureStep : forall h sh tid s1 s2 M M' T T',
                            step h T (tSingleton (tid,s1,s2,M)) 
                                 (OK h T (tSingleton(tid,s1,s2,M'))) ->
                            erasePool T T' -> eraseHeap h = sh ->
                            pstep sh T' (pSingleton (eraseTerm M)) (pOK sh T' (pSingleton (eraseTerm M'))).
Proof.
  intros. inversion H; cleanup.
  {apply simBasicStep in H6. eapply PBasicStep. auto. }
  {inversion H1. inversion H2. rewrite H4 in H8. destruct s1; inversion H8. }
  {rewrite H15 in H11. destruct s1. simpl in H11. inversion H11. invertListNeq. 
   simpl in H11. inversion H11. invertListNeq. simpl in *. inversion H11. invertListNeq. }
  {rewrite H16 in H12. destruct s1; inversion H12; invertListNeq. } 
  {apply AddEqSingleton in H4. apply AddEqSingleton in H2. inv H2. inv H4. }
  {rewrite H14 in H10. destruct s1; inversion H10. invertListNeq. invertListNeq. 
   invertListNeq. }
  {inversion H2. invertListNeq. }
  {inv H1. inv H6. inversion H1. inv H6. inversion H5. }
  {subst. apply AddEqSingleton in H4. inv H4. apply AddEqSingleton in H2. inv H2. 
   rewrite eraseFill. simpl. eapply pSpecRunRaise. eapply decomposeErase in H5; eauto. 
   simpl. eauto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill.  
   eapply pSpecJoinRaise. rewrite decomposeErase; eauto. rewrite eraseFill. auto. simpl. eauto. }
  {rewrite <- H18 in H14. invertListNeq. }
  {rewrite H17 in H13. invertListNeq. }
  {rewrite H17 in H13. invertListNeq. }
  {rewrite H17 in H13. invertListNeq. }
  {inv H3. inv H2. inv H8. }
  {inv H3. inv H1. }
Qed. *)


Theorem NonSpecPureStep' : forall h sh tid s1 s2 M M' T T',
     spec_step h T (tSingleton (tid,s1,s2,M)) 
               h T (tSingleton(tid,s1,s2,M')) ->
     erasePool T T' -> eraseHeap h = sh ->
     pstep sh T' (pSingleton (eraseTerm M)) (pOK sh T' (pSingleton (eraseTerm M'))).
Proof.
  intros. inversion H; try subst. 
  {unfoldTac; repeat invertHyp. inv H2. inv H3. apply simBasicStep in H6. 
   eapply PBasicStep. auto. }
  {symmetry in H5. apply SingleEqCouple in H5. invertHyp. invThreadEq. 
   inversion H1. destruct b; inv H5. }
  {clear H9. unfoldTac; repeat invertHyp. inv H2. inversion H3. destruct s1. 
   simpl in *. inversion H2. invertListNeq. simpl in *. inversion H2. 
   invertListNeq. simpl in *. inversion H2. invertListNeq. }
  {eapply heapUpdateNeq in H9; eauto. inv H9. introsInv. }
  {destruct h. simpl in *. inversion H8. destruct h. inv H10. 
   unfold raw_extend in H10. simpl in *. invertListNeq. }
  {symmetry in H8. apply SingleEqCouple in H8. invertHyp. inv H2. inversion H1. 
   destruct b; inv H7. }
Qed. 







