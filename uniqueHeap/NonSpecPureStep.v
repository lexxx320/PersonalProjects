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

Theorem NonSpecPureStep : forall h sh tid s1 s2 M M' T T',
                            step h T (tSingleton (tid,s1,s2,M)) (OK h T (tSingleton(tid,s1,s2,M'))) ->
                            erasePool T T' -> eraseHeap h = sh ->
                            pstep sh T' (pSingleton (eraseTerm M)) (pOK sh T' (pSingleton (eraseTerm M'))).
Proof.
  intros. inversion H; cleanup. 
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill. 
   rewrite eraseOpenComm. eapply PBetaRed. rewrite decomposeErase; eauto. rewrite eraseFill. 
   auto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill. 
   eapply pProjectL. rewrite decomposeErase; eauto. rewrite eraseFill. auto. simpl. eauto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill. 
   eapply pProjectR. rewrite decomposeErase; eauto. rewrite eraseFill. auto. simpl. eauto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill. 
   eapply PBind. rewrite decomposeErase; eauto. rewrite eraseFill. auto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill. 
   eapply PBindRaise. rewrite decomposeErase; eauto. rewrite eraseFill. auto. simpl. eauto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill. 
   eapply pHandle. rewrite decomposeErase; eauto. rewrite eraseFill. auto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill. 
   eapply pHandleRet. rewrite decomposeErase; eauto. rewrite eraseFill. auto. simpl. eauto. }
  {inversion H1. inversion H2. rewrite H4 in H8. destruct s1; inversion H8. }
  {rewrite H15 in H11. destruct s1. simpl in H11. inversion H11. invertListNeq. 
   simpl in H11. inversion H11. invertListNeq. }
  {rewrite H16 in H12. destruct s1; inversion H12; invertListNeq. } 
  {apply AddEqSingleton in H4. apply AddEqSingleton in H2. inv H2. inv H4. }
  {destruct s0; inversion H3; invertListNeq. }
  {inv H2. inv H1. }
  {inversion H1. inversion H5. }
  {subst. apply AddEqSingleton in H4. inv H4. apply AddEqSingleton in H2. inv H2. 
   rewrite eraseFill. simpl. eapply pSpecRunRaise. eapply decomposeErase in H5; eauto. 
   simpl. eauto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill.  
   eapply pSpecJoinRaise. rewrite decomposeErase; eauto. rewrite eraseFill. auto. simpl. eauto. }
  {rewrite <- H18 in H14. invertListNeq. }
  {invertListNeq. }
  {invertListNeq. }
  {invertListNeq. }
  {inv H3. inv H2. inv H8. }
  {destruct s1'; inversion H3; invertListNeq. }
Qed. 





















