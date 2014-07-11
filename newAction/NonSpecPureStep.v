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

Theorem lastElementEq : forall (T:Type) s1 s2 (e1 e2 : T), s1 ++ [e1] = s2 ++ [e2] -> e1 = e2. 
Proof.
  intros. generalize dependent s2. induction s1; intros. 
  {destruct s2. inversion H. reflexivity. inversion H. destruct s2; inversion H2. }
  {destruct s2. inversion H. destruct s1; inversion H2. inversion H. apply IHs1 in H2.
   assumption. } Qed.  

Ltac cleanup := unfold tSingleton in *; unfold tCouple in *; unfold tAdd in *;
  repeat(match goal with
           |H : ?x = ?x |- _ => clear H; try subst
           |H : Singleton ?T ?x = Singleton ?T ?y |- _ => apply SingletonEq in H; inversion H; try subst
           |H : Singleton ?T ?x = Couple ?T ?y ?z |- _ => apply SingleEqCouple in H; inversion H; try subst
           |H : Couple ?T ?y ?z = Singleton ?t ?x |- _ => symmetry in H
         end). 

Theorem listNeq : forall (T:Type) l (e:T), l = e::l -> False. 
Proof.
  intros. induction l. 
  {inversion H. }{inversion H. apply IHl in H2. assumption. }Qed. 

Theorem heapLookupSomeReplace : forall T x H (v v' : T),
                                  heap_lookup x (replace x v H) = Some v' -> v = v'.
Proof.
  induction H; intros. 
  {inversion H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl in *. rewrite <- beq_nat_refl in H0. inv H0; auto. }
   {simpl in *. rewrite eq in H0. apply IHlist in H0; auto. }
  }
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
  {symmetry in H6. apply SingletonNeqEmpty in H6. inversion H6. }
  {inversion H1. inversion H2. rewrite H4 in H8. destruct s1; inversion H8. }
  {rewrite H15 in H11. symmetry in H11. invertListNeq. }
  {rewrite H16 in H12. symmetry in H12. invertListNeq. } 
  {subst. apply heapLookupSomeReplace in H7. inv H7. }
  {invertListNeq. }
  {inv H2. inv H1. }
  {inversion H1. inversion H5. rewrite H7 in H10. invertListNeq. }
  {subst. apply AddEqSingleton in H4. inv H4. apply AddEqSingleton in H2. inv H2. 
   rewrite eraseFill. simpl. eapply pSpecRunRaise. eapply decomposeErase in H5; eauto. 
   simpl. eauto. }
  {copy H6. apply decomposeEq in H6. subst. rewrite eraseFill. simpl. rewrite eraseFill.  
   eapply pSpecJoinRaise. rewrite decomposeErase; eauto. rewrite eraseFill. auto. simpl. eauto. }
  {invertListNeq. }
  {invertListNeq. }
  {invertListNeq. }
  {invertListNeq. }
  {inv H3. inv H2. inv H8. inv H9. }
Qed. 





















