Require Import erasure. 

Ltac cleanup := unfold tSingleton in *; unfold tCouple in *; unfold tAdd in *;
  repeat(match goal with
           |H : ?x = ?x |- _ => clear H; try subst
           |H : Singleton ?T ?x = Singleton ?T ?y |- _ => apply SingletonEq in H; inversion H; try subst
           |H : Singleton ?T ?x = Couple ?T ?y ?z |- _ => apply SingleEqCouple in H; inversion H; try subst
           |H : Couple ?T ?y ?z = Singleton ?t ?x |- _ => symmetry in H
         end). 

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







