Require Import Spec. 
Require Import Coq.Program.Equality. 
Require Import SfLib. 
 
(*These are used in the reorder lemma (after we switch from using lists to MSets for 
 * the speculative and commit actions, they shouldn't be needed)*)
Theorem listNeq : forall (T:Type) (h:T) l, l = h::l -> False. 
Proof.
  intros. induction l. 
  {inversion H. }
  {inversion H. apply IHl in H2. assumption. }
Qed. 
  
Theorem listNeq2 : forall (T:Type) (h:T) t l, 
                        h <> t -> h::l = l++[t] -> False. 
Proof.
  intros. induction l. 
  {inversion H0. contradiction. }
  {inversion H0. subst. apply IHl in H3. assumption. }
Qed. 

Theorem listNeq3 : forall (T:Type) (h:T) l, 
                     l = l ++ [h] -> False. 
Proof.
  intros. induction l. 
  {inversion H. }
  {inversion H. apply IHl in H1. assumption. }
Qed. 
 
Theorem NEQRecPar : forall T1 T2, par T1 T2 <> T2. 
Proof.
  intros. unfold not. intros. induction T2. 
  {inversion H. }
  {inversion H. }
  {inversion H. subst T1. apply IHT2_2 in H2.  assumption. }
Qed. 

Theorem RBUntouched : forall tid H H' T1 T2 T1', 
                        rollback tid H (par T1 T2) H' (par T1' T2) -> 
                        forall T2', rollback tid H (par T1 T2') H' (par T1' T2').
Proof.
  intros. remember (par T1 T2). remember (par T1' T2). 
  generalize dependent T1'. induction H0. 
  {intros. inversion Heqp; inversion Heqp0; subst. constructor. }
  {intros. inversion Heqp; inversion Heqp0; subst. 



  remember (par T1 T2). 
  



remember (par T1 T2). remember (par T1' T2). generalize dependent T1.
  generalize dependent T2. generalize dependent T1'. induction H0. 
  {intros. inversion Heqp0. inversion Heqp; subst. constructor. }
  {intros. inversion Heqp0; inversion Heqp; subst. eauto. }
  {intros. inversion Heqp0; inversion Heqp; subst. eauto. }
  {intros. inversion Heqp0; inversion Heqp; subst. eauto. }
  {intros. inversion Heqp0; inversion Heqp; subst. eauto. }
  {intros. inversion Heqp0; inversion Heqp; subst. eauto. }
  {simplify_dep_elim. inversion H; inversion H0; subst. 



 admit. }
Qed. 



Theorem RBUntouched2 : forall tid H H' T1 T2 T1', 
                        rollback tid H (par T1 T2) H' (par T1' T2) -> 
                        forall T2',rollback tid H (par T1 T2') H' (par T1' T2').
Proof.
  intros. generalize_eqs_vars H0. induction H0. simplify_dep_elim. 
  {constructor. }
  {simplify_dep_elim; eauto. }
  {simplify_dep_elim; eauto. }
  {simplify_dep_elim; eauto. }
  {simplify_dep_elim; eauto. }
  {simplify_dep_elim; eauto. }
  {simplify_dep_elim. 


inversion H; subst. inversion H0; subst. 



Theorem NeqRecPar : forall T1 T2, par T1 T2 = T2-> False.
Proof.
  intros. induction T2. 
  {inversion H. }
  {inversion H. }
  {inversion H. subst T1. apply IHT2_2 in H2. assumption. }
Qed. 

Theorem Reorder1Step' : forall H T1 T2 H' T1' T2' T sa ca,
                         specActions T2 sa -> 
                         specActions T2' sa -> 
                         commitActions T2 ca ->
                         commitActions T2' ca -> 
                         step H (par T1 (par T2 T)) H' (par T1' (par T2 T)) ->
                         step H' (par T2 (par T1' T)) H' (par T2' (par T1' T)) -> 
                         step H (par T2 (par T1 T)) H (par T2' (par T1 T)) /\ 
                         step H (par T1 (par T2' T)) H' (par T1' (par T2' T)). 
Proof.  
  intros. inversion H5. 
  {inversion H4; eauto. subst. 
   {constructor. constructor. assumption. reflexivity. econstructor. 
    assumption. reflexivity. eapply RBUntouched in H21. eassumption. }
   {split. constructor. assumption. assumption. subst. inversion H13. subst. 
    constructor. constructor. apply NeqRecPar in H12. inversion H12. 
    symmetry in H12. apply NeqRecPar in H12. inversion H12. subst. econstructor. 
    constructor. }
  }
  {inversion H4; eauto. subst. 
   {constructor. eapply Eval.  assumption. reflexivity. reflexivity. assumption. 
    econstructor. assumption. reflexivity. eapply RBUntouched in H23. eassumption. }
   {split. subst. eapply Eval. assumption. reflexivity. reflexivity. assumption. 
    subst. inversion H15. subst. constructor. constructor. apply NeqRecPar in H11. 
    inversion H11. symmetry in H11. apply NeqRecPar in H11. inversion H11. subst.
    econstructor. constructor. }
  }
  {inversion H4; eauto. subst. 
   {constructor. eapply BindRaise. constructor. assumption. reflexivity. econstructor. 
    assumption. reflexivity. eapply RBUntouched in H21. eassumption. }
   {split. subst. eapply BindRaise. assumption. reflexivity. subst. inversion H13. 
     subst. constructor. constructor. apply NeqRecPar in H12. inversion H12. 
    symmetry in H12. apply NeqRecPar in H12. inversion H12. subst. econstructor. 
    constructor. }
  }
   {subst. inversion H0. inversion H1. inversion H15. inversion H17. subst. 
   inversion H16. }
  {clear H14. subst. inversion H0. inversion H1. subst. inversion H12. 
   symmetry in H10. apply listNeq in H10. inversion H10. }
  {clear H14. subst. inversion H0. inversion H1. subst. inversion H12. 
   symmetry in H10. apply listNeq in H10. inversion H10. }
  {subst. inversion H0. inversion H1. inversion H15. inversion H17. subst. 
   inversion H16. }
  {subst. inversion H0. inversion H1. subst. inversion H8. inversion H12. 
   inversion H15. inversion H17. subst. inversion H16. 
   assert(AST.joinAct <> AST.sAct tid'' M). unfold not. intros. inversion H6. 
   eapply listNeq2 in H6. inversion H6. eassumption. }
  {subst. inversion H0. inversion H1. subst. inversion H8. inversion H12. 
   subst. inversion H13. }
  {subst. inversion H0. inversion H1. subst. inversion H8. inversion H10. 
   subst. inversion H11. }
  {subst. inversion H0. inversion H1. subst. inversion H8. inversion H12. 
   subst. inversion H13. }
  {subst. inversion H0. inversion H1. subst. inversion H12. symmetry in H9. 
   apply listNeq in H9. inversion H9. }
  {inversion H4; eauto; subst. 
   {split. eapply Handle. assumption. reflexivity. econstructor. assumption. 
    reflexivity. eapply RBUntouched in H21. eassumption. }
   {split. eapply Handle. assumption. reflexivity. inversion H13. subst. 
    constructor. constructor. apply NeqRecPar in H12. inversion H12. 
    symmetry in H12. apply NeqRecPar in H12. inversion H12. subst. econstructor. 
    constructor. }
  }
  {inversion H4; eauto; subst. 
   {split. eapply HandleRet; auto. econstructor. assumption. 
    reflexivity. eapply RBUntouched in H21. eassumption. }
   {split. eapply HandleRet. assumption. reflexivity. inversion H13. 
    subst. constructor. constructor.  apply NeqRecPar in H12. inversion H12. 
    symmetry in H12. apply NeqRecPar in H12. inversion H12. subst. econstructor. 
    constructor. }
  }
  {clear H13. subst. inversion H0. inversion H1. subst. inversion H11. 
   apply listNeq3 in H9. inversion H9. }
  {clear H13. subst. inversion H0. inversion H1. subst. inversion H11. 
   apply listNeq3 in H9. inversion H9. }
  {subst. inversion H0. inversion H1. subst. inversion H8. inversion H11. 
   inversion H14. inversion H16. subst. inversion H15. apply listNeq3 in H18. 
   inversion H18. }
  {subst. inversion H0. inversion H1. subst. inversion H13. }
  {subst. inversion H6.
   {subst. split. constructor. constructor. assumption. }
   {eapply NeqRecPar in H13. inversion H13. }
   {symmetry in H13. eapply NeqRecPar in H13. inversion H13. }
   {subst. split; repeat constructor. assumption. }
  }

Qed. 




Theorem Reorder : forall H T1 T2 H' T1' T2' T sa ca,
                    specActions T2 sa -> 
                    specActions T2' sa -> 
                    commitActions T2 ca ->
                    commitActions T2' ca -> 
                    step H (par T2 (par T1 T)) H (par T2' (par T1 T)) ->
                    multistep H (par T1 (par T2' T)) H' (par T1' (par T2' T)) ->
                    multistep H (par T1 (par T2 T)) H' (par T1' (par T2 T)) /\
                    step H' (par T2 (par T1' T)) H' (par T2' (par T1' T)).
Proof.
  intros. generalize_eqs_vars H5.  induction H5. 
  {simplify_dep_elim. split. constructor. assumption. }
  {simplify_dep_elim. split. 