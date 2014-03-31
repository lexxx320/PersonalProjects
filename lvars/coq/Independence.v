Require Import Spec. 
Require Import Coq.Program.Equality. 
Require Import SfLib. 

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


(*
IHrollback : forall T T', congr (par T1 T2') T -> congr T' (par T1' T2') ->
                          rollback h T h' T'
*)

Theorem RBUntouched : forall tid H H' T1 T2 T1', 
                        rollback tid H (par T1 T2) H' (par T1' T2) ->
                        forall T2',rollback tid H (par T1 T2') H' (par T1' T2').
Proof. intros. dependent induction H0; eauto.  
  {inversion H; subst. 
   {inversion H0; subst. 
    {admit. }
    {admit. }
    {
  }
Qed. 

Theorem Reorder1Step3 : forall H T1 T2 H' T1' T2' sa ca,
                         specActions T2 sa -> 
                         specActions T2' sa -> 
                         commitActions T2 ca ->
                         commitActions T2' ca -> 
                         step H (par T1 T2) H' (par T1' T2) ->
                         step H' (par T2 T1') H' (par T2' T1') -> 
                         step H (par T2 T1) H (par T2' T1) /\ 
                          step H (par T1 T2') H' (par T1' T2'). 
Proof.   
  intros. dependent induction H5.
  {dependent induction H4; try(solve[eauto]). 
   {constructor. constructor. assumption. reflexivity. eapply SpecRB with (E := E0). 
    assumption. reflexivity. 
    apply RBUntouched with (T2' := (thread (bump tid) s1 s2 (E(app t2 t1)))) in H5. 
    apply H5. }
   {inversion H; subst; admit. }
  }
  {dependent induction H4; try(solve[eauto]). 
   {constructor. econstructor. assumption. reflexivity. 
    eapply SpecRB with (E := E0). assumption. reflexivity. 
    apply RBUntouched with (T2' := (thread (bump tid)s1 s2) (E(raise M'))) in H5. 
    eassumption. }
   {admit. }
  }
  {dependent induction H4; try(solve[eauto]). 
   {constructor. econstructor. eassumption. reflexivity. 
    econstructor. assumption. reflexivity. eapply RBUntouched. eassumption. }
   {admit. }
  } 
  {inversion H0. inversion H1. rewrite <- H12 in H5. inversion H5.
   apply listNeq in H20. inversion H20. }
  {inversion H0. inversion H1. subst sa. inversion H12. 
   symmetry in H19. apply listNeq in H19. inversion H19. }
  {inversion H0. inversion H1. inversion H13. inversion H15. 
   subst. inversion H14. }
  {inversion H0. inversion H1. inversion H13. inversion H15. 
   inversion H8. inversion H10. subst. inversion H14. 
   assert(joinAct <> sAct tid'' M). unfold not; intros. 
   inversion H5. apply listNeq2 with (l := s1') in H5. 
   inversion H5. assumption. }
  {inversion H0. inversion H1. inversion H8. inversion H10. 
   subst. inversion H9. }
  {inversion H0. inversion H1. inversion H9. inversion H11. 
   subst. inversion H10. }
  {inversion H0. inversion H1. inversion H8. inversion H10. 
   subst. inversion H9. }
  {inversion H0. inversion H1. subst. inversion H12. 
   symmetry in H10. apply listNeq in H10. inversion H10. }
  {dependent induction H4; try(solve[eauto]). 
   {constructor. eapply Handle. apply H6. reflexivity. 
    econstructor. assumption. reflexivity. eapply RBUntouched. 
    eassumption. }
   {admit. }
  }
  {inversion H0. inversion H1. subst sa. inversion H11. 
   apply listNeq3 in H18. inversion H18. }
  {inversion H0. inversion H1. subst sa. inversion H11. 
   apply listNeq3 in H18. inversion H18. }
  {inversion H0. inversion H1. inversion H7. inversion H9.
   inversion H12. inversion H14. subst. inversion H8. 
   symmetry in H16. apply listNeq3 in H16. inversion H16. }
  {inversion H0. inversion H1. subst sa. inversion H11. }
  {admit. }
Qed. 




Theorem Reorder1Step2 : forall H T1 T2 H' T1' T2' sa ca,
                         specActions T2 sa -> 
                         specActions T2' sa -> 
                         commitActions T2 ca ->
                         commitActions T2' ca -> 
                         step H (par T1 T2) H' (par T1' T2) ->
                         step H' (par T2 T1') H' (par T2' T1') -> 
                         step H (par T2 T1) H (par T2' T1) /\ step H (par T1 T2') H' (par T1' T2'). 
Proof.  
  intros. dependent induction H5. 
  {inversion H4; try(solve[try(repeat constructor; try(assumption; assumption); try subst);
   try (solve[econstructor; try eassumption; try reflexivity])]). 
   {constructor. econstructor. assumption. reflexivity. econstructor. assumption. 
    eassumption. subst. 
    apply RBUntouched with (T2' := (thread (bump tid) s1 s2 (E (app t2 t1)) )) in H14. 
    eapply H14. }
   {constructor. constructor. assumption. reflexivity. eapply SpecRaise. 
    assumption. eassumption. }
   {split. subst. constructor. assumption. reflexivity. apply Handle. 
    assumption. assumption. }
   {split. constructor. assumption. reflexivity. eapply PopNewEmpty. 
    assumption. eassumption. eassumption. } 
   {split. subst. 
    {constructor. assumption. reflexivity. }
    {subst. admit. }
Admitted. 

Theorem Reorder1Step : forall H T1 T2 H' T1' T2' sa ca,
                         specActions T2 sa -> 
                         specActions T2' sa -> 
                         commitActions T2 ca ->
                         commitActions T2' ca -> 
                         step H (par T1 T2) H' (par T1' T2) ->
                         step H' (par T2 T1') H' (par T2' T1') -> 
                         step H (par T2 T1) H (par T2' T1) /\ step H (par T1 T2') H' (par T1' T2'). 
Proof.  
  intros. dependent induction H4. 
  {inversion H5; try(solve[try(repeat constructor; try(assumption; assumption); try subst);
   try (solve[econstructor; try eassumption; try reflexivity])]). 
   {constructor. econstructor. assumption. eassumption. subst. 
    apply RBUntouched with (T2' := (thread tid s1 s2 (E (bind (ret t1) t2)))) in H13. 
    apply H13. constructor. assumption. reflexivity. }
   {constructor. eapply SpecRaise. assumption. eassumption. constructor. eassumption. 
    reflexivity. }
   {split. subst. apply Handle. assumption. reflexivity. subst. apply Bind. 
    assumption. reflexivity. }
   {split. eapply PopNewEmpty. assumption. eassumption. eassumption. 
    constructor. assumption. reflexivity. }
   {split. subst. inversion H4; subst. 
    {inversion H6; subst. 


Theorem Reorder : forall H T1 T2 H' T1' T2' sa ca,
                    specActions T2 sa -> 
                    specActions T2' sa -> 
                    commitActions T2 ca ->
                    commitActions T2' ca -> 
                    step H (par T2 T1) H (par T2' T1) ->
                    multistep H (par T1 T2') H' (par T1' T2') ->
                    multistep H (par T1 T2 ) H' (par T1' T2) /\
                    step H' (par T2 T1') H' (par T2' T1').
Proof.
  intros. dependent destruct H5. 