Require Import Spec. 
Require Import Coq.Program.Equality. 

(*
Theorem RBUntouched : 
  forall tid H H' T1 T2 T2' T1', rollback tid H (par T1 T2) H' (par T1' T2) ->
                                 rollback tid H (par T1 T2') H' (par T1' T2').
Proof.
  intros. apply rollback_ind. 
  {intros. constructor. }
  {intros. subst. eapply RBRead. reflexivity. eassumption. 
   reflexivity. eassumption. }
  {intros. subst. eapply RBFork. reflexivity. eassumption. }
  {intros. subst. eapply RBWrite. reflexivity. eassumption. 
   reflexivity. eassumption. }
  {intros. subst. eapply RBNew. reflexivity. eassumption. 
   reflexivity. eassumption. }
  {intros. subst. eapply RBSpec. reflexivity. eassumption. }
  {intros. apply RBCongr with (T' := T') (T'' := T''). 
   assumption. assumption. assumption. }
  *)


Theorem RBUntouched : 
  forall tid H H' T1 T2 T2' T1', rollback tid H (par T1 T2) H' (par T1' T2) ->
                                 rollback tid H (par T1 T2') H' (par T1' T2').
Proof. intros. dependent induction H0; intros.  
  {constructor. }
  {eapply RBRead. reflexivity. eassumption. symmetry. reflexivity.  
   assert((par (thread tid'' s1' s2 M') T2) = (par (thread tid'' s1' s2 M') T2)). 
   reflexivity.  eapply IHrollback with (T1'0 := T1') in H. 
   eassumption. reflexivity. }
  {assert(par(thread tid'' s1' s2 M') T2 = par(thread tid'' s1' s2 M') T2). reflexivity. 
   eapply IHrollback with (T1'0 := T1') in H. econstructor. reflexivity. 
   eassumption. reflexivity. }
  {assert(par (thread tid'' s1' s2 M') T2 = par (thread tid'' s1' s2 M') T2). 
   reflexivity. eapply RBWrite. reflexivity. eassumption. 
   reflexivity. eapply IHrollback with (T1'0 := T1') in H. 
   eassumption. reflexivity. }
  {eapply RBNew. reflexivity. eassumption. reflexivity. 
   assert(par (thread tid'' s1' s2 M') T2 = par (thread tid'' s1' s2 M') T2 ). 
   reflexivity. eapply IHrollback in H. eassumption. reflexivity. }
  {eapply RBSpec. reflexivity. 
   assert(par (thread tid'' s1' s2 M') T2 = par (thread tid'' s1' s2 M') T2). 
   reflexivity. eapply IHrollback in H. eassumption. reflexivity. }
  {admit. }
Qed. 

Theorem Reorder1Step3 : forall H T1 T2 H' T1' T2' sa ca,
                         specActions T2 sa -> 
                         specActions T2' sa -> 
                         commitActions T2 ca ->
                         commitActions T2' ca -> 
                         step H (par T1 T2) H' (par T1' T2) ->
                         step H' (par T2 T1') H' (par T2' T1') -> 
                         step H (par T2 T1) H (par T2' T1) /\ step H (par T1 T2') H' (par T1' T2'). 
Proof.  
  intros. dependent induction H5. 
  {dependent induction H4; try(solve[try(repeat constructor; try(assumption; assumption); try subst);
   try (solve[econstructor; try eassumption; try reflexivity])]). 
   {constructor. constructor. assumption. reflexivity. 
    apply Fork with (E := E0). assumption. reflexivity. }
   {constructor. constructor. assumption. reflexivity. eapply PopSpec with (E := E0). 
    assumption. reflexivity. reflexivity. }
   {constructor. constructor. assumption. reflexivity. eapply SpecJoin with (E := E0).
    assumption. reflexivity. }
   {constructor. constructor. assumption. reflexivity. eapply SpecRB with (E := E0). 
    assumption. reflexivity. apply RBUntouched with (T2' := (thread (bump tid) s1 s2 (E(app t2 t1)))) in H5. 
    apply H5. }
   {constructor. constructor. assumption. reflexivity. eapply SpecRaise with (E := E0). 
    assumption. reflexivity. }
   {constructor. constructor. assumption. reflexivity. eapply Handle with (E := E0). 
    assumption. reflexivity. }
   {constructor. constructor. assumption. reflexivity. eapply PopNewEmpty. 
    reflexivity. eassumption. reflexivity. }
   {constructor. constructor. assumption. reflexivity. eapply IHstep in H6. 
    

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