Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 



Theorem eqImpliesSameSet : forall (T:Type) T1 T2, T1 = T2 -> Same_set T T1 T2. 
Proof.
  intros. unfold Same_set. unfold Included. split; intros. 
  {subst. assumption. }
  {subst. assumption. }
Qed. 

Theorem AddEq : forall T t1 t2, (tIn T t1 -> False) -> tAdd T t1 = tAdd T t2 -> t2 = t1. 
Proof.
  intros. apply eqImpliesSameSet in H0. unfold Same_set in H0. 
  unfold Included in H0. inversion H0. assert(tIn (tAdd T t1) t1) by auto. 
  assert(tIn (tAdd T t1) t1). assumption. apply H1 in H3. inversion H3. 
  unfold tIn in *. subst. unfold In in *. unfold tAdd in *. unfold Add in *. 
  inversion H3. 
  {contradiction. }
  {subst. inversion H6. reflexivity. }
  {subst. inversion H5. reflexivity. }
Qed.

Hint Resolve AddEq. 

Theorem heapUpdateNeq : forall (T:Type) h i (v v' : T),
                          heap_lookup i h = Some v ->
                          v <> v' -> h <> replace i v' h. 
Proof.
  intros. unfold not in *. intros. unfold replace in H1. 
  induction h. 
  {inversion H. }
  {destruct a. simpl in *. destruct (beq_nat i i0). 
   {inversion H. subst. inversion H1. contradiction. }
   {inversion H1. apply IHh in H3. assumption. assumption. }
  }
Qed. 

Hint Resolve heapUpdateNeq. 

Theorem listNeq : forall (T : Type) (h:T) t, t = h::t -> False. 
Proof.
  intros. induction t. 
  {inversion H. }
  {inversion H. apply IHt in H2. assumption. }
Qed. 

Ltac neqInContra :=
  match goal with
      | _ : ~(tIn(tAdd ?T ?t) ?t) |- _ => assert(tIn(tAdd T t) t); auto; contradiction
  end.

Theorem Reorder : forall T t1 t2 t1' t2' h h',
                    step h (tAdd T t2) (Some t1) h' (tAdd T t2) (Some t1') ->
                    step h' (tAdd T t1') (Some t2) h' (tAdd T t1') (Some t2') ->
                    step h (tAdd T t1) (Some t2) h (tAdd T t1) (Some t2') /\
                    step h (tAdd T t2') (Some t1) h' (tAdd T t2') (Some t1'). 
Proof.
  intros. 
  inversion H; subst. 
  {inversion H0;try(repeat constructor; apply AddEq in H3; contradiction). }
  {inversion H0; eauto. 
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {neqInContra. }
  }
  {inversion H0; eauto. 
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {neqInContra. }
  }
  {inversion H0; eauto. 
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {neqInContra. }
  }
  {inversion H0; eauto.
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {neqInContra. }
  }
  {neqInContra. }
  {inversion H0; eauto. 
   {subst. apply AddEq in H4. contradiction. intros. contradiction. }
   {neqInContra. }
   {subst. eapply heapUpdateNeq in H8. unfold not in H8. apply H8 in H10. 
    inversion H10. intros contra. inversion contra. apply listNeq in H2. 
    assumption. }
   {eapply heapUpdateNeq in H8. unfold not in H8. apply H8 in H10. 
    inversion H10. intros contra. inversion contra. }
   {subst. unfold extend in *. 
    destruct (replace x (sfull sc (tid :: ds) s writer N) h). 
    {inversion H9. }
    {destruct p. inversion H9. apply listNeq in H8. inversion H8. }
   }
  }
  {inversion H0; eauto. 
   {subst. apply AddEq in H4. contradiction. intros. contradiction. }
   {neqInContra. }
   {eapply heapUpdateNeq in H8. unfold not in H8. apply H8 in H10. 
    inversion H10. intros contra. inversion contra. apply listNeq in H12. 
    assumption. }
   {eapply heapUpdateNeq in H8. unfold not in H8. apply H8 in H10. 
    inversion H10. intros contra. inversion contra. }
   {destruct(replace x (sfull sc [] s1 tid N) h). 
    {inversion H9. }
    {destruct p. inversion H9. apply listNeq in H14. inversion H14. }
   }
  }
  {inversion H0; eauto. 
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {neqInContra. }
   {eapply heapUpdateNeq in H8. unfold not in *. apply H8 in H10. 
    inversion H10. intros contra. inversion contra. apply listNeq in H12. 
    assumption. }
   {eapply heapUpdateNeq in H8. unfold not in H8. apply H8 in H10. 
    inversion H10. intros contra. inversion contra. }
   {destruct h'. 
    {inversion H9. }
    {destruct p. inversion H9. apply listNeq in H14. inversion H14. }
   }
  }
Qed. 
