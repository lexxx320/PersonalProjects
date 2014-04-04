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
   {assert(tIn (tAdd (tAdd T (bump tid, s1, s2, E (app N M))) (tid', [], [], M0)) (tid', [], [], M0)). 
    auto. contradiction. }
  }
  {inversion H0; eauto. 
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {assert(tIn (tAdd (tAdd T (bump tid, s1, s2, E (raise M))) (tid', [], [], M0)) (tid', [], [], M0)).
    auto. contradiction. }
  }
  {inversion H0; eauto. 
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {assert(tIn(tAdd (tAdd T (bump tid, s1, s2, E (app N M))) (tid', [], [], M0)) (tid', [], [], M0)).
    auto. contradiction. }
  }
  {inversion H0; eauto.
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {assert(tIn (tAdd (tAdd T (bump tid, s1, s2, E (ret M))) (tid', [], [], M0)) (tid', [], [], M0)). 
    auto. contradiction. }
  }
  {assert(tIn (tAdd (tAdd T t2) ((1, 1) :: tid, [], [], M)) ((1, 1) :: tid, [], [], M)).
   auto. contradiction. }
  {inversion H0; eauto. 
   {subst. apply AddEq in H4. contradiction. intros. contradiction. }
   {assert(tIn
          (tAdd
             (tAdd T (bump tid, rAct x tid (E (get x)) :: s1, s2, E (ret N)))
             (tid', [], [], M)) (tid', [], [], M)). auto. contradiction. }
   {subst. 
                                                                                      
Qed. 

Theorem Reorder : forall T t1 t2 t1' t2' h h' sa ca,
                    specActions t2 sa -> specActions t2' sa ->
                    commitActions t2 ca -> commitActions t2' ca ->
                    step h (tAdd T t2) (Some t1) h' (tAdd T t2) (Some t1') ->
                    step h' (tAdd T t1') (Some t2) h' (tAdd T t1') (Some t2') ->
                    step h (tAdd T t1) (Some t2) h (tAdd T t1) (Some t2') /\
                    step h (tAdd T t2') (Some t1) h' (tAdd T t2') (Some t1'). 
Proof.
  intros. 
  inversion H; subst. 
  {inversion H0;try(repeat constructor; apply AddEq in H3; contradiction). }
  {inversion H0; auto. 
   {subst. apply AddEq in H3. contradiction. intros. contradiction. }
   {subst. 
   }
  {inversion H0; subst; auto. 
   {apply AddEq in H3. contradiction. intros. contradiction. }
  }
  {inversion H0; subst; auto. 
   {apply AddEq in H3. contradiction. intros. contradiction. }
  }
  {inversion H0; subst; auto.
   {apply AddEq in H3. contradiction. intros. contradiction. }
  }
Qed. 
