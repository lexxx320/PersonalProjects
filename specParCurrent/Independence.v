Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 



Theorem eqImpliesSameSet : forall (T:Type) T1 T2, T1 = T2 -> Same_set T T1 T2. 
Proof.
  intros. unfold Same_set. unfold Included. split; intros. 
  {subst. assumption. }
  {subst. assumption. }
Qed. 

Theorem UnionEq : forall T t1 t2, tIntersection T t1 = tEmptySet -> tIntersection T t2 = tEmptySet -> 
                                  tUnion T t1 = tUnion T t2 -> t1 = t2.
Proof.
  intros. apply eqImpliesSameSet in H1. unfold Same_set in H1. inversion H1. 
  unfold Included in *. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
  {intros. assert(tIn (tUnion T t1) x). apply Union_intror. assumption. 
   apply H2 in H5. inversion H5. 
   {subst. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. 
    inversion H. assert(tIn (tIntersection T t1) x). constructor; assumption. 
    apply H7 in H9. inversion H9. }
   {assumption. }
  }
  {intros. assert(tIn (tUnion T t2) x). apply Union_intror. assumption. 
   apply H3 in H5. inversion H5. 
   {subst. apply eqImpliesSameSet in H0. unfold Same_set in H0. unfold Included in H0. 
    inversion H0. assert(tIn (tIntersection T t2) x). constructor; assumption. 
    apply H7 in H9. inversion H9. }
   {assumption. }
  }
Qed. 

Hint Resolve UnionEq. 

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

Theorem listNeq : forall (T:Type) (h:T) l, l = h::l -> False. 
Proof.
  intros. induction l. 
  {inversion H. }{inversion H. apply IHl in H2. assumption. } Qed. 

Ltac handleReadWrite :=
  match goal with
      |H1 : heap_lookup ?x ?h = Some ?v, H2 : ?h = replace ?x ?v2 ?h |- _ =>
       eapply heapUpdateNeq with (v' := v2) in H1
  end. 

Theorem emptyNeqSingle : forall e, Empty_set thread = tSingleton e -> False. 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in *. 
  inversion H. assert(tIn (tSingleton e) e). constructor. apply H1 in H2. inversion H2. 
  Qed. 

Theorem emptyNeqAdd : forall (T:Type) S e, Add T S e = Empty_set T -> False. 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. 
  unfold Included in *. inversion H. assert(Ensembles.In T (Add T S e) e). 
  apply Union_intror. constructor. apply H0 in H2. inversion H2. Qed. 

Theorem AddIn : forall T T' t, tAdd T t = T' -> tIn T' t. 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. 
  unfold Included in *. inversion H. assert(tIn (tAdd T t) t). 
  apply Union_intror. constructor. apply H0 in H2. assumption. Qed. 

Axiom specActionsCardinalityNeq : forall t1 t2 t3 sa sa',
                                    specActions (tCouple t1 t2) sa ->
                                    specActions (tSingleton t3) sa' ->
                                    sa <> sa'.

Ltac unfoldSetEq :=
  match goal with
      |H : ?S1 = ?S2 |- _ => try apply eqImpliesSameSet in H; unfold Same_set in H;
                             unfold Included in *; inversion H
  end.

Theorem addSpecAction : forall tid a s1 s2 M M' sa,
                          specActions (tSingleton (tid, s1, s2, M)) sa ->
                          specActions (tSingleton (bump tid, a::s1, s2, M')) sa -> False.
Proof.
  intros. inversion H; inversion H0. subst. 
  {repeat unfoldSetEq. assert(tIn (tSingleton (tid, s1, s2, M)) (tid, s1, s2, M)). 
   constructor. apply H9 in H10. inversion H10. }
  {repeat unfoldSetEq. assert(tIn (tSingleton (tid, s1, s2, M)) (tid, s1, s2, M)). 
   constructor. apply H14 in H15. inversion H15. }
  {repeat unfoldSetEq. assert(tIn (tSingleton (bump tid, a::s1, s2, M')) (bump tid, a::s1, s2, M')). 
   constructor. apply H10 in H15. inversion H15. }
  {admit. }
Qed. 

Theorem addCommitAction : forall tid a s1 s1' s2 M M' sa,
                          commitActions (tSingleton (tid, s1, s2, M)) sa ->
                          commitActions (tSingleton (tid, s1', a::s2, M')) sa -> False.
Proof.
  intros. inversion H; inversion H0. subst. 
  {repeat unfoldSetEq. assert(tIn (tSingleton (tid, s1, s2, M)) (tid, s1, s2, M)). 
   constructor. apply H9 in H10. inversion H10. }
  {repeat unfoldSetEq. assert(tIn (tSingleton (tid, s1, s2, M)) (tid, s1, s2, M)). 
   constructor. apply H14 in H15. inversion H15. }
  {repeat unfoldSetEq. assert(tIn (tSingleton (tid, s1', a::s2, M')) (tid, s1', a::s2, M')). 
   constructor. apply H10 in H15. inversion H15. }
  {admit. }
Qed. 

Hint Resolve addSpecAction.

Theorem Reorder : forall T t1 t2 t1' t2' h h' sa ca,
                    specActions t2 sa -> specActions t2' sa ->
                    commitActions t2 ca -> commitActions t2' ca ->
                    step h (tUnion T t2) t1 h' (tUnion T t2) t1' ->
                    step h' (tUnion T t1') t2 h' (tUnion T t1') t2' ->
                    step h (tUnion T t1) t2 h (tUnion T t1) t2' /\
                    step h (tUnion T t2') t1 h' (tUnion T t2') t1'.
Proof.
  intros. inversion H3. 
  {inversion H4; try(subst; assert(t1 = t1'); eauto;contradiction; subst; 
                     assert(t1 = t1'); eauto;contradiction). 
   {handleReadWrite. contradiction. intros c. inversion c. apply listNeq in H23. assumption. }
   {handleReadWrite. contradiction. intros c. inversion c. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'); eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'); eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'); eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'); eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'); eauto. contradiction. }
  }
  {inversion H4; eauto; try(subst; eapply AddSpecAction in H; inversion H; eassumption).
   {subst. assert(t2 = t2'); eauto. contradiction. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. admit.  }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
  }
  {inversion H4; eauto; try(subst; eapply AddSpecAction in H; inversion H; eassumption).
   {subst. assert(t2 = t2'); eauto. contradiction. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. admit. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
  }
  {inversion H4; eauto; try(subst; eapply AddSpecAction in H; inversion H; eassumption).
   {subst. assert(t2 = t2'); eauto. contradiction. }
   {handleReadWrite. contradiction. intros contra. inversion contra. apply listNeq in H21. assumption. }
   {handleReadWrite. contradiction. intros contra. inversion contra. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. admit. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'); eauto. contradiction. }
   {handleReadWrite. contradiction. intros contra. inversion contra. apply listNeq in H23. assumption. }
   {handleReadWrite. contradiction. intros contra. inversion contra. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. admit. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
   {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  }
  {inversion H4; eauto. 
   {subst. assert(t2 = t2'). eauto. contradiction. }
  } 
Qed. 

