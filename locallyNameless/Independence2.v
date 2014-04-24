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
  Admitted.

Theorem addCommitAction : forall tid a s1 s1' s2 M M' sa,
                          commitActions (tSingleton (tid, s1, s2, M)) sa ->
                          commitActions (tSingleton (tid, s1', a::s2, M')) sa -> False.
Proof.
  Admitted. 

Hint Resolve addSpecAction.

Hint Constructors Couple. 
Hint Constructors Union. 
Hint Constructors Singleton. 

 Ltac invertSetNeq :=
       match goal with
           |H : Empty_set thread = tAdd ?T ?t |- _ =>
            apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H;
            inversion H as [sameSet1 sameSet2]; assert(Assump:tIn (tAdd T t) t);
            auto; apply sameSet2 in Assump; inversion Assump
           |H : Empty_set thread = tCouple ?t1 ?t2 |- _ =>
            apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H;
            inversion H as [sameSet1 sameSet2]; assert(Assump:tIn (tCouple t1 t2) t1) by apply Couple_l;
            apply sameSet2 in Assump; inversion Assump
       end.
Unset Ltac Debug. 

Theorem AddEqIn : forall T t T', tAdd T t = T' -> tIn T' t. 
Proof.
  intros. unfoldSetEq. assert(tIn (tAdd T t) t). auto. apply H0 in H2. assumption. 
  Qed. 

Theorem SingletonAddEq : forall e1 e2 T, tSingleton e1 = tAdd T e2 -> e1 = e2.
Proof.
  intros. unfoldSetEq. assert(tIn (tAdd T e2) e2) by auto. apply H1 in H2. 
  inversion H2. reflexivity. Qed. 


Ltac evalSpecActions :=
  match goal with
      |H:specActions (tCouple (Tid(?maj,?min) ?t, ?s1, ?s2, ?M)
                              (Tid(?maj',?min') ?t', ?s1', ?s2', ?M')) ?a |- _ =>
       assert(a = Couple (tid*specStack) (Tid(maj,0)t, s1) (Tid (maj',0)t', s1'))by admit
  end.       

Theorem Reorder : forall  t1 t2 t1' t2' h h' sa ca,
                    specActions t2 sa -> specActions t2' sa ->
                    commitActions t2 ca -> commitActions t2' ca ->
                    step h t2 t1 h' t2 t1' ->
                    step h' t1' t2 h' t1' t2' ->
                    step h t1 t2 h t1 t2' /\
                    step h t2' t1 h' t2' t1'.
Proof.
  intros. inversion H3.
  {inversion H4; try(subst; assert(t1 = t1'); eauto;contradiction; subst; 
                     assert(t1 = t1'); eauto;contradiction). 
   {subst. apply UnionEq in H5. contradiction. assumption. assumption. }
   {handleReadWrite. contradiction. intros c. inversion c. apply listNeq in H24. assumption. }
   {handleReadWrite. contradiction. intros c. inversion c. }
  }
  {inversion H4; eauto; try(subst; assert(t2 = t2') by eauto; contradiction). }
  {inversion H4; eauto; try(subst; assert(t2 = t2') by eauto; contradiction). }
  {inversion H4; eauto; try(subst; assert(t2 = t2') by eauto; contradiction). }
  {inversion H4; eauto; try(subst; assert(t2 = t2') by eauto; contradiction). }
  {inversion H4; eauto; try(subst; assert(t2 = t2') by eauto; contradiction). }
  {inversion H4; eauto; try(subst; assert(t2 = t2') by eauto; contradiction). }
  {inversion H4; eauto; try(subst; eapply AddSpecAction in H; inversion H; eassumption).
   {subst. assert(t2 = t2'); eauto. contradiction. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {subst. eapply addSpecAction in H. inversion H. eassumption. }
   {admit. }
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
   {subst. assert(t2 = t2'); eauto. contradiction. }
   {handleReadWrite. contradiction. intros contra. inversion contra. apply listNeq in H28. assumption. }
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


Inductive multistep : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|multi_refl : forall h p1 p2, multistep h p1 p2 h p1 p2
|multi_step : forall h h' h'' p1 p1' p1'' p2 p2' p2'',
                step h p1 p2 h' p1' p2' -> multistep h' p1' p2' h'' p1'' p2'' ->
                multistep h p1 p2 h'' p1'' p2''.

Inductive multistep : 


Require Import Coq.Program.Equality. 

Theorem stepNoProgress : forall h T t,
                           step h T t h T t -> False. 
Proof.
  Admitted. 

Theorem ReorderStepStar : forall t1 t2 t1' t2' h T h' sa ca,
                            specActions t2 sa -> specActions t2' sa ->
                            commitActions t2 ca -> commitActions t2' ca ->
                            step h T t2 h T t2' ->
                            multistep h T t1 h' T t1' ->
                            multistep h T t1 h' T t1' /\
                            step h' T t2 h' T t2'.
Proof.
  intros. generalize dependent t2. generalize dependent t2'.  induction H4. 
  {intros. split. constructor. assumption. }
  {intros. split. 
   {apply multi_step with (h' := h')(p1' :=p1')(p2' := p2'). admit. assumption. }


Theorem ReorderStepStar : forall T t1 t2 t1' t2' h h' sa ca,
                            specActions t2 sa -> specActions t2' sa ->
                            commitActions t2 ca -> commitActions t2' ca ->
                            step h (tUnion T t1) t2 h (tUnion T t1) t2' ->
                            multistep h (tUnion T t2') t1 h' (tUnion T t2') t1' ->
                            multistep h (tUnion T t2) t1 h' (tUnion T t2) t1' /\
                            step h' (tUnion T t1') t2 h' (tUnion T t1') t2'.
Proof.
  intros. dependent induction H4. 
  {split. constructor. assumption. }
  {split.  
   {inversion H5; subst. 
    {admit. } 
    {assert(specActions t2 sa). assumption. eapply IHmultistep in H; try eassumption. 
     inversion H. eapply multi_step. eapply Reorder in H7. inversion H7. eassumption. 
     eassumption. eassumption. eassumption. econstructor. assumption. 
     apply stepNoProgress in H9. inversion H9. eassumption. 



