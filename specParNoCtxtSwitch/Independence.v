Require Import Spec.  
Require Import sets. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import Coq.Sets.Powerset_facts. 

Hint Unfold Ensembles.In Add. 
Hint Constructors Singleton Couple Union.  

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

Ltac unfoldSetEq H :=
  match type of H with
      |?S1 = ?S2  => try apply eqImpliesSameSet in H; unfold Same_set in H;
                             unfold Included in *; inversion H; clear H
  end.

Theorem addSpecAction : forall tid a s1 s2 M M' sa,
                          specActions (tSingleton (tid, s1, s2, M)) sa ->
                          specActions (tSingleton (bump tid, a::s1, s2, M')) sa -> False.
Proof.
  intros. inversion H; inversion H0; subst. unfoldSetEq H4. 
  assert(Ensembles.In(AST.tid*specStack) (specActionsAux (tSingleton (tid, s1, s2, M))) (tid, s1)). 
  econstructor. destruct tid. destruct p. econstructor. econstructor. eapply hit. econstructor. 
  reflexivity. apply H2 in H3. inversion H3. inversion H5. inversion H7. inversion H8. 
  subst. inversion H9. symmetry in H11. apply listNeq in H11. assumption. Qed. 

Theorem addCommitAction : forall tid a s1 s1' s2 M M' sa,
                          commitActions (tSingleton (tid, s1, s2, M)) sa ->
                          commitActions (tSingleton (tid, s1', a::s2, M')) sa -> False.
Proof.
  intros. inversion H; inversion H0; subst. unfoldSetEq H4. 
  assert(Ensembles.In(AST.tid*specStack) (commitActionsAux (tSingleton (tid, s1, s2, M))) (tid, s2)). 
  econstructor. destruct tid. destruct p. econstructor. econstructor. econstructor. 
  econstructor. reflexivity. apply H2 in H3. inversion H3. inversion H5. inversion H7. inversion H8. 
  inversion H9. symmetry in H16. apply listNeq in H16. assumption. Qed. 


Theorem Reorder : forall T t1 t2 t1' t2' h h' sa ca,
                    specActions t2 sa -> specActions t2' sa ->
                    commitActions t2 ca -> commitActions t2' ca ->
                    step h (tUnion T t1) t2 h (tUnion T t1) t2' ->
                    step h (tUnion T t2') t1 h' (tUnion T t2') t1' ->
                    step h (tUnion T t2) t1 h' (tUnion T t2) t1' /\
                    step h' (tUnion T t1') t2 h' (tUnion T t1') t2'.
Proof.
  intros. inversion H3. 
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; try(subst; eapply addSpecAction in H0; [inversion H0| eassumption]).
   {handleReadWrite. contradiction. intros c. inversion c. apply listNeq in H22. assumption. }
   {handleReadWrite. contradiction. intros c. inversion c. apply listNeq in H22. assumption. }
   {handleReadWrite. contradiction. intros c. inversion c. apply listNeq in H21. assumption. }
   {handleReadWrite. contradiction. intros c. inversion c. apply listNeq in H26. assumption. }
  }  
  {inversion H4; try(subst; eapply addSpecAction in H0; [inversion H0 | eassumption]).
   {handleReadWrite. contradiction. intros c. inversion c. } 
   {handleReadWrite. contradiction. intros c. inversion c. }
   {handleReadWrite. contradiction. intros c. inversion c. }
   {handleReadWrite. contradiction. intros c. inversion c. }
  } 
  {inversion H4; try(subst; eapply addSpecAction in H0; [inversion H0| eassumption]). }
  {inversion H4; eauto. }
  {inversion H4; eauto. } 
  {inversion H4; eauto. }
  {inversion H4; subst; try eauto. 
   {inversion H0. inversion H. subst sa. unfoldSetEq H13. 
    assert(Ensembles.In(AST.tid*specStack) (specActionsAux
            (tAdd TRB
               (tid, [], s2,
               E' (specReturn (raise E) (threadId (Tid (maj, min'') tid')))))) (Tid(maj,min) tid', a::s1')). 
    econstructor. econstructor. econstructor. econstructor. econstructor. inversion H9. eassumption. reflexivity. 
    apply H7 in H13. inversion H13. inversion H17. inversion H20. inversion H21. 
    assert(exists X, thread_lookup T' (Tid (maj, min) tid') X). econstructor. eapply hit.  
    inversion H27. eassumption. inversion H29. reflexivity. contradiction. }
   {inversion H0. inversion H. subst sa. unfoldSetEq H13. 
    assert(Ensembles.In(AST.tid*specStack) (specActionsAux
            (tAdd TRB
               (tid, [], s2,
               E' (specReturn (raise E) (threadId (Tid (maj, min'') tid')))))) (Tid(maj,min) tid', a::s1')). 
    econstructor. econstructor. econstructor. econstructor. econstructor. inversion H9. eassumption. reflexivity. 
    apply H7 in H13. inversion H13. inversion H17. inversion H20. inversion H21. 
    assert(exists X, thread_lookup T' (Tid (maj, min) tid') X). econstructor. eapply hit.  
    inversion H27. eassumption. inversion H29. reflexivity. contradiction. }
   {inversion H0. inversion H. subst sa. unfoldSetEq H13. 
    assert(Ensembles.In(AST.tid*specStack) (specActionsAux
            (tAdd TRB
               (tid, [], s2,
               E' (specReturn (raise E) (threadId (Tid (maj, min'') tid')))))) (Tid(maj,min) tid', a::s1')). 
    econstructor. econstructor. econstructor. econstructor. econstructor. inversion H9. eassumption. reflexivity. 
    apply H7 in H13. inversion H13. inversion H17. inversion H20. inversion H21. 
    assert(exists X, thread_lookup T' (Tid (maj, min) tid') X). econstructor. eapply hit.  
    inversion H27. eassumption. inversion H29. reflexivity. contradiction. }
   {inversion H0. inversion H. subst sa. unfoldSetEq H13. 
    assert(Ensembles.In(AST.tid*specStack) (specActionsAux
            (tAdd TRB
               (tid, [], s2,
               E' (specReturn (raise E) (threadId (Tid (maj, min'') tid')))))) (Tid(maj,min) tid', a::s1')). 
    econstructor. econstructor. econstructor. econstructor. econstructor. inversion H9. eassumption. reflexivity. 
    apply H7 in H13. inversion H13. inversion H17. inversion H19. inversion H24. 
    assert(exists X, thread_lookup T' (Tid (maj, min) tid') X). econstructor. eapply hit.  
    inversion H30. eassumption. inversion H32. reflexivity. contradiction. }
  }
  {inversion H4; eauto. }
  {inversion H4; try(subst; eapply addCommitAction in H2; [inversion H2 | eassumption]). }
  {inversion H4; try(subst; eapply addCommitAction in H2; [inversion H2 | eassumption]). }
  {inversion H4;  try(subst; eapply addCommitAction in H2; [inversion H2 | eassumption]). }
  {inversion H4; try(subst; eapply addCommitAction in H2; [inversion H2 | eassumption]). }
  {inversion H4; eauto. }
Qed. 

Theorem ReorderStepStar : forall t1 t2 t1' t2' h h' sa ca,
                            specActions t2 sa -> specActions t2' sa ->
                            commitActions t2 ca -> commitActions t2' ca ->
                            step h t1 t2 h t1 t2' ->
                            multistep h t2' t1 h' t2' t1' ->
                            multistep h t2 t1 h' t2 t1' /\
                            step h' t1' t2 h' t1' t2'.
Proof.
  intros. induction H4. 
  {split. constructor. assumption. } 
  {subst. split. 
   {clear t2'. rename T1 into t2'. assert(specActions t2' sa). assumption. apply IHmultistep in H0. 
    {inversion H0. apply multi_step with (P1 := P1) (P2 := P2) (P2' := P2') (h' := h'). 
     reflexivity. assumption. assert(specActions t2 sa) by assumption. 
     apply Reorder with (T := P1) (t1 := P2) (t1' := P2') 
                                  (t2' := t2') (h := h) (h' := h') (ca := ca) in H; try assumption. 
     inversion H. assumption. assumption. }
    {assumption. }
    {apply Reorder with (T := P1)(t1:=P2)(t1':=P2')(t2:=t2)(t2':=t2')(h:=h)(h':=h')(ca:=ca) in H.
     inversion H. assumption. assumption. assumption. assumption. assumption. assumption. }
   }
   {clear t2'. rename T1 into t2'. apply IHmultistep in H0. inversion H0. assumption. 
    assumption. apply Reorder with (T:=P1)(t1:=P2)(t1':=P2')(t2:=t2)(t2':=t2')(h:=h)(h':=h')(ca:=ca) in H.
    inversion H. assumption. assumption. assumption. assumption. assumption. assumption. }
  }
Qed. 

Theorem HeapUnchanged : forall T t h h' t' sa, step h T t h' T t' -> specActions t sa ->
                                               specActions t' sa -> h' = h. 
Proof.
  intros. inversion H; eauto. 
  {subst. eapply addSpecAction in H0. inversion H0. eassumption. }
  {subst. eapply addSpecAction in H1. inversion H1. eassumption. }
  {subst. eapply addSpecAction in H1. inversion H1. eassumption. }
  {subst. inversion H0; inversion H1; subst. unfoldSetEq H10. 
   assert(Ensembles.In (AST.tid*specStack)(specActionsAux
            (tAdd TRB
               (tid, [], s2,
               E' (specReturn (raise E) (threadId (Tid (maj, min'') tid')))))) (Tid(maj, min)tid', a::s1')).
   econstructor. econstructor. econstructor. econstructor. inversion H6. eapply Union_introl. 
   eassumption. reflexivity. apply H4 in H9. inversion H9. inversion H11. inversion H14. 
   inversion H15. inversion H21. assert(exists p, thread_lookup T' (Tid(maj, min) tid') p). 
   econstructor. eapply hit. eassumption. reflexivity. contradiction. inversion H23. }
Qed. 

Ltac copy H :=
  match type of H with
      | ?P => assert(P) by assumption
  end. 


Inductive splitMultistep : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|splitRefl : forall h p1 p2, splitMultistep h p1 p2 h p1 p2
|splitStepL : forall h h' h'' p1 p1' p2 p2' t1 t2 t2', 
                p1 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t1 p2) t2 h' (tUnion t1 p2) t2' ->
                splitMultistep h' (tUnion t1 t2') p2 h'' p1' p2' ->
                splitMultistep h p1 p2 h'' p1' p2'
|splitStepR : forall h h' h'' p1 p1' p2 p2' t1 t2 t2', 
                p2 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t1 p1) t2 h' (tUnion t1 p1) t2' ->
                splitMultistep h' p1 (tUnion t1 t2') h'' p1' p2' ->
                splitMultistep h p1 p2 h'' p1' p2'
.

Theorem pureStepActionPreserve : forall T tid s1 s2 M M' sa,
                                   specActions (tUnion T (tSingleton (tid, s1, s2, M))) sa ->
                                   specActions (tUnion T (tSingleton (tid, s1, s2, M'))) sa.
Proof.
  intros. inversion H. assert(specActionsAux(tUnion T (tSingleton (tid, s1, s2, M))) = 
                              specActionsAux(tUnion T (tSingleton (tid, s1, s2, M')))). 
  apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
   {intros. inversion H2. inversion H3. inversion H5. inversion H6. inversion H7.
    {constructor. econstructor. econstructor. eapply hit. eapply Union_introl. eassumption. 
     reflexivity. }
    {constructor. econstructor. econstructor. eapply hit. eapply Union_intror. inversion H12. 
     econstructor. reflexivity. }
   }
   {intros. inversion H2. inversion H3. inversion H5. inversion H6. inversion H7.
    {constructor. econstructor. econstructor. eapply hit. eapply Union_introl. eassumption. 
     reflexivity. }
    {constructor. econstructor. econstructor. eapply hit. eapply Union_intror. inversion H12. 
     econstructor. reflexivity. }
   }
   {rewrite H2. constructor. }
Qed. 
Hint Resolve pureStepActionPreserve. 
Theorem pureStepCActionPreserve : forall T tid s1 s2 M M' ca,
                            commitActions(tUnion T(tSingleton(tid, s1, s2, M))) ca ->
                            commitActions(tUnion T(tSingleton(tid, s1, s2, M'))) ca. 
Proof.
  intros. 
  inversion H. assert(commitActionsAux(tUnion T(tSingleton(tid, s1, s2, M))) = 
                     commitActionsAux(tUnion T(tSingleton(tid, s1, s2, M')))). 
  apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
  {intros. inversion H2. inversion H3. inversion H5. inversion H6. inversion H7. 
   {constructor. econstructor. econstructor. eapply hit. eapply Union_introl. eassumption. 
    reflexivity. }
   {constructor. econstructor. econstructor. eapply hit. eapply Union_intror. inversion H12. 
    econstructor. reflexivity. }
  }
  {intros. inversion H2. inversion H3. inversion H5. inversion H6. inversion H7.
   {constructor. econstructor. econstructor. eapply hit. eapply Union_introl. eassumption. 
    reflexivity. }
   {constructor. econstructor. econstructor. eapply hit. eapply Union_intror. inversion H12. 
    econstructor. reflexivity. }
   }
  {rewrite H2. constructor. }
Qed. 
Hint Resolve pureStepCActionPreserve. 

Axiom UniqueThreadPool : forall t1 t2, tIntersection t1 t2 = tEmptySet. 

Theorem actionPreservation' : forall t1 t2 t2' p1 p1' p2' sa ca h h' h'',
                               specActions (tUnion t1 t2) sa -> commitActions (tUnion t1 t2) ca ->
                               specActions p2' sa -> commitActions p2' ca ->
                               step h (tUnion t1 p1) t2 h' (tUnion t1 p1) t2' ->
                               splitMultistep h' p1 (tUnion t1 t2') h'' p1' p2' ->
                               specActions (tUnion t1 t2') sa /\ 
                               commitActions (tUnion t1 t2') ca.
Proof.
  intros. assert(splitMultistep h p1 (tUnion t1 t2) h'' p1' p2'). 
  eapply splitStepR. reflexivity. admit. eassumption. eassumption.
  remember (tUnion t1 t2). copy H5. induction H5. 
  {rewrite Heqe in H6. rewrite Heqe in H4. admit. }
Admitted. 

Theorem actionPreservation : forall t1 t2 t2' p1 p1' p2' sa ca h h' h'',
                               specActions (tUnion t1 t2) sa -> commitActions (tUnion t1 t2) ca ->
                               specActions p2' sa -> commitActions p2' ca ->
                               step h (tUnion t1 p1) t2 h' (tUnion t1 p1) t2' ->
                               splitMultistep h' p1 (tUnion t1 t2') h'' p1' p2' ->
                               specActions (tUnion t1 t2') sa /\ 
                               commitActions (tUnion t1 t2') ca.
Proof.
  intros. inversion H3; subst.   
  {split. eapply pureStepActionPreserve in H. eassumption. eapply pureStepCActionPreserve. eassumption. }
  {split. eapply pureStepActionPreserve in H. eassumption. eapply pureStepCActionPreserve. eassumption. }
  {split. eapply pureStepActionPreserve in H. eassumption. eapply pureStepCActionPreserve. eassumption. }
  {split. eapply pureStepActionPreserve in H. eassumption. eapply pureStepCActionPreserve. eassumption. }
  {inversion H. inversion H0. rewrite <- H6 in H1. inversion H1. 
Admitted. 

Theorem specActionsAuxDistribute : forall t1 t2, 
                                     specActionsAux (tUnion t1 t2) = 
                                     Union (tid*specStack) (specActionsAux t1) (specActionsAux t2). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
  {intros. inversion H. inversion H0. inversion H2. inversion H3. inversion H4. 
   {constructor. constructor. econstructor. econstructor. econstructor. eassumption. 
    reflexivity. }
   {apply Union_intror. constructor. econstructor. econstructor. econstructor. eassumption. 
    reflexivity. }
  }
  {intros. inversion H. inversion H0. inversion H2. inversion H4. 
   {constructor. econstructor. econstructor. destruct t. destruct p. eapply hit. econstructor. 
    inversion H5. eassumption. reflexivity. }
   {inversion H0. inversion H2. inversion H4. inversion H5. constructor. econstructor. 
    econstructor. econstructor. eapply Union_intror. eassumption. reflexivity. }
  }
Qed. 

Theorem UnionEq' : forall T S1 S2 S2', Intersection T S1 S2 = Empty_set T ->
                                       Intersection T S1 S2' = Empty_set T ->
                                       Union T S1 S2 = Union T S1 S2' -> S2 = S2'. 
Proof.
  intros. 
  unfoldSetEq H1. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {assert(Ensembles.In T (Union T S1 S2) x). apply Union_intror. assumption. 
   apply H2 in H4. inversion H4. 
   {assert(Ensembles.In T (Intersection T S1 S2) x). constructor. assumption. assumption. 
    unfoldSetEq H. apply H8 in H7. inversion H7. }
   {assumption. }
  }
  {assert(Ensembles.In T (Union T S1 S2') x). apply Union_intror. assumption. 
   apply H3 in H4. inversion H4. 
   {assert(Ensembles.In T (Intersection T S1 S2') x). constructor; assumption. 
    unfoldSetEq H0. apply H8 in H7. inversion H7. }
   {assumption. }
  }
Qed. 

Axiom UniqueActionSet : forall x y S1 S2 S, 
                          S = Union (tid*specStack) S1 S2 ->
                          Ensembles.In (tid*specStack) S x -> Ensembles.In (tid*specStack) S y ->
                          Ensembles.In (tid*specStack) (Union (tid*specStack) S1 S2) x ->
                          Ensembles.In (tid*specStack) (Union (tid*specStack) S1 S2) y ->
                          x <> y. 


Theorem disjointUnionActionSet : forall t1 t2, 
                                   specActions (tUnion t1 t2) (specActionsAux (tUnion t1 t2)) ->
                                   Intersection (tid*specStack) (specActionsAux t1) (specActionsAux t2) = 
                                   Empty_set (tid*specStack). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0. assert(x<>x). eapply UniqueActionSet with (S1:=specActionsAux t1)(S2:=specActionsAux t2). 
   reflexivity. constructor. eassumption. auto. auto. auto. exfalso. apply H4. reflexivity. }
  {inversion H0. }Qed.  

Theorem specActionsFrameRule : forall t1 t2 t2' sa,
                                 specActions (tUnion t1 t2) sa ->
                                 specActions (tUnion t1 t2') sa ->
                                 exists sa', specActions t2 sa' /\ specActions t2' sa'.
Proof. intros. inversion H; inversion H0; subst. rewrite specActionsAuxDistribute in H4. 
       rewrite specActionsAuxDistribute in H4. econstructor. split. econstructor. 
       apply disjointUnionActionSet in H.
       assert(Intersection (tid*specStack) (specActionsAux t1) (specActionsAux t2') = Empty_set (tid*specStack)).
       apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
       {inversion H1. assert(x <> x). eapply UniqueActionSet with(S1:=specActionsAux t1)(S2:=specActionsAux t2'). 
        reflexivity. auto. auto. auto. auto. exfalso. apply H6. reflexivity. }
       {inversion H1. }
       {apply UnionEq' with(S2:=specActionsAux t2)(S2':=specActionsAux t2')in H. rewrite H. 
        constructor. assumption. symmetry. assumption. }
Qed. 

Theorem commitActionsAuxDistribute : forall t1 t2, 
                                       commitActionsAux (tUnion t1 t2) = 
                                       Union (tid*specStack) (commitActionsAux t1) (commitActionsAux t2). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
  {intros. inversion H. inversion H0. inversion H2. inversion H3. inversion H4. 
   {constructor. constructor. econstructor. econstructor. econstructor. eassumption. 
    reflexivity. }
   {apply Union_intror. constructor. econstructor. econstructor. econstructor. eassumption. 
    reflexivity. }
  }
  {intros. inversion H. inversion H0. inversion H2. inversion H4. 
   {constructor. econstructor. econstructor. destruct t. destruct p. eapply hit. econstructor. 
    inversion H5. eassumption. reflexivity. }
   {inversion H0. inversion H2. inversion H4. inversion H5. constructor. econstructor. 
    econstructor. econstructor. eapply Union_intror. eassumption. reflexivity. }
  }
Qed. 

Theorem commitActionsFrameRule : forall t1 t2 t2' ca,
                                   commitActions(tUnion t1 t2) ca ->
                                   commitActions(tUnion t1 t2') ca ->
                                   exists ca', commitActions t2 ca' /\ commitActions t2' ca'.
Proof. 
  intros. inversion H; inversion H0; subst. rewrite commitActionsAuxDistribute in H4. 
  rewrite commitActionsAuxDistribute in H4. econstructor. split. econstructor. 
  assert(Intersection(tid*specStack)(commitActionsAux t1)(commitActionsAux t2) = Empty_set(tid*specStack)). 
  apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H1. assert(x<>x). eapply UniqueActionSet; eauto. exfalso. apply H6. reflexivity. }
  {inversion H1. }
  assert(Intersection(tid*specStack)(commitActionsAux t1)(commitActionsAux t2') = Empty_set(tid*specStack)). 
  apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H2. assert(x<>x). eapply UniqueActionSet; eauto. exfalso. apply H7. reflexivity. }
  {inversion H2. }
  apply UnionEq' with(S2:=commitActionsAux t2)(S2':=commitActionsAux t2') in H1. rewrite H1. 
  constructor. assumption. symmetry. assumption. Qed. 



Theorem listNeqEnd : forall (T:Type) l (e:T), l = l ++ [e] -> False. 
Proof.
  intros. induction l. 
  {inversion H. }
  {inversion H. apply IHl in H1. assumption. }
Qed. 

Theorem popSpecActionFalse : forall tid a s1 s2 s2' M M' sa,
                               specActions(tSingleton(tid, s1, s2, M)) sa ->
                               specActions(tSingleton(tid, s1 ++ [a], s2', M')) sa -> False. 
Proof. 
  intros. inversion H. inversion H0; subst. unfoldSetEq H4. 
  destruct tid. destruct p. 
  assert(Ensembles.In (AST.tid * specStack)(specActionsAux (tSingleton (Tid (n, n0) l, s1, s2, M))) 
                      (Tid(n, n0) l, s1)). 
  constructor. econstructor. econstructor. eapply hit. econstructor. reflexivity. 
  apply H2 in H3. inversion H3. inversion H5. inversion H7. inversion H8. 
  inversion H14. symmetry in H17. apply listNeqEnd in H17. assumption. 
Qed. 


Theorem pureStepHeapChange : forall h h' T t t' sa,
                               specActions t sa -> specActions t' sa ->
                               step h T t h T t' ->
                               step h' T t h' T t'.
Proof.
  intros. inversion H1; eauto. 
  {eapply heapUpdateNeq in H3. unfold not in H3. exfalso. apply H3. eassumption. 
   intros c. inversion c. apply listNeq in H12. assumption. }
  {eapply heapUpdateNeq in H3. unfold not in H3. exfalso. apply H3. eassumption. 
   intros c. inversion c. }
  {subst. destruct h.
   {simpl in H3. inversion H3. }
   {simpl in H3. inversion H3. destruct p. inversion H5. apply listNeq in H10. inversion H10. }
  }
  {subst. inversion H. inversion H0. subst. unfoldSetEq H10. 
   assert(Ensembles.In (AST.tid * specStack)
         (specActionsAux
            (tAdd TRB
               (tid, [], s2,
                E' (specReturn (raise E) (threadId (Tid (maj, min'') tid'))))))
         (Tid(maj, min) tid', a::s1')). constructor. econstructor. econstructor. 
   eapply hit. unfold tAdd. unfold Add. apply Union_introl. inversion H6. eassumption. 
   reflexivity. apply H4 in H9. inversion H9. 
   assert(exists y, thread_lookup T' (Tid(maj, min) tid') y). inversion H11. 
   inversion H14. inversion H15. inversion H21. exists(Tid (maj, min) tid', a :: s1', x, x0). 
   eapply hit. assumption. reflexivity. inversion H23. contradiction. }
  {subst. eapply popSpecActionFalse in H0. inversion H0. eassumption.  }
  {subst. eapply popSpecActionFalse in H0. inversion H0. eassumption.  }
  {subst. eapply popSpecActionFalse in H0. inversion H0. eassumption.  }
  {subst. eapply popSpecActionFalse in H0. inversion H0. eassumption.  }
Qed. 


Theorem Independence : forall t1 t2 t1' t2' h h' sa ca,
                         specActions t2 sa -> specActions t2' sa ->
                         commitActions t2 ca -> commitActions t2' ca ->
                         splitMultistep h t1 t2 h' t1' t2' ->
                         multistep h t2 t1 h' t2 t1' /\ multistep h' t1' t2 h' t1' t2'.
Proof.
  intros. induction H3. 
  {split. constructor. constructor. }
  {split. subst. eapply multi_step; try eassumption. reflexivity. 
   apply IHsplitMultistep in H. inversion H. assumption. assumption. 
   assumption. assumption. apply IHsplitMultistep in H. inversion H. 
   assumption. assumption. assumption. assumption. }
  {split. rewrite H3 in H. copy H. apply specActionsFrameRule with(t2:=t2)(t2':=t2')in H. inversion H. 
   {copy H5. apply HeapUnchanged with(sa:=x)in H5. 
    {copy H9. eapply actionPreservation with (p2':=p2')
     (t1:=t1)(t2:=t2)(t2':=t2')(p1:=p1)(p1':=p1')(ca:=ca)(h:=h)(h':=h')(h'':=h'')in H9. 
     inversion H9. copy H11. apply IHsplitMultistep in H11. 
     inversion H11. rewrite stepUnusedPool in H10. rewrite multistepUnusedPool in H14. 
     rewrite H5 in H10. apply specActionsFrameRule with (t2:=t2)(t2':=t2')in H7. inversion H7. inversion H16.
     rewrite H3 in H1. apply commitActionsFrameRule with(t2:=t2)(t2':=t2') in H1.
     inversion H1. inversion H19. 
     eapply ReorderStepStar with (t1:=p1)(t2:=t2)(t2':=t2')(t1':=p1')(h:=h)(h':=h'')in H17. rewrite H3. 
     rewrite multistepUnusedPool. inversion H17. assumption. eassumption. 
     eassumption. eassumption. assumption. rewrite H5 in H14. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption. rewrite H3 in H1. assumption. 
     assumption. assumption. assumption. }
    {inversion H8. assumption. }
    {inversion H8. assumption. }
   }
   {copy H. apply actionPreservation with (p2':=p2')
     (t1:=t1)(t2:=t2)(t2':=t2')(p1:=p1)(p1':=p1')(ca:=ca)(h:=h)(h':=h')(h'':=h'')in H; try assumption. 
    inversion H. copy H9. apply IHsplitMultistep in H9; try assumption. rewrite H3 in H1. assumption. }
   {rewrite H3 in H. copy H. apply actionPreservation with (p2':=p2')
     (t1:=t1)(t2:=t2)(t2':=t2')(p1:=p1)(p1':=p1')(ca:=ca)(h:=h)(h':=h')(h'':=h'')in H; try assumption.
    inversion H. copy H8. apply IHsplitMultistep in H8; try assumption. rewrite H3 in H1. 
    unfold tUnion in H5. rewrite Union_commutative in H5. eapply multi_step. eassumption. 
    assumption. rewrite stepUnusedPool in H5. rewrite <- stepUnusedPool with(t1:=p1')in H5. 
    unfold tUnion in H5. rewrite Union_commutative in H5. copy H5. 
    apply specActionsFrameRule with (t2:=t2)(t2':=t2') in H7. inversion H7. inversion H12. 
    apply HeapUnchanged with(sa:=x) in H5.  
    rewrite H5 in H11. eapply pureStepHeapChange in H11. eassumption.  eassumption. eassumption. 
    eassumption. eassumption. eassumption. inversion H8. eassumption. rewrite H3 in H1. assumption. 
   }
  }
  Qed. 

(*---------------------------Read Independence--------------------------*)

Theorem HeapUpdateShadow : forall (h:sHeap) v1 v2 x, 
                           replace x v1 (replace x v2 h) = replace x v1 h. 
Proof.
  intros. induction h. 
  {simpl. reflexivity. }
  {simpl. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl. rewrite <- beq_nat_refl. reflexivity. }
   {simpl. rewrite eq. rewrite IHh. reflexivity. }
  }
Qed. 


Theorem HeapUpdateSame : forall (h:sHeap) v x, heap_lookup x h = Some v ->
                                               replace x v h = h. 
Proof.
  intros. induction h. 
  {inversion H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H. apply beq_nat_true in eq. subst. reflexivity. }
   {apply IHh in H. rewrite H. reflexivity. }
  }
Qed. 

Hint Resolve HeapUpdateSame. 

Require Import Coq.Logic.Classical_Prop. 

Theorem HeapUpdateMiss : forall (h:sHeap) x x' v, x'<>x -> heap_lookup x (replace x' v h) = heap_lookup x h. 
Proof.
  intros. simpl. induction h. 
  {simpl. reflexivity. }
  {simpl. destruct a. destruct (beq_nat x i) eqn:eq. 
   {destruct (beq_nat x' i) eqn :c. 
    {rewrite beq_nat_true_iff in eq. rewrite beq_nat_true_iff in c. subst. exfalso. 
     apply H. reflexivity. }
    {simpl. rewrite eq. reflexivity. }
   }
   {destruct (beq_nat x' i). 
    {simpl. destruct (beq_nat x x') eqn:c. 
     {rewrite beq_nat_true_iff in c. symmetry in c. contradiction. }
     {reflexivity. }
    }
    {simpl. rewrite eq. assumption. }
   }
  }
Qed. 

Hint Constructors multistep. 

Require Import Coq.Program.Equality. 

Theorem AddSingletonEq : forall T S1 s1 s2, Add T S1 s1 = Singleton T s2 -> s1 = s2. 
Proof.
  intros. unfoldSetEq H. assert(Ensembles.In T (Add T S1 s1) s1). apply Union_intror. 
  constructor. apply H0 in H. inversion H. reflexivity. Qed. 


Theorem ReadInd : forall h h' h'' T' T tid s1 s2 E x N t s ds t' M,
                    heap_lookup x h = Some(sfull nil ds s t N) -> decompose M E (get x) ->
                    t' = (tSingleton (bump tid, rAct x tid M::s1, s2, E(ret N))) ->
                    step h T (tSingleton (tid,s1,s2,M)) h' T t' -> 
                    multistep h' t' T h'' t' T' ->
                    multistep h (tSingleton (tid,s1,s2,M)) T (replace x (sfull nil ds s t N) h'')
                              (tSingleton (tid,s1,s2,M)) T'. 
Proof.
  intros. generalize dependent h. induction H3. 
  {intros. subst. inversion H2; try(subst; apply HeapUpdateSame in H; rewrite H; constructor). 
   {apply SingletonEq in H1. inversion H1. apply uniqueCtxtDecomp with(E':=E)(e':=get x)in H4. 
    inversion H4. inversion H16. subst. 
    {rewrite HeapUpdateShadow. cleanup. clear H4. apply HeapUpdateSame in H. rewrite H. constructor. }
    {subst. assumption. }
   }
   {apply SingletonEq in H1. inversion H1. subst. apply uniqueCtxtDecomp with (E':=E)(e':=get x) in H4. 
    inversion H4. inversion H6. assumption. }
   {apply SingletonEq in H1. inversion H1. subst. apply uniqueCtxtDecomp with (E':=E)(e':=get x) in H6. 
    inversion H6. inversion H5. assumption. }
   {subst. apply AddSingletonEq in H3. inversion H3. }
  }
  {Case "Inductive Case". intros. subst. 

Ltac eqImpliesX :=
  match goal with
      |H:?x = ?x -> ?p |- _ => assert(eqAssump : x = x) by reflexivity; eapply H in eqAssump
  end. 

Theorem HeapLookupReplace : forall x (h:sHeap) v v', heap_lookup x h = Some v' ->
                                                     heap_lookup x (replace x v h) = Some v. 
Proof.
  intros. induction h. 
  {inversion H. }
  {simpl. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl. rewrite <- beq_nat_refl. reflexivity. }
   {simpl in *.  rewrite eq. rewrite eq in H. apply IHh in H. assumption. }
  }
Qed.  

Theorem ReadInd' : forall h h' T' T  tid s1 s2 E x N t s ds t' M,
                    heap_lookup x h = Some(sfull nil ds s t N) -> decompose M E (get x) ->
                    t' = (tSingleton (bump tid, rAct x tid (E(get x))::s1, s2, E(ret N))) ->
                    step h T (tSingleton (tid,s1,s2,E(get x))) 
                         (replace x (sfull nil (tid::ds) s t N) h) T t' -> 
                    multistep (replace x (sfull nil (tid::ds) s t N) h) t' T h' t' T' ->
                    multistep h (tSingleton (tid,s1,s2,E(get x))) T (replace x (sfull nil ds s t N) h')
                              (tSingleton (tid,s1,s2,E(get x))) T'. 
Proof.
  intros. remember (replace x (sfull [] (tid :: ds) s t N) h). generalize dependent h.  induction H3. 
  {intros. subst. rewrite HeapUpdateShadow. apply HeapUpdateSame in H. rewrite H. 
   constructor. }
  {intros. subst. inversion H3; subst. 
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor; eauto. }
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor. eauto. }
   {eqImpliesX; eauto. eapply multi_step; eauto. eapply Handle. eauto. }
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor. eauto. }
   {eqImpliesX; eauto. }
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor; eauto. }
   {admit. } 
   {admit. }
   {admit. }
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor; eauto. }
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor; eauto. }
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor; eauto. }
   {admit. }
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor; eauto. }
   {admit. }
   {admit. }
   {admit. }
   {admit. }
   {eqImpliesX; eauto. eapply multi_step; eauto. econstructor; eauto. }
  }
Qed. 

Theorem ForkInd : forall h h' T T' tid s1 s2 E t t' M,
                    decompose t E (fork M) ->
                    t' = (bump tid, fAct (extendTid tid) tid t::s1, s2, E(ret unit)) ->
                    step h T (tSingleton (tid, s1, s2, t)) h T (tCouple t' (extendTid tid, [specAct], nil, M)) ->
                    multistep h (tCouple t' (extendTid tid, [specAct], nil, M)) T h'
                              (tCouple t' (extendTid tid, [specAct], nil, M)) T' ->
                    multistep h (tSingleton(tid, s1, s2, t)) T h' (tSingleton (tid, s1, s2, t)) T'.
Proof.
  intros. remember (tCouple t' (extendTid tid, [specAct], [], M)). induction H2; auto. 
  {apply IHmultistep in Heqe. inversion H4; subst; try(solve[eapply multi_step; eauto; eauto]).
   {copy H. apply decomposeEq in H. subst t. inversion H1; eauto. 
    {eapply heapUpdateNeq in H11. inversion H11. eassumption. intros c. inversion c. 
     apply listNeq in H16. assumption. }
    {eapply heapUpdateNeq in H11. inversion H11. eassumption. intros c. inversion c. }
    {destruct h. simpl in H10. inversion H10. inversion H10. destruct p. inversion H15. 
     apply listNeq in H19. inversion H19. }
    {subst. apply AddSingletonEq in H. inversion H. 
     eapply uniqueCtxtDecomp with (E':=E)(e':=fork M)in H7. inversion H7. inversion H14. 
     rewrite <- H13 in H6. assumption. }
    {subst T1. apply SingleEqCouple in H13. inversion H13. inversion H15. }
    {subst T1. apply SingleEqCouple in H14. inversion H14. inversion H16. }
    {subst T1. apply SingleEqCouple in H14. inversion H14. inversion H16. }
    {subst T1. apply SingleEqCouple in H14. inversion H14. inversion H16. }
   }
  }
Qed. 