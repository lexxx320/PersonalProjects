Require Import Spec.    
Require Import sets. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import Coq.Sets.Powerset_facts. 
Require Import SpecLib. 

Hint Unfold Ensembles.In Add. 
Hint Constructors Singleton Couple Union.  
Hint Resolve heapUpdateNeq. 

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
                          specActions (tSingleton (tid, a::s1, s2, M')) sa -> False.
Proof.
  intros. inversion H; inversion H0; subst. unfoldSetEq H4. 
  assert(Ensembles.In(AST.tid*actionStack) (specActionsAux (tSingleton (tid, s1, s2, M))) (tid, s1)). 
  econstructor. econstructor. econstructor. eapply hit. econstructor. 
  reflexivity. apply H2 in H3. inversion H3. inversion H5. inversion H7. inversion H8. 
  subst. inversion H9. symmetry in H6. invertListNeq. Qed. 

Theorem addCommitAction : forall tid a s1 s1' s2 M M' sa,
                          commitActions (tSingleton (tid, s1, s2, M)) sa ->
                          commitActions (tSingleton (tid, s1', a::s2, M')) sa -> False.
Proof.
  intros. inversion H; inversion H0; subst. unfoldSetEq H4.  
  assert(Ensembles.In(AST.tid*actionStack) (commitActionsAux (tSingleton (tid, s1, s2, M))) (tid, s2)). 
  econstructor. econstructor. econstructor. econstructor. 
  econstructor. reflexivity. apply H2 in H3. inversion H3. inversion H5. inversion H7. inversion H8. 
  inversion H9. symmetry in H16. invertListNeq. Qed. 

Axiom uniqueThreadPool : forall T tid t t', 
                           thread_lookup T tid t -> thread_lookup T tid t' -> t = t'. 

Theorem addCommitUnion : forall T T' tid s1 a s2 M M' ca,
              commitActions (tAdd T (tid, s1, s2, M)) ca -> 
              commitActions (tAdd T' (tid, s1, a::s2, M')) ca -> False.
Proof.
  intros. inversion H; inversion H0; subst. unfoldSetEq H4. 
  assert(Ensembles.In (AST.tid * actionStack)(commitActionsAux (tAdd T (tid, s1, s2, M))) (tid,s2)). 
  econstructor. econstructor. econstructor. econstructor.
  unfold tAdd. unfold Add. apply Union_intror. econstructor. reflexivity. eapply H2 in H3. 
  inversion H3. invertHyp. inv H4. inv H6. inv H5.
  {assert(thread_lookup (tAdd T' (tid, s1, a :: s3, M')) tid (tid, s1, a::s3, M')). 
   econstructor. apply Union_intror. constructor. auto.
   apply uniqueThreadPool with (t':= (tid, s0, s3, M0)) in H5. inversion H5. 
   invertListNeq. econstructor. econstructor. eauto. eauto. }
  {inversion H4. invertListNeq. }
Qed.  

Theorem addSpecUnion : forall T T' tid s1 a s2 M M' ca,
              specActions (tAdd T (tid, s1, s2, M)) ca -> 
              specActions (tAdd T' (tid, a::s1,s2, M')) ca -> False.
Proof.
  intros. inversion H; inversion H0; subst. unfoldSetEq H4.  
  assert(Ensembles.In (AST.tid * actionStack)(specActionsAux (tAdd T (tid, s1, s2, M))) (tid,s1)). 
  econstructor. econstructor. econstructor. econstructor. 
  unfold tAdd. unfold Add. apply Union_intror. econstructor. reflexivity. eapply H2 in H3. 
  inversion H3. invertHyp. inv H4. inv H6. inv H5.  
  {assert(thread_lookup (tAdd T' (tid, a::s0, s3, M')) tid (tid, a::s0,s3, M')).  
   econstructor. apply Union_intror. constructor. auto.
   apply uniqueThreadPool with (t':= (tid, s0, s3, M0)) in H5. inversion H5. 
   invertListNeq. econstructor. econstructor.  eauto. eauto. }
  {inversion H4. invertListNeq. }
Qed.  


Ltac handleReadWrite :=
  match goal with
      |H1 : heap_lookup ?x ?h = Some ?v, H2 : ?h = replace ?x ?v2 ?h |- _ =>
       eapply heapUpdateNeq with (v' := v2) in H1; 
         [contradiction | intros c; inversion c as [lneq]; invertListNeq]
  end. 

Theorem Reorder : forall T t1 t2 t1' t2' h h' sa ca,
                    specActions t2 sa -> specActions t2' sa ->
                    commitActions t2 ca -> commitActions t2' ca ->
                    step h (tUnion T t1) t2 (OK h (tUnion T t1) t2') ->
                    step h (tUnion T t2') t1 (OK h' (tUnion T t2') t1') ->
                    step h (tUnion T t2) t1 (OK h' (tUnion T t2) t1') /\
                    step h' (tUnion T t1') t2 (OK h' (tUnion T t1') t2').
Proof.
  intros. inversion H3. 
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
  {clear H11. subst. eapply addSpecAction in H0; eauto. inv H0. }
  {eapply heapUpdateNeq in H11. exfalso. apply H11. eauto. intros c. inversion c. }
  {subst. eapply addSpecUnion in H0. inv H0. eauto. }
  {subst. eapply addSpecAction in H0. inversion H0. eassumption. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }  
  {subst. inversion H0; inversion H; subst. unfoldSetEq H9. 
   assert(Ensembles.In(AST.tid*actionStack) (specActionsAux
            (tAdd TRB(tid, [], s2,t))) (2::tid, s1'++[specAct])). 
   econstructor. econstructor. econstructor. econstructor. econstructor. 
   inversion H11. eassumption. reflexivity. apply H5 in H8. inversion H8. 
   invertHyp. inv H9. inv H12.  assert(exists X, thread_lookup T' (2::tid) X). 
   eauto. contradiction. inversion H9. invertListNeq. }
  {inversion H4; eauto. } 
  {clear H13. subst. eapply addCommitAction in H2. inversion H2. eassumption. }
  {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
  {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
  {subst. eapply addCommitAction in H2. inversion H2. eassumption. }
  {inversion H4; eauto. }
  {inversion H4; eauto. }
Qed. 

Theorem ReorderStepStar : forall t1 t2 t1' t2' h h' sa ca,
                            specActions t2 sa -> specActions t2' sa ->
                            commitActions t2 ca -> commitActions t2' ca ->
                            step h t1 t2 (OK h t1 t2') ->
                            multistep h t2' t1 (OK h' t2' t1') ->
                            multistep h t2 t1 (OK h' t2 t1') /\
                            step h' t1' t2 (OK h' t1' t2').
Proof.
  intros. remember (OK h' t2' t1'). induction H4. 
  {inversion Heqc; subst. split. constructor. assumption. } 
  {inversion Heqc; subst. split. 
   {rename T1 into t2'. assert(specActions t2' sa). assumption. apply IHmultistep in H0; auto. 
    {inversion H0. apply multi_step with (P1 := P1) (P2 := P2) (P2' := P2') (h' := h'0); auto. 
     apply Reorder with (T := P1) (t1 := P2) (t1' := P2') 
                                  (t2' := t2') (h := h) (h' := h'0) (ca := ca) in H.  
     inversion H. assumption. assumption. assumption. assumption. assumption. assumption. 
    }

    {apply Reorder with (T := P1)(t1:=P2)(t1':=P2')(t2:=t2)(t2':=t2')(h:=h)(h':=h'0)(ca:=ca) in H.
     inversion H. assumption. assumption. assumption. assumption. assumption. assumption. }
   }
   {rename T1 into t2'. apply IHmultistep in H0. inversion H0. assumption. 
    assumption. apply Reorder with (T:=P1)(t1:=P2)(t1':=P2')(t2:=t2)(t2':=t2')(h:=h)(h':=h'0)(ca:=ca) in H.
    inversion H. assumption. assumption. assumption. assumption. assumption. assumption. reflexivity. }
  }
  {inversion Heqc. }
Qed. 

Theorem HeapUnchanged : forall T t h h' t' sa ca, step h T t (OK h' T t') -> specActions t sa ->
                                                  specActions t' sa -> commitActions t ca -> 
                                                  commitActions t' ca -> h' = h. 
Proof.
  intros. inversion H; eauto. 
  {subst. eapply addSpecAction in H0. inversion H0. eassumption. }
  {subst. eapply addSpecAction in H1. inversion H1. eassumption. }
  {subst. eapply addSpecUnion in H1. inv H1. eauto. }
  {subst. eapply addSpecAction in H1. inversion H1. eassumption. }
  {subst. inversion H0; inversion H1; subst. unfoldSetEq H8. 
   assert(Ensembles.In (AST.tid*actionStack)(specActionsAux
            (tAdd TRB (tid, [], s2, t0))) (2::tid, s1'++[specAct])).
   econstructor. econstructor. econstructor. econstructor. inversion H10. 
   eapply Union_introl. eassumption. reflexivity. apply H5 in H7. inversion H7. 
   invertHyp. inv H8. inv H11. assert(exists p, thread_lookup T' (2::tid) p). 
   eauto. contradiction. inversion H8. invertListNeq. }
  {subst. eapply addCommitAction in H3; eauto. inv H3. }
Qed. 

Inductive splitMultistep : sHeap -> pool -> pool -> config -> Prop :=
|splitRefl : forall h p1 p2, splitMultistep h p1 p2 (OK h p1 p2)
|splitStepL : forall h h' p1 p2 t1 t2 t2' config, 
                p1 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t1 p2) t2 (OK h' (tUnion t1 p2) t2') ->
                splitMultistep h' (tUnion t1 t2') p2 config ->
                splitMultistep h p1 p2 config
|splitStepR : forall h h' p1 p2 t1 t2 t2' config, 
                p2 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t1 p1) t2 (OK h' (tUnion t1 p1) t2') ->
                splitMultistep h' p1 (tUnion t1 t2') config ->
                splitMultistep h p1 p2 config
|errorL : forall h p1 p2 t1 t2 , 
                p1 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t1 p2) t2 Error ->
                splitMultistep h p1 p2 Error
|errorR : forall h p1 p2 t1 t2 , 
                p1 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t2 p2) t1 Error ->
                splitMultistep h p1 p2 Error
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

Theorem actionPreservation : forall t1 t2 t2' p1 p1' p2' sa ca h h' h'',
                               specActions (tUnion t1 t2) sa -> commitActions (tUnion t1 t2) ca ->
                               specActions p2' sa -> commitActions p2' ca ->
                               step h (tUnion t1 p1) t2 (OK h' (tUnion t1 p1) t2') ->
                               splitMultistep h' p1 (tUnion t1 t2') (OK h'' p1' p2') ->
                               specActions (tUnion t1 t2') sa /\ 
                               commitActions (tUnion t1 t2') ca.
Admitted. 

Theorem specActionsAuxDistribute : forall t1 t2, 
                                     specActionsAux (tUnion t1 t2) = 
                                     Union (tid*actionStack) (specActionsAux t1) (specActionsAux t2). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
  {intros. inversion H. inversion H0. inversion H2. inversion H3. inversion H4. 
   {constructor. constructor. econstructor. econstructor. econstructor. eassumption. 
    reflexivity. }
   {apply Union_intror. constructor. econstructor. econstructor. econstructor. eassumption. 
    reflexivity. }
  }
  {intros. inversion H. inversion H0. inversion H2. inversion H4. 
   {constructor. econstructor. econstructor. eapply hit. econstructor. 
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
                          S = Union (tid*actionStack) S1 S2 ->
                          Ensembles.In (tid*actionStack) S x -> Ensembles.In (tid*actionStack) S y ->
                          Ensembles.In (tid*actionStack) (Union (tid*actionStack) S1 S2) x ->
                          Ensembles.In (tid*actionStack) (Union (tid*actionStack) S1 S2) y ->
                          x <> y. 


Theorem disjointUnionActionSet : forall t1 t2, 
                                   specActions (tUnion t1 t2) (specActionsAux (tUnion t1 t2)) ->
                                   Intersection (tid*actionStack) (specActionsAux t1) (specActionsAux t2) = 
                                   Empty_set (tid*actionStack). 
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
       assert(Intersection (tid*actionStack) (specActionsAux t1) (specActionsAux t2') = Empty_set (tid*actionStack)).
       apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
       {inversion H1. assert(x <> x). eapply UniqueActionSet with(S1:=specActionsAux t1)(S2:=specActionsAux t2'). 
        reflexivity. auto. auto. auto. auto. exfalso. apply H6. reflexivity. }
       {inversion H1. }
       {apply UnionEq' with(S2:=specActionsAux t2)(S2':=specActionsAux t2')in H. rewrite H. 
        constructor. assumption. symmetry. assumption. }
Qed. 

Theorem commitActionsAuxDistribute : forall t1 t2, 
                                       commitActionsAux (tUnion t1 t2) = 
                                       Union (tid*actionStack) (commitActionsAux t1) (commitActionsAux t2). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
  {intros. inversion H. inversion H0. inversion H2. inversion H3. inversion H4. 
   {constructor. constructor. econstructor. econstructor. econstructor. eassumption. 
    reflexivity. }
   {apply Union_intror. constructor. econstructor. econstructor. econstructor. eassumption. 
    reflexivity. }
  }
  {intros. inversion H. inversion H0. inversion H2. inversion H4. 
   {constructor. econstructor. econstructor. eapply hit. econstructor. 
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
  assert(Intersection(tid*actionStack)(commitActionsAux t1)(commitActionsAux t2) = Empty_set(tid*actionStack)). 
  apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H1. assert(x<>x). eapply UniqueActionSet; eauto. exfalso. apply H6. reflexivity. }
  {inversion H1. }
  assert(Intersection(tid*actionStack)(commitActionsAux t1)(commitActionsAux t2') = Empty_set(tid*actionStack)). 
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
  assert(Ensembles.In (AST.tid * actionStack)(specActionsAux (tSingleton (tid, s1, s2, M))) 
                      (tid, s1)). 
  constructor. econstructor. econstructor. eapply hit. econstructor. reflexivity. 
  apply H2 in H3. inversion H3. inversion H5. inversion H7. inversion H8. 
  subst. inversion H9. symmetry in H6. apply listNeqEnd in H6. auto. 
Qed. 


Theorem pureStepHeapChange : forall h h' T t t' sa ca,
                               specActions t sa -> specActions t' sa ->
                               commitActions t ca -> commitActions t' ca ->
                               step h T t (OK h T t') ->
                               step h' T t (OK h' T t').
Proof.
  intros. inversion H3; eauto;
  try solve[repeat match goal with
       |H:heap_lookup ?x ?h = Some ?v, H' : ?h = replace ?x ?v' ?h |- _ =>
        eapply heapUpdateNeq in H;[exfalso; apply H; eauto| intros c; inversion c] 
       |H : ?y = ?x::?y |- _ => invertListNeq
   end].
  {clear H10. subst. eapply addSpecAction in H0; eauto. inv H0. }
  {subst. eapply addSpecUnion in H0; eauto. inv H0.  }
  {subst. eapply addSpecAction in H0; eauto. inv H0. }
  {subst. inversion H. inversion H0. subst. unfoldSetEq H8. 
   assert(Ensembles.In (AST.tid * actionStack)
         (specActionsAux
            (tAdd TRB  (tid, [], s2, t0)))(2::tid, s1'++[specAct])). 
   constructor. econstructor. econstructor. eapply hit. unfold tAdd. unfold Add. 
   apply Union_introl. inversion H10. eassumption. reflexivity. apply H5 in H7. 
   inversion H7. invertHyp. inv H8. inv H11.  
   assert(exists y, thread_lookup T' (2::tid) y). eauto. contradiction. 
   inv H12. inversion H8. invertListNeq. }
  {clear H12. subst. eapply popSpecActionFalse in H0. inversion H0. eassumption.  }
  {subst. eapply popSpecActionFalse in H0. inversion H0. eassumption.  }
  {subst. eapply popSpecActionFalse in H0. inversion H0. eassumption.  }
  {subst. eapply popSpecActionFalse in H0. inversion H0. eassumption.  }
Qed. 
 
Theorem Independence : forall t1 t2 t1' t2' h h' sa ca,
                         specActions t2 sa -> specActions t2' sa ->
                         commitActions t2 ca -> commitActions t2' ca ->
                         splitMultistep h t1 t2 (OK h' t1' t2') ->
                         multistep h t2 t1 (OK h' t2 t1') /\ multistep h' t1' t2 (OK h' t1' t2').
Proof.
  intros. remember (OK h' t1' t2'). induction H3.  
  {inversion Heqc; subst. split. constructor. constructor. }
  {inversion Heqc; subst. split. subst. eapply multi_step; try eassumption. reflexivity. 
   apply IHsplitMultistep in H. inversion H. assumption. assumption. 
   assumption. apply IHsplitMultistep; auto. }
  {inversion Heqc; subst. split. 
   {copy H. apply specActionsFrameRule with(t2:=t2)(t2':=t2'0)in H.  
    {inversion H. copy H1. apply commitActionsFrameRule with (t2:=t2)(t2':=t2'0) in H1.   
     {inversion H; clear H. inversion H1; clear H1. inversion H10. copy H3.
      eapply actionPreservation with (t1:=t1)(t2:=t2)(t2':=t2'0)(p1:=p1)(p1':=t1')(p2':=t2') 
        (sa:=sa)(ca:=ca)(h:=h)(h':=h'0)(h'':=h')in H3; auto. inversion H3. 
      apply specActionsFrameRule with(t2:=t2)(t2':=t2'0) in H12; auto. inversion H12; clear H12.  
      apply commitActionsFrameRule with (t2:=t2)(t2':=t2'0) in H9; auto. inversion H9; clear H9. inversion H12. 
      inversion H15. copy H5.
      apply HeapUnchanged with(sa:=x2)(ca:=x3)in H5; auto. copy H13. apply IHsplitMultistep in H13. 
      inversion H13. rewrite multistepUnusedPool in H21. apply stepUnusedPool in H19. subst h'0.  
      eapply ReorderStepStar with (t1:=p1)(t2:=t2)(t1':=t1')(t2':=t2'0)(h:=h)(h':=h')(sa:=x2)(ca:=x3) in H17. 
      inversion H17. rewrite multistepUnusedPool. assumption. assumption. assumption. assumption. 
      assumption. assumption. assumption. reflexivity. }
     {apply actionPreservation with (t1:=t1)(t2:=t2)(t2':=t2'0)(p1:=p1)(p1':=t1')(p2':=t2')
        (sa:=sa)(ca:=ca)(h:=h)(h':=h'0)(h'':=h')in H3; auto. inversion H3. assumption. }
    }
    {eapply actionPreservation with (t1:=t1)(t2:=t2)(t2':=t2'0)(p1:=p1)(p1':=t1')(p2':=t2')
        (sa:=sa)(ca:=ca)(h:=h)(h':=h'0)(h'':=h')in H3; auto. inversion H3. assumption. }
   }
   {copy H. apply actionPreservation with (t1:=t1)(t2:=t2)(t2':=t2'0)(p1:=p1)(p1':=t1')(p2':=t2')
                                          (sa:=sa)(ca:=ca)(h:=h)(h':=h'0)(h'':=h') in H; auto. 
    inversion H. copy H8. apply IHsplitMultistep in H8; auto. 
    unfold tUnion in H5. rewrite Union_commutative in H5. eapply multi_step. reflexivity.
    rewrite stepUnusedPool in H5. rewrite <- stepUnusedPool with(t1:=t1')in H5. 
    unfold tUnion in H5. rewrite Union_commutative in H5. copy H5. 
    apply specActionsFrameRule with (t2:=t2)(t2':=t2'0) in H3. invertHyp. 
    apply commitActionsFrameRule with(t2:=t2)(t2':=t2'0) in H1. invertHyp. 
    apply HeapUnchanged with(sa:=x)(ca:=x0) in H5; auto. 
    rewrite H5 in H11. eapply pureStepHeapChange in H11. eassumption.  eassumption. eassumption. 
    eassumption. eassumption. eassumption. inversion H8. eassumption. inversion H8. assumption. 
   }
  }
  {inversion Heqc. }{inversion Heqc. }
  Qed. 
