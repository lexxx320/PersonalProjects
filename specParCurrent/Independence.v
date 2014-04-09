Require Import Spec.
Require Import sets. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 

Hint Unfold Ensembles.In Add. 
Hint Constructors Singleton Couple Union. 

Theorem InAdd : forall (T:Type) S s, Ensembles.In T (Add T S s) s. 
Proof.  intros. unfold Add. unfold Ensembles.In. apply Union_intror. 
  unfold Ensembles.In. apply In_singleton. 

Theorem SingletonEq : forall (T:Type) e e', Singleton T e = Singleton T e' -> e = e'.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. 
  inversion H. assert(Ensembles.In T (Singleton T e) e). auto. apply H0 in H2. 
  inversion H2. reflexivity. Qed. 

Ltac invertSetEq := 
  match goal with
      |H : Empty_set ?T = Singleton ?T ?e |- _ => 
       apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H;
       inversion H as [sameSet1 sameSet2]; 
       assert(Hin:Ensembles.In T (Singleton T e) e) by auto;
       apply sameSet2 in Hin; inversion Hin
      |H : Empty_set ?T = Couple ?T ?e1 ?e2 |- _ =>
       apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H;
       inversion H as [sameSet1 sameSet2];
       assert(Hin:Ensembles.In T (Couple T e1 e2) e1) by auto; apply sameSet2 in Hin;
       inversion Hin
      |H:Singleton ?T ?e = Empty_set ?T |- _ => symmetry in H; invertSetEq
      |H:Couple ?T ?e1 ?e2 = Empty_set ?T |- _ => symmetry in H; invertSetEq
      |H:Singleton ?T ?e1 = Couple ?T ?e2 ?e3 |- _ => apply SingleEqCouple in H
      |H:Couple ?T ?e2 ?e3 = Singleton ?T ?e1 |- _ => symmetry in H; invertSetEq
      |H : Empty_set ?T = Add ?T ?S ?s |- _ => 
       apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H; 
       inversion H as [sameSet1 sameSet2]; assert(Hin:Ensembles.In T (Add T S s) s) by apply InAdd;
       apply sameSet2 in Hin; inversion Hin
      |H : Add ?T ?S ?s = Empty_set ?T |- _ => symmetry in H; invertSetEq
      |H : Singleton ?T ?e = Singleton ?T ?e' |- _ => apply SingletonEq in H
  end. 

Ltac unfoldSetOp := repeat(try unfold tAdd in *; try unfold tIn in *; try unfold tCouple in *;
                           try unfold tSingleton in *; try unfold tEmptySet in *).

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

Ltac setNeq :=
  unfold tAdd in *; 
  match goal with
      |H:Empty_set ?T = Add ?T ?S ?s |- _ =>
       apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H;
       inversion H as [sameSet1 sameSet2]; assert(Assump:In T (Add T S s) s) by auto;
       apply sameSet2 in Assump; inversion Assump
      |H:Empty_set ?T = Couple ?T ?t1 ?t2 |- _ =>
       apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H; 
       inversion H as [sameSet1 sameSet2]; assert(Assump:In T (Couple T t1 t2) t1) by apply Couple_l;
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

Axiom eqSA : forall T1 T2 sa,
               specActions T1 sa -> specActions T2 sa ->
              (forall tid t t', thread_lookup T1 tid t -> thread_lookup T2 tid t') /\
              (forall tid t t', thread_lookup T2 tid t -> thread_lookup T1 tid t'). 


Theorem InWeakening : forall T e1 e2 tid, thread_lookup T tid e1 -> thread_lookup (tAdd T e2) tid e1. 
Proof.
  intros. inversion H. econstructor. subst. unfold tAdd. unfold Add. 
  apply Union_introl. assumption. eassumption. Qed. 

Theorem invertTIDLookup : forall tid T e e', thread_lookup (tAdd T e) tid e' ->
                                             thread_lookup T tid e' \/ 
                                             thread_lookup (tSingleton e) tid e'. 
Proof.
  intros. inversion H. subst. inversion H0; subst. 
  {left. econstructor. assumption. reflexivity. }
  {right. econstructor. assumption. reflexivity. }
Qed. 

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
  {Case "t1 does a read". inversion H4; eauto; try(subst; eapply AddSpecAction in H; inversion H; eassumption).
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
   {handleReadWrite. contradiction. intros contra. inversion contra. apply listNeq in H26. assumption. }
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

Inductive multistep2 : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|multi_refl2 : forall h p1 p2, multistep2 h p1 p2 h p1 p2
|multi_step2 : forall T1 T2 P1 P2 P1' P2' T2' H H' H'',
                 T2 = tUnion P1 P2 -> Disjoint thread P1 P2 -> step H (tUnion T1 P1) P2 H' (tUnion T1 P1') P2' ->
                 multistep2 H' T1 (tUnion P1' P2') H'' T1 T2' ->
                 multistep2 H T1 T2 H'' T1 T2'
.

Require Import Coq.Program.Equality. 

Inductive untouched : pool -> sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
  |UntouchedRefl : forall t1 h T t2, untouched t1 h T t2 h T t2
  |UntouchedStep : forall t1 T T' T'' t2 t2' t2'' h h' h'',
                     Included thread t1 T -> Included thread t1 T'->
                     step h T t2 h' T' t2' -> multistep h' T' t2' h'' T'' t2'' ->
                     untouched t1 h' T' t2' h'' T'' t2'' -> untouched t1 h T t2 h'' T'' t2''
.

Theorem multistepUntouched : forall h T t h' T' t' t1,
                               multistep h (tUnion T t1) t h' (tUnion T' t1) t' ->
                               untouched t1 h (tUnion T t1) t h' (tUnion T' t1) t'. 
Proof.
  intros. induction H. 
  {constructor. }
  {






Theorem ReorderStepStar : forall t1 t2 t1' t2' h h' sa ca,
                            specActions t2 sa -> specActions t2' sa ->
                            commitActions t2 ca -> commitActions t2 ca ->
                            step h t1 t2 h t1 t2' ->
                            multistep2 h t2' t1 h' t2' t1' ->
                            multistep2 h t2 t1 h' t2 t1' /\
                            step h' t1' t2 h' t1' t2'. 
Proof.
  intros. 
  induction H4. 
  {split. constructor. assumption. }
  {split. 
   {subst. 


Theorem ReorderStepStar : forall T t1 t2 t1' t2' h h' sa ca,
                            specActions t2 sa -> specActions t2' sa ->
                            commitActions t2 ca -> commitActions t2 ca ->
                            step h (tUnion T t1) t2 h (tUnion T t1) t2' ->
                            multistep h (tUnion T t2') t1 h' (tUnion T t2') t1' ->
                            multistep h (tUnion T t2) t1 h' (tUnion T t2) t1' /\
                            step h' (tUnion T t1') t2 h' (tUnion T t1') t2'. 
Proof.
  intros. remember (tUnion T t2'). generalize dependent t2'. induction H4. 
  {intros. split. constructor. assumption. }
  {intros. split. 
   {subst. 


Theorem EvalCtxtNeq : forall E e1 e2, e1 <> e2 -> ctxt E -> E e1 = E e2 -> False. 
Proof.
  intros. unfold not in *. intros. induction H0. 
  {inversion H1. apply IHctxt in H3. assumption. }
  {inversion H1. apply H in H3. assumption. }
  {inversion H1. apply H in H3. assumption. }
  {apply IHctxt in H1. assumption. }
Qed. 


Ltac termNeq := 
  match goal with
    |H: ?E ?x = ?E ?y |- _ => eapply EvalCtxtNeq with (e1 := x) (e2 := y);
                             [intros contra; inversion contra |eassumption| assumption]
  end.

Theorem stepNoProgress : forall h T t,
                           step h T t h T t -> False. 
Proof.
  intros. inversion H; try(subst; unfoldSetOp; invertSetEq; inversion H0; termNeq).  
  {unfold not in H7. apply H7. reflexivity. }  
  {subst. unfoldSetOp. invertSetEq. inversion H0. inversion H2. termNeq. }
  {eapply heapUpdateNeq in H2. unfold not in H2. apply H2. eassumption. 
   intros c. inversion c. apply listNeq in H10. assumption. }
  {unfoldSetOp. invertSetEq. inversion H0. termNeq. }
  {unfoldSetOp. invertSetEq. inversion H0. inversion H9. termNeq. }
Admitted. 


Theorem ReorderStepStar : forall T t1 t2 t1' t2' h h' sa ca,
                            specActions t2 sa -> specActions t2' sa ->
                            commitActions t2 ca -> commitActions t2' ca ->
                            step h T t2 h T t2' ->
                            multistep h T t1 h' T t1' ->
                            multistep h T t1 h' T t1' /\
                            step h' T t2 h' T t2'.
Proof.
  intros. induction H4. 
  {split. constructor. assumption. }
  {split. 
   {eapply multi_step with (h' := h') (p1' := p1') (p2' := p2').



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



