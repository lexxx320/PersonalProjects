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

Axiom specActionsEq : forall T T' sa,
                          specActions T sa -> specActions T' sa ->
                          (forall tid s1 s2 M, tIn T (tid,s1,s2,M) -> exists x, thread_lookup T' tid x) /\
                          (forall tid s1 s2 M, tIn T' (tid,s1,s2,M) -> exists x, thread_lookup T tid x).

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
   {admit. }
   {admit. }
   {admit. }
   {admit. }
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
                splitMultistep h' (tUnion t1 t2') p1 h'' p1' p1' ->
                splitMultistep h p1 p2 h'' p1' p2'
.

Theorem Independence : forall t1 t2 t1' t2' h h' sa ca,
                         specActions t2 sa -> specActions t2' sa ->
                         commitActions t2 ca -> commitActions t2' ca ->
                         Disjoint thread t1 t2 -> Disjoint thread t1' t2' ->
                         multistep h tEmptySet (tUnion t1 t2) h' tEmptySet (tUnion t1' t2') ->
                         multistep h t2 t1 h' t2 t1' /\ multistep h' t1' t2 h' t1' t2'. 
Proof.  
  intros. induction H5. 
  {

Theorem Independence : forall t1 t2 t1' t2' h h' sa ca,
                         specActions t2 sa -> specActions t2' sa ->
                         commitActions t2 ca -> commitActions t2' ca ->
                         Disjoint thread t1 t2 -> Disjoint thread t1' t2' ->
                         multistep h tEmptySet (tUnion t1 t2) h' tEmptySet (tUnion t1' t2') ->
                         multistep h t2 t1 h' t2 t1' /\ multistep h' t1' t2 h' t1' t2'. 
Proof.  
  intros. remember (tUnion t1 t2). remember (tUnion t1' t2'). generalize dependent t1. 
  generalize dependent t2. generalize dependent t1'. generalize dependent t2'. induction H5. 
  {intros. 












