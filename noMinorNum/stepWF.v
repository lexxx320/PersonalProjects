Require Import SfLib.  
Require Import NonSpec. 
Require Import Spec.  
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import hetList. 
Require Import Coq.Program.Equality. 
Require Import unspec. 
Require Import sets. 
Require Import Heap.

Theorem multi_trans : forall H T1 T2 H' T1' T2' H'' T1'' T2'', 
                        multistep H T1 T2 (OK H' T1' T2') -> 
                        multistep H' T1' T2' (OK H'' T1'' T2'') ->
                        multistep H T1 T2 (OK H'' T1'' T2''). 
Proof.
  intros. genDeps {H''; T1''; T2''}. remember (OK H' T1' T2'). induction H0. 
  {inv Heqc. intros. auto. }
  {intros. apply IHmultistep in H2; auto. subst. econstructor; eauto. }
  {inversion Heqc. }
Qed. 

Theorem destructEnd : forall (T:Type) (l : list T), l = [] \/ exists (a:T) l', l = l' ++ [a]. 
Proof.
  induction l. 
  {auto. }
  {inversion IHl. right. exists a. exists nil. simpl. subst. auto. 
   inv H. inv H0. right. exists x. exists (a::x0). auto. }
Qed. 

Axiom unspec_thread : forall t, exists t', unspecThread t (Some t') \/ unspecThread t None. 

Ltac eUnspec :=
  match goal with
      |H:wellFormed ?H (tUnion ?T (tSingleton ?t)) |- _ => 
       assert(exists t', unspecThread t (Some t') \/ unspecThread t None)
         by apply unspec_thread
  end. 


Theorem unspecPoolEmpty : forall t, unspecThread t None -> unspecPoolAux (tSingleton t) = tEmptySet. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H3; subst. inversion H4; subst. 
   clear H3 H4. eapply unspecDeterm in H2; eauto. inversion H2. }
  {inversion H0. }
Qed. 


Axiom uniqueTP : forall T1 T2 t, tIn (tUnion T1 T2) t -> tIn T1 t -> tIn T2 t -> False. 

Theorem unionEq : forall T1 T2 T2', tUnion T1 T2 = tUnion T1 T2' -> T2 = T2'.  
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
   assert(tIn (tUnion T1 T2) x). apply Union_intror. auto. copy H. apply H1 in H.
   inversion H; subst. eapply uniqueTP in H0; eauto. inversion H0. auto. }
  {apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
   assert(tIn (tUnion T1 T2') x). apply Union_intror. auto. copy H. apply H2 in H3. 
   inversion H3; subst. eapply uniqueTP in H0; eauto. inversion H0. auto. }
Qed. 

Hint Constructors Union Couple. 

Theorem coupleUnion : forall X t1 t2, Couple X t1 t2 = Union X (Singleton X t1) (Singleton X t2). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H; subst; auto. }
  {inversion H; subst. inversion H0; subst; auto. inversion H0; subst; auto. }
Qed. 

Axiom moveToUnused : forall t T T' H H', 
              multistep H tEmptySet (tUnion T (tSingleton t)) (OK H' tEmptySet (tUnion T' (tSingleton t))) <->
              multistep H (tSingleton t) T (OK H' (tSingleton t) T'). 

Ltac replaceWithEmpty :=
  match goal with
      |H:multistep ?H (tSingleton ?t) ?T ?x |- _ => 
       let n := fresh in
       assert(n:(tSingleton t) = tUnion (tSingleton t) tEmptySet) by (unfold tUnion; rewrite union_empty; auto)
      | |-multistep ?H (tSingleton ?t) ?T ?x => 
       let n := fresh in
       assert(n:(tSingleton t) = tUnion (tSingleton t) tEmptySet) by (unfold tUnion; rewrite union_empty; auto)  
  end. 

(*Helper theorems for reasoning about the erasure of heaps being rolled back*)
Theorem unspecHeapRBNew : forall H H' x S A,
                           unspecHeap H H' ->
                           heap_lookup x H = Some(sempty (S::A)) ->
                           unspecHeap (remove H x) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst; clear H1. inversion H0; subst. assumption. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem unspecHeapRead :  forall H H' x sc ds ds' S t N,
                            unspecHeap H H' ->
                            heap_lookup x H = Some (sfull sc ds S t N) ->
                            unspecHeap (replace x (sfull sc ds' S t N) H) H'. 
Proof.
  induction H; intros. 
  {simpl in *. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. inversion H0; subst; auto. 
    {apply beq_nat_true in eq. subst. auto. }
    {apply beq_nat_true in eq. subst; auto. }
   }
   {apply beq_nat_false in eq. inv H0; eauto. }
  }
Qed.  

Theorem unspecHeapRBWrite : forall H H' x sc S A tid N,
                      unspecHeap H H' ->
                      heap_lookup x H = Some(sfull sc nil (S::A) tid N) ->
                      unspecHeap (replace x (sempty sc) H) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst. clear H1. inversion H0; subst. 
    econstructor. assumption. apply beq_nat_true in eq. subst. auto. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem unspecHeapSpecWrite : forall H H' x s sc s1 tid M a,
                            unspecHeap H H' ->
                            heap_lookup x H = Some (sempty sc) ->
                            unspecHeap (replace x (sfull sc s (a::s1) tid M) H) H'.
Proof.
  induction H; intros. 
  {simpl in *. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {apply beq_nat_true in eq; subst. inv H1. inv H0; auto. }
   {inv H0; auto. }
  }
Qed. 

Theorem unspecHeapCommWrite : forall H H' x t N,
                            unspecHeap H H' -> heap_lookup x H = Some(sempty nil) ->
                            unspecHeap (replace x (sfull nil nil nil t N) H)
                                       (replace x (sfull nil nil nil t N) H'). 
Proof. 
  induction H; intros. 
  {simpl in *. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst. inversion H0; subst. simpl. rewrite eq. auto. }
   {inversion H0; subst; auto. 
    {simpl. rewrite eq. auto. }
    {simpl. rewrite eq. auto. }
    {simpl. rewrite eq. auto. }
   }
  }
Qed. 

Theorem lookupUnspecFull : forall H H' x ds t N, 
                             unspecHeap H H' -> heap_lookup x H = Some(sfull nil ds nil t N) ->
                             heap_lookup x H' = Some(sfull nil nil nil t N).
Proof.
  induction H; intros. 
  {simpl in *. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. inversion H0; subst. simpl. rewrite eq. auto. }
   {inversion H0; subst; eauto.  
    {simpl. rewrite eq. eapply IHlist. auto. eauto. }
    {simpl. rewrite eq; eauto. }
    {simpl. rewrite eq. eauto. }
   }
  }
Qed. 

Theorem stepHeapExt : forall H H' x T t t' N tid,
                             heap_lookup x H' = Some(sempty nil) -> unspecHeap H H' ->
                             step H' T t (OK H T t') -> 
                             step (replace x (sfull nil nil nil tid N) H') T t
                                       (OK (replace x (sfull nil nil nil tid N) H) T t). 
Proof.
  intros. Admitted. 

Ltac introsInv := let n := fresh in intros n; inversion n.

Theorem multistepHeapExt : forall H H' x T t t' N tid,
                             Heap.heap_lookup x H = Some(sempty nil) -> unspecHeap H H' ->
                             multistep H' T t (OK H T t') -> 
                             multistep (Heap.replace x (sfull nil nil nil tid N) H') T t
                                       (OK (Heap.replace x (sfull nil nil nil tid N) H) T t'). 
Proof.
  intros. genDeps{x; N; tid}. remember (OK H T t'). induction H2; intros. 
  {inversion Heqc. auto. }
  {
Admitted. 


Theorem stepWF : forall H T t H' t', 
                   wellFormed H (tUnion T t) -> step H T t (OK H' T t') ->
                   wellFormed H' (tUnion T t'). 
Proof.
  intros. inversion H1; subst.   
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply moveToUnused in H4. replaceWithEmpty. 
    rewrite H in H4. apply multistepUnusedPool in H4. rewrite moveToUnused. replaceWithEmpty. 
    rewrite H5. rewrite multistepUnusedPool. assumption. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. invertHyp. inv H5. 
    {destruct tid. destruct p. erewrite unspecSingleton in *; eauto. Focus 2.
     erewrite unspecTwoActs. eauto. eapply multi_trans. eauto. econstructor. 
     eauto.  unfold tUnion. rewrite union_empty. eauto. auto. }
    {rewrite unspecPoolEmpty in H4; auto. eapply multi_trans. rewrite unspecPoolEmpty. 
     eassumption. destruct tid. destruct p. erewrite unspecTwoActs. eauto. econstructor. 
     auto. unfold tUnion. rewrite union_empty. eauto. auto. }
   }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply moveToUnused in H4. replaceWithEmpty. 
    rewrite H in H4. apply multistepUnusedPool in H4. rewrite moveToUnused. replaceWithEmpty. 
    rewrite H5. rewrite multistepUnusedPool. assumption. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. invertHyp. inv H5. 
    {destruct tid. destruct p. erewrite unspecSingleton in *; eauto. Focus 2.
     erewrite unspecTwoActs. eauto. eapply multi_trans. eauto. econstructor. 
     eauto.  unfold tUnion. rewrite union_empty. eauto. auto. }
    {rewrite unspecPoolEmpty in H4; auto. eapply multi_trans. rewrite unspecPoolEmpty. 
     eassumption. destruct tid. destruct p. erewrite unspecTwoActs. eauto. econstructor. 
     auto. unfold tUnion. rewrite union_empty. eauto. auto. }
   }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply moveToUnused in H4. replaceWithEmpty. 
    rewrite H in H4. apply multistepUnusedPool in H4. rewrite moveToUnused. replaceWithEmpty. 
    rewrite H5. rewrite multistepUnusedPool. assumption. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. invertHyp. inv H5. 
    {destruct tid. destruct p. erewrite unspecSingleton in *; eauto. Focus 2.
     erewrite unspecTwoActs. eauto. eapply multi_trans. eauto. econstructor. 
     eauto.  unfold tUnion. rewrite union_empty. eauto. auto. }
    {rewrite unspecPoolEmpty in H4; auto. eapply multi_trans. rewrite unspecPoolEmpty. 
     eassumption. destruct tid. destruct p. erewrite unspecTwoActs. eauto. econstructor. 
     auto. unfold tUnion. rewrite union_empty. eauto. auto. }
   }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply moveToUnused in H4. replaceWithEmpty. 
    rewrite H in H4. apply multistepUnusedPool in H4. rewrite moveToUnused. replaceWithEmpty. 
    rewrite H5. rewrite multistepUnusedPool. assumption. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. invertHyp. inv H5. 
    {destruct tid. destruct p. erewrite unspecSingleton in *; eauto. Focus 2.
     erewrite unspecTwoActs. eauto. eapply multi_trans. eauto. econstructor. 
     eauto.  unfold tUnion. rewrite union_empty. eauto. auto. }
    {rewrite unspecPoolEmpty in H4; auto. eapply multi_trans. rewrite unspecPoolEmpty. 
     eassumption. destruct tid. destruct p. erewrite unspecTwoActs. eauto. econstructor. 
     auto. unfold tUnion. rewrite union_empty. eauto. auto. }
   }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply moveToUnused in H4. replaceWithEmpty. 
    rewrite H in H4. apply multistepUnusedPool in H4. rewrite moveToUnused. replaceWithEmpty. 
    rewrite H5. rewrite multistepUnusedPool. assumption. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. invertHyp. inv H5. 
    {destruct tid. destruct p. erewrite unspecSingleton in *; eauto. Focus 2.
     erewrite unspecTwoActs. eauto. eapply multi_trans. eauto. econstructor. 
     eauto.  unfold tUnion. rewrite union_empty. eauto. auto. }
    {rewrite unspecPoolEmpty in H4; auto. eapply multi_trans. rewrite unspecPoolEmpty. 
     eassumption. destruct tid. destruct p. erewrite unspecTwoActs. eauto. econstructor. 
     auto. unfold tUnion. rewrite union_empty. eauto. auto. }
   }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply moveToUnused in H4. replaceWithEmpty. 
    rewrite H in H4. apply multistepUnusedPool in H4. rewrite moveToUnused. replaceWithEmpty. 
    rewrite H5. rewrite multistepUnusedPool. assumption. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. invertHyp. inv H5. 
    {destruct tid. destruct p. erewrite unspecSingleton in *; eauto. Focus 2.
     erewrite unspecTwoActs. eauto. eapply multi_trans. eauto. econstructor. 
     eauto.  unfold tUnion. rewrite union_empty. eauto. auto. }
    {rewrite unspecPoolEmpty in H4; auto. eapply multi_trans. rewrite unspecPoolEmpty. 
     eassumption. destruct tid. destruct p. erewrite unspecTwoActs. eauto. econstructor. 
     auto. unfold tUnion. rewrite union_empty. eauto. auto. }
   }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto.  
    erewrite unspecSingleton in H4; eauto. apply moveToUnused in H4. replaceWithEmpty. 
    rewrite H in H4. apply multistepUnusedPool in H4. rewrite moveToUnused. replaceWithEmpty. 
    rewrite H5. rewrite multistepUnusedPool. assumption. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. invertHyp. inv H5. 
    {destruct tid. destruct p. erewrite unspecSingleton in *; eauto. Focus 2.
     erewrite unspecTwoActs. eauto. eapply multi_trans. eauto. econstructor. 
     eauto.  unfold tUnion. rewrite union_empty. eauto. auto. }
    {rewrite unspecPoolEmpty in H4; auto. eapply multi_trans. rewrite unspecPoolEmpty. 
     eassumption. destruct tid. destruct p. erewrite unspecTwoActs. eauto. econstructor. 
     auto. unfold tUnion. rewrite union_empty. eauto. auto. }
   }
  }
  {inversion H0; subst. inversion H2; subst. econstructor; eauto. unfold tUnion. 
   rewrite union_empty. rewrite unspecUnionComm in H4. erewrite unspecSingleton in H4; eauto. 
   apply moveToUnused in H4. replaceWithEmpty. rewrite H in H4. rewrite multistepUnusedPool in H4.
   auto. }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    replace (unspecPoolAux(Singleton thread(Tid(1,1)((i,j)::tid),[specAct],[],M))) 
    with tEmptySet. Focus 2. symmetry. apply unspecPoolEmpty. eapply unspecCreatedSpec; auto. 
    unfold tUnion. rewrite union_empty. erewrite unspecSingleton. Focus 2. eapply unSpecFork. eauto. 
    apply decomposeEq in H7. subst. auto. erewrite unspecSingleton in H4; eauto. 
    eapply multi_trans. apply decomposeEq in H7. subst. eapply H4. 
    econstructor. auto. unfold tUnion. rewrite union_empty. apply decomposeEq in H7. subst.
    eauto. rewrite <- coupleUnion. constructor. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. unfold tCouple. 
    rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    eUnspec. inv H. inversion H5. 
    {erewrite unspecSingleton. Focus 2. rewrite unspecTwoActs'. eauto. rewrite unspecPoolEmpty. 
     unfold tUnion. rewrite union_empty. erewrite unspecSingleton in H4; eauto. eapply multi_trans. 
     eapply H4. econstructor. auto. unfold tUnion. rewrite union_empty. eauto. rewrite <- coupleUnion. 
     constructor. eauto. }
    {rewrite unspecPoolEmpty in H4; auto. rewrite unspecPoolEmpty; auto. rewrite unspecPoolEmpty. 
     unfold tUnion in *. repeat rewrite union_empty in *.  eapply multi_trans. eapply H4. 
     econstructor. auto. unfold tUnion. rewrite union_empty. eauto. rewrite <- coupleUnion. 
     constructor. eauto. eauto. rewrite unspecTwoActs'. eauto. }
   }
  }
  {inversion H0; subst. econstructor; eauto. eapply unspecHeapRead; eauto. destruct s1.  
   {inversion H3; subst. unfold tUnion in *. rewrite unspecUnionComm in *.
    erewrite unspecSingleton. Focus 2. eapply unspecRead; eauto. apply decomposeEq in H4; subst. 
    auto. erewrite unspecSingleton in H7; auto. eapply multi_trans. eapply H7. econstructor. auto. 
    unfold tUnion. rewrite union_empty. eauto. constructor. }
   {inversion H3; subst. eUnspec. inv H2. inv H8. 
    {unfold tUnion in *. rewrite unspecUnionComm in *. erewrite unspecSingleton. 
     Focus 2. simpl. rewrite unspecTwoActs'. eauto. erewrite unspecSingleton in H7; eauto. eapply multi_trans. 
     eapply H7. econstructor. auto. unfold tUnion. rewrite union_empty. eauto. constructor. }
    {rewrite unspecUnionComm in *. erewrite unspecPoolEmpty in H7; eauto. 
     erewrite unspecPoolEmpty. unfold tUnion in*. rewrite union_empty in *. 
     eapply multi_trans. eapply H7. econstructor. auto. unfold tUnion. rewrite union_empty. 
     eauto. constructor. simpl. erewrite unspecTwoActs'. eauto. }
   }
  }
  {inversion H0; subst. inversion H3; subst. destruct s1.  
   {econstructor; eauto. eapply unspecHeapCommWrite; eauto. eapply multistepHeapExt; eauto.
    eapply multi_trans. eauto. econstructor. 
    


admit. }
   {eUnspec. inv H2. inv H8. 
    {econstructor; eauto. eapply unspecHeapSpecWrite; eauto. unfold tUnion in *. 
     rewrite unspecUnionComm in *. erewrite unspecSingleton. Focus 2. simpl. rewrite unspecTwoActs'. 
     eauto. erewrite unspecSingleton in H7; eauto. eapply multi_trans. 
     eapply H7. econstructor. auto. unfold tUnion. rewrite union_empty. eauto. constructor. }
    {econstructor; eauto. eapply unspecHeapSpecWrite; eauto. rewrite unspecUnionComm in *. 
     erewrite unspecPoolEmpty in H7; eauto. erewrite unspecPoolEmpty. unfold tUnion in*. 
     rewrite union_empty in *. eapply multi_trans. eapply H7. econstructor. auto. unfold tUnion. 
     rewrite union_empty. eauto. constructor. simpl. erewrite unspecTwoActs'. eauto. }
   }
  }
  {(*Overwrite*) admit. }
  {admit. }
  {destruct s1.  
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    erewrite unspecSingleton. Focus 2. eapply unSpecSpecret. eauto. apply decomposeEq in H4. 
    subst. auto. erewrite unspecPoolEmpty; eauto. unfold tUnion. rewrite union_empty.
    erewrite unspecSingleton in H5; eauto. eapply multi_trans. apply decomposeEq in H4; subst. 
    eapply H5. econstructor. auto. unfold tUnion. rewrite union_empty. apply decomposeEq in H4. subst.
    eauto. rewrite <- coupleUnion. constructor. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. unfold tCouple. 
    rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    eUnspec. inv H. inv H6. 
    {erewrite unspecSingleton. Focus 2. simpl. rewrite unspecTwoActs'. eauto. rewrite unspecPoolEmpty. 
     unfold tUnion. rewrite union_empty. erewrite unspecSingleton in H5; eauto. eapply multi_trans. 
     eapply H5. econstructor. auto. unfold tUnion. rewrite union_empty. eauto. rewrite <- coupleUnion. 
     constructor. eauto. }
    {rewrite unspecPoolEmpty in H5; auto. rewrite unspecPoolEmpty; auto. rewrite unspecPoolEmpty. 
     unfold tUnion in *. repeat rewrite union_empty in *.  eapply multi_trans. eapply H5. 
     econstructor. auto. unfold tUnion. rewrite union_empty. eauto. rewrite <- coupleUnion. 
     constructor. eauto. eauto. simpl. rewrite unspecTwoActs'. eauto. }
   }
  }
  {inversion H0; subst. inversion H2; subst. econstructor; eauto. destruct s1'. 
   {simpl in *. unfold tUnion in *. unfold tCouple in *. rewrite coupleUnion in H5. 
    repeat rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H5; eauto. rewrite unspecPoolEmpty in H5; eauto. admit. }
   {admit. }
  }
  {admit. }
  {inversion H0; subst. inversion H2; subst. econstructor; eauto.
   rewrite unspecUnionComm in *. erewrite unspecSingleton in *; auto. apply moveToUnused. 
   apply moveToUnused in H4. replaceWithEmpty. rewrite H in H4. apply multistepUnusedPool in H4. 
   replaceWithEmpty. rewrite H5. apply multistepUnusedPool. auto. }
  {inversion H0; subst. inversion H2; subst. econstructor; eauto. destruct s1'. 
   {eUnspec. unfold tUnion in *. rewrite unspecUnionComm in *. simpl in *. inv H. 
    inv H5. Focus 2. inversion H; subst. destruct s1'; inversion H6. invertListNeq. 
    erewrite unspecSingleton in H4; eauto. inversion H; subst; 
                                           try(destruct s1'; inversion H12; invertListNeq). 
    destruct s1'; inversion H12; try invertListNeq. subst. simpl in H12. 









