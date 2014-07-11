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
Require Import classifiedStep. 

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
       assert(n:(tSingleton t) = tUnion (tSingleton t) tEmptySet) by (unfold tUnion; rewrite union_empty_r; auto)
      | |-multistep ?H (tSingleton ?t) ?T ?x => 
       let n := fresh in
       assert(n:(tSingleton t) = tUnion (tSingleton t) tEmptySet) by (unfold tUnion; rewrite union_empty_r; auto)  
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

Theorem unspecHeapLookupFull : forall H H' x t N ds xs tid M,
                            unspecHeap H H' -> heap_lookup x H = Some (sfull nil ds xs tid M) ->
                            unspecHeap (replace x (sfull nil nil nil t N) H)
                                       (replace x (sfull nil nil nil t N) H'). 
Proof.
  induction H; intros. 
  {simpl in *. inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i)eqn:eq. 
   {inv H1. inv H0. simpl. rewrite eq. eauto. simpl. rewrite eq. eauto. }
   {inv H0; eauto; try solve[simpl; rewrite eq; eauto]. }
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


Theorem lookupNeq : forall (T:Type) x H x' (v : T) (v' : T),
                      heap_lookup x H = Some v -> x <> x' ->
                      heap_lookup x (replace x' v' H) = Some v.
Proof.
  induction H; intros. 
  {simpl in *. inv H. }
  {simpl in *. destruct a. destruct (beq_nat x' i) eqn:eq1. 
   {destruct (beq_nat x i) eqn:eq2.
    {apply beq_nat_true in eq2. apply beq_nat_true in eq1. subst. exfalso. apply H1. auto. }
    {simpl. apply beq_nat_false_iff in H1. rewrite H1. auto. }
   }
   {destruct (beq_nat x i) eqn :eq2. 
    {simpl. rewrite eq2. auto. }
    {simpl. rewrite eq2. auto. }
   }
  }
Qed. 

Theorem lookupReplaceSwitch : forall T x x' (v v':T) H,
                                x<>x' -> replace x v (replace x' v' H) = replace x' v' (replace x v H).
Proof.
  induction H. 
  {auto. }
  {intros. simpl. destruct a. destruct(beq_nat x' i) eqn:eq1. 
   {destruct(beq_nat x i) eqn:eq2. 
    {apply beq_nat_true in eq1. apply beq_nat_true in eq2. subst. exfalso; apply H0; auto. }
    {simpl. apply beq_nat_false_iff in H0. rewrite H0. rewrite eq1. auto. }
   }
   {destruct (beq_nat x i) eqn:eq2. 
    {simpl. rewrite eq2. apply beq_nat_false_iff in H0. rewrite beq_nat_sym in H0. rewrite H0. 
     auto. }
    {simpl. rewrite eq1. rewrite eq2. rewrite IHlist. auto. assumption. }
   }
  }
Qed. 

(*
Theorem stepHeapExt : forall H H' x T t t' N tid,
                             heap_lookup x H' = Some(sempty nil) -> unspecHeap H H' ->
                             step H' T t (OK H T t') -> 
                             step (replace x (sfull nil nil nil tid N) H') T t
                                       (OK (replace x (sfull nil nil nil tid N) H) T t'). 
Proof.
  intros. inversion H2; subst; eauto. 
  {assert(x <> x0). intros c. subst. eapply lookupDeterministic in H8; eauto. inv H8. 
   eapply Get. eauto. eapply lookupNeq. eauto. intros c. symmetry in c. contradiction. 
   apply lookupReplaceSwitch. auto. }
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. 

Admitted. 

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
*)

Theorem listAlign2 : forall (T:Type) b a, exists (c : list T) d, a::b = c++[d]. 
Proof.
  induction b; intros. 
  {eauto. }
  {specialize (IHb a). invertHyp. rewrite H0. eauto. }
Qed. 

Ltac alignTac a b := assert(exists c d, a::b = c++[d]) by apply listAlign2; invertHyp.

Theorem unspecSpecSame : forall tid a b s2 M M' t, 
                          unspecThread(tid, a::b, s2, M) t ->
                          unspecThread(tid, a::b, s2, M') t.
Proof.
  intros. alignTac a b. rewrite H0 in *. 
  destruct x0; inv H; try solve[invertListNeq]; 
  match goal with
      |H:?x++[?a]=?y++[?b] |- _ => apply lastElementEq in H; inv H; unspecThreadTac; auto
  end. 
Qed. 

Ltac eUnspec :=
  match goal with
    | |-spec_multistep ?H ?t ?H' (tUnion ?T' (tSingleton ?t')) =>
        assert(exists t'', unspecThread t' t'') by apply unspecThreadTotal; invertHyp
  end. 

Ltac rewriteEmpty xs := 
      match xs with
          |HNil => unfold tUnion; try rewrite union_empty_l; try rewrite union_empty_r
          |HCons ?x ?xs' => unfold tUnion in x; try rewrite union_empty_l in x; 
                          try rewrite union_empty_r in x; rewriteEmpty xs'
      end. 

Theorem rollbackWF : forall H H' T TR TR' tid s2 M M' tidR acts,
                       wellFormed H (tUnion T (tAdd TR (tid, nil, s2, M))) ->
                       rollback tidR acts H TR H' TR' ->
                       wellFormed H' (tUnion T (tAdd TR' (tid, nil, s2, M'))). 
Admitted. 

Require Import Coq.Sets.Powerset_facts. 
Theorem spec_multi_unsued : forall H T1 T2 T1' H', 
                              spec_multistep H (tUnion T1 T2) H' (tUnion T1' T2) <->
                              spec_multistep H T1 H' T1'.
Admitted. 

Theorem spec_multi_trans : forall H H' H'' T T' T'',
                        spec_multistep H T H' T' ->
                        spec_multistep H' T' H'' T'' ->
                        spec_multistep H T H'' T''.  
Proof.
  intros. genDeps {H''; T''}. induction H0; intros.  
  {auto. }
  {apply IHspec_multistep in H1. econstructor. eauto. auto. }
Qed. 
   
Hint Constructors spec_step. 

Theorem stepWF : forall H T t H' t', 
                   wellFormed H (tUnion T t) -> step H T t (OK H' T t') ->
                   wellFormed H' (tUnion T t'). 
Proof.
  intros. inversion H1; subst.   
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply spec_multi_unsued in H4. 
    rewrite spec_multi_unsued. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SBetaRed; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply spec_multi_unsued in H4. 
    rewrite spec_multi_unsued. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SProjL; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply spec_multi_unsued in H4. 
    rewrite spec_multi_unsued. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SProjR; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply spec_multi_unsued in H4. 
    rewrite spec_multi_unsued. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SBind; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply spec_multi_unsued in H4. 
    rewrite spec_multi_unsued. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SBindRaise; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply spec_multi_unsued in H4. 
    rewrite spec_multi_unsued. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SHandle; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. apply spec_multi_unsued in H4. 
    rewrite spec_multi_unsued. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SHandleRet; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {inversion H0; subst. inversion H2; subst. econstructor; eauto. unfold tUnion. 
   rewrite union_empty_r. rewrite unspecUnionComm in H4. erewrite unspecSingleton in H4; eauto. 
   apply spec_multi_unsued in H4. auto. }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    erewrite unspecSingleton;try unspecThreadTac; auto. erewrite unspecSingleton; eauto. 
    unfold tUnion. rewrite union_empty_r. eapply spec_multi_trans. copy d. apply decomposeEq in H. subst. 
    erewrite unspecSingleton in H4; eauto. copy d. apply decomposeEq in H. rewrite <- H.  
    econstructor. auto. unfold tUnion. eapply SFork. eassumption. unfold tCouple. 
    rewrite coupleUnion. constructor. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    assert(exists t', unspecThread (tid, fAct t0 E M d :: a :: s1, s2, fill E (ret unit)) t'). 
    apply unspecThreadTotal. invertHyp. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton; eauto. unfold tUnion. rewrite union_empty_r. 
    erewrite unspecSingleton in H4; eauto. eapply multi_trans. eassumption. 
    econstructor. eauto. unfold tUnion. rewrite union_empty_r. eassumption. 
    unfold tCouple. rewrite coupleUnion. constructor. rewrite <- unspecTwoActs'. eauto. }
  }
  {inversion H0; subst. econstructor; eauto. eapply unspecHeapRead; eauto. destruct s1.  
   {inversion H3; subst. unfold tUnion in *. rewrite unspecUnionComm in *.
    erewrite unspecSingleton; try unspecThreadTac; eauto. copy d. apply decomposeEq in H2; subst. 
    erewrite unspecSingleton in H5; auto. eapply multi_trans. eassumption. econstructor. auto. 
    unfold tUnion. rewrite union_empty_r. eauto. constructor. }
   {inversion H3; subst. rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H5. Focus 2. rewrite <- unspecTwoActs'. eauto. eapply multi_trans. 
    eassumption. econstructor. auto. unfold tUnion. rewrite union_empty_r. eauto. 
    constructor. }
  }
  {inversion H0; subst. econstructor; eauto. eapply unspecHeapSpecWrite; eauto. destruct s1.  
   {inversion H3; subst. unfold tUnion in *. rewrite unspecUnionComm in *.
    erewrite unspecSingleton; try unspecThreadTac; eauto. copy d. apply decomposeEq in H2; subst. 
    erewrite unspecSingleton in H6; auto. eapply multi_trans. eassumption. econstructor. auto. 
    unfold tUnion. rewrite union_empty_r. eauto. constructor. }
   {inversion H3; subst. rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
   erewrite unspecSingleton in H6. Focus 2. rewrite <- unspecTwoActs'. eauto. eapply multi_trans. 
    eassumption. econstructor. auto. unfold tUnion. rewrite union_empty_r. eauto. 
    constructor. }
  }
  {inversion H0; subst. inversion H3; subst. econstructor; eauto. eapply rollbackIdempotent in H8; eauto. 
   invertHyp. eapply unspecHeapLookupFull; eauto. eauto. eassumption. ; eauto. 
   




   (*Overwrite*) admit. }
  {admit. }
  {destruct s1.  
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    erewrite unspecSingleton. Focus 2. eapply unSpecSpecret. eauto. apply decomposeEq in H4. 
    subst. auto. erewrite unspecPoolEmpty; eauto. unfold tUnion. rewrite union_empty_r.
    erewrite unspecSingleton in H5; eauto. eapply multi_trans. apply decomposeEq in H4; subst. 
    eapply H5. econstructor. auto. unfold tUnion. rewrite union_empty_r. apply decomposeEq in H4. subst.
    eauto. rewrite <- coupleUnion. constructor. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. unfold tCouple. 
    rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    eUnspec. inv H. inv H6. 
    {erewrite unspecSingleton. Focus 2. simpl. rewrite unspecTwoActs'. eauto. rewrite unspecPoolEmpty. 
     unfold tUnion. rewrite union_empty_r. erewrite unspecSingleton in H5; eauto. eapply multi_trans. 
     eapply H5. econstructor. auto. unfold tUnion. rewrite union_empty_r. eauto. rewrite <- coupleUnion. 
     constructor. eauto. }
    {rewrite unspecPoolEmpty in H5; auto. rewrite unspecPoolEmpty; auto. rewrite unspecPoolEmpty. 
     unfold tUnion in *. repeat rewrite union_empty_r in *.  eapply multi_trans. eapply H5. 
     econstructor. auto. unfold tUnion. rewrite union_empty_r. eauto. rewrite <- coupleUnion. 
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









