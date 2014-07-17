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
Require Import Coq.Sets.Powerset_facts.

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

Theorem raw_unspecHeapSpecWrite : forall H x s s1 M a c d TID tid' M',
                            raw_heap_lookup x H = Some (sfull nil s (c::d) tid' M')->
                            raw_unspecHeap (raw_replace x (sfull nil (Empty_set tid) (a::s1) TID M) H) = 
                            raw_unspecHeap H.
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. apply beq_nat_true in eq. subst; auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed. 

Theorem unspecHeapSpecWrite : forall H x s s1 M a c d TID tid' M',
                            heap_lookup x H = Some (sfull nil s (c::d) tid' M')->
                            unspecHeap (replace x (sfull nil (Empty_set tid) (a::s1) TID M) H) =
                            unspecHeap H.
Proof.
  intros. destruct H. apply rawHeapsEq. eapply raw_unspecHeapSpecWrite; eauto.
Qed. 

Theorem raw_lookupUnspecFull : forall H x ds t N, 
                             raw_heap_lookup x H = Some(sfull nil ds nil t N) ->
                             raw_heap_lookup x (raw_unspecHeap H) = Some(sfull nil (Empty_set tid) nil t N).
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct a; eauto. simpl. rewrite eq. eauto. destruct a; eauto.
    destruct a0. simpl. rewrite eq. eauto. simpl. rewrite eq; eauto. }
  }
Qed. 

Theorem lookupUnspecFull : forall H x ds t N, 
                             heap_lookup x H = Some(sfull nil ds nil t N) ->
                             heap_lookup x (unspecHeap H) = Some(sfull nil (Empty_set tid) nil t N).
Proof.
  intros. destruct H. simpl. eapply raw_lookupUnspecFull; eauto.
Qed. 

(*lookupNeq --> lookupReplaceNeq in Heap.v*)

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
    | H:spec_multistep ?H ?t ?H' (tUnion ?T' (tSingleton ?t')) |- _ =>
        assert(exists t'', unspecThread t' t'') by apply unspecThreadTotal; invertHyp
  end. 

Ltac rewriteEmpty xs := 
      match xs with
          |HNil => unfold tUnion; try rewrite union_empty_l; try rewrite union_empty_r
          |HCons ?x ?xs' => unfold tUnion in x; try rewrite union_empty_l in x; 
                          try rewrite union_empty_r in x; rewriteEmpty xs'
      end. 

Theorem rollbackWF : forall H H' T TR TR' tidR acts,
                       wellFormed H (tUnion T TR) ->
                       rollback tidR acts H TR H' TR' ->
                       wellFormed H' (tUnion T TR'). 
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


Theorem UnionEqTID : forall T T' tid s1 s2 M s1' s2' M',
                       tUnion T (tSingleton(tid,s1,s2,M)) = tUnion T' (tSingleton(tid,s1',s2',M')) ->
                       T = T' /\ s1 = s1' /\ s2 = s2' /\ M = M'. 
Proof. 
  intros. unfoldSetEq H. assert(tIn (tUnion T (tSingleton(tid,s1,s2,M)))(tid,s1,s2,M)). 
  apply Union_intror. constructor. copy H.  apply H0 in H. inversion H.  
  {assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1,s2,M)). 
   econstructor. econstructor. eauto. auto. 
   assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1',s2',M')). 
   econstructor. apply Union_intror. constructor. auto. eapply uniqueThreadPool in H5; eauto. 
   inv H5. repeat constructor; auto. eqSets. 
   {assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H5. apply H0 in H5. 
    inversion H5; subst. auto. inv H8. exfalso. eapply uniqueTP; eauto. constructor. }
   {assert(tIn (tUnion T' (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H5. 
    apply H1 in H5. inversion H5; subst. auto. inv H8. exfalso. eapply uniqueTP; eauto. 
    constructor. }
  }
  {subst. inv H3. repeat constructor; auto. eqSets. 
   {assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H4. apply H0 in H4. 
    inversion H4; subst. auto. inv H6. exfalso. eapply uniqueTP; eauto. constructor. }
   {assert(tIn (tUnion T' (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H4. 
    apply H1 in H4. inversion H4; subst. auto. inv H6. exfalso. eapply uniqueTP; eauto. 
    constructor. }
  }
Qed. 

Ltac foldTac := fold Add in *; fold tAdd in *; fold tUnion in *; fold tSingleton in *; fold tCouple in *.



Theorem stepWF : forall H T t H' t', 
                   wellFormed H (tUnion T t) -> step H T t (OK H' T t') ->
                   wellFormed H' (tUnion T t'). 
Proof.
  intros. inversion H1; subst.    
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. apply spec_multi_unused in H3. 
    rewrite spec_multi_unused. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SBetaRed; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. apply spec_multi_unused in H3. 
    rewrite spec_multi_unused. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SProjL; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. apply spec_multi_unused in H3. 
    rewrite spec_multi_unused. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SProjR; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. apply spec_multi_unused in H3. 
    rewrite spec_multi_unused. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SBind; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. apply spec_multi_unused in H3. 
    rewrite spec_multi_unused. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SBindRaise; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. apply spec_multi_unused in H3. 
    rewrite spec_multi_unused. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SHandle; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. apply spec_multi_unused in H3. 
    rewrite spec_multi_unused. auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SHandleRet; eauto. constructor. eapply unspecTwoActs. eauto. }
  }
  {destruct s1. 
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    erewrite unspecSingleton;try unspecThreadTac; auto. erewrite unspecSingleton; eauto. 
    unfold tUnion. rewrite union_empty_r. eapply spec_multi_trans. copy d. apply decomposeEq in H. subst. 
    erewrite unspecSingleton in H3; eauto. copy d. apply decomposeEq in H. rewrite <- H.  
    econstructor. auto. unfold tUnion. eapply SFork. rewrite <- coupleUnion. unfoldTac. 
    constructor. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    assert(exists t', unspecThread (tid, fAct t0 E M d :: a :: s1, s2, fill E (ret unit)) t'). 
    apply unspecThreadTotal. invertHyp. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton; eauto. unfold tUnion. rewrite union_empty_r. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. 
    econstructor. eapply SFork. rewrite <- coupleUnion. constructor. 
    rewrite <-unspecTwoActs'; eauto. }
  }
  {inversion H0; subst. econstructor; eauto. erewrite unspecHeapRBRead; eauto. destruct s1.  
   {inversion H3; subst. unfold tUnion in *. rewrite unspecUnionComm in *.
    erewrite unspecSingleton; try unspecThreadTac; eauto. copy d. apply decomposeEq in H2; subst. 
    erewrite unspecSingleton in H4; auto. eapply spec_multi_trans. eassumption. econstructor. 
    eapply SGet; eauto. simpl. constructor. }
   {inversion H3; subst. rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4. Focus 2. rewrite <- unspecTwoActs'. eauto. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SGet; eauto. constructor. }
  }
  {inversion H0; subst. econstructor; eauto. erewrite unspecHeapAddWrite; eauto. destruct s1.  
   {inversion H3; subst. unfold tUnion in *. rewrite unspecUnionComm in *.
    erewrite unspecSingleton; try unspecThreadTac; eauto. copy d. apply decomposeEq in H2; subst. 
    erewrite unspecSingleton in H5; auto. eapply spec_multi_trans. eassumption. econstructor. 
    eapply SPut; eauto. constructor. }
   {inversion H3; subst. rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H5. Focus 2. rewrite <- unspecTwoActs'. eauto. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SPut; eauto. constructor. 
   }
  }   
  {inversion H0; subst. inversion H3; subst. copy H5. eapply rollbackIdempotent in H5; eauto.
   apply rollbackWF with(T:=T)in H2. econstructor; eauto. inv H5. erewrite unspecHeapAddWrite; eauto. 
   unfoldTac. repeat rewrite unspecUnionComm in *. 
   erewrite unspecSingleton. Focus 2. eapply unspecWrite; eauto. erewrite unspecSingleton in H6; eauto.
   admit. admit.  }
  {inversion H0; subst. inversion H3; subst. econstructor; eauto. erewrite unspecHeapExtend; eauto. 
   destruct s1. 
   {unfoldTac. rewrite unspecUnionComm in *. erewrite unspecSingleton. Focus 2.
    eapply unspecCreate; auto. erewrite unspecSingleton in H4; eauto. eapply spec_multi_trans. 
    copy d. apply decomposeEq in H2. subst. eassumption. copy d. apply decomposeEq in H2. subst. 
    econstructor. eapply SNew; eauto. constructor. }
   {rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto.
    erewrite unspecSingleton in H4. Focus 2. rewrite <- unspecTwoActs'. eauto. eapply spec_multi_trans. 
    eassumption. copy d. apply decomposeEq in H2. subst. econstructor. eapply SNew; eauto. constructor. }
  }
  {destruct s1.  
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    erewrite unspecSingleton. Focus 2. eapply unSpecSpecret. eauto. copy d. apply decomposeEq in H. 
    subst. auto. erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption.  
    econstructor. eapply SSpec; eauto. unfold tUnion. rewrite <- coupleUnion. constructor. 
    eapply unspecCreatedSpec with (s1':=[specAct]); auto. }
   {inversion H0; subst. inversion H2; subst. econstructor; eauto. unfoldTac. rewrite coupleUnion. 
    repeat rewrite unspecUnionComm in *. foldTac. eUnspec. erewrite unspecSingleton in H3; eauto. 
    repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SSpec. rewrite <- coupleUnion. constructor.
    eapply unspecCreatedSpec with (s1':=[specAct]); auto. rewrite unspecTwoActs'. eauto. }
  }
  {inversion H0; subst. inversion H2; subst. econstructor; eauto. destruct s1'. 
   {simpl in *. unfoldTac.  rewrite coupleUnion in H3. 
    repeat rewrite unspecUnionComm in *. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. erewrite unspecSingleton in H3; eauto. unfoldTac. 
    rewrite union_empty_r in H3.  admit. }
   {admit. }
  }   
  {copy H13. unfoldTac. rewrite <- Union_associative. rewrite wfFrame. Focus 2. 
   unfold commitPool. intros. inv H3. auto. rewrite <- Union_associative in H0. 
   rewrite wfFrame in H0. Focus 2. unfold commitPool; intros. inv H3. auto.
   eapply rollbackWF; eauto. }
  {inversion H0; subst. inversion H2; subst. econstructor; eauto. rewrite unspecUnionComm in *. 
   erewrite unspecSingleton; eauto. erewrite unspecSingleton in H3; eauto. 
   rewrite spec_multi_unused in H3. rewrite spec_multi_unused. auto. }
  {inversion H0; subst. inversion H3; subst. econstructor; eauto. erewrite unspecHeapRBRead; eauto. 
   rewrite unspecUnionComm in *. admit. (*insert read ind here*) }
  {admit. }
  {admit. }
  {admit. }
  {inv H0. inv H2. econstructor; eauto. unfoldTac. rewrite coupleUnion in *.
   repeat rewrite unspecUnionComm in *. erewrite unspecSingleton in H3. Focus 2. 
   eapply unSpecFork; auto. erewrite unspecSingleton in H3. Focus 2. 
   eapply unspecCreatedSpec; auto. unfoldTac. rewrite union_empty_r in H3. 
   rewrite <- coupleUnion in H3. apply forkInd' in H3. unfoldTac. rewrite coupleUnion in H3. 
   rewrite unspecUnionComm in H3. eauto. }

                    

a;lkhdj



