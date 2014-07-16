Require Import Spec.         
Require Import AST.   
Require Import SfLib.  
Require Import sets. 
Require Import SpecLib. 
Require Import Coq.Sets.Powerset_facts. 
Require Import Heap.  
Require Import classifiedStep. 
Require Import hetList. 
Require Import Coq.Sets.Ensembles. 

(*------------------------------------Unspec Definitions----------------------------*)
Fixpoint raw_unspecHeap (H : rawHeap ivar_state) :=
  match H with
      |(i, sempty (hd::tl))::H' => raw_unspecHeap H'
      |(i, sempty nil)::H' => (i, sempty nil)::raw_unspecHeap H'
      |(i, sfull (hd::tl) _ _ _ _)::H' => raw_unspecHeap H'
      |(i, sfull nil _ (hd::tl) _ _) :: H' => (i, sempty nil)::raw_unspecHeap H'
      |(i, sfull nil ds nil t M)::H' => (i, sfull nil (Empty_set tid) nil t M)::raw_unspecHeap H'
      |nil => nil
  end. 

Hint Constructors monotonic. 

Theorem unspecMonotonic : forall h u,
                            monotonic u ivar_state h ->
                            monotonic u ivar_state (raw_unspecHeap h). 
Proof.
  induction h; intros; auto. destruct a. 
  {destruct i0; auto. 
   {destruct a. simpl. inv H. constructor. auto. eauto. simpl. inv H. 
    eapply monotonicLowerUB; eauto. }
   {destruct a. 
    {simpl. destruct a0. 
     {inv H. constructor; auto. }
     {inv H. constructor; auto. }
    }
    {destruct a0. 
     {simpl. inv H. eapply monotonicLowerUB; eauto. }
     {simpl. inv H. eapply monotonicLowerUB; eauto. }
    }
   }
  }
Qed. 

Definition unspecHeap H := 
  match H with
      heap_ h' prf => heap_ (ivar_state) (raw_unspecHeap h') (unspecMonotonic h' None prf)
  end. 

Inductive unspecThread : thread -> Ensemble thread -> Prop :=
|unspecCommit : forall tid s2 M,
                  unspecThread (tid, nil, s2, M) (tSingleton(tid, nil, s2, M))
|unspecRead : forall tid s1 s1' s2 M i t E (d:decompose t E (get (fvar i))),
             s1 = s1' ++ [rAct i t E d] -> 
             unspecThread (tid, s1, s2, M) (tSingleton(tid, nil, s2, t))
|unspecWrite : forall tid s1 s1' s2 M M' i c t (d:decompose t c (put (fvar i) M')),
       s1 = s1' ++ [wAct i t c M' d] ->
       unspecThread (tid, s1, s2, M) (tSingleton(tid, nil, s2, t))
|unspecCreate : forall tid s1 s1' s2 M i c t (d:decompose t c new),
                  s1 = s1' ++ [nAct t c d i] ->
                  unspecThread (tid, s1, s2, M) (tSingleton(tid, nil, s2, t))
|unSpecFork : forall c tid s1 s1' s2 M M' t (d:decompose t c (fork M')),
                s1 = s1' ++ [fAct t c M' d] ->
                unspecThread (tid, s1, s2, M) (tSingleton(tid, nil, s2, t))
|unSpecSpecret : forall t c M M' N tid s1 s1' s2 (d:decompose t c (spec M' N)), 
                   s1 = s1' ++ [srAct t c M' N d] ->
                   unspecThread(tid, s1, s2, M) (tSingleton(tid, nil, s2, t))
|unspecCreatedSpec : forall s1 s1' s2 M tid,
                       s1 = s1' ++ [specAct] -> unspecThread (tid, s1, s2, M) tEmptySet
. 

Hint Constructors unspecThread. 

Inductive unspecPoolAux (T:pool) : pool :=
|unspecAux : forall t t' s1 s2 M, thread_lookup T t (t, s1, s2, M) ->
                                  unspecThread (t, s1, s2, M) t' -> Included thread t' (unspecPoolAux T).

Inductive unspecPool : pool -> pool -> Prop :=
|unspecP : forall T, unspecPool T (unspecPoolAux T).

Hint Constructors unspecPool. 

Inductive wellFormed : sHeap -> pool -> Prop :=
|wf : forall H T T', unspecPool T T' ->  spec_multistep (unspecHeap H) T' H T ->
                     wellFormed H T
.

Definition commitPool (T:pool) : Prop := forall tid s1 s2 M, tIn T (tid, s1, s2, M) -> s1 = nil. 

Inductive actionTerm : action -> trm -> Prop :=
|basicRead : forall x t E d, actionTerm (rAct x t E d) t
|basicWrite : forall x t E M d, actionTerm (wAct x t E M d) t
|basicNew : forall x t E d, actionTerm (nAct t E d x) t
|basicFork : forall t E M d, actionTerm (fAct t E M d) t
|basicSR : forall t E M N d, actionTerm (srAct t E M N d) t. 

Hint Resolve app_comm_cons app_nil_l. 

Ltac unspecThreadTac :=
  match goal with
    | |-unspecThread(?t, [], ?s, ?m) ?z => eapply unspecCommit
    | |-unspecThread(?t, ?x++[rAct ?a ?b ?c ?d], ?s, ?m) ?z => eapply unspecRead
    | |-unspecThread(?t, ?x++[wAct ?a ?b ?c ?d ?e], ?s, ?m) ?z => eapply unspecWrite
    | |-unspecThread(?t, ?x++[nAct ?a ?b ?c ?d], ?s, ?m) ?z => eapply unspecCreate
    | |-unspecThread(?t, ?x++[fAct ?a ?b ?c ?d], ?s, ?m) ?z => eapply unSpecFork
    | |-unspecThread(?t, ?x++[srAct ?a ?b ?c ?d ?e], ?s, ?m) ?z => eapply unSpecSpecret
    | |-unspecThread(?t, ?x++[specAct], ?s, ?m) ?z => eapply unspecCreatedSpec
    | |-unspecThread(?t, [rAct ?a ?b ?c ?d], ?s, ?m) ?z => eapply unspecRead
    | |-unspecThread(?t, [wAct ?a ?b ?c ?d ?e], ?s, ?m) ?z => eapply unspecWrite
    | |-unspecThread(?t, [nAct ?a ?b ?c ?d], ?s, ?m) ?z => eapply unspecCreate
    | |-unspecThread(?t, [fAct ?a ?b ?c ?d], ?s, ?m) ?z => eapply unSpecFork
    | |-unspecThread(?t, [srAct ?a ?b ?c ?d ?e], ?s, ?m) ?z => eapply unSpecSpecret
    | |-unspecThread(?t, [specAct], ?s, ?m) ?z => eapply unspecCreatedSpec
  end. 

(*---------------------------------Theorems---------------------------------------------*)

Theorem commitPoolUnspecUnchanged : forall T, commitPool T -> T = unspecPoolAux T. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split.  
  {intros. destruct x. destruct p. destruct p. 
   econstructor. econstructor. eassumption. reflexivity. unfold commitPool in H.  
   apply H in H0. subst. eauto. constructor. }
  {intros. inv H0. inv H1. inv H4. unfold commitPool in H. copy H0. apply H in H0. subst. 
   inv H2; try invertListNeq. inv H3. auto. }
Qed. 

Theorem unspecUnionComm : forall T1 T2, unspecPoolAux (tUnion T1 T2) = 
                                        tUnion (unspecPoolAux T1) (unspecPoolAux T2).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inv H. inv H0. inv H3. inv H. 
   {econstructor. econstructor; eauto. }
   {apply Union_intror. econstructor; eauto. }
  }
  {inv H. 
   {inv H0. inv H. inv H3. econstructor; eauto. econstructor. econstructor. 
    eauto. eauto. }
   {inv H0. inv H. inv H3. econstructor; eauto. econstructor. apply Union_intror. 
    eauto. eauto. }
  }
Qed. 


Theorem LookupSame :
  forall P P', unspecPool P P' ->
               forall tid T, thread_lookup P' tid T ->
                             exists T', thread_lookup P tid T' /\ unspecThread T' (tSingleton T).
Proof.
  intros. inversion H; subst. inv H0. inv H1. inv H0. inv H4. inv H2; try solve[inv H3; eauto]. 
Qed. 

Theorem raw_unspecHeapRBNew : forall H x S A,
                            raw_heap_lookup x H = Some(sempty (S::A)) ->
                            raw_unspecHeap H = raw_unspecHeap (raw_remove H x). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. auto. }
   {erewrite IHlist; eauto. destruct i0; simpl; auto. }
  }
Qed. 

Theorem unspecHeapRBNew : forall H x S A,
                            heap_lookup x H = Some(sempty (S::A)) ->
                            unspecHeap H = unspecHeap (remove H x). 
Proof.
  intros. destruct H. simpl in *. eapply raw_unspecHeapRBNew in H0. 
  eapply rawHeapsEq; auto. 
Qed. 

Theorem raw_unspecHeapRBWrite : forall H x sc S A TID N,
                                  raw_heap_lookup x H = Some(sfull sc (Empty_set tid) (S::A) TID N) ->
                                  raw_unspecHeap (raw_replace x (sempty sc) H) = (raw_unspecHeap H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. destruct sc. simpl. apply beq_nat_true in eq. subst. auto. auto. }
   {simpl in *. erewrite IHlist; eauto. }
  }
Qed. 

Theorem unspecHeapRBWrite : forall H x sc S A TID N,
                              heap_lookup x H = Some(sfull sc (Empty_set tid) (S::A) TID N) ->
                              unspecHeap (replace x (sempty sc) H) = (unspecHeap H). 
Proof.
  intros. destruct H. simpl in *. eapply raw_unspecHeapRBWrite in H0. 
  eapply rawHeapsEq. auto. 
Qed. 

  
Theorem raw_unspecHeapRBRead : forall H x sc ds S ds' t N,
                   raw_heap_lookup x H = Some (sfull sc ds S t N) ->
                   raw_unspecHeap (raw_replace x (sfull sc ds' S t N) H) = raw_unspecHeap H.
Proof. 
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. destruct sc; auto. simpl. apply beq_nat_true in eq. subst; auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed. 

Theorem unspecHeapRBRead : forall H x sc ds S ds' t N,
                   heap_lookup x H = Some (sfull sc ds S t N) ->
                   unspecHeap (replace x (sfull sc ds' S t N) H) = unspecHeap H.
Proof. 
  intros. destruct H. simpl in *. eapply raw_unspecHeapRBRead in H0. 
  eapply rawHeapsEq. eauto. 
Qed. 

Theorem rollbackUnspeculatedHeap : forall H H' tid T T' S, 
                                     rollback tid S H T H' T' -> unspecHeap H = unspecHeap H'. 
Proof.
  intros. induction H0; auto. 
  {subst. erewrite unspecHeapRBRead in IHrollback; eauto. }
  {subst. erewrite <- unspecHeapRBWrite; eauto. }
  {subst. erewrite unspecHeapRBNew; eauto. }
Qed. 

Theorem unspecSomeLookup : forall T tid t t', unspecThread t (tSingleton t') -> 
                                             thread_lookup T tid t ->
                                             thread_lookup (unspecPoolAux T) tid t'.
Proof.
  intros. inversion H; subst;  try solve[repeat 
  match goal with
    |H:tEmptySet = tSingleton ?t |- _ => symmetry in H; apply SingletonNeqEmpty in H; inv H
    |H:tSingleton ?t = tSingleton ?t' |- _ => apply SingletonEq in H; subst
    |H:thread_lookup ?t ?T ?t' |- _ => inv H
    |H:?a = ?b |- _ => inv H
    |_ => econstructor; eauto
  end]. 
Qed. 

Theorem unspecThreadTotal : forall t, exists t', unspecThread t t'. 
Proof.
  intros. destruct t. destruct p. destruct p. destructLast a0. 
  {eauto. }
  {invertHyp. destruct x; econstructor; unspecThreadTac; eauto. }
Qed. 

Theorem unspecLastAct : forall tid A s2 M M' t,
                         actionTerm A M' ->
                         (unspecThread (tid, [A], s2, M) t <->
                          unspecThread (tid, nil, s2, M') t). 
Proof.
  intros. split; intros. 
  {inversion H0; subst;    
   match goal with
       |H:[?A]=?s++[?a], H':actionTerm ?ac ?m |- _ =>
        destruct s; inv H; try invertListNeq; inv H'
   end; auto. }
  {inversion H0; subst; try invertListNeq.
   inv H; unspecThreadTac; auto. }
Qed. 

Theorem unspecTwoActs : forall tid A1 As s2 M M' t,
                         unspecThread (tid, (A1::As), s2, M') t <->
                         unspecThread (tid, (A1::As), s2, M) t. 
Proof.
  intros. split; intros. 
  {inversion H; subst;
   match goal with
       |H:?A::?As=?s++[?a] |- _ => rewrite H; eauto
   end. }
  {inversion H; subst;
   match goal with
       |H:?A::?As=?s++[?a] |- _ => rewrite H; eauto
   end. }
Qed. 

Theorem unspecTwoActs' : forall tid A1 A2 As s2 M M' t,
                         unspecThread (tid, (A1::A2::As), s2, M') t <->
                         unspecThread (tid, (A2 :: As), s2, M) t. 
Proof.
  intros. split; intros. 
  {inversion H; subst;  
   match goal with
     |H:?A1::?A2::?As=?s++[?a] |- _ =>
      apply listAlign in H; inversion H as [Ex1 Ex2]; rewrite Ex2; eauto
   end. 
  }
  {inversion H; subst; 
   match goal with
       |H:?A::?As=?s++[?a] |- _ => rewrite H in *; eauto 
   end. 
  }
Qed.

Theorem unspecDeterm : forall t t' t'', unspecThread t t' -> unspecThread t t'' -> t' = t''. 
Proof.
  intros.
  inv H; inv H0; auto; try solve[invertListNeq]; 
  match goal with
       |H:?s++[?a]=?s'++[?a'], H':decompose ?M ?E ?e |- _ => 
        apply lastElementEq in H; inv H
   end; auto. 
Qed. 

Theorem unspecSingleton : forall t t', 
                            unspecThread t t' ->
                            unspecPoolAux (tSingleton t) = t'.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inv H0. inv H1. inv H4. inv H0. eapply unspecDeterm in H2; eauto. subst. auto. }
  {destruct t. destruct p. destruct p. econstructor. econstructor. econstructor. 
   auto. eauto. auto. }
Qed. 

Ltac unfoldTac := unfold tAdd in *; unfold Add in *; unfold tUnion in *; unfold tSingleton in *;
                  unfold tCouple in *. 
  


Theorem specStepSingleton : forall H T t H' t', 
                              spec_step H T t H' T t' -> exists t'', t = tSingleton t''. 
Proof.
  intros. inv H0; eauto. Qed. 

Ltac helper :=
  match goal with
    | |- unspecPool (tSingleton ?t') ?t =>
      assert(exists t'', unspecThread t' t'') by apply unspecThreadTotal; invertHyp
  end. 


Theorem raw_unspecHeapAddWrite : forall x sc H a b TID N,
                               raw_heap_lookup x H = Some(sempty sc) -> 
                               raw_unspecHeap (raw_replace x (sfull sc (Empty_set tid) (a::b) TID N) H) = 
                               raw_unspecHeap H. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. apply beq_nat_true in eq. subst. destruct sc; auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed. 

Theorem unspecHeapAddWrite : forall x sc H a b TID N,
                               heap_lookup x H = Some(sempty sc) -> 
                               unspecHeap (replace x (sfull sc (Empty_set tid) (a::b) TID N) H) = unspecHeap H. 
Proof.
  intros. destruct H. simpl in *. eapply raw_unspecHeapAddWrite in H0; eauto.
  apply rawHeapsEq; eauto. 
Qed. 

Theorem raw_unspecHeapExtend : forall res H a b,
                                 res = raw_extend(sempty (a::b)) H -> 
                                 raw_unspecHeap (SND res) = raw_unspecHeap H.
Proof. 
  induction H; intros. 
  {simpl in H. inv H. auto. }
  {simpl in *. destruct a. inv H0. auto. }
Qed.
  
Theorem unspecHeapExtend : forall x H H' a b,
                             (x,H')=extend(sempty (a::b)) H -> 
                             unspecHeap H' = unspecHeap H.
Proof. 
  intros. destruct H. simpl in *. inv H0. 
  eapply rawHeapsEq. eapply raw_unspecHeapExtend. auto. 
Qed. 

Theorem unspecSpecStep : forall H t H' T t' t'', 
                           spec_step H T t H' T t' -> 
                           unspecPool t t'' -> unspecHeap H = unspecHeap H' /\ unspecPool t' t''. 
Proof.
  intros. inversion H0; subst.
  {inv H1; split; auto. helper. erewrite unspecSingleton; eauto. erewrite unspecSingleton.
   rewrite unspecTwoActs; eauto. eauto. }
  {inv H1; split; auto. helper. erewrite unspecSingleton; eauto. erewrite unspecSingleton.
   rewrite unspecTwoActs; eauto. eauto. }
  {inv H1; split; auto. helper. erewrite unspecSingleton; eauto. erewrite unspecSingleton.
   rewrite unspecTwoActs; eauto. eauto. }
  {inv H1; split; auto. helper. erewrite unspecSingleton; eauto. erewrite unspecSingleton.
   rewrite unspecTwoActs; eauto. eauto. }
  {inv H1; split; auto. helper. erewrite unspecSingleton; eauto. erewrite unspecSingleton.
   rewrite unspecTwoActs; eauto. eauto. }
  {inv H1; split; auto. helper. erewrite unspecSingleton; eauto. erewrite unspecSingleton.
   rewrite unspecTwoActs; eauto. eauto. }
  {inv H1; split; auto. helper. erewrite unspecSingleton; eauto. erewrite unspecSingleton.
   rewrite unspecTwoActs; eauto. eauto. }
  {inv H1; split; auto. destruct b. 
   {erewrite unspecSingleton; auto. unfoldTac. rewrite coupleUnion. rewrite unspecUnionComm. 
    repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. eauto. 
    eauto. }
   {assert(exists t', unspecThread (tid,a::b,s2,t0) t') by apply unspecThreadTotal. 
    invertHyp. erewrite unspecSingleton; eauto. unfoldTac. rewrite coupleUnion. 
    rewrite unspecUnionComm. repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. 
    eauto. rewrite unspecTwoActs'. eauto. }
  }
  {split. symmetry. eapply unspecHeapRBRead; eauto. inv H1. destruct b. erewrite unspecSingleton; eauto. 
   erewrite unspecSingleton; eauto. helper. erewrite unspecSingleton; eauto. 
   erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. }
  {split. symmetry. eapply unspecHeapAddWrite; eauto. inv H1. destruct b. erewrite unspecSingleton; eauto. 
   erewrite unspecSingleton; eauto. helper. erewrite unspecSingleton; eauto. 
   erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. }
  {split. erewrite <- unspecHeapExtend; eauto. inv H1. destruct b. erewrite unspecSingleton; eauto.
   erewrite unspecSingleton; eauto. helper. erewrite unspecSingleton; eauto. 
   erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. }
  {split; eauto. inv H1. destruct b. 
   {erewrite unspecSingleton; eauto. unfoldTac. rewrite coupleUnion. rewrite unspecUnionComm. 
    repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. eauto. 
    apply unspecCreatedSpec with(s1':=[specAct]).  auto. eauto. }
   {assert(exists t', unspecThread(tid,a::b,s2,t0) t') by apply unspecThreadTotal. invertHyp. 
    erewrite unspecSingleton; eauto. unfoldTac. rewrite coupleUnion. rewrite unspecUnionComm. 
    repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. eauto.
    apply unspecCreatedSpec with (s1':=[specAct]); auto. rewrite unspecTwoActs'; eauto. }
  }
Qed. 

Theorem unspecSpecMultistep : forall H T H' T' T'', 
                                spec_multistep H T H' T' -> 
                                unspecPool T T'' -> unspecHeap H' = unspecHeap H' /\ unspecPool T' T''.
Proof.
  intros. genDeps{T''}. induction H0; intros. 
  {auto. }
  {eapply unspecSpecStep in H; eauto. inv H. eapply IHspec_multistep; eauto. 
   inv H3. inv H1. rewrite unspecUnionComm. rewrite <- H5. rewrite <- unspecUnionComm. constructor. }
Qed. 

Require Import Coq.Sets.Powerset_facts. 

Ltac rollbackIdemHelper :=
  match goal with
    | |-unspecPool (Union ?x ?T ?t) (Union ?p (unspecPoolAux ?T) (unspecPoolAux ?t')) => 
      assert(unspecPoolAux t' = unspecPoolAux t)
    | |- unspecPoolAux(Singleton ?T ?t) = unspecPoolAux(Singleton ?T ?t') =>
      assert(exists t', unspecThread t t') by apply unspecThreadTotal
  end. 

Theorem rollbackIdempotent : forall tid stack H T H' T' T'', 
                               rollback tid stack H T H' T' ->  unspecPool T T'' ->
                               unspecPool T' T''. 
Proof.
  intros. induction H0; subst. 
  {auto. }
  {inversion H1; subst. apply IHrollback. unfoldTac. rewrite unspecUnionComm in *. 
   destruct s1'. 
   {unfoldTac. rollbackIdemHelper. repeat erewrite unspecSingleton; eauto. rewrite H. 
    rewrite <- unspecUnionComm. constructor. }
   {unfoldTac. rollbackIdemHelper. rollbackIdemHelper. invertHyp. 
    repeat erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. rewrite H. 
    rewrite <- unspecUnionComm. constructor. } 
  }
  {inv H1. apply IHrollback; auto. unfoldTac. rewrite unspecUnionComm. unfoldTac. rollbackIdemHelper. 
   rewrite coupleUnion. rewrite unspecUnionComm. unfoldTac. rewrite Union_commutative.  
   erewrite unspecSingleton; eauto. rewrite union_empty_l. destruct s1'. 
   repeat erewrite unspecSingleton; eauto. rollbackIdemHelper. invertHyp. 
   repeat erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. rewrite H.  
   rewrite <- unspecUnionComm. constructor. }
  {inv H1. apply IHrollback. unfoldTac. rewrite unspecUnionComm. unfoldTac. rollbackIdemHelper. 
   destruct s1'. repeat erewrite unspecSingleton; eauto. rollbackIdemHelper. invertHyp. 
   repeat erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. rewrite H. 
   rewrite <- unspecUnionComm. constructor.  }
  {inv H1. apply IHrollback. unfoldTac. rewrite unspecUnionComm. unfoldTac. rollbackIdemHelper. 
   destruct s1'. repeat erewrite unspecSingleton; eauto. rollbackIdemHelper. invertHyp. 
   repeat erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. rewrite H. 
   rewrite <- unspecUnionComm. constructor. }
  {inv H1. apply IHrollback; auto. unfoldTac. repeat rewrite unspecUnionComm. unfoldTac.  
   replace(unspecPoolAux (Singleton thread (2 :: TID', [specAct; specAct], s2', N))) with tEmptySet.
   rewrite union_empty_r. rollbackIdemHelper. destruct s1'. repeat erewrite unspecSingleton; eauto. 
   rollbackIdemHelper. invertHyp. repeat erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. 
   eauto. rewrite H. rewrite <- unspecUnionComm. constructor. erewrite unspecSingleton; eauto. 
   apply unspecCreatedSpec with (s1':=[specAct]). auto. 
  }
Qed. 

Theorem specStepChangeUnused : forall H T T' t t' H',
                                 spec_step H T t H' T t' ->
                                 spec_step H T' t H' T' t'. 
Proof.
  intros. Hint Constructors spec_step.  inversion H0; eauto. 
Qed. 

Require Import Coq.Sets.Powerset_facts. 
Theorem spec_multi_unused : forall H T1 T2 T1' H', 
                              spec_multistep H (tUnion T1 T2) H' (tUnion T1' T2) <->
                              spec_multistep H T1 H' T1'.
Proof.
  intros. split; intros. 
  {remember (tUnion T1 T2). remember (tUnion T1' T2). induction H0. 
   {subst. admit. }
   {admit. }
  }
  {induction H0. constructor. unfoldTac. rewrite Union_associative. 
   rewrite (Union_commutative thread t).  rewrite <- Union_associative. 
   econstructor. eapply specStepChangeUnused. eauto. unfoldTac. rewrite Union_associative. 
   rewrite (Union_commutative thread T2). rewrite <- Union_associative. auto. 
  }
Qed. 

Theorem wfFrame : forall T1 T2 H, commitPool T2 ->
                                  (wellFormed H (tUnion T1 T2) <-> wellFormed H T1).
Proof.
  intros. split; intros. 
  {inversion H1; subst. inversion H3; subst. rewrite unspecUnionComm in *. 
   econstructor; eauto. rewrite <- (commitPoolUnspecUnchanged T2) in H4; auto. 
   rewrite spec_multi_unused in H4. auto. }
  {inversion H1; subst. inversion H3; subst. econstructor; eauto. rewrite unspecUnionComm.
   rewrite <- (commitPoolUnspecUnchanged T2); auto. rewrite spec_multi_unused. 
   auto. }
Qed. 



