Require Import Spec. 
Require Import AST.  
Require Import SfLib. 
Require Import erasure. 
Require Import sets. 
Require Import Coq.Sets.Ensembles. 

Hint Resolve app_comm_cons app_nil_l. 

Ltac inv H := inversion H; subst; clear H.

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

Theorem listAlign : forall (T:Type) l (x y :T) l' (e:T),
                      x::y::l = l' ++ [e] ->
                      exists l'', (y::l) = l'' ++ [e]. 
Proof.
  induction l; intros. 
  {destruct l'. inversion H. exists nil. inversion H.
   destruct l'. inversion H2. auto. inversion H2. destruct l'; inversion H4. }
  {destruct l'. 
   {inversion H. }
   {inversion H. exists l'. assumption. }
  }
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

Axiom unspec_thread : forall t, exists t', unspecThread t t'.

Ltac unfoldTac := unfold tAdd in *; unfold Add in *; unfold tUnion in *; unfold tSingleton in *;
                  unfold tCouple in *. 

(*Helper theorems for reasoning about the erasure of heaps being rolled back*)
Theorem unspecHeapRBNew : forall H H' x S A,
                           unspecHeap H H' ->
                           Heap.heap_lookup x H = Some(sempty (S::A)) ->
                           unspecHeap (Heap.remove H x) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst; clear H1. inversion H0; subst. assumption. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem unspecHeapRBRead : forall H H' x sc tid ds S A t N,
                   unspecHeap H H' ->
                   Heap.heap_lookup x H = Some (sfull sc (tid::ds) (S::A) t N) ->
                   unspecHeap (Heap.replace x (sfull sc ds (S::A) t N) H) H'. 
Proof. 
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst. clear H1. inversion H0; subst; eauto. 
    apply beq_nat_true in eq. subst. eauto. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem unspecHeapRBWrite : forall H H' x sc S A tid N,
                      unspecHeap H H' ->
                      Heap.heap_lookup x H = Some(sfull sc nil (S::A) tid N) ->
                      unspecHeap (Heap.replace x (sempty sc) H) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst. clear H1. inversion H0; subst. 
    econstructor. assumption. apply beq_nat_true in eq. subst. auto. }
   {inversion H0; eauto. }
  }
Qed. 

Ltac rollbackIdemHelper :=
  match goal with
    | |-unspecPool (Union ?x ?T ?t) (Union ?p (unspecPoolAux ?T) (unspecPoolAux ?t')) => 
      assert(unspecPoolAux t' = unspecPoolAux t)
    | |- unspecPoolAux(Singleton ?T ?t) = unspecPoolAux(Singleton ?T ?t') =>
      assert(exists t', unspecThread t t') by apply unspec_thread
  end. 

Require Import Coq.Sets.Powerset_facts. 

Theorem rollbackIdempotent : forall tid stack H T H' H'' T' T'', 
                               rollback tid stack H T H' T' ->  unspecPool T T'' ->
                               unspecHeap H H'' ->
                               unspecHeap H' H'' /\ unspecPool T' T''. 
Proof.
  intros. induction H0. 
  {auto. }
  {inversion H1; subst. apply IHrollback. unfoldTac. rewrite unspecUnionComm in *. 
   destruct s1'. 
   {unfoldTac. rollbackIdemHelper. repeat erewrite unspecSingleton; eauto. rewrite H. 
    rewrite <- unspecUnionComm. constructor. }
   {unfoldTac. rollbackIdemHelper. rollbackIdemHelper. invertHyp. 
    repeat erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. rewrite H. 
    rewrite <- unspecUnionComm. constructor. } eapply unspecHeapRBRead; eauto. 
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
   rewrite <- unspecUnionComm. constructor. eapply unspecHeapRBWrite; eauto. }
  {inv H1. apply IHrollback. unfoldTac. rewrite unspecUnionComm. unfoldTac. rollbackIdemHelper. 
   destruct s1'. repeat erewrite unspecSingleton; eauto. rollbackIdemHelper. invertHyp. 
   repeat erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. eauto. rewrite H. 
   rewrite <- unspecUnionComm. constructor. eapply unspecHeapRBNew; eauto. }
  {inv H1. apply IHrollback; auto. unfoldTac. repeat rewrite unspecUnionComm. unfoldTac. 
   replace(unspecPoolAux (Singleton thread (2 :: tid, [specAct], s2', N))) with tEmptySet.
   rewrite union_empty_r. rollbackIdemHelper. destruct s1'. repeat erewrite unspecSingleton; eauto. 
   rollbackIdemHelper. invertHyp. repeat erewrite unspecSingleton; eauto. rewrite <- unspecTwoActs'. 
   eauto. rewrite H. rewrite <- unspecUnionComm. constructor. erewrite unspecSingleton; eauto. }
Qed. 
