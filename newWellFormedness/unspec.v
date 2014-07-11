Require Import Spec.      
Require Import AST.   
Require Import SfLib. 
Require Import sets. 
Require Import Coq.Sets.Ensembles. 
Require Import SpecLib. 
Require Import Coq.Sets.Powerset_facts. 
Require Import Heap.  
Require Import classifiedStep. 

(*------------------------------------Unspec Definitions----------------------------*)
Inductive unspecHeap : sHeap -> sHeap -> Prop :=
  |unSpecSE : forall h h' i hd tl, unspecHeap h h' -> (*spec empty*)
                                   unspecHeap ((i, sempty (hd::tl)) :: h) h'
  |unSpecCE : forall h h' i, unspecHeap h h' -> (*commit empty*)
                             unspecHeap ((i, sempty nil) :: h) ((i, sempty nil) :: h')
  |unspecSF : forall h h' i hd tl d s t N, 
                unspecHeap h h' -> (*spec created full*)
                unspecHeap ((i, sfull (hd::tl) d s t N) :: h) h'
  |unspecCCSF : forall h h' i d hd tl t M, 
                  unspecHeap h h' ->  (*commit created spec full*)
                  unspecHeap ((i, sfull nil d (hd::tl) t M)::h) ((i, sempty nil)::h')
  |unspecCCCF : forall h h' i d t M, 
                  unspecHeap h h' ->   (*commit created, commit full*)
                  unspecHeap ((i, sfull nil d nil t M)::h) 
                             ((i, sfull nil nil nil t M)::h')
  |unspecNil : unspecHeap nil nil
.
Hint Constructors unspecHeap. 

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
|wf : forall H H' T T', unspecPool T T' -> unspecHeap H H' -> 
                        spec_multistep H' T' H T ->
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

Theorem unspecUnspeculatedHeap : forall H H', unspecHeap H H' -> unspecHeap H' H'. 
Proof.
  intros. induction H0; auto. Qed. 

Theorem LookupSame :
  forall P P', unspecPool P P' ->
               forall tid T, thread_lookup P' tid T ->
                             exists T', thread_lookup P tid T' /\ unspecThread T' (tSingleton T).
Proof.
  intros. inversion H; subst. inv H0. inv H1. inv H0. inv H4. inv H2; try solve[inv H3; eauto]. 
Qed. 

Theorem unspecDependentReader : forall H H',
                                  unspecHeap H H' -> 
                                  forall x sc ds s w N tid, heap_lookup x H = Some (sfull sc ds s w N) ->
                                  unspecHeap (replace x (sfull sc (tid::ds) s w N) H) H'. 
Proof.
  intros H H' U. induction U; intros; auto. 
  {simpl in *. destruct (beq_nat x i). inversion H. eapply IHU in H. 
   constructor. eassumption. }
  {simpl in *. destruct (beq_nat x i). inversion H. constructor. eapply IHU in H. eassumption. }
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H; subst. constructor. assumption. 
   eapply IHU in H. constructor. eassumption. }
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. constructor. assumption. eapply IHU in H. constructor. eassumption. }
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. constructor. assumption. eapply IHU in H. constructor. eassumption. }
Qed. 

Theorem unspecDependentReader2 : forall h H', unspecHeap h H' -> forall x sc d ds a t N,
                                              heap_lookup x h = Some (sfull sc (d::ds) a t N) -> 
                                              unspecHeap (replace x (sfull sc ds a t N) h) H'.
Proof. 
  intros h H' U. induction U; intros; eauto;
  try solve[simpl in *; destruct(beq_nat x i);[inversion H; eauto|eauto]]. 
  {simpl in *. destruct (beq_nat x i) eqn :eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. constructor. assumption. constructor. eapply IHU; eauto. }
  {simpl in *; destruct (beq_nat x i) eqn:eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. eauto. eauto. }
Qed.   

Theorem unspecSpecfull : forall h H', unspecHeap h H' -> forall x sc S A t N,
                                              heap_lookup x h = Some (sfull sc nil (S::A) t N) -> 
                                              unspecHeap (replace x (sempty sc) h) H'.
Proof. 
  intros h H' U. induction U; intros; eauto; 
  try solve[simpl in *; destruct(beq_nat x i);[inversion H; eauto|eauto]]. 
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. eauto. eauto. }
Qed. 

Theorem unspecSpecEmpty : forall h H', unspecHeap h H' -> forall x S A, 
                                              heap_lookup x h = Some (sempty (S::A)) -> 
                                              unspecHeap (remove h x) H'.
Proof.
  intros h H' U; induction U; intros; eauto;
  try solve[simpl in *; destruct (beq_nat x i); [inversion H; eauto|eauto]]. Qed. 

Theorem rollbackUnspeculatedHeap : forall H H' H'' tid T T' S, 
                                     unspecHeap H H' -> rollback tid S H T H'' T' -> unspecHeap H'' H'. 
Proof.
  intros. generalize dependent H'. induction H1; intros; subst; auto.
  {eapply IHrollback. eapply unspecDependentReader2 in H5; eauto. }
  {eapply IHrollback. eapply unspecSpecfull in H5; eauto. }
  {eapply IHrollback. eapply unspecSpecEmpty in H6; eauto. }
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
      assert(exists t', unspecThread t t') by apply unspecThreadTotal
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






