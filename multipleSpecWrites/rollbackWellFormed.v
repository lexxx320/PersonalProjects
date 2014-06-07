Require Import NonSpec. 
Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import SfLib. 

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

Inductive actionIDs : thread -> Prop :=
|nilAct : forall tid s2 M, actionIDs (tid, nil, s2, M)
|consSpec : forall maj min min' tid s1 s2 M N,
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, sAct (Tid(maj,min') tid) N::s1, s2, M)
|consOtherwise : forall tid M s1 s2 a,
                   (forall tid' N, a <> sAct tid' N) -> actionIDs(tid, s1, s2, M) ->
                   actionIDs(tid, a::s1, s2, M)
.

Axiom ConsistentIDs : forall T, actionIDs T. 

Theorem lastActionConsistent : forall tid x a s N,
                                 actionIDs(tid, x++[a], s, N) -> 
                                 actionIDs(tid, [a], s, N).
Proof.
  induction x; intros. 
  {simpl in H. assumption. }
  {simpl in *. inversion H; subst; auto. }
Qed. 

Ltac copy H := 
  match type of H with
      |?x => assert(x) by assumption
  end. 

Theorem unspecLastAct : forall i j j' l A s2 M M' t,
                         basicAction A M' j' ->
                         (unspecThread (Tid(i,j)l, [A], s2, M) t <->
                          unspecThread (Tid(i,j')l, nil, s2, M') t). 
Proof.
  intros. split; intros. 
  {inversion H0; subst; 
   match goal with
       H:[?A]=?s++[?a], H':basicAction ?ac ?m ?t |- _ => 
       destruct s; inversion H; subst; try invertListNeq; inversion H'; subst
   end; copy H6; apply decomposeEq in H6; subst; rewrite H1 in H8; inversion H8; subst; econstructor.  
  }
  {inversion H0; subst; try invertListNeq. 
   inversion H; subst; try solve[
    copy H1; apply decomposeEq in H1; subst; econstructor;[eassumption|rewrite app_nil_l; auto]]. 
  }
Qed. 

Hint Resolve app_comm_cons. 

Theorem unspecTwoActs : forall i j j' l A1 A2 As s2 M M' t,
                         unspecThread (Tid(i,j')l, (A1::A2::As), s2, M') t <->
                         unspecThread (Tid(i,j)l, (A2 :: As), s2, M) t. 
Proof.
  intros. split; intros. 
  {inversion H; subst; 
   match goal with
       |H:?A1::?A2::?As=?s++[?a] |- _ =>
        apply listAlign in H; inversion H as[Ex1 Ex2]; rewrite Ex2; econstructor; eauto
   end. 
  }
  {inversion H; subst; 
   match goal with
       |H:?A::?As=?s++[?a], H':unspecThread ?t ?t' |- unspecThread ?t'' ?t''' =>
        rewrite H
   end; econstructor; eauto. 
  }
Qed. 

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

Theorem appNil : forall (T:Type) (x:T), [x] = nil ++ [x]. 
Proof.
  intros. auto. Qed. 

Theorem unspecBasicAction1 : forall a M M' s2 T i j j' l,
                               basicAction a M' j' ->
                               unspecPoolAux(tAdd T (Tid(i,j)l, [a], s2, M)) = 
                               unspecPoolAux(tAdd T (Tid(i,j')l, nil, s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {econstructor. econstructor. eapply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecLastAct. eassumption. eassumption. } 
  }
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecLastAct; eauto. }
  }
Qed. 


Theorem unspecBasicAction2 : forall a b s1' s2 M M' T i j j' l,
                              basicAction a M' j' ->
                              unspecPoolAux(tAdd T (Tid(i,j) l, a::b::s1', s2, M)) = 
                              unspecPoolAux(tAdd T (Tid(i,j')l, b::s1', s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecTwoActs. eassumption. }
  }
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecTwoActs. eassumption. }
  }
Qed. 

Theorem unspecAdd : forall T t t', unspecThread t (Some t') -> 
                                   unspecPoolAux(tAdd T t) = tAdd(unspecPoolAux T) t'. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {apply Union_intror. inversion H4; subst; clear H4. Admitted. 



Theorem rollbackWellFormed : forall tid As H T H' T', 
                               wellFormed H T -> rollback tid As H T H' T' ->
                               wellFormed H' T'. 
Proof.
  intros. induction H1; subst. 
  {assumption. }
  {apply IHrollback. inversion H0; subst. inversion H3; subst. destruct s1'. 
   {eapply wf with (T' :=(unspecPoolAux (tAdd T (Tid (i, j) l, [rAct x j' M'], s2, M)))) . 
    erewrite unspecBasicAction1. econstructor. econstructor. eassumption. eapply unspecHeapRBRead; eauto. 
    erewrite unspecAdd. Focus 2. econstructor. eassumption. rewrite app_nil_l. reflexivity.  
    