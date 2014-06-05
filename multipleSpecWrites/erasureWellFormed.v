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
|consRead : forall maj min min' E tid s1 s2 M N x,
              decompose N = (E, get (fvar x)) ->
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, rAct x (Tid(maj,min') tid) N::s1, s2, M)
|consWrite : forall maj min min' E tid s1 s2 M N x N',
               decompose N = (E, put (fvar x) N') ->
               actionIDs(Tid(maj,min)tid, s1, s2, M) ->
               actionIDs(Tid(maj,min)tid, wAct x (Tid(maj,min') tid) N::s1, s2, M)
|consNew : forall maj min min' E tid s1 s2 M N x,
             decompose N = (E, new) ->
             actionIDs(Tid(maj,min)tid, s1, s2, M) ->
             actionIDs(Tid(maj,min)tid, cAct x (Tid(maj,min') tid) N::s1, s2, M)
|consSpec : forall maj min min' tid s1 s2 M N,
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, sAct (Tid(maj,min') tid) N::s1, s2, M)
|consFork : forall maj min min' tid s1 s2 M N N' E x,
              decompose N = (E, fork N') -> 
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, fAct x (Tid(maj,min') tid) N::s1, s2, M)
|consCSpec : forall maj min tid s1 s2 M,
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, specAct::s1, s2, M)
.

Axiom ConsistentIDs : forall T, actionIDs T. 

Ltac copy H := 
  match type of H with
      |?x => assert(x) by assumption
  end. 

Theorem lastActionConsistent : forall tid x a s N,
                                 actionIDs(tid, x++[a], s, N) -> 
                                 actionIDs(tid, [a], s, N).
Proof.
  induction x; intros. 
  {simpl in H. assumption. }
  {simpl in *. inversion H; subst; auto. }
Qed. 

Theorem unspecLastAct : forall tid tid' A s2 M M' t,
                         basicAction A M' tid' ->
                         (unspecThread (tid, [A], s2, M) t <->
                          unspecThread (tid', nil, s2, M') t). 
Proof.
  intros. split; intros. 
  {inversion H0; subst; try solve[
   match goal with
        |H:[?A]=?s++[?a], H':basicAction ?ac ?m ?t |- _ => 
         destruct s; inversion H; subst; try invertListNeq; inversion H'; subst
    end; apply decomposeEq in H6; subst; constructor]. 
  }
  {destruct tid. destruct p. destruct tid'. destruct p. inversion H0; subst; try invertListNeq. 
   inversion H; subst; try solve[
   match goal with
       | |- unspecThread ?t ?t' => 
         assert(C:actionIDs t) by apply ConsistentIDs; inversion C; subst
   end; copy H3; apply decomposeEq in H3; subst; econstructor;[eassumption|rewrite app_nil_l; auto]]. 
  }
Qed. 

Hint Resolve app_comm_cons. 

Theorem unspecTwoActs : forall tid tid' A1 A2 As s2 M M' t,
                         unspecThread (tid', (A1::A2::As), s2, M') t <->
                         unspecThread (tid, (A2 :: As), s2, M) t. 
Proof.
  intros. split; intros. 
  {destruct tid. destruct p. inversion H; subst; try solve[
   match goal with
       |H:?A1::?A2::?As=?s++[?a] |- _ =>
        apply listAlign in H; inversion H as[Ex1 Ex2]; rewrite Ex2
   end; match goal with
       | |- unspecThread ?t ?t' => assert(C:actionIDs t) by apply ConsistentIDs; 
                                  apply lastActionConsistent in C; inversion C; subst
   end; solve[eauto|copy H5; apply decomposeEq in H5; subst; econstructor; [eassumption| reflexivity]]]. 
  }
  {inversion H; subst; destruct tid'; destruct p; try solve[ 
   match goal with
       |H:?A::?As=?s++[?a], H':unspecThread ?t ?t' |- unspecThread ?t'' ?t''' =>
        rewrite H; assert(C:actionIDs t'') by apply ConsistentIDs; rewrite H in C;
        rewrite app_comm_cons in C; apply lastActionConsistent in C; inversion C; subst 
   end; solve[eauto|copy H5; apply decomposeEq in H5; subst; eauto]]. 
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

Theorem unspecBasicAction1 : forall a M M' s2 tid tid' T,
                               basicAction a M' tid' ->
                               unspecPoolAux(tAdd T (tid, [a], s2, M)) = 
                               unspecPoolAux(tAdd T (tid', nil, s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {destruct tid'. destruct p. econstructor. econstructor. eapply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecLastAct. eassumption. eassumption. } 
  }
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {destruct tid. destruct p. econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecLastAct; eauto. }
  }
Qed. 


Theorem unspecBasicAction2 : forall a b s1' s2 M M' tid tid' T,
                              basicAction a M' tid' ->
                              unspecPoolAux(tAdd T (tid, a::b::s1', s2, M)) = 
                              unspecPoolAux(tAdd T (tid', b::s1', s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {destruct tid'. destruct p. econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecTwoActs. eassumption. }
  }
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {destruct tid. destruct p. econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecTwoActs. eassumption. }
  }
Qed. 

Theorem rollbackWellFormed : forall tid As H T H' T', 
                               wellFormed H T -> rollback tid As H T H' T' ->
                               wellFormed H' T'. 
Proof.
  intros. induction H1; subst. 
  {assumption. }
  {apply IHrollback. inversion H0; subst. inversion H2; subst. destruct s1'. 
   {eapply wf with (T' := (unspecPoolAux (tAdd T (tid', [rAct x tid'' M'], s2, M)))). 
    erewrite unspecBasicAction1. econstructor. constructor. eapply unspecHeapRBRead; eauto. 
    
