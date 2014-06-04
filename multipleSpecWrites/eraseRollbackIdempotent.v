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
|consRead : forall maj min min' tid s1 s2 M N x,
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, rAct x (Tid(maj,min') tid) N::s1, s2, M)
|consWrite : forall maj min min' tid s1 s2 M N x,
               actionIDs(Tid(maj,min)tid, s1, s2, M) ->
               actionIDs(Tid(maj,min)tid, wAct x (Tid(maj,min') tid) N::s1, s2, M)
|consNew : forall maj min min' tid s1 s2 M N x,
             actionIDs(Tid(maj,min)tid, s1, s2, M) ->
             actionIDs(Tid(maj,min)tid, cAct x (Tid(maj,min') tid) N::s1, s2, M)
|consSpec : forall maj min min' tid s1 s2 M N,
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, sAct (Tid(maj,min') tid) N::s1, s2, M)
|consFork : forall maj min min' tid s1 s2 M N x,
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, fAct x (Tid(maj,min') tid) N::s1, s2, M)
|consJoin : forall maj min tid s1 s2 M,
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, joinAct::s1, s2, M)
|consCSpec : forall maj min tid s1 s2 M,
              actionIDs(Tid(maj,min)tid, s1, s2, M) ->
              actionIDs(Tid(maj,min)tid, specAct::s1, s2, M)
.

Axiom ConsistentIDs : forall T, actionIDs T. 

Inductive actionTerm : action -> trm -> Prop :=
|readTerm : forall x tid M, actionTerm (rAct x tid M) M
|writeTerm : forall x tid M, actionTerm (wAct x tid M) M
|newTerm : forall x tid M, actionTerm (cAct x tid M) M. 

Theorem eraseLastAct : forall tid A s2 M M' T t,
                         actionTerm A M' ->
                         eraseThread (tid, [A], s2, M) T t ->
                         eraseThread (tid, nil, s2, M') T t. 
Proof.
  intros. inversion H0; subst; try solve[
  match goal with
       |H:[?A] = ?s++[?x], H':actionTerm ?A ?M |- _ => 
        destruct s; inversion H; subst; inversion H'; subst; constructor; auto;
        invertListNeq
  end]. 
  {destruct s1'; inversion H7. subst. inversion H. destruct s1'; inversion H3. }
  {destruct s1'; inversion H7. subst. inversion H. destruct s1'; inversion H3. }
Qed. 

Theorem eraseTwoActs : forall tid A1 A2 As s2 M T t,
                         eraseThread (tid, (A1::A2::As), s2, M) T t ->
                         eraseThread (tid, (A2 :: As), s2, M) T t. 
Proof.
  intros. 
  inversion H; subst; match goal with
       |H:?A1::?A2::?As = ?s1 ++ [?x] |- _ => apply listAlign in H;
                                             invertExists; eauto
   end. 
Qed. 

Theorem lookupWeakening : forall tid T t t', thread_lookup T tid t ->
                                             thread_lookup (tAdd T t') tid t. 
Proof.
  intros. inversion H; subst. econstructor. constructor. assumption. reflexivity. 
Qed. 

Theorem eraseWeaken : forall T t M M', eraseTerm M T M' -> eraseTerm M (tAdd T t) M'.
Proof.
  intros. generalize dependent t. induction H; intros; auto. 
  {econstructor. apply IHeraseTerm1. eassumption. eapply IHeraseTerm2. 
   eapply lookupWeakening in H2. eassumption. }
Qed. 

Theorem x : forall T t t' t'' P M M', 
              eraseThread t P t'' -> eraseThread t' P t'' ->
              eraseTerm M (tAdd T t) M' ->
              eraseTerm M (tAdd T t') M'.
Proof.
  intros. generalize dependent t'. generalize dependent t''. generalize dependent P. 
  remember (tAdd T t). induction H1; intros; auto; 
  try solve[constructor; [eapply IHeraseTerm1; eauto|eauto]];
  try solve[constructor; eapply IHeraseTerm; eauto].           
  {econstructor. eapply IHeraseTerm1. assumption. eassumption. assumption. 
   eassumption. eapply IHeraseTerm2. assumption. eassumption. assumption. 
   subst. inversion H0; subst. inversion H8; subst; clear H8. inversion H7; subst. 
   {econstructor. apply Union_introl. eassumption. reflexivity. }
   {inversion H; subst; clear H. admit. }
  }
Qed. 

Theorem erasePoolSame : forall T T' t t' t'',
                          erasePool (tAdd T t) T' -> eraseThread t T t'' ->
                          eraseThread t' T t'' -> erasePool (tAdd T t') T'. 
Proof.
  intros. inversion H; subst. 
  assert(erasePoolAux(tAdd T t) = erasePoolAux(tAdd T t')). 
  apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H2; subst. inversion H3; subst. inversion H6. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. 
    Focus 2. eassumption. inversion H4; subst. 
    {econstructor. eapply x. eapply H0. eapply H1. assumption. }
    {econstructor. reflexivity. eapply x. eapply H0. auto. auto. eassumption. }
    {eapply tEraseWrite; eauto. eapply x. eapply H0. auto. auto. }
    {eapply tEraseNew; eauto. eapply x. eapply H0. auto. auto. }
    {eapply tEraseSpec; eauto. }
    {eapply tEraseFork; eauto. eapply x. eapply H0; auto. auto. auto. }
    {eapply tEraseJoin. reflexivity. eapply x. eapply H0. auto. auto. }
    {eapply tEraseCreatedSpec. reflexivity. }
   } 
   (*{inversion H7; subst; clear H7. inversion H8; subst; clear H8.
    inversion H1; subst. 
    {destruct tid0. destruct p. econstructor. econstructor. eapply Union_intror. 
     econstructor. reflexivity. econstructor. eapply x. Focus 2. eapply H1. 
     econstructor. eassumption. apply eraseWeaken. eassumption. 

  } *)
Admitted. 

Theorem y : forall T t t' t'' P M M', 
              eraseThread t P t'' -> eraseThread t' P t'' ->
              eraseThread M (tAdd T t) M' ->
              eraseThread M (tAdd T t') M'.
Proof.
  intros. generalize dependent t'. generalize dependent t''. generalize dependent P. 
  remember (tAdd T t). induction H1; intros; auto; subst; 
  try solve[constructor; [eapply IHeraseTerm1; eauto|eauto]];
  try solve[constructor; eapply IHeraseTerm; eauto].           
  {constructor. eapply x. eapply H0. assumption. assumption. }
  {econstructor. reflexivity. eapply x. eapply H2. assumption. assumption. eauto. }
  {eapply tEraseWrite. reflexivity. eapply x. eapply H2. auto. auto. eauto. }
  {eapply tEraseNew. reflexivity. eapply x. eapply H2. auto. auto. eauto. }
  {eapply tEraseSpec. reflexivity. }
  {eapply tEraseFork. reflexivity. eapply x. eapply H2. auto. auto. eauto. }
  {eapply tEraseJoin. reflexivity. eapply x. eapply H1. auto. auto. }
  {eapply tEraseCreatedSpec. reflexivity. }
Admitted. 

(*Helper theorems for reasoning about the erasure of heaps being rolled back*)
Theorem eraseHeapRBNew : forall H H' x S A,
                           eraseHeap H H' ->
                           Heap.heap_lookup x H = Some(sempty (S::A)) ->
                           eraseHeap (Heap.remove H x) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x0 i) eqn:eq. 
   {inversion H1; subst; clear H1. inversion H0; subst. assumption. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem eraseHeapRBRead : forall H H' x sc tid ds S A t N,
                   eraseHeap H H' ->
                   Heap.heap_lookup x H = Some (sfull sc (tid::ds) (S::A) t N) ->
                   eraseHeap (Heap.replace x (sfull sc ds (S::A) t N) H) H'. 
Proof. 
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x0 i) eqn:eq. 
   {inversion H1; subst. clear H1. inversion H0; subst; eauto. 
    apply beq_nat_true in eq. subst. eauto. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem eraseHeapRBWrite : forall H H' x sc S A tid N,
                      eraseHeap H H' ->
                      Heap.heap_lookup x H = Some(sfull sc nil (S::A) tid N) ->
                      eraseHeap (Heap.replace x (sempty sc) H) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x0 i) eqn:eq. 
   {inversion H1; subst. clear H1. inversion H0; subst. 
    econstructor. assumption. apply beq_nat_true in eq. subst. auto. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem appNil : forall (T:Type) (x:T), [x] = nil ++ [x]. 
Proof.
  intros. simpl. reflexivity. Qed. 

Theorem z : forall T t T', erasePool (tAdd T t) T' -> 
                           exists t', eraseThread t (tAdd T t) t'. 
Proof.
  Admitted. 

Theorem erasePoolAuxEq : forall A M M' tid tid' s2 T,
                           actionTerm A M' ->
                           erasePoolAux(tAdd T (tid, [A], s2, M)) = 
                           erasePoolAux(tAdd T (tid', nil, s2, M')). 
Admitted. 

Theorem asdf : forall T t t' t'', 
                 eraseThread t (tAdd T t) t'' -> eraseThread t' (tAdd T t') t'' ->
                 erasePoolAux(tAdd T t) = erasePoolAux(tAdd T t'). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H1; subst. inversion H2; subst. inversion H5; subst. 
   {inversion H6; subst; clear H6. inversion H3; subst. 
    {inversion H4; subst. clear H4. econstructor. econstructor. apply Union_intror. 
     

Theorem erasePoolReadEq1 : forall T tid' x0 tid'' M' s2 M,                
        erasePoolAux(tAdd T (tid',[rAct x0 tid'' M'], s2, M)) = 
        erasePoolAux(tAdd T (tid'', nil, s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. inversion H3.  
   {econstructor. econstructor. econstructor; eauto. reflexivity. 
    Focus 2. eassumption. 
    assert(exists TE, erasePool(tAdd T (tid',[rAct x0 tid'' M'], s2, M)) TE).
    exists (erasePoolAux(tAdd T (tid', [rAct x0 tid'' M'], s2, M))). constructor. 
    invertExists. apply z in H8. invertExists. eapply y. eassumption. 
    inversion H7; try solve[
       match goal with
         |H:?x=?s++[?y]|- _ => destruct s; inversion H; invertListNeq
       end]. 
       {destruct s1'; inversion H14; subst. econstructor. assumption. 
        constructor. invertListNeq. } assumption. } 
      { destruct tid''. destruct p. inversion H4; subst; clear H4.
       inversion H5; subst; clear H5. inversion H1; subst; try invertListNeq. 
       {econstructor. econstructor. apply Union_intror. econstructor. 
        reflexivity. econstructor.  Focus 2. eassumption. destruct s1'.
        inversion H12; subst. eapply x. eassumption. econstructor. assumption. 
        assumption. inversion H12. invertListNeq. }
      }
  }
  {inversion H. inversion H0. inversion H4; subst. 
   {econstructor. econstructor. econstructor; eauto. reflexivity. 
    Focus 2. eassumption.
    assert(exists TE, erasePool(tAdd T (tid',[rAct x0 tid'' M'], s2, M)) TE).
    exists(erasePoolAux (tAdd T (tid', [rAct x0 tid'' M'], s2, M))). econstructor. 
    invertExists. apply z in H6. invertExists. eapply y. eassumption. 
    inversion H3; subst; try solve[
             match goal with
               |H:?x=?s++[?y] |- _ => destruct s; inversion H; invertListNeq
             end]. 
    {destruct s1'. inversion H13; subst. clear H13. econstructor. rewrite <- appNil. 
     reflexivity. assumption. eassumption. assumption. }
    {eapply y. Focus 3. eapply H1. Focus 2. eassumption. inversion H3; subst;
                                                         try invertListNeq. 
     {destruct s1'; inversion H13; subst. constructor. assumption. 
      destruct s1'; inversion H8. }
    }
   }
   {destruct tid'. destruct p. inversion H5; subst; clear H5. inversion H9; subst. 
    clear H9. inversion H1; subst; try invertListNeq. 
    {econstructor. econstructor. apply Union_intror. econstructor. reflexivity.
     


     Admitted.


Theorem rollbackIdempotent : forall tid stack H T H' T' H'' T'', 
                               rollback tid stack H T H' T' -> 
                               eraseHeap H H'' -> erasePool T T'' ->
                               eraseHeap H' H'' /\ erasePool T' T''. 
Proof.
  intros. generalize dependent H''. generalize dependent T''.
  induction H0; intros; subst. {split; auto. }
  {destruct s1'. 
   {eapply IHrollback. inversion H5; subst. 
    assert(erasePoolAux(tAdd T (tid',[rAct x0 tid'' M'], s2, M)) = 
           erasePoolAux(tAdd T (tid'', nil, s2, M'))). 
    {apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
     split; intros.  
     {inversion H; subst. inversion H1; subst. inversion H8. 
      {econstructor. econstructor. econstructor; eauto. reflexivity. 
       Focus 2. eassumption. apply z in H5. invertExists. eapply y. eassumption. 
       rewrite appNil in H12. inversion H12; try solve[
       match goal with
         |H:?x=?s++[?y]|- _ => destruct s; inversion H; invertListNeq
       end]. 
       {destruct s1'; inversion H18; subst. econstructor. assumption. 
        constructor. invertListNeq. } assumption. } 
      {destruct tid''. destruct p. inversion H10; subst. clear H10. 
       inversion H3; subst; try invertListNeq.
       {econstructor. econstructor. eapply Union_intror. econstructor. 
        reflexivity. econstructor. Focus 2. eassumption. destruct s1'. 
        inversion H18; subst. eapply x. eapply H3. econstructor. 
        assumption. assumption. inversion H18. invertListNeq. }
      }
     }
     {inversion H; subst. inversion H1; subst. inversion H8; subst. 
      {econstructor. econstructor. econstructor; eauto. reflexivity. 
       Focus 2. eassumption. apply z in H5. invertExists. eapply y. eassumption.
       assumption. inversion H9; subst; clear H9. inversion H3; subst. 
       {inversion H11; subst. 
        {destruct s1'. inversion H17; subst. clear H17. econstructor. 
         eapply x. Focus 2. eapply H11. eassumption. eassumption. 



econstructor. eapply x. Focus 2. eapply H11. eassumption. eassumption.   
        assert(actionIDs (tid', [rAct x0 tid'' M'], s2, M)). apply ConsistentIDs. 
        inversion H5; subst. econstructor. rewrite <- appNil. reflexivity.



       inversion H11; subst; try solve[
       match goal with
           |H:?x=?s++[?y] |- _ => destruct s; inversion H; invertListNeq
       end]. 
       {inversion H9; subst; clear H9. destruct s1'. inversion H17; subst. econstructor; eauto. auto. }
       {

admit. }
    }
    rewrite H. constructor. eapply eraseHeapRBRead; eauto. }
   {eapply IHrollback. admit. eapply eraseHeapRBRead; eauto. }
  }
  {destruct s1'. 
   {eapply IHrollback. admit. assumption. }
   {eapply IHrollback. admit. assumption. }
  }
  {destruct s1'. 
   {eapply IHrollback. admit. eapply eraseHeapRBWrite; eauto. }
   {eapply IHrollback. admit. eapply eraseHeapRBWrite; eauto. }
  }
  {destruct s1'. 
   {eapply IHrollback. admit. eapply eraseHeapRBNew; eauto. }
   {eapply IHrollback. admit. eapply eraseHeapRBNew; eauto. }
  }
  {destruct s1'. 
   {eapply IHrollback. admit. assumption. }
   {eapply IHrollback. admit. assumption. }
  }
Qed. 




    











