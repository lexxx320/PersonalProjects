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


Ltac eraseThreadTac :=
  match goal with
      | |- eraseThread (?tid, [rAct ?x ?tid' ?M], ?s2, ?N) ?T ?m => eapply tEraseRead
      | |- eraseThread (?tid, [wAct ?x ?tid' ?M], ?s2, ?N) ?T ?m => eapply tEraseWrite
      | |- eraseThread (?tid, [cAct ?x ?tid' ?M], ?s2, ?N) ?T ?m => eapply tEraseNew
      | |- eraseThread (?tid, [fAct ?x ?tid' ?M], ?s2, ?N) ?T ?m => eapply tEraseFork
      | |- eraseThread (?tid, ?z++[rAct ?x ?tid' ?M], ?s2, ?N) ?T ?m => eapply tEraseRead
      | |- eraseThread (?tid, ?z++[wAct ?x ?tid' ?M], ?s2, ?N) ?T ?m => eapply tEraseWrite
      | |- eraseThread (?tid, ?z++[cAct ?x ?tid' ?M], ?s2, ?N) ?T ?m => eapply tEraseNew
      | |- eraseThread (?tid, ?z++[fAct ?x ?tid' ?M], ?s2, ?N) ?T ?m => eapply tEraseFork
  end. 

Theorem eraseLastAct : forall A s2 M M' T t i j j' l,
                         basicAction A M' j' ->
                         (eraseThread (Tid(i, j) l, [A], s2, M) T t <->
                         eraseThread (Tid(i, j') l, nil, s2, M') T t). 
Proof.
  intros. split; intros. 
  {inversion H0; subst; try solve[
            match goal with
              |H:[?A] = ?s++[?x], H':basicAction ?A ?M ?tid'|- _ => 
               destruct s; inversion H; subst; inversion H'; subst; constructor; auto;
               invertListNeq
            end].  
   {destruct s1'; inversion H7. subst. inversion H. destruct s1'; inversion H3. }
   {destruct s1'; inversion H7. subst. inversion H. destruct s1'; inversion H3. }
  }
  {Hint Resolve app_nil_l. inversion H0; subst; try invertListNeq.
   inversion H; eauto.  
  }
Qed. 

Hint Resolve app_comm_cons. 

Theorem eraseTwoActs : forall tid tid' A1 A2 As s2 M M' T t,
                         eraseThread (tid', (A1::A2::As), s2, M') T t <->
                         eraseThread (tid, (A2 :: As), s2, M) T t. 
Proof.
  intros. split; intros. 
  {inversion H; subst; match goal with
       |H:?A1::?A2::?As=?s++[?a] |- _ => apply listAlign in H; invertExists
        end; match goal with
               |H:?A::?As=?x++[?a] |- eraseThread(?t,?A::?As,?s2,?m) ?T ?M =>
                rewrite H; destruct t; destruct p
             end; eauto. 
  }
  {inversion H; subst; rewrite H6; eauto. }
Qed. 

Ltac copy H := 
  match type of H with
      |?x => assert(x) by assumption
  end. 

(*Helper theorems for reasoning about the erasure of heaps being rolled back*)
Theorem eraseHeapRBNew : forall H H' x S A,
                           eraseHeap H H' ->
                           Heap.heap_lookup x H = Some(sempty (S::A)) ->
                           eraseHeap (Heap.remove H x) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
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
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
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
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst. clear H1. inversion H0; subst. 
    econstructor. assumption. apply beq_nat_true in eq. subst. auto. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem appNil : forall (T:Type) (x:T), [x] = nil ++ [x]. 
Proof.
  intros. simpl. reflexivity. Qed. 

Theorem eraseTermDiffPool :  forall tid tid' T t'' P M M' s1 s2 a b N N', 
              eraseThread (tid', a::b::s1, s2, N') P t'' -> eraseThread (tid, b::s1, s2, N) P t'' ->
              (eraseTerm M (tAdd T (tid', a::b::s1, s2, N')) M' <->
              eraseTerm M (tAdd T (tid, b::s1, s2, N)) M'). 
Proof.
  intros. split; intros. 
  {remember(tAdd T (tid', a ::b::s1, s2, N')). generalize dependent T. 
   induction H1; eauto; intros.  
   {subst. inversion H2; subst. inversion H8; subst; clear H8. inversion H7; subst. 
    {econstructor. eapply IHeraseTerm1; eauto. reflexivity. eapply IHeraseTerm2; eauto. 
     econstructor. econstructor. eassumption. reflexivity. }
    {inversion H1; subst. clear H1. apply listAlign in H5. invertExists. 
     assert(actionIDs(tid, x ++ [sAct (Tid (maj, min'') tid0) M'], s4, N)). apply ConsistentIDs. 
     apply lastActionConsistent in H3. inversion H3; subst. 
     {econstructor. eapply IHeraseTerm1; eauto. reflexivity. eapply IHeraseTerm2; eauto. 
      econstructor. apply Union_intror. rewrite H1. econstructor. auto. }
     {assert(sAct (Tid (maj, min'') tid0) M'=sAct (Tid (maj, min'') tid0) M') by auto. 
      apply H6 in H4. inversion H4. }
    }
   }
  }
  {remember(tAdd T (tid, b :: s1, s2, N)). generalize dependent T. induction H1; auto. 
   {intros. subst. inversion H2; subst. inversion H7; subst. 
    {inversion H8; subst; clear H8. econstructor. eapply IHeraseTerm1; eauto. 
     reflexivity. eapply IHeraseTerm2; eauto. econstructor. econstructor. eauto. eauto. }
    {inversion H8; subst; clear H8. inversion H1; subst; clear H1. 
     assert(actionIDs(tid', a::s1'++[sAct(Tid(maj,min'')tid0)M'], s4, N')). apply ConsistentIDs. 
     rewrite app_comm_cons in H1. apply lastActionConsistent in H1. inversion H1; subst. 
     econstructor. eapply IHeraseTerm1; eauto. reflexivity. eapply IHeraseTerm2; eauto. 
     econstructor. apply Union_intror. rewrite H5. rewrite app_comm_cons. econstructor. 
     reflexivity. assert(sAct (Tid (maj, min'') tid0) M'=sAct (Tid (maj, min'') tid0) M') by auto. 
     apply H6 in H3. inversion H3. }
   }
  }
Qed. 

Theorem eraseThreadDiffPool : forall tid tid' T t'' P M M' s1 s2 a b N N', 
              eraseThread (tid', a::b::s1, s2, N') P t'' -> eraseThread (tid, b::s1, s2, N) P t'' ->
              (eraseThread M (tAdd T (tid', a::b::s1, s2, N')) M' <->
              eraseThread M (tAdd T (tid, b::s1, s2, N)) M'). 
Proof.
  intros. split; intros. 
  {inversion H1. 
   {constructor. subst. eapply eraseTermDiffPool; eauto. }
   {subst. eapply tEraseRead. reflexivity. eapply eraseTermDiffPool; eauto. eassumption. }
   {subst. eapply tEraseWrite. reflexivity. eapply eraseTermDiffPool; eauto. eassumption. }
   {subst. eapply tEraseNew. reflexivity. eapply eraseTermDiffPool; eauto. eauto. }
   {subst. eapply tEraseSpec. reflexivity. }
   {subst. eapply tEraseFork. reflexivity. eapply eraseTermDiffPool; eauto. eauto. }
   {subst. eapply tEraseSpecRet. reflexivity. eapply eraseTermDiffPool; eauto. eauto. }
   {subst. eapply tEraseCreatedSpec. reflexivity. }
  }
  {inversion H1; subst; eauto. 
   {econstructor. eapply eraseTermDiffPool; eauto. }
   {econstructor. reflexivity. eapply eraseTermDiffPool; eauto. eauto. }
   {eapply tEraseWrite; eauto. eapply eraseTermDiffPool; eauto. }
   {eapply tEraseNew; eauto. eapply eraseTermDiffPool; eauto. }
   {eapply tEraseFork; eauto. eapply eraseTermDiffPool; eauto. }
   {eapply tEraseSpecRet; eauto. eapply eraseTermDiffPool; eauto. }
  }
Qed. 

Theorem eraseTermStrengthen : forall s1 s2 t t' T tid a M, 
              (forall tid' M', a <> sAct tid' M') ->
              eraseTerm t (tAdd T (tid, s1++[a], s2, M)) t' ->
              eraseTerm t T t'.
Proof.
  intros. remember (tAdd T (tid, s1 ++ [a], s2, M)). induction H0; auto. 
  {subst. inversion H1; subst. inversion H7; subst. clear H7. inversion H6; subst. 
   {econstructor. eapply IHeraseTerm1; eauto. reflexivity. eapply IHeraseTerm2. reflexivity. 
    econstructor. eassumption. reflexivity. }
   {inversion H0; subst. apply lastElementEq in H4. unfold not in H. apply H in H4. inversion H4. }
  }
Qed. 

Theorem eraseTermStrengthenNil : forall t t' T tid s2 M,
                                   eraseTerm t (tAdd T (tid, nil, s2, M)) t' ->
                                   eraseTerm t T t'. 
Proof.
  intros. remember (tAdd T (tid, nil, s2, M)). induction H; auto. 
  {subst. inversion H2; subst. inversion H7; subst. 
   {econstructor. apply IHeraseTerm1. reflexivity. reflexivity. eapply IHeraseTerm2. 
    reflexivity. econstructor. eassumption. reflexivity. }
   {inversion H0; subst. invertListNeq. }
  }
Qed. 

Theorem eraseTermWeakening : forall t t' T T', 
                                 eraseTerm t T t' ->
                                 eraseTerm t (tAdd T T') t'.  
Proof.
  intros. induction H; eauto. 
  {inversion H2; subst. econstructor. eapply IHeraseTerm1. reflexivity. eapply IHeraseTerm2. 
   econstructor. econstructor. inversion H2. eassumption. reflexivity. }
Qed. 

Theorem eraseThreadStrengthenNil : forall t t' tid' T s2 M,
                                     eraseThread t (tAdd T (tid', nil, s2, M)) t' ->
                                     eraseThread t T t'.
Proof.
  intros. inversion H; subst. 
  {econstructor. eapply eraseTermStrengthenNil. eauto. }
  {econstructor. reflexivity. eapply eraseTermStrengthenNil. eauto. eauto. }
  {eapply tEraseWrite. reflexivity. eapply eraseTermStrengthenNil. eauto. eauto. }
  {eapply tEraseNew. reflexivity. eapply eraseTermStrengthenNil. eauto. eauto. }
  {eapply tEraseSpec. reflexivity. }
  {eapply tEraseFork. reflexivity. eapply eraseTermStrengthenNil. eauto. eauto. }
  {eapply tEraseSpecRet. reflexivity. eapply eraseTermStrengthenNil. eauto. eauto. }
  {eapply tEraseCreatedSpec. reflexivity. }
Qed. 

Theorem eraseThreadStrengthen : forall t t' T tid' a s1 s2 M, 
              (forall tid M', a <> sAct tid M') ->
              eraseThread t (tAdd T (tid', s1 ++ [a], s2, M)) t' ->
              eraseThread t T t'. 
Proof.
  intros. inversion H0; subst; try solve[match goal with
       |H:eraseTerm ?M ?T ?M' |- _ => eapply eraseTermStrengthen in H; eauto
   end]. 
  {econstructor. reflexivity. }
  {eapply tEraseCreatedSpec. reflexivity. }
Qed. 

Theorem eraseThreadWeakening : forall t t' T T', 
                                 eraseThread t T t' ->
                                 eraseThread t (tAdd T T') t'. 
Proof.
  intros. inversion H; subst. 
  {econstructor. apply eraseTermWeakening. assumption. }
  {econstructor. reflexivity. apply eraseTermWeakening; eauto. eassumption. }
  {eapply tEraseWrite. reflexivity. apply eraseTermWeakening; eauto. eassumption. }
  {eapply tEraseNew; eauto. apply eraseTermWeakening; eauto. }
  {eapply tEraseSpec; eauto. }
  {eapply tEraseFork; eauto. apply eraseTermWeakening; eauto. }
  {eapply tEraseSpecRet; eauto. apply eraseTermWeakening; eauto. }
  {eapply tEraseCreatedSpec; eauto. }
Qed. 

Theorem eraseExists : forall T t T', 
                        erasePool (tAdd T t) T' -> exists t', eraseThread t (tAdd T t) t'. 
Proof.
  intros. eapply erasePoolEraseThread. eassumption. apply Union_intror. constructor. Qed. 

Theorem eraseBasicAction2 : forall a b s1' s2 M M' T i j l j',
                              basicAction a M' j' ->
                              erasePoolAux(tAdd T (Tid(i,j) l, a::b::s1', s2, M)) = 
                              erasePoolAux(tAdd T (Tid(i,j') l, b::s1', s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H5; subst; clear H5. inversion H4; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. 
    assert(exists y, erasePool (tAdd T (Tid (i, j) l, a :: b :: s1', s2, M)) y). eauto. invertExists. 
    apply eraseExists in H7. invertExists. eapply eraseThreadDiffPool. Focus 3. 
    eassumption. eassumption. eapply eraseTwoActs. eassumption. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. Focus 2. eassumption. inversion H5; subst; clear H5. inversion H; subst; 
    copy H2; apply eraseTwoActs with(tid0:= Tid(maj,j') tid) (M:=M')in H2; 
    eapply eraseThreadDiffPool; eauto. 
   }
  }
  {inversion H0; subst. inversion H1; subst. inversion H5; subst; clear H5. inversion H4; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. 
    assert(exists y, erasePool(tAdd T (Tid(i,j')l, b :: s1', s2, M')) y); eauto. invertExists. 
    apply eraseExists in H7. invertExists. eapply eraseThreadDiffPool. eapply eraseTwoActs. 
    eassumption. eassumption. eassumption. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H5; subst; clear H5. inversion H; subst; try solve[ 
         eapply eraseTwoActs; eapply eraseThreadDiffPool; [eapply eraseTwoActs; eauto|eauto|eauto]]. 
    assumption. }
  }
Qed. 

Theorem erasePoolCSpec : forall T tid s2 N l,
                           erasePoolAux(tAdd T (tid, l++[specAct], s2, N)) = erasePoolAux T. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros.  
  {inversion H; subst. inversion H0; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. eassumption. reflexivity. 
    apply eraseThreadStrengthen in H1. eassumption. intros. intros c. inversion c. auto. }
   {inversion H4; subst; clear H4. inversion H1; try invertListNeq. 
    {subst. inversion H2. }
   }
  }
  {inversion H; subst. inversion H0; subst. inversion H4; subst; clear H4. econstructor. 
   econstructor. econstructor. eassumption. reflexivity. eapply eraseThreadWeakening.
   eassumption. eassumption. }
Qed. 
  
Theorem eraseBasicAction1 : forall a M M' s2 i j j' l T,
                               basicAction a M' j' ->
                               erasePoolAux(tAdd T (Tid(i,j)l, [a], s2, M)) = 
                               erasePoolAux(tAdd T (Tid(i,j')l, nil, s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H5; subst; clear H5. inversion H4; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. 
    rewrite appNil in H2. eapply eraseThreadStrengthen in H2. apply eraseThreadWeakening. 
    eassumption. intros. intros c. inversion H; subst; inversion H7. assumption. }
   {econstructor. econstructor. eapply Union_intror. econstructor. 
    reflexivity. inversion H5; subst; clear H5. inversion H; subst;
    try solve[
    match goal with
         |H:eraseThread ?t ?T ?t' |- _ => 
           erewrite <- eraseLastAct; [idtac|eauto]; rewrite appNil in H;  eapply eraseThreadStrengthen in H;
           [eapply eraseThreadWeakening;eassumption|intros;intros c; inversion c];
           eapply eraseThreadWeakening 
     end]. auto.  
   }
  }
  {inversion H0; subst. inversion H1; subst. inversion H5; subst; clear H5. inversion H4; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. 
    apply eraseThreadStrengthenNil in H2. eapply eraseThreadWeakening. eassumption. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H5; subst; clear H5. inversion H; subst;
    match goal with
         |H:eraseThread ?t ?T ?m |- eraseThread ?t' ?T' ?m' =>
          erewrite eraseLastAct;[idtac|eauto]; eapply eraseThreadStrengthenNil in H;
          apply eraseThreadWeakening; eauto
    end. auto. 
   }
  }
Qed. 
  
Theorem rollbackIdempotent : forall tid stack H T H' T' H'' T'', 
                               rollback tid stack H T H' T' -> 
                               eraseHeap H H'' -> erasePool T T'' ->
                               eraseHeap H' H'' /\ erasePool T' T''. 
Proof.
  intros. generalize dependent H''. generalize dependent T''.
  induction H0; intros; subst. {split; auto. }
  {destruct s1'. 
   {eapply IHrollback. inversion H6; subst. 
    erewrite eraseBasicAction1. econstructor. econstructor. eassumption. eapply eraseHeapRBRead; eauto. }
   {eapply IHrollback. inversion H6; subst. erewrite eraseBasicAction2. econstructor. 
    econstructor. eassumption. eapply eraseHeapRBRead; eauto. }
  }
  {destruct s1'. 
   {eapply IHrollback. inversion H6; subst. rewrite appNil with (x:=specAct). rewrite erasePoolCSpec. 
    erewrite eraseBasicAction1; eauto. econstructor. eauto. assumption. }
   {eapply IHrollback. inversion H6; subst. rewrite appNil. rewrite erasePoolCSpec. 
    erewrite eraseBasicAction2; eauto. econstructor. eassumption. assumption. }
  }
  {destruct s1'. 
   {eapply IHrollback. inversion H6; subst. erewrite eraseBasicAction1. 
    econstructor. econstructor. eassumption. eapply eraseHeapRBWrite; eauto. }
   {eapply IHrollback. inversion H6; subst. erewrite eraseBasicAction2; eauto. 
    econstructor. eassumption. eapply eraseHeapRBWrite; eauto. }
  }
  {destruct s1'. 
   {eapply IHrollback. inversion H6; subst. erewrite eraseBasicAction1. 
    econstructor. econstructor. eassumption. eapply eraseHeapRBNew; eauto. }
   {eapply IHrollback. inversion H6; subst. erewrite eraseBasicAction2; eauto. 
    econstructor. eassumption. eapply eraseHeapRBNew; eauto. }
  }
  {destruct s1'. 
   {eapply IHrollback. inversion H6; subst. 
    replace [sAct tid2 N'; specAct] with ([sAct tid2 N']++[specAct]). rewrite erasePoolCSpec. 
    erewrite eraseBasicAction1. econstructor. econstructor. eassumption. auto. assumption. }
   {eapply IHrollback. inversion H6; subst. 
    replace [sAct tid2 N';specAct] with ([sAct tid2 N']++[specAct]). rewrite erasePoolCSpec. 
    erewrite eraseBasicAction2. econstructor. econstructor. eauto. auto. assumption. }
  }
Qed. 




    











