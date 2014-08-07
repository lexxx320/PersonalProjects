Require Export classifiedStep.  

Definition commit a :=
  match a with
      |unlocked nil => true
      |_ => false
  end. 

(*------------------------------------Unspec Definitions----------------------------*)
Fixpoint raw_unspecHeap (H : rawHeap ivar_state) :=
  match H with
      |(i, sempty COMMIT)::H' => (i, sempty COMMIT)::raw_unspecHeap H'
      |(i, sempty SPEC)::H' => raw_unspecHeap H'
      |(i, sfull SPEC a2 a3 a4 a5) :: H' => raw_unspecHeap H'
      |(i, sfull COMMIT a2 SPEC a4 a5) :: H' => (i, sempty COMMIT)::raw_unspecHeap H'
      |(i, sfull COMMIT a2 COMMIT a4 a5) :: H' => (i, sfull COMMIT nil COMMIT a4 a5)::raw_unspecHeap H'
      |nil => nil
  end. 

Hint Constructors unique. 

Theorem unspecUnique : forall h S,
                         unique ivar_state S h ->
                         unique ivar_state S (raw_unspecHeap h). 
Proof.
  induction h; intros; auto. simpl in *. destruct a. 
  destruct i0. 
  {destruct s. 
   {inv H. eapply uniqueSubset. apply IHh. eauto.  
    unfold Ensembles.Included. intros. constructor. auto. }
   {inv H. constructor. eauto. eauto. }
  }
  {destruct s. 
   {inv H. eapply uniqueSubset. eauto. unfold Ensembles.Included. intros. constructor. auto. }
   {destruct s0. 
    {inv H. constructor; auto. }
    {inv H. constructor; auto. }
   }
  }
Qed. 

Definition unspecHeap H := 
  match H with
      heap_ h' prf => heap_ (ivar_state) (raw_unspecHeap h') 
                            (unspecUnique h' (Ensembles.Empty_set AST.id) prf)
  end. 

Definition getTrm a :=
  match a with
      |rAct i t E d => t
      |wAct i t c M' d => t
      |nAct t c d i => t
      |fAct t c M' d n => t
      |srAct t c M' N d => t
  end. 

Definition unspecThread t :=
  match t with
      |(tid,unlocked nil, s2, M) => tSingleton (tid, unlocked nil, s2, M)
      |(tid,unlocked (a::b), s2, M) => tSingleton (tid, unlocked nil, s2, getTrm (last (a::b) a))
      |(tid, locked l, s2, M) => tEmptySet
      |(tid, specStack l N, s2, M) => tSingleton (tid, specStack nil N, s2, N)
  end. 

Fixpoint unspecPool T :=
  match T with
      |t::ts => tUnion (unspecThread t) (unspecPool ts)
      |nil => nil
  end. 

Inductive wellFormed : sHeap -> pool -> Prop :=
|wf : forall H T, spec_multistep (unspecHeap H) (unspecPool T) H T -> wellFormed H T.

Fixpoint commitPool (T:pool) : Prop :=
  match T with
      |(tid, unlocked nil, s2, M)::ts => commitPool ts
      |nil => True
      |_ => False
  end. 

Inductive actionTerm : action -> trm -> Prop :=
|basicRead : forall x t E d, actionTerm (rAct x t E d) t
|basicWrite : forall x t E M d, actionTerm (wAct x t E M d) t
|basicNew : forall x t E d, actionTerm (nAct t E d x) t
|basicFork : forall t E M d n, actionTerm (fAct t E M d n) t
|basicSR : forall t E M N d, actionTerm (srAct t E M N d) t. 

Hint Resolve app_comm_cons app_nil_l. 

(*---------------------------------Theorems---------------------------------------------*)

Theorem commitPoolUnspecUnchanged : forall T, commitPool T -> T = unspecPool T. 
Proof.
  induction T; intros. 
  {auto. }
  {simpl. unfoldTac. unfold Union. destruct a. destruct p. destruct p. destruct a. 
   {simpl in *. contradiction. }
   {simpl in *. destruct l0. simpl. rewrite <- IHT; auto. contradiction. }
   {simpl in *. contradiction. }
  }
Qed. 

Theorem unspecUnionComm : forall T1 T2, unspecPool (tUnion T1 T2) = 
                                        tUnion (unspecPool T1) (unspecPool T2).
Proof.
  induction T1; intros. 
  {simpl. auto. }
  {simpl. destruct a. destruct p. destruct p. destruct a. 
   {simpl. auto. }
   {destruct l0; simpl. rewrite IHT1. auto. rewrite <- IHT1. eauto. }
   {simpl. rewrite IHT1; eauto. }
  }
Qed. 

(*
Theorem LookupSame :
  forall P P', unspecPool P P' ->
               forall tid T, thread_lookup P' tid T ->
                             exists T', thread_lookup P tid T' /\ unspecThread T' (tSingleton T).
Proof.
  intros. inversion H; subst. inv H0. inv H1. inv H0. inv H4. inv H2; try solve[inv H3; eauto]. 
Qed. 
*)

Theorem raw_unspecHeapRBNew : forall H x,
                            raw_heap_lookup x H = Some(sempty SPEC) ->
                            raw_unspecHeap H = raw_unspecHeap (raw_remove H x). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct i0. 
   {destruct s.
    {destruct (beq_nat x i) eqn:eq; simpl; auto.  }
    {destruct (beq_nat x i). inv H0. simpl. erewrite IHlist; eauto. }
   }
   {destruct s. 
    {destruct (beq_nat x i); eauto. }
    {destruct s0. destruct (beq_nat x i); eauto. inv H0. simpl.
     erewrite IHlist; eauto. destruct (beq_nat x i). inv H0. 
     simpl. erewrite IHlist; eauto. }
   }
  }
Qed. 

(*---------------------Unspec Heap Equality Theorems-----------------------*)
Theorem unspecHeapRBNew : forall H x,
                            heap_lookup x H = Some(sempty SPEC) ->
                            unspecHeap H = unspecHeap (Heap.remove H x). 
Proof.
  intros. destruct H. simpl in *. eapply raw_unspecHeapRBNew in H0. 
  eapply rawHeapsEq; auto. 
Qed. 

Theorem raw_unspecHeapRBWrite : forall H x sc TID N,
                                  raw_heap_lookup x H = Some(sfull sc nil SPEC TID N) ->
                                  raw_unspecHeap (raw_replace x (sempty sc) H) = (raw_unspecHeap H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl in *. inv H0. destruct sc. auto. apply beq_nat_true in eq. subst; auto. }
   {simpl in *. erewrite IHlist; eauto. }
  }
Qed. 

Theorem unspecHeapRBWrite : forall H x sc TID N,
                              heap_lookup x H = Some(sfull sc nil SPEC TID N) ->
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
   {simpl. inv H0. apply beq_nat_true in eq. subst. destruct sc. auto. 
    destruct S; auto. }
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

Theorem raw_unspecUnspecHeap : forall H, raw_unspecHeap(raw_unspecHeap H) = raw_unspecHeap H. 
Proof.
  induction H; intros; auto. simpl. destruct a. destruct i0. 
  {destruct s; auto. simpl. rewrite IHlist; auto. }
  {destruct s; auto. destruct s0. simpl. rewrite IHlist; auto. simpl. 
   rewrite IHlist; auto. }
Qed. 

Theorem unspecUnspecHeap : forall H, unspecHeap(unspecHeap H) = unspecHeap H. 
Proof.
  intros. destruct H. apply rawHeapsEq. apply raw_unspecUnspecHeap. 
Qed. 

Theorem raw_unspecHeapCommitNewFull : forall H x S ds t N,
                 unique ivar_state S H ->                        
                 raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                 raw_unspecHeap(raw_replace x (sfull COMMIT ds SPEC t N) H) = 
                 raw_extend x (sempty COMMIT) (raw_unspecHeap H). 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. unfold raw_extend. simpl. auto. }
   {simpl. inv H0. erewrite IHlist; eauto. destruct i0. destruct s. auto. 
    unfold raw_extend. apply heapExtensionality. intros. simpl.
    destruct (beq_nat x0 i) eqn:eq1. apply beq_nat_true in eq1. subst. 
    rewrite beq_nat_sym in eq. rewrite eq. auto. destruct (beq_nat x0 x) eqn:eq2; auto. 
    destruct s; auto. destruct s0. unfold raw_extend. apply heapExtensionality. intros. 
    simpl. destruct (beq_nat x0 i) eqn:eq1. apply beq_nat_true in eq1. subst. 
    rewrite beq_nat_sym in eq. rewrite eq. auto. destruct (beq_nat x0 x); auto.
    unfold raw_extend. apply heapExtensionality. intros. simpl. destruct (beq_nat x0 i) eqn:eq1. 
    destruct (beq_nat x0 x) eqn:eq2. apply beq_nat_true in eq1. apply beq_nat_true in eq2.
    subst. rewrite eq2 in eq. apply beq_nat_false in eq. exfalso. apply eq. auto. auto. 
    destruct (beq_nat x0 x); auto. }
}
Qed. 

Theorem unspecHeapCommitNewFull : forall H x ds t N p,
                 heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                 unspecHeap(replace x (sfull COMMIT ds SPEC t N) H) = 
                 Heap.extend x (sempty COMMIT) (unspecHeap H) p. 
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq.
  eapply raw_unspecHeapCommitNewFull; eauto. 
Qed. 

Theorem raw_unspecHeapCommitCreateFull : forall H x ds tid M,
         raw_heap_lookup x H = Some(sfull COMMIT ds SPEC tid M) ->
         raw_unspecHeap (raw_replace x (sfull COMMIT ds COMMIT tid M) H) =
         raw_replace x (sfull COMMIT nil COMMIT tid M) (raw_unspecHeap H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {simpl. erewrite IHlist; eauto. destruct i0. destruct s. auto. simpl. rewrite eq. 
    auto. destruct s; auto. destruct s0; simpl; rewrite eq; auto. }
  }
Qed. 

Theorem unspecHeapCommitCreateFull : forall H x ds tid M,
         heap_lookup x H = Some(sfull COMMIT ds SPEC tid M) ->
         unspecHeap (replace x (sfull COMMIT ds COMMIT tid M) H) =
         replace x (sfull COMMIT nil COMMIT tid M) (unspecHeap H). 
Proof. intros. destruct H. simpl. apply rawHeapsEq. eapply raw_unspecHeapCommitCreateFull; eauto. 
Qed. 



(*----------------------Unspec Heap Lookup Theorems---------------------*)

Theorem raw_lookupUnspecFull : forall H x ds t N, 
                             raw_heap_lookup x H = Some(sfull COMMIT ds COMMIT t N) ->
                             raw_heap_lookup x (raw_unspecHeap H) =
                             Some(sfull COMMIT nil COMMIT t N).
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct s; eauto. simpl. rewrite eq. eauto. destruct s. eauto. 
    destruct s0. simpl. rewrite eq. eauto. simpl. rewrite eq; eauto. }
  }
Qed. 
 
Theorem lookupUnspecFull : forall H x ds t N, 
                             heap_lookup x H = Some(sfull COMMIT ds COMMIT t N) ->
                             heap_lookup x (unspecHeap H) = 
                             Some(sfull COMMIT nil COMMIT t N).
Proof.
  intros. destruct H. simpl. eapply raw_lookupUnspecFull; eauto.
Qed. 

Theorem raw_unspecHeapLookupFull : forall H  x a b c,
                                 raw_heap_lookup x H = Some(sfull COMMIT a COMMIT b c) ->
                                 raw_heap_lookup x (raw_unspecHeap H) = 
                                 Some(sfull COMMIT nil COMMIT b c).
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {apply IHlist in H0. destruct i0. destruct s; eauto. simpl. rewrite eq. eauto. 
    destruct s; eauto. destruct s0; eauto. simpl. rewrite eq. eauto. simpl. rewrite eq; eauto. }
  }
Qed. 

Theorem unspecHeapLookupFull : forall H x a b c,
                                 heap_lookup x H = Some(sfull COMMIT a COMMIT b c) ->
                                 heap_lookup x (unspecHeap H) = 
                                 Some(sfull COMMIT nil COMMIT b c).
Proof.
  intros. destruct H; simpl in *. eapply raw_unspecHeapLookupFull; eauto. 
Qed. 

Theorem raw_lookupUnspecEmpty : forall x H ds t N,
                              raw_heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                              raw_heap_lookup x (raw_unspecHeap H) = Some(sempty COMMIT). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct s; eauto. simpl. rewrite eq. eauto. destruct s. 
    eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 
Theorem lookupUnspecEmpty : forall x H ds t N,
                              heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                              heap_lookup x (unspecHeap H) = Some(sempty COMMIT). 
Proof.
  intros. destruct H; simpl. eapply raw_lookupUnspecEmpty; eauto. 
Qed. 

(*------Other Stuff--------*)

Theorem rollbackUnspeculatedHeap : forall H H' tid T T' S, 
                                     rollback tid S H T H' T' -> unspecHeap H = unspecHeap H'. 
Proof.
  intros. induction H0; auto. 
  {subst. erewrite unspecHeapRBRead in IHrollback; eauto. }
  {subst. erewrite <- unspecHeapRBWrite; eauto. }
  {subst. erewrite unspecHeapRBNew; eauto. }
Qed. 

Hint Resolve app_nil_l.

Theorem unspecLastAct : forall tid A s2 M M',
                         actionTerm A M' -> unspecThread(tid,unlocked[A],s2,M) = 
                                            unspecThread(tid,unlocked nil,s2,M').
Proof.
  intros. inv H; simpl; auto. 
Qed. 

Theorem unspecTwoActs : forall tid A1 As s2 M M',
                         unspecThread (tid, (aCons A1 As), s2, M')=unspecThread (tid, (aCons A1 As), s2, M). 
Proof.
  intros. destruct As; simpl; auto. 
Qed. 


Theorem getLastNonEmpty : forall (T:Type) b (a:T) c d, 
                            last(a::b) c = last(a::b) d. 
Proof.
  induction b; intros; auto. simpl in *. eauto. 
Qed. 

Theorem getLastNonEmpty' : forall (T:Type) b (a:T) e c d, 
                            last(a::b) c = last(e::a::b) d. 
Proof.
  induction b; intros; auto. simpl in *. eauto. 
Qed. 

Theorem unspecTwoActs' : forall tid A1 A2 As s2 M M',
                         unspecThread (tid, (aCons A1 (aCons A2 As)), s2, M') =
                         unspecThread (tid, (aCons A2 As), s2, M). 
Proof.
  intros. destruct As; simpl in *; auto. destruct l; auto. 
  erewrite getLastNonEmpty; eauto. 
Qed. 

(*
Theorem unspecSingleton : forall t t', 
                            unspecThread t t' ->
                            unspecPoolAux (tSingleton t) = t'.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inv H0. inv H1. inv H4. inv H0. eapply unspecDeterm in H2; eauto. subst. auto. }
  {destruct t. destruct p. destruct p. econstructor. econstructor. econstructor. 
   auto. eauto. auto. }
Qed. *)
  
Theorem specStepSingleton : forall H T t H' t', 
                              spec_step H T t H' T t' -> exists t'', t = tSingleton t''. 
Proof.
  intros. inv H0; eauto. Qed. 

Theorem raw_unspecHeapAddWrite : forall x sc H TID N,
                               raw_heap_lookup x H = Some(sempty sc) -> 
                               raw_unspecHeap (raw_replace x (sfull sc nil SPEC TID N) H) = 
                               raw_unspecHeap H. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl. inv H0. apply beq_nat_true in eq. subst. destruct sc; auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed. 

Theorem unspecHeapAddWrite : forall x sc H TID N,
                               heap_lookup x H = Some(sempty sc) -> 
                               unspecHeap (replace x (sfull sc nil SPEC TID N) H) = unspecHeap H. 
Proof.
  intros. destruct H. simpl in *. eapply raw_unspecHeapAddWrite in H0; eauto.
  apply rawHeapsEq; eauto. 
Qed. 

Theorem unspecHeapExtend : forall x H p,
     unspecHeap (Heap.extend x (sempty SPEC) H p) = unspecHeap H. 
Proof. 
  intros. destruct H; simpl in *. apply rawHeapsEq. auto. 
Qed. 

Ltac uCons a b := replace (unlocked (a::b)) with (aCons a (unlocked b)); auto. 

Theorem unspecSpecStep : forall H t H' T t', 
                           spec_step H T t H' T t' ->  
                           unspecHeap H = unspecHeap H' /\ unspecPool t' = unspecPool t. 
Proof.
  intros. inversion H0; subst.
  {split; eauto. inv H2; simpl; eauto. }
  {split; auto. destruct b; simpl; auto. destruct l; auto.
   erewrite getLastNonEmpty'. simpl. eauto. }
  {split. symmetry. eapply unspecHeapRBRead; eauto. destruct b; simpl; auto. 
   destruct l; auto. erewrite getLastNonEmpty'; simpl; eauto. }
  {split. symmetry. eapply unspecHeapAddWrite; eauto. destruct b; simpl; auto. 
   destruct l; auto. erewrite getLastNonEmpty'; simpl; eauto. }
  {split. symmetry. eapply unspecHeapExtend; eauto. destruct b; simpl; auto. 
   destruct l; auto. erewrite getLastNonEmpty'; simpl; eauto. }
  {split; auto. destruct b; simpl; auto. destruct l; auto. 
   erewrite getLastNonEmpty'; simpl; eauto. }
  Grab Existential Variables. auto. auto. auto. auto. auto. 
Qed. 

Theorem unspecSpecMultistep : forall H T H' T', 
                                spec_multistep H T H' T' -> 
                                unspecPool T = unspecPool T' /\ unspecHeap H = unspecHeap H'. 
Proof.
  intros. induction H0; intros. 
  {auto. }
  {eapply unspecSpecStep in H; eauto. invertHyp. split. 
   rewrite unspecUnionComm. rewrite <- H4. rewrite <- unspecUnionComm. 
   rewrite H1. auto. rewrite H3. rewrite H2. auto. }
Qed. 

Theorem rollbackIdempotent : forall tid stack H T H' T', 
                               rollback tid stack H T H' T' ->  unspecPool T = unspecPool T'.
Proof.
  intros. induction H0; subst. 
  {auto. }
  {rewrite <- IHrollback. destruct s1'; simpl; auto. destructLast l; simpl;auto. 
   invertHyp. 



inversion H1; subst. apply IHrollback. unfoldTac. rewrite unspecUnionComm in *. 
   destruct s1'. 
   {unfoldTac. rollbackIdemHelper. repeat erewrite unspecSingleton; simpl; eauto. rewrite H. 
    rewrite <- unspecUnionComm. constructor. }
   {destruct l. 
    {unfoldTac. simpl; erewrite unspecSingleton; eauto. rewrite <- unspecUnionComm. constructor.
     erewrite unspecSingleton; eauto. unspecThreadTac. rewrite app_nil_l. auto. }
    {erewrite unspecSingleton. rewrite <- unspecUnionComm. constructor. simpl.
     rollbackIdemHelper. invertHyp. erewrite unspecSingleton; eauto. uCons a l; auto.
     rewrite <- unspecTwoActs'. simpl. eauto. }
   }
   {unfoldTac. rollbackIdemHelper. erewrite unspecSingleton; eauto. simpl.  
    erewrite unspecSingleton; eauto. rewrite H. rewrite <- unspecUnionComm. constructor. }
  }
  {inv H1. apply IHrollback. unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm. 
   destruct s1'. 
   {simpl. repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_l. 
    rewrite union_empty_r. rollbackIdemHelper. rewrite unspecUnionComm. 
    erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. auto. 
    rewrite <- H. constructor. }
   {simpl. destruct l. 
    {repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. 
     rewrite <- unspecUnionComm. constructor. erewrite unspecSingleton; eauto.
     unspecThreadTac. rewrite app_nil_l. auto. }
    {repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. 
     rewrite <- unspecUnionComm. constructor. rollbackIdemHelper. invertHyp. 
     erewrite unspecSingleton; eauto. uCons a l; auto. rewrite  <- unspecTwoActs'. simpl. 
     eauto. }
   }
   {unfoldTac. rollbackIdemHelper. erewrite unspecSingleton; eauto. erewrite unspecSingleton; eauto. 
    rewrite union_empty_r. rewrite <- unspecUnionComm. constructor. simpl. 
    erewrite unspecSingleton; eauto. rewrite <- H. auto. } 
  }
  {inversion H1; subst. apply IHrollback. unfoldTac. rewrite unspecUnionComm in *. 
   destruct s1'. 
   {unfoldTac. rollbackIdemHelper. repeat erewrite unspecSingleton; simpl; eauto. rewrite H. 
    rewrite <- unspecUnionComm. constructor. }
   {destruct l. 
    {unfoldTac. simpl; erewrite unspecSingleton; eauto. rewrite <- unspecUnionComm. constructor.
     erewrite unspecSingleton; eauto. unspecThreadTac. rewrite app_nil_l. auto. }
    {erewrite unspecSingleton. rewrite <- unspecUnionComm. constructor. simpl.
     rollbackIdemHelper. invertHyp. erewrite unspecSingleton; eauto. uCons a l; auto.
     rewrite <- unspecTwoActs'. simpl. eauto. }
   }
   {unfoldTac. rollbackIdemHelper. erewrite unspecSingleton; eauto. simpl.  
    erewrite unspecSingleton; eauto. rewrite H. rewrite <- unspecUnionComm. constructor. } 
  }
  {inversion H1; subst. apply IHrollback. unfoldTac. rewrite unspecUnionComm in *. 
   destruct s1'. 
   {unfoldTac. rollbackIdemHelper. repeat erewrite unspecSingleton; simpl; eauto. rewrite H. 
    rewrite <- unspecUnionComm. constructor. }
   {destruct l. 
    {unfoldTac. simpl; erewrite unspecSingleton; eauto. rewrite <- unspecUnionComm. constructor.
     erewrite unspecSingleton; eauto. unspecThreadTac. rewrite app_nil_l. auto. }
    {erewrite unspecSingleton. rewrite <- unspecUnionComm. constructor. simpl.
     rollbackIdemHelper. invertHyp. erewrite unspecSingleton; eauto. uCons a l; auto.
     rewrite <- unspecTwoActs'. simpl. eauto. }
   }
   {unfoldTac. rollbackIdemHelper. erewrite unspecSingleton; eauto. simpl.  
    erewrite unspecSingleton; eauto. rewrite H. rewrite <- unspecUnionComm. constructor. } 
  }
  {inv H1. unfoldTac. apply IHrollback. rewrite coupleUnion. repeat rewrite unspecUnionComm. destruct s1'. 
   {simpl. repeat erewrite unspecSingleton; eauto. unfoldTac. repeat rewrite union_empty_r.
    rollbackIdemHelper. rewrite unspecUnionComm. erewrite unspecSingleton; eauto. unfoldTac. 
    rewrite union_empty_r; auto. rewrite <- H. constructor. }
   {simpl. destruct l. 
    {repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. 
     rewrite <- unspecUnionComm. constructor. erewrite unspecSingleton; eauto.
     unspecThreadTac. rewrite app_nil_l. auto. }
    {repeat erewrite unspecSingleton; eauto. unfoldTac. rewrite union_empty_r. 
     rewrite <- unspecUnionComm. constructor. rollbackIdemHelper. invertHyp. 
     erewrite unspecSingleton; eauto. uCons a l; auto. rewrite  <- unspecTwoActs'. simpl. 
     eauto. }
   }
   {unfoldTac. rollbackIdemHelper. erewrite unspecSingleton; eauto.
    erewrite unspecSingleton; eauto. rewrite union_empty_r. rewrite <- unspecUnionComm. 
    constructor. simpl. erewrite unspecSingleton; eauto. rewrite <- H. auto. }
  }
Qed. 


Theorem specStepChangeUnused : forall H T T' t t' H',
                                 spec_step H T t H' T t' ->
                                 spec_step H T' t H' T' t'. 
Proof.
  intros. Hint Constructors spec_step.  inversion H0; eauto. 
Qed. 

Require Import Coq.Sets.Powerset_facts. 
Require Import Coq.Program.Equality. 

Theorem spec_multi_unused : forall H T1 T2 T1' H', 
                              spec_multistep H (tUnion T1 T2) H' (tUnion T1' T2) <->
                              spec_multistep H T1 H' T1'.
Proof.
  intros. split; intros. 
  {dependent induction H0. 
   {admit. }
   {copy H. apply specStepSingleton in H. invertHyp. copy x. unfoldSetEq x. 
    assert(tIn(tUnion T (tSingleton x0)) x0). apply Union_intror. constructor. 
    apply H2 in H4. inv H4. 
    {apply pullOut in H5. rewrite H5. econstructor. eapply specStepChangeUnused; eauto. 
     eapply IHspec_multistep; eauto. admit. }
    {admit. }
   }
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



Ltac invThreadEq :=
  match goal with
      |H:(?a,?b,?c,?d) = (?e,?f,?g,?h) |- _ => inv H
  end. 

Theorem unspecUnspecPool : forall T, unspecPoolAux(unspecPoolAux T) = unspecPoolAux T. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. cleanup. 
   match goal with
       |H:thread_lookup (unspecPoolAux ?T) ?TID ?t |- _ =>
        assert(US:unspecPool T (unspecPoolAux T)) by constructor;
          eapply LookupSame with(tid:=TID) in US; inversion US as [EX1 EX2];
          inversion EX2; clear EX2
   end. Focus 2. eassumption. destruct EX1. destruct p. destruct p.
   copy H4. inv H4. inv H8. econstructor. eassumption. Focus 2. eauto. inv H1.
   {inv H5; auto; unspecThreadTac; auto. }
   {inv H5; try solve[invertHyp; unfoldTac; invertHyp;invThreadEq; invertListNeq].
    symmetry in H11; apply SingletonNeqEmpty in H11; solveByInv. }
   {inv H5; try solve[invertHyp; unfoldTac; invertHyp;invThreadEq; invertListNeq].
    symmetry in H11; apply SingletonNeqEmpty in H11; solveByInv. }
   {inv H5; try solve[invertHyp; unfoldTac; invertHyp;invThreadEq; invertListNeq].
    symmetry in H11; apply SingletonNeqEmpty in H11; solveByInv. }
   {inv H5; try solve[invertHyp; unfoldTac; invertHyp;invThreadEq; invertListNeq].
    symmetry in H11; apply SingletonNeqEmpty in H11; solveByInv. } 
   {inv H5; try solve[invertHyp; unfoldTac; invertHyp;invThreadEq; invertListNeq].
    symmetry in H11; apply SingletonNeqEmpty in H11; solveByInv. } 
   {inv H5; try solve[invertHyp; unfoldTac; invertHyp;invThreadEq; invertListNeq].
    symmetry in H11; apply SingletonNeqEmpty in H11; solveByInv. }
   {inv H5; try solve[invertHyp; unfoldTac; invertHyp;invThreadEq; invertListNeq].
    symmetry in H11; apply SingletonNeqEmpty in H11; solveByInv. 
    invertHyp. unfoldTac; invertHyp. invThreadEq. auto. }
  }
  {inv H. inv H1; inv H2. 
   {econstructor. econstructor. econstructor. eassumption. eauto. constructor. 
    auto. auto. constructor. } 
   {econstructor. econstructor. econstructor. eassumption. unspecThreadTac;
    eauto. constructor. auto. auto. constructor. }
   {econstructor. econstructor. econstructor. eassumption. unspecThreadTac;
    eauto. constructor. auto. auto. constructor. }
   {econstructor. econstructor. econstructor. eassumption. unspecThreadTac;
    eauto. constructor. auto. auto. constructor. }
   {econstructor. econstructor. econstructor. eassumption. unspecThreadTac;
    eauto. constructor. auto. auto. constructor. }
   {econstructor. econstructor. econstructor. eassumption. unspecThreadTac;
    eauto. constructor. auto. auto. constructor. }
   {econstructor. econstructor. econstructor. eassumption. constructor. constructor. 
    auto. constructor. constructor. }
  }
Qed. 