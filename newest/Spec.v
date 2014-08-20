Require Export NonSpec. 
Require Export Coq.Logic.Classical_Prop. 

(*Representation for specualtive heaps (see Heap.v for details)*)
Definition sHeap := heap (ivar_state).

Ltac cleanup :=
  match goal with
    |H:?x=?y |- _ => inversion H; subst; clear H
  end. 

Theorem decomposeEq : forall M E e, decompose M E e -> M = fill E e.
Proof.
  induction M; intros; try solve[inversion H; subst; auto];
  try solve[inversion H; subst; auto; simpl; apply IHM1 in H5; subst; auto].
  {inversion H; subst. apply IHM1 in H5. subst. auto. apply IHM2 in H6; subst; auto. }
  {inversion H; subst; auto. apply IHM1 in H5. subst. auto. apply IHM2 in H6; subst; auto. }
  {inversion H; subst; auto. apply IHM2 in H6; subst; auto. }
  {inversion H; subst; auto. apply IHM in H2; subst; auto. }
  {inversion H; subst; auto. apply IHM in H2. subst. auto. } 
Qed. 

Theorem uniqueCtxtDecomp : forall t E e E' e',
                             decompose t E e -> decompose t E' e' ->
                             E = E' /\ e = e'. 
Proof.
  induction t; intros; try solve[inversion H; inversion H0; subst; auto]; try solve[
  inversion H; inversion H0; subst; simpl in *; try contradiction; auto; 
   eapply IHt1 in H6; eauto; inversion H6; subst; auto].
  {inversion H; inversion H0; subst; auto; try contradiction. eapply IHt1 in H6; eauto. 
   inversion H6; subst; auto. eapply IHt2 in H7; eauto. inversion H7; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction. eapply IHt1 in H6; eauto. 
   inversion H6; subst; auto. eapply IHt2 in H7; eauto. inversion H7; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction. eapply IHt2 in H7; eauto. 
   inversion H7; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction. 
   eapply IHt in H3; eauto. 
   inversion H3; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction.
   eapply IHt in H3; eauto. 
   inversion H3; subst; auto. }
Qed. 

Open Scope type_scope. 
 
Definition thread := tid * actionStack * list action * trm. 
Definition pool := multiset thread.
Definition tAdd := Add thread. 
Definition tIn := In thread. 
Definition tUnion := Union thread. 
Definition tCouple := Couple thread. 
Definition tSingleton := Single thread. 
Definition tEmptySet := Empty_set thread. 
 
Inductive lastAct : actionStack -> actionStack -> action -> Prop :=
|lastLocked : forall s1 a, lastAct (locked (s1 ++ [a])) (locked s1) a
|lastUnlocked : forall s1 a, lastAct (unlocked (s1 ++ [a])) (unlocked s1) a. 

Definition aCons h tl :=
  match tl with
      |locked l => locked (h::l) 
      |unlocked l => unlocked (h::l)
      |specStack l M => specStack (h::l) M
  end. 

Inductive rollback : tid -> actionStack -> sHeap -> pool -> sHeap -> pool -> Prop :=
RBDone : forall T h M tid s1 s2 t1,
           tIn T t1 -> t1 = (tid, s1, s2, M) ->
           rollback (tid) s1 h T h T
|RBRead : forall s1 s1' s2 x TID TID' ds1 ds2 M M' N h h' h'' T T' sc t ds t1 SRoll E d, 
            s1 = aCons (rAct x M' E d) s1' -> ds = ds1 ++ [TID'] ++ ds2 -> ~ List.In TID' ds1 ->
            heap_lookup x h = Some (sfull sc ds SPEC t N) ->
            h' = replace x (sfull sc (ds1++ds2) SPEC t N) h -> 
            ~(tIn T t1) -> t1 = (TID', s1, s2, M) ->
            rollback TID SRoll h' (tAdd T (TID', s1', s2, M')) h'' T' ->
            rollback TID SRoll h (tAdd T t1) h'' T'
|RBFork : forall s1 s1' s2 s2' TID TID' M M' N T T' h h' t1 t2 SRoll E N' d n,
            s1 = aCons (fAct M' E N' d n) s1' ->  ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (TID', s1, s2, M) -> t2 = (n::TID', locked nil, s2', N) ->
            rollback TID SRoll h (tAdd T (TID', s1', s2, M')) h' T' ->
            rollback TID SRoll h (tUnion T (tCouple t1 t2)) h' T'
|RBWrite : forall s1 s1' s2 TID TID' M M' sc T T' h h' h'' x t1 SRoll E N' d,
             s1 = aCons (wAct x M' E N' d) s1' ->
             heap_lookup x h = Some(sfull sc nil SPEC TID' N') ->
             h' = replace x (sempty sc) h -> ~(tIn T t1) ->
             t1 = (TID', s1, s2, M) -> rollback TID SRoll h' (tAdd T (TID', s1', s2, M')) h'' T' ->
             rollback TID SRoll h (tAdd T t1) h'' T'
|RBNew : forall s1 s1' s2 TID TID' M M' T T' h h' h'' x t1 SRoll E d,
           s1 = aCons (nAct M' E d x) s1' -> decompose M' E new -> 
           heap_lookup x h = Some (sempty SPEC) ->
           h' = Heap.remove h x -> ~(tIn T t1) -> t1 = (TID', s1, s2, M) ->
           rollback TID SRoll h' (tAdd T (TID', s1', s2, M')) h'' T' ->
           rollback TID SRoll h (tAdd T t1) h'' T'
|RBSpec : forall s1 s1' s2 s2' TID TID' M M' M'' N'' N E T T' h h' t1 t2 SRoll d,
            s1 = aCons (srAct M' E M'' N'' d) s1' ->
            ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (TID', s1, s2, M) -> t2 = (2::TID', locked nil, s2', N) ->
            rollback TID SRoll h (tAdd T (TID', s1', s2, M')) h' T' ->
            rollback TID SRoll h (tUnion T (tCouple t1 t2)) h' T'
.

Hint Constructors rollback. 

(*Lookup a thread ID in a pool, yields a thread if a particular thread in the pool
**matches the specified thread ID up to the minor number*)
Inductive thread_lookup : pool -> tid -> thread -> Prop :=
|hit : forall T t tid s1 s2 M,
         tIn T t -> t = (tid, s1, s2, M) -> thread_lookup T tid t.

Hint Constructors thread_lookup. 

Inductive config : Type :=
|OK : sHeap -> pool -> pool -> config
|Error : config. 

Hint Constructors val. 

Inductive ctxtWF (e:trm) : ctxt -> Prop :=
|bindWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (bindCtxt E N)
|specWF : forall N E, ctxtWF e E -> ~val (fill E e) ->
                      ctxtWF e (specRunCtxt E N)
|specJoinWF : forall N E,ctxtWF e E -> val N -> ~val (fill E e) -> 
                         ctxtWF e (specJoinCtxt E N)
|handleWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (handleCtxt E N)
|appWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (appCtxt E N)
|appValWF : forall M E, ctxtWF e E -> val M -> ~val (fill E e) -> ctxtWF e (appValCtxt E M)
|pairWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (pairCtxt E N)
|pairValWF : forall M E, ctxtWF e E -> val M -> ~val (fill E e) -> 
                         ctxtWF e (pairValCtxt E M)
|fstWF : forall E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (fstCtxt E)
|sndWF : forall E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (sndCtxt E)
|holEWF : ctxtWF e holeCtxt. 

Theorem decomposeDecomposed : forall E e, ctxtWF e E ->
                                          decompose e holeCtxt e -> 
                                          decompose (fill E e) E e. 
Proof.
  intros. induction H; try solve[simpl; constructor; auto].
  {simpl. assumption. }
Qed. 

Hint Constructors ctxtWF. 

Theorem decomposeWF : forall t E e, decompose t E e -> ctxtWF e E. 
Proof.
  induction t; intros; try solve[inversion H]; 
  try solve[inversion H; subst; auto; copy H5; apply IHt1 in H5; constructor; auto; 
   apply decomposeEq in H0; subst; auto].
  {inversion H; subst. constructor. eauto. apply decomposeEq in H5; subst; auto. 
   constructor; auto. apply decomposeEq in H6; subst; auto. }
  {inversion H; subst. constructor; auto. apply decomposeEq in H5; subst; auto. 
   constructor; auto. apply decomposeEq in H6; subst; auto. constructor. }
  {inversion H; subst; auto. econstructor. apply IHt2; auto. apply decomposeEq in H6.
   subst. assumption. apply decomposeEq in H6; subst; auto. }
  {inversion H; subst; auto. constructor. apply IHt. auto. 
   apply decomposeEq in H2; subst; auto. }
  {inversion H; subst; auto. constructor. apply IHt. auto. 
   apply decomposeEq in H2; subst; auto. }
Qed. 

Fixpoint joinCtxts E1 E2 :=
  match E1 with
      | bindCtxt E M => bindCtxt (joinCtxts E E2) M
      | handleCtxt E M => handleCtxt (joinCtxts E E2) M
      | appCtxt E M => appCtxt (joinCtxts E E2) M
      | appValCtxt E M => appValCtxt (joinCtxts E E2) M
      | pairCtxt E M => pairCtxt (joinCtxts E E2) M
      | pairValCtxt E M => pairValCtxt (joinCtxts E E2) M
      | fstCtxt E => fstCtxt (joinCtxts E E2)
      | sndCtxt E => sndCtxt (joinCtxts E E2)
      | specRunCtxt E M => specRunCtxt (joinCtxts E E2) M
      | specJoinCtxt E M => specJoinCtxt (joinCtxts E E2) M
      | holeCtxt => E2
  end. 

Theorem notValFill : forall E e, ~ val e -> ~val (fill E e). 
Proof.
  induction E; intros; simpl; try solve[introsInv].
  {intros c. inv c. apply IHE in H. contradiction. }
  {intros c. inv c. apply IHE in H. contradiction. }
  {auto. }
Qed. 

Theorem decomposeNotVal : forall t E e, decompose t E e -> E <> holeCtxt -> ~val t. 
Proof.
  intros. induction H; try solve[introsInv].
  {intros c. inv c. contradiction. }
  {introsInv. contradiction. }
Qed. 

Theorem decomposeFurther : forall E E' e e' e'',
                                  ctxtWF e E -> decompose e' E' e'' -> ~ val e' ->
                                  decompose (fill E e') (joinCtxts E E') e''.
Proof.
  induction E; intros. 
  {simpl. constructor. inv H. eapply notValFill. auto. inv H. eapply IHE; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. constructor; eauto. apply notValFill; auto. }
  {inv H. simpl. auto. }
Qed. 

Theorem joinFill : forall E1 E2 e, fill (joinCtxts E1 E2) e = fill E1 (fill E2 e). 
Proof.
  induction E1; intros; try solve[simpl; rewrite IHE1; eauto]. 
  simpl. auto. 
Qed. 

Theorem wrapDecompose : forall t E e M, decompose t E e ->
                                        decompose (specJoin (ret M) t) (specJoinCtxt E (ret M)) e. 
Proof.
  intros. induction H; try solve[constructor; auto;[introsInv| constructor; auto]].
  constructor; auto. introsInv. contradiction. constructor; auto. constructor; auto. 
  introsInv. contradiction. constructor; auto. 
Qed. 

Theorem wrapDecompose' : forall E' t E e e' M, 
                           decompose t E e -> ctxtWF e' E' ->
                           decompose (fill E' (specJoin (ret M) t))
                                     (joinCtxts E' (specJoinCtxt E (ret M))) e.
Proof.
  induction E'; intros. 
  {inv H0. simpl. constructor. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {inv H0. simpl. constructor; auto. apply notValFill. introsInv. eapply IHE'; eauto. }
  {simpl. apply wrapDecompose. auto. }
Qed. 


Fixpoint wrapActs (acts : list action) (N:trm) E' e (p:ctxtWF e E') :=
  match acts with
      |rAct x M E d::acts' => 
       rAct x (fill E' (specJoin (ret N) M)) (joinCtxts E' (specJoinCtxt E (ret N)))
             (wrapDecompose' E' M E (get (fvar x)) e N d p)::wrapActs acts' N E' e p
      |wAct x M E M' d::acts' =>
       wAct x (fill E' (specJoin (ret N) M)) (joinCtxts E' (specJoinCtxt E (ret N))) M'
            (wrapDecompose' E' M E (put (fvar x) M') e N d p)::wrapActs acts' N E' e p
      |nAct M E d x::acts' =>
       nAct (fill E' (specJoin (ret N) M)) (joinCtxts E' (specJoinCtxt E (ret N))) 
            (wrapDecompose' E' M E new e N d p) x::wrapActs acts' N E' e p
      |fAct M E M' d n::acts' =>
       fAct (fill E' (specJoin (ret N) M)) (joinCtxts E' (specJoinCtxt E (ret N))) M'
            (wrapDecompose' E' M E (fork M') e N d p) n::wrapActs acts' N E' e p
      |srAct M E M' N' d::acts' =>
       srAct (fill E' (specJoin (ret N) M)) (joinCtxts E' (specJoinCtxt E (ret N))) M' N'
             (wrapDecompose' E' M E (spec M' N') e N d p)::wrapActs acts' N E' e p
      |nil => nil
  end. 

Inductive basic_step : trm -> trm -> Prop :=
|basicBeta : forall t E e N,  decompose t E (AST.app(lambda e) N) ->
                              basic_step t (fill E (open 0 N e))
|basicProjL : forall t E V1 V2,
                decompose t E (fst(pair_ V1 V2)) -> basic_step t (fill E V1)
|basicProjR : forall t E V1 V2,
                decompose t E (snd(pair_ V1 V2)) -> basic_step t (fill E V2)
|basicBind : forall t E M N,
               decompose t E (bind (ret M) N) -> basic_step t (fill E (AST.app N M))
|basicBindRaise : forall t E M N,
                    decompose t E (bind (raise M) N) -> basic_step t (fill E (raise M))
|basicHandle : forall t E M N,
                 decompose t E (handle (raise M) N) -> basic_step t (fill E (AST.app N M))
|basicHandleRet : forall t E M N,
                    decompose t E (handle (ret M) N) -> basic_step t (fill E (ret M))
|specJoinRaise : forall t E M N,
                   decompose t E (specJoin (ret M) (raise N)) ->
                   basic_step t (fill E (raise N))
|specJoinRet : forall t E M N,
                 decompose t E (specJoin (ret M) (ret N)) ->
                 basic_step t (fill E (ret (pair_ M  N))). 

Definition notIn T tid := ~(exists t, thread_lookup T tid t). 

Fixpoint numForks' s :=
  match s with
      |nil => 0
      |fAct t E M d n::ss => S(numForks' ss)
      |_::ss => numForks' ss
  end. 

Definition numForks s :=
  match s with
      |locked s => numForks' s
      |unlocked s => numForks' s
      |specStack s N => numForks' s
  end. 

Inductive errorWriteStack x : actionStack -> actionStack -> Prop :=
|errorWriteLocked : forall s1 t E M d s2,  
                      errorWriteStack x (locked(s1++[wAct x t E M d]++s2)) (locked s2)
|errorWriteUnlocked : forall s1 t E M d s2,
                        errorWriteStack x (unlocked(s1++[wAct x t E M d]++s2)) (locked s2)
|errorWriteSpecStack : forall s1 t E M d s2 N,
                         errorWriteStack x (specStack(s1++[wAct x t E M d]++s2)N) (specStack s2 N).

Inductive step : sHeap -> pool -> pool -> config -> Prop :=
|BasicStep : forall t t' tid s1 s2 h T,
               basic_step t t' -> step h T (tSingleton(tid,s1,s2,t)) (OK h T (tSingleton(tid,s1,s2,t')))
|Fork : forall tid h T M s1 s2 E t n (d:decompose t E (fork M)), 
          n = plus (numForks s1) (numForks' s2) ->
          step h T (tSingleton (tid, s1, s2,t)) 
        (OK h T(tCouple (tid, aCons (fAct t E M d n)s1, s2, fill E(ret unit)) 
                        (n::tid, locked nil, nil, M)))
|Get : forall TID h h' T N s1 s2 E x sc s ds writer t (d:decompose t E (get (fvar x))),
         heap_lookup x h = Some(sfull sc ds s writer N) -> 
         h' = replace x (sfull sc (TID::ds) s writer N) h ->
         step h T (tSingleton (TID, s1, s2, t))
              (OK h' T (tSingleton (TID, aCons (rAct x t E d) s1, s2, fill E(ret N))))
|Put : forall E x sc N h h' s1 s2 TID T t (d:decompose t E (put (fvar x) N)), 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil SPEC TID N) h -> 
         step h T (tSingleton (TID, s1, s2, t)) (OK h' T
              (tSingleton (TID, aCons(wAct x t E N d) s1, s2, fill E(ret unit))))
|Overwrite : forall t E x N N' h h' h'' T TR s1 TR' s2' M A s2 ds TID TID' (d:decompose t E (put (fvar x) N)), 
               heap_lookup x h = Some (sfull COMMIT ds SPEC TID' N') ->
               thread_lookup TR TID' (TID', s1,s2',M) -> errorWriteStack x s1 A -> 
               rollback TID' A h TR h' TR' -> heap_lookup x h' = Some(sempty COMMIT) ->
               h'' = replace x (sfull COMMIT nil SPEC TID N) h' -> 
               step h T (tAdd TR (TID, unlocked nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (TID, unlocked [wAct x t E N d], s2, fill E (ret unit))))
|ErrorWrite : forall h T t E x N N' tid tid' ds s2,  
                decompose t E (put (fvar x) N) ->
                heap_lookup x h = Some(sfull COMMIT ds COMMIT tid' N') ->
                step h T (tSingleton (tid, unlocked nil, s2, t)) Error
|New : forall E h h' x tid t s1 s2 T (d:decompose t E new)
              (p:heap_lookup x h = None),
         h' = Heap.extend x (sempty SPEC) h p -> 
         step h T (tSingleton (tid, s1, s2, fill E new)) 
              (OK h' T (tSingleton (tid, aCons (nAct t E d x) s1, s2, fill E(ret(fvar x)))))
|Spec : forall E M t N tid s1 s2 T h (d:decompose t E (spec M N)), 
          step h T (tSingleton (tid, s1, s2, t)) (OK h T
               (tCouple (tid, aCons (srAct t E M N d)s1, s2,fill E (specRun M N)) 
                        (2::tid, locked nil, nil, N))) 
|SpecJoin : forall t E M N0 N1 tid T h t1 t2 tid' s1 s1' s2 s2' wf (p:decompose t E (specRun (ret N1) N0)),
              t1 = (tid,unlocked nil,s2, t) -> t2 = (tid',specStack s1 N0,s2',M) ->
              wf = decomposeWF t E (specRun (ret N1) N0) p ->
              s1' = (wrapActs s1 N1 E (specRun (ret N1) N0) wf) ->
              step h T (tCouple t1 t2) 
                   (OK h T (tSingleton(tid',unlocked s1', s2', fill E (specJoin (ret N1) M)))) 
|SpecRB : forall t E' h h' tid T T' E M' tid' N0 s2 s1' s2' M'' t1 t2 TRB, 
            decompose t E' (specRun (raise E) N0) -> 
            t1 = (tid,unlocked nil,s2,t) -> t2 = (tid', specStack s1' N0,s2',M') -> 
            rollback tid' (specStack nil N0) h (tAdd TRB t2) h' 
                     (tAdd T' (tid',specStack nil N0, s2', M'')) ->
            step h T (tUnion TRB (tCouple t2 t1)) (OK h' T (tAdd T' (tid, unlocked nil, s2, fill E'(raise E))))
|PopRead : forall TID t s1 s1' s2 M M' N T h x ds E d h' ds1 ds2, 
             s1 = unlocked (s1' ++ [rAct x M' E d]) -> ds = ds1 ++ [TID] ++ ds2 -> 
             ~ List.In TID ds2 -> heap_lookup x h = Some (sfull COMMIT ds COMMIT t N) ->
             h' = replace x (sfull COMMIT (ds1++ds2) COMMIT t N) h ->
             step h T (tSingleton (TID, s1, s2, M)) (OK h' T (tSingleton (TID, unlocked s1', (rAct x M' E d)::s2, M)))
|PopWrite : forall tid s1 s1' s2 M M' M'' T h h' x ds E d,
              s1 = unlocked (s1' ++ [wAct x M' E M'' d]) -> 
              heap_lookup x h = Some(sfull COMMIT ds SPEC tid M'') ->
              h' = replace x (sfull COMMIT ds COMMIT tid M'') h -> 
              step h T (tSingleton (tid, s1, s2, M)) 
                   (OK h' T (tSingleton (tid, unlocked s1', (wAct x M' E M'' d)::s2, M)))
|PopNewFull : forall h h' s1 s1' s2 i tid M' ds t M N T E d, 
                s1 = unlocked(s1' ++ [nAct M' E d i]) -> 
                heap_lookup i h = Some(sfull SPEC ds SPEC t N) ->
                h' = replace i (sfull COMMIT ds SPEC t N) h -> 
                step h T (tSingleton (tid, s1, s2, M)) 
                     (OK h' T (tSingleton (tid, unlocked s1', nAct M' E d i::s2, M)))
|PopNewEmpty : forall h h' s1 s1' s2 i tid M' M T E d, 
                 s1 = unlocked(s1' ++ [nAct M' E d i]) -> heap_lookup i h = Some(sempty SPEC) ->
                  h' = replace i (sempty COMMIT) h -> 
                 step h T (tSingleton (tid, s1, s2, M))
                      (OK h' T (tSingleton (tid, unlocked s1', nAct M' E d i::s2, M)))
|PopFork : forall h s1 s1' s2 tid M' M N T M'' E n d s1'', 
             s1 = unlocked(s1' ++ [fAct M' E M'' d n]) -> n = numForks' s2 ->
             step h T (tCouple (tid, s1, s2, M) (n::tid, locked s1'', nil, N)) (OK h T 
                  (tCouple (tid, unlocked s1', fAct M' E M'' d n::s2, M)
                           (n::tid, unlocked s1'', nil, N)))
|PopSpec : forall h s1 s1' s1'' s2 t tid M' M N T E d M'', 
             s1 = unlocked (s1' ++ [srAct t E M N d]) -> 
             step h T (tCouple(tid, s1, s2, M')(2::tid,locked s1'',nil,M''))
                  (OK h T (tCouple(tid,unlocked s1',srAct t E M N d::s2,M')(2::tid,specStack s1'' N,nil,M'')))
.

Hint Constructors step. 

Inductive multistep : sHeap -> pool -> option (sHeap * pool) -> Prop :=
|multi_refl : forall H T, multistep H T (Some (H, T))
|multi_step : forall H H' c T t t',
                step H T t (OK H' T t') -> multistep H' (tUnion T t') c ->
                multistep H (tUnion T t) c
|smulti_error : forall H T t, 
                  step H T t Error -> multistep H (tUnion T t) None. 

Hint Constructors multistep. 

Theorem multi_trans : forall H T H' T' H'' T'',
                        multistep H T (Some(H', T')) -> 
                        multistep H' T' (Some(H'', T'')) ->
                        multistep H T (Some (H'', T'')). 
Proof.
  intros. depInd H0; eauto. 
Qed. 

(*------------------------------------Theorems------------------------------------*)

Theorem stepUnusedPool : forall t1 t2 t2' p1 h h', 
                           step h (tUnion t1 p1) t2 (OK h' (tUnion t1 p1) t2') <->
                           step h p1 t2 (OK h' p1 t2').
Proof.
  intros. split. 
  {intros. inversion H; eauto. }
  {intros. inversion H; eauto. }
Qed. 
