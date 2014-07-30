Require Import AST.   
Require Import NonSpec.   
Require Import Spec.  
Require Import Heap. 
Require Import sets. 
Require Import Coq.Sets.Ensembles. 
Require Import hetList.
Require Import Coq.Program.Equality.  

Inductive Spec : actionStack -> Prop :=
|lockSpec : forall s, Spec (locked s)
|unlockedSpec : forall a b, Spec(unlocked (a::b))
|specStackSpec : forall s N, Spec(specStack s N). 

Inductive prog_step : sHeap -> pool -> pool -> config -> Prop :=
|CBasicStep : forall tid s2 h T t t',
               basic_step t t' ->
               prog_step h T (tSingleton(tid,unlocked nil, s2,t))
                         (OK h T (tSingleton(tid,unlocked nil,s2,t')))
|CFork : forall tid h T M s2 E t (d:decompose t E (fork M)) n, 
          n = numForks' s2 ->
          prog_step h T (tSingleton (tid, (unlocked nil), s2,t)) 
        (OK h T(tCouple (tid, (unlocked nil), fAct t E M d n :: s2, fill E(ret unit)) 
                        (n::tid, (unlocked nil), [], M)))
|CGet : forall TID h h' T N s2 E x s sc ds writer t (d:decompose t E (get (fvar x))),
         heap_lookup x h = Some(sfull sc ds s writer N) -> 
         h' = replace x (sfull sc (TID::ds) s writer N) h ->
         prog_step h T (tSingleton (TID, (unlocked nil), s2, t))
              (OK h' T (tSingleton (TID, (unlocked nil), rAct x t E d::s2, fill E(ret N))))
|CPut : forall E x sc N h h' s2 TID T t (d:decompose t E (put (fvar x) N)), 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil COMMIT TID N) h -> 
         prog_step h T (tSingleton (TID, (unlocked nil), s2, t)) (OK h' T
              (tSingleton (TID, (unlocked nil), wAct x t E N d::s2, fill E(ret unit))))
|COverwrite : forall t E x N N' h h' h'' T s1 s2' M TR TR' S' A s2 ds TID TID' (d:decompose t E (put (fvar x) N)), 
               heap_lookup x h = Some (sfull COMMIT ds SPEC TID' N') ->
               thread_lookup TR TID' (TID',s1,s2',M) -> errorWriteStack x s1 A -> 
               rollback TID' (aCons S' A) h TR h' TR' ->
               h'' = replace x (sfull COMMIT nil COMMIT TID N) h' -> 
               prog_step h T (tAdd TR (TID, (unlocked nil), s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (TID, (unlocked nil), wAct x t E N d::s2, fill E (ret unit))))
|CNew : forall E h h' x tid t s2 T (d:decompose t E new) (p:heap_lookup x h = None),
         h' = extend x (sempty COMMIT) h p -> 
         prog_step h T (tSingleton (tid, (unlocked nil), s2, fill E new)) 
              (OK h' T (tSingleton (tid, (unlocked nil), nAct t E d x::s2, fill E(ret(fvar x)))))
|CSpec : forall E M t N tid s2 T h (d:decompose t E (spec M N)), 
          prog_step h T (tSingleton (tid, (unlocked nil), s2, t)) (OK h T
               (tCouple (tid, (unlocked nil), srAct t E M N d::s2,t) (2::tid, (unlocked nil), [], N))) 
|CSpecJoin : forall t E M N0 N1 tid T h t1 t2 s1 s1' s2 s2' wf (p:decompose t E (specRun (ret N1) N0)),
              t1 = (tid,unlocked nil,s2, t) -> t2 = (2::tid,specStack s1 N0,s2',M) ->
              wf = decomposeWF t E (specRun (ret N1) N0) p ->
              s1' = (wrapActs s1 N1 E (specRun (ret N1) N0) wf) ->
              prog_step h T (tCouple t1 t2) 
                   (OK h T (tSingleton(tid,unlocked s1', s2, fill E (specJoin (ret N1) M)))) 
|CSpecRB : forall t E' h h' tid T T' E M' N0 s2 s1 s2' t1 t2 TRB, 
            decompose t E' (specRun (raise E) N0)->
            t1 = (tid,(unlocked nil),s2,t) -> t2 = (2::tid,locked s1,s2',M') -> 
            ~ (exists p, thread_lookup TRB (tid) p) -> 
            thread_lookup TRB (2::tid) t2 -> 
            ~ (exists p', thread_lookup T' (2::tid) p') ->
            rollback (2::tid) (locked nil) h TRB h' T' ->
            prog_step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, (unlocked nil), s2, fill E'(raise E))))
|CSpecRaise : forall E' N h tid s2 T E t1 t,
               decompose t E' (specJoin(ret N)(raise E)) ->
               t1 = (tid, (unlocked nil), s2, t) -> 
               prog_step h T (tSingleton t1) 
                    (OK h T (tSingleton (tid, (unlocked nil), s2, fill E' (raise E))))
|CPopRead : forall TID t s1 s1' s2 M M' N T h x ds E d h' ds1 ds2, 
             s1 = unlocked (s1' ++ [rAct x M' E d]) -> ds = ds1 ++ [TID] ++ ds2 ->
             heap_lookup x h = Some (sfull COMMIT ds COMMIT t N) ->
             h' = replace x (sfull COMMIT (ds1++ds2) COMMIT t N) h ->
             prog_step h T (tSingleton (TID, s1, s2, M)) 
                       (OK h' T (tSingleton (TID, unlocked s1', (rAct x M' E d)::s2, M)))
|CPopWrite : forall tid s1 s1' s2 M M' M'' T h h' x ds E d,
              s1 = unlocked(s1' ++ [wAct x M' E M'' d]) -> 
              heap_lookup x h = Some(sfull COMMIT ds SPEC tid M'') ->
              h' = replace x (sfull COMMIT ds COMMIT tid M'') h -> 
              prog_step h T (tSingleton (tid, s1, s2, M))
                        (OK h' T (tSingleton (tid, unlocked s1', (wAct x M' E M'' d)::s2, M)))
|CPopNewFull : forall h h' s1 s1' s2 i tid M' ds t M N T E d, 
                s1 = unlocked(s1' ++ [nAct M' E d i]) ->
                heap_lookup i h = Some(sfull SPEC ds SPEC t N) ->
                h' = replace i (sfull COMMIT ds SPEC t N) h -> 
                prog_step h T (tSingleton (tid, s1, s2, M)) 
                          (OK h' T (tSingleton (tid, unlocked s1', nAct M' E d i::s2, M)))
|CPopNewEmpty : forall h h' s1 s1' s2 i tid M' M T E d, 
                 s1 = unlocked(s1' ++ [nAct M' E d i]) -> heap_lookup i h = Some(sempty SPEC) ->
                  h' = replace i (sempty COMMIT) h -> 
                 prog_step h T (tSingleton (tid, s1, s2, M))
                           (OK h' T (tSingleton (tid, unlocked s1', nAct M' E d i::s2, M)))
|CPopFork : forall h s1 s1' s1'' s2 s2' tid M' M N T M'' n E d, 
             s1 = unlocked(s1' ++ [fAct M' E M'' d n]) -> n = numForks' s2 ->
             prog_step h T (tCouple (tid, s1, s2, M) (n::tid, locked s1'', s2', N)) (OK h T 
                  (tCouple (tid, unlocked s1', fAct M' E M'' d n::s2, M)
                           (1::tid, unlocked s1'', s2', N)))
|CPopSpec : forall h s1 s1' s1'' s2 s2' t tid M' M N T E d M'', 
             s1 = unlocked (s1' ++ [srAct t E M N d]) -> 
             prog_step h T (tCouple(tid, s1, s2, M')(2::tid,locked s1'',s2',M''))
                  (OK h T (tCouple(tid,unlocked s1',srAct t E M N d::s2,M')(2::tid,specStack s1'' N,s2',M'')))
.

Inductive spec_step : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|SBasicStep : forall h T tid s1 s2 t t',
                basic_step t t' -> Spec s1 ->
                spec_step h T (tSingleton(tid,s1,s2,t)) h T (tSingleton(tid,s1,s2,t'))
|SFork : forall tid h T M b s2 E t (d:decompose t E (fork M)) n, 
           n = plus (numForks b) (numForks' s2) ->
          spec_step h T (tSingleton(tid, b, s2,t)) h T
               (tCouple (tid, aCons(fAct t E M d n) b, s2, fill E(ret unit)) (n::tid, locked nil, nil, M))
|SGet : forall TID h h' T N b s2 E x s ds writer sc t (d:decompose t E (get(fvar x))),
         heap_lookup x h = Some(sfull sc ds s writer N) -> 
         h' = replace x (sfull sc (TID::ds) s writer N) h ->
         spec_step h T (tSingleton(TID, b, s2, t)) h' T 
              (tSingleton (TID, aCons (rAct x t E d) b, s2, fill E(ret N)))
|SPut : forall E x N h sc h' b s2 TID T t (d:decompose t E (put (fvar x) N)), 
         heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil (SPEC) TID N) h ->
         spec_step h T (tSingleton(TID, b, s2, t)) h' T
              (tSingleton (TID, aCons (wAct x t E N d) b, s2, fill E(ret unit)))
|SNew : forall E h h' x tid t b s2 T (d:decompose t E new)
               (p:heap_lookup x h = None),
         h' = extend x (sempty SPEC) h p ->
         spec_step h T (tSingleton(tid, b, s2, t))h' T
              (tSingleton (tid, aCons (nAct t E d x) b, s2, fill E(ret(fvar x))))
|SSpec : forall E M t N tid b s2 T h (d:decompose t E (spec M N)), 
          spec_step h T (tSingleton(tid, b, s2, t)) h T
               (tCouple (tid, aCons (srAct t E M N d) b, s2,fill E(specRun M N))
                        (2::tid, locked nil, nil, N))

.

(*speculative steps cannot raise an error, so no need for config*)
Inductive spec_multistep : sHeap -> pool -> sHeap -> pool -> Prop :=
|smulti_refl : forall (h : sHeap) p2,
                 spec_multistep h p2 h p2
| smulti_step : forall T T' t t' h h' h'',
                  spec_step h T t h' T t' ->
                  spec_multistep h' (tUnion T t') h'' T' ->
                  spec_multistep h (tUnion T t) h'' T'. 


Theorem specStepSingleton : forall h t h' T t', 
                              spec_step h T t h' T t' -> 
                              exists t'', t = tSingleton t''. 
Proof.
  intros. inv H; eauto. Qed. 

Theorem specStepFullIVar:  forall x H H' ds tid M T t t' S sc,
         spec_step H T t H' T t' ->
         heap_lookup x H = Some(sfull sc ds S tid M) ->
         exists ds', heap_lookup x H' = 
                     Some(sfull sc ds' S tid M). 
Proof. 
  intros. inversion H0; subst; try solve[econstructor; eauto]. 
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H2 in H1. inv H1. 
    exists (TID::ds). erewrite HeapLookupReplace; eauto. }
   {rewrite lookupReplaceNeq. eauto. intros c. subst. apply beq_nat_false in eq. apply eq. 
    auto. }
  }
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H2 in H1. inv H1. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; auto. eauto. }
  }
  {destruct H; simpl in *. destruct h. 
   {inv H1. } 
   {assert(x<>x0). intros c. subst. rewrite p in H1. inv H1. 
    rewrite <- beq_nat_false_iff in H. rewrite H. exists ds. eassumption. }
  }
Qed.

Definition alength l :=
  match l with
      |locked l' => length l'
      |unlocked l' => length l'
      |specStack l' M => length l'
  end. 

Axiom uniqueThreadPool : forall T tid t t', 
                           thread_lookup T tid t -> thread_lookup T tid t' -> t = t'. 

Theorem monotonicActions : forall H tid H' T T' s1 s1' s2 s2' M M',
                             spec_multistep H T H' T' ->
                             tIn T (tid,s1,s2,M) -> tIn T' (tid,s1',s2',M') ->
                             alength s1 + length s2 <= alength s1' + length s2'. 
Proof.
  intros. genDeps{tid; s1; s1'; s2; s2'; M; M'}. dependent induction H0. 
  {intros. assert(thread_lookup p2 tid (tid,s1,s2,M)). econstructor. auto. 
   auto. assert(thread_lookup p2 tid (tid,s1',s2',M')). econstructor. auto. 
   auto. eapply uniqueThreadPool in H; eauto. inv H. omega. }
  {intros. inversion H1; subst. 
   {assert(tIn (tUnion T t') (tid,s1,s2,M)). constructor; auto. eapply IHspec_multistep in H4. 
    eauto. eauto. }
   {inversion H; subst. 
    {inv H3. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {inv H3. eapply IHspec_multistep in H2. Focus 2. apply Union_intror. constructor. 
     destruct s1; simpl in *; omega. }
    {inv H3. eapply IHspec_multistep in H2. Focus 2. apply Union_intror. constructor. 
     destruct s1; simpl in *; omega. }
    {inv H3. eapply IHspec_multistep in H2. Focus 2. apply Union_intror. constructor. 
     destruct s1; simpl in *; omega. }
    {inv H3. eapply IHspec_multistep in H2. Focus 2. apply Union_intror. constructor. 
     destruct s1; simpl in *; omega. }
    {inv H3. eapply IHspec_multistep in H2. Focus 2. apply Union_intror. constructor. 
     destruct s1; simpl in *; omega. }
   }
  }
Qed. 

Ltac unfoldTac := unfold tAdd in *; unfold Add in *; unfold tUnion in *; unfold tSingleton in *;
                  unfold tCouple in *. 

Theorem consedActEq : forall H H' tid s1 s1' a b c s2 M M' T T',
                 spec_multistep H T H' T' -> tIn T (tid,unlocked (s1++[a;b]),s2,M) -> 
                 tIn T' (tid,unlocked(s1'++[c;b]),s2,M') -> a = c. 
Proof.
  intros. genDeps{s1';s1;s2;a;b;c;M;M';tid}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,unlocked(s1++[a;b]),s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,unlocked(s1'++[c;b]),s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. replace [a;b] with ([a]++[b]) in H4; auto. 
   replace [c;b] with ([c]++[b]) in H4; auto. repeat rewrite app_assoc in H4. 
   apply app_inj_tail in H4. inv H4. apply lastElementEq in H. subst. auto. }
  {inv H1. 
   {eapply IHspec_multistep. constructor. eauto. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H3. inv H1. 
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep; eauto. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H5. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
   }
  }
Qed. 

Theorem lockedFirstActEq : forall H H' tid s1 s1' a c s2 M M' T T',
                 spec_multistep H T H' T' -> tIn T (tid,locked (s1++[a]),s2,M) -> 
                 tIn T' (tid,locked(s1'++[c]),s2,M') -> a = c. 
Proof.
  intros. genDeps{s1';s1;s2;a;c;M;M';tid}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,locked(s1++[a]),s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,locked(s1'++[c]),s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. eapply lastElementEq. eauto. }
  {inv H1. 
   {eapply IHspec_multistep. constructor. eauto. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H3. inv H1. 
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H5. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
   }
  }
Qed. 

Theorem firstActEq : forall H H' tid s1 s1' a c s2 M M' T T',
                 spec_multistep H T H' T' -> tIn T (tid,unlocked (s1++[a]),s2,M) -> 
                 tIn T' (tid,unlocked(s1'++[c]),s2,M') -> a = c. 
Proof.
  intros. genDeps{s1';s1;s2;a;c;M;M';tid}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,unlocked(s1++[a]),s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,unlocked(s1'++[c]),s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. apply lastElementEq in H4. subst. auto. }
  {inv H1. 
   {eapply IHspec_multistep. constructor. eauto. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H3. inv H1. 
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H5. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
   }
  }
Qed. 

Theorem firstSpecActEq : forall H H' tid s1 s1' a c s2 M M' T T' N,
                 spec_multistep H T H' T' -> tIn T (tid,specStack (s1++[a]) N,s2,M) -> 
                 tIn T' (tid,specStack(s1'++[c])N,s2,M') -> a = c. 
Proof.
  intros. genDeps{s1';s1;s2;a;c;M;M';tid}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,specStack(s1++[a]) N,s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,specStack(s1'++[c]) N,s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. apply lastElementEq in H4. subst. auto. }
  {inv H1. 
   {eapply IHspec_multistep. constructor. eauto. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H3. inv H1. 
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H5. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
   }
  }
Qed. 

Theorem spec_multistepWriteFull : forall x H H' T T' sc ds s t N N' s1 s2 tid E M M' M'' d,
                                    heap_lookup x H = Some(sfull sc ds s t N') ->
                                    spec_multistep H T H' T' -> tIn T (tid,unlocked nil,s2,M) ->
                                    tIn T' (tid,unlocked(s1++[wAct x M' E N d]), s2, M'') -> False. 
Proof.
  intros. genDeps{sc;ds;s;t;N;s2;M;M';M'';E;tid;s1;x}. induction H1; intros. 
  {assert(thread_lookup p2 tid (tid,unlocked nil, s2, M)). eauto. 
   assert(thread_lookup p2 tid (tid,unlocked(s1++[wAct x M' E N d]), s2, M'')). eauto. 
   eapply uniqueThreadPool in H; eauto. inv H. invertListNeq. }
  {inv H2. 
   {eapply specStepFullIVar in H; eauto. invertHyp. eapply IHspec_multistep; eauto. 
    constructor; eauto. }
   {copy H. apply specStepSingleton in H2. invertHyp. inv H4. inv H. 
    {unfoldTac; invertHyp. inv H2. eapply IHspec_multistep; eauto. apply Union_intror. 
     constructor. }
    {unfoldTac; invertHyp. inv H2.  eapply firstActEq in H1. Focus 2. apply Union_intror. 
     rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. }
    {unfoldTac; invertHyp. inv H2. eapply firstActEq in H1. Focus 2. apply Union_intror. 
     rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. }
    {unfoldTac; invertHyp. inv H2. eapply firstActEq in H1. Focus 2. apply Union_intror. 
     rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. rewrite H0 in H4. inv H4. }
    {unfoldTac; invertHyp. inv H2. eapply firstActEq in H1. Focus 2. apply Union_intror. 
     rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. }
    {unfoldTac; invertHyp. inv H6. eapply firstActEq in H1. Focus 2. apply Union_intror. 
    rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. }
   }
  }
Qed. 

Theorem specStepEmptyIVar : forall x H H' H'' T T' t t' M M' M'' N E d s s2 tid,
                              heap_lookup x H = Some(sempty COMMIT) -> 
                              spec_step H T (tSingleton t) H' T t' ->
                              spec_multistep H' (tUnion T t') H'' T' ->
                              tIn (tUnion T t') (tid, unlocked nil, s2, M) ->
                              tIn T' (tid, unlocked(s++[wAct x M' E N d]), s2, M'') -> 
                              heap_lookup x H' = Some(sempty COMMIT). 
Proof. 
  intros. inv H1; eauto. 
  {unfold tSingleton in *; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H6 in H0. inv H0. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. }
  }
  {unfold tSingleton in *; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. eapply spec_multistepWriteFull in H2; eauto. 
    inv H2. erewrite HeapLookupReplace; eauto. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. }
  }
  {unfold tSingleton in *; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. copy p. rewrite H0 in H1. inv H1. }
   {apply beq_nat_false in eq. apply lookupExtendNeq; auto. }
  }
Qed. 

Theorem specStepSomeIVar:  forall x H H' v T t t',
         spec_step H T t H' T t' ->
         heap_lookup x H = Some v ->
         exists v', heap_lookup x H' = Some v'. 
Proof. 
  intros. inversion H0; subst; try solve[econstructor; eauto]. 
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H1 in H2. inv H2. 
    econstructor. eauto. erewrite HeapLookupReplace; eauto. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. }
  }
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H2 in H1. inv H1. econstructor. 
    erewrite HeapLookupReplace; eauto. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. }
  }
  {destruct H; simpl in *. destruct h. 
   {inv H1. } 
   {assert(x<>x0). intros c. subst. rewrite p in H1. inv H1. 
    rewrite <- beq_nat_false_iff in H. rewrite H. econstructor. eauto. }
  }
Qed.

Theorem spec_multistepNewSome : forall x H H' T T' v s1 s2 tid E M M' M'' d,
                                    heap_lookup x H = Some v ->
                                    spec_multistep H T H' T' -> tIn T (tid,unlocked nil,s2,M) ->
                                    tIn T' (tid,unlocked(s1++[nAct M' E d x]), s2, M'') -> False. 
Proof.
  intros. genDeps{s2;M;M';M'';E;tid;s1;x; v}. induction H1; intros. 
  {assert(thread_lookup p2 tid (tid,unlocked nil, s2, M)). eauto. 
   assert(thread_lookup p2 tid (tid,unlocked(s1++[nAct M' E d x]), s2, M'')). eauto. 
   eapply uniqueThreadPool in H; eauto. inv H. invertListNeq. }
  {inv H2. 
   {eapply specStepSomeIVar in H; eauto. invertHyp. eapply IHspec_multistep; eauto. 
    constructor; eauto. }
   {copy H. apply specStepSingleton in H2. invertHyp. inv H4. inv H. 
    {unfoldTac; invertHyp. inv H2. eapply IHspec_multistep; eauto. apply Union_intror. 
     constructor. }
    {unfoldTac; invertHyp. inv H2.  eapply firstActEq in H1. Focus 2. apply Union_intror. 
     rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. }
    {unfoldTac; invertHyp. inv H2. eapply firstActEq in H1. Focus 2. apply Union_intror. 
     rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. }
    {unfoldTac; invertHyp. inv H2. eapply firstActEq in H1. Focus 2. apply Union_intror. 
     rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. }
    {unfoldTac; invertHyp. inv H2. eapply firstActEq in H1. Focus 2. apply Union_intror. 
     rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. copy p. rewrite H in H0. 
     inv H0. }
    {unfoldTac; invertHyp. inv H6. eapply firstActEq in H1. Focus 2. apply Union_intror. 
    rewrite app_nil_l. constructor.  Focus 2. eauto. inv H1. }
   }
  }
Qed. 

Theorem specStepNoneIVar : forall x H H' H'' T T' t t' M M' M'' E d s s2 tid,
                              heap_lookup x H = None -> 
                              spec_step H T (tSingleton t) H' T t' ->
                              spec_multistep H' (tUnion T t') H'' T' ->
                              tIn (tUnion T t') (tid, unlocked nil, s2, M) ->
                              tIn T' (tid, unlocked(s++[nAct M' E d x]), s2, M'') -> 
                              heap_lookup x H' = None. 
Proof. 
  intros. inversion H1; subst; eauto. 
  {unfoldTac; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H6 in H0. inv H0. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. }
  }
  {unfold tSingleton in *; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H0 in H6. inv H6. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. }
  }
  {unfold tSingleton in *; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. eapply spec_multistepNewSome in H2; eauto. 
    inv H2. rewrite lookupExtend. auto. }
   {apply beq_nat_false in eq. erewrite <- lookupExtendNeq; eauto. }
  }
Qed. 


Theorem spec_multi_trans : forall H H' H'' T T' T'',
                        spec_multistep H T H' T' ->
                        spec_multistep H' T' H'' T'' ->
                        spec_multistep H T H'' T''.  
Proof.
  intros. genDeps {H''; T''}. induction H0; intros.  
  {auto. }
  {apply IHspec_multistep in H1. econstructor. eauto. auto. }
Qed. 


