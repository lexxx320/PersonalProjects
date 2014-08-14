Require Export Spec. 
Require Export hetList. 

Inductive Spec : actionStack -> Prop :=
|lockSpec : forall s, Spec (locked s)
|unlockedSpec : forall a b, Spec(unlocked (a::b))
|specStackSpec : forall s N, Spec(specStack s N). 

Inductive prog_step : sHeap -> pool -> pool -> config -> Prop :=
|CBasicStep : forall t t' tid s2 h T,
               basic_step t t' -> 
               prog_step h T (tSingleton(tid,unlocked nil,s2,t)) (OK h T (tSingleton(tid,unlocked nil,s2,t')))
|CFork : forall tid h T M s2 E t n (d:decompose t E (fork M)), 
          n = (numForks' s2) ->
          prog_step h T (tSingleton (tid, unlocked nil, s2,t)) 
        (OK h T(tCouple (tid, unlocked nil, fAct t E M d n::s2, fill E(ret unit)) 
                        (n::tid, unlocked nil, nil, M)))
|CGet : forall TID h h' T N s2 E x ds writer t (d:decompose t E (get (fvar x))),
         heap_lookup x h = Some(sfull COMMIT ds COMMIT writer N) -> 
         h' = replace x (sfull COMMIT (TID::ds) COMMIT writer N) h ->
         prog_step h T (tSingleton (TID, unlocked nil, s2, t))
              (OK h' T (tSingleton (TID, unlocked nil, rAct x t E d::s2, fill E(ret N))))
|CPut : forall E x N h h' s2 TID T t (d:decompose t E (put (fvar x) N)), 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty COMMIT) ->
         h' = replace x (sfull COMMIT nil COMMIT TID N) h -> 
         prog_step h T (tSingleton (TID, unlocked nil, s2, t)) (OK h' T
              (tSingleton (TID, unlocked nil, wAct x t E N d::s2, fill E(ret unit))))
|COverwrite : forall t E x N N' h h' h'' T TR s1 TR' s2' M A s2 ds TID TID' (d:decompose t E (put (fvar x) N)), 
               heap_lookup x h = Some (sfull COMMIT ds SPEC TID' N') ->
               thread_lookup TR TID' (TID', s1,s2',M) -> errorWriteStack x s1 A -> 
               rollback TID' A h TR h' TR' -> heap_lookup x h' = Some(sempty COMMIT) ->
               h'' = replace x (sfull COMMIT nil COMMIT TID N) h' -> 
               prog_step h T (tAdd TR (TID, unlocked nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (TID, unlocked nil, wAct x t E N d::s2, fill E (ret unit))))
|CErrorWrite : forall h T t E x N N' tid tid' ds s2,  
                decompose t E (put (fvar x) N) ->
                heap_lookup x h = Some(sfull COMMIT ds COMMIT tid' N') ->
                prog_step h T (tSingleton (tid, unlocked nil, s2, t)) Error
|CNew : forall E h h' x tid t s2 T (d:decompose t E new)
              (p:heap_lookup x h = None),
         h' = Heap.extend x (sempty COMMIT) h p -> 
         prog_step h T (tSingleton (tid, unlocked nil, s2, fill E new)) 
              (OK h' T (tSingleton (tid, unlocked nil, nAct t E d x::s2, fill E(ret(fvar x)))))
|CSpec : forall E M t N tid s2 T h (d:decompose t E (spec M N)), 
          prog_step h T (tSingleton (tid, unlocked nil, s2, t)) (OK h T
               (tCouple (tid, unlocked nil, srAct t E M N d::s2,fill E (specRun M N)) 
                        (2::tid, specStack nil N, nil, N))) 
|CSpecJoin : forall t E M N0 N1 tid T h t1 t2 s1 s1' s2 s2' wf (p:decompose t E (specRun (ret N1) N0)),
              t1 = (tid,unlocked nil,s2, t) -> t2 = (2::tid,specStack s1 N0,s2',M) ->
              wf = decomposeWF t E (specRun (ret N1) N0) p ->
              s1' = (wrapActs s1 N1 E (specRun (ret N1) N0) wf) ->
              prog_step h T (tCouple t1 t2) 
                   (OK h T (tSingleton(2::tid,unlocked s1', s2', fill E (specJoin (ret N1) M)))) 
|CSpecRB : forall t E' h h' tid T T' E M' N0 s2 s1' s2' M'' t1 t2 TRB, 
            decompose t E' (specRun (raise E) N0) -> 
            t1 = (tid,unlocked nil,s2,t) -> t2 = (2::tid, specStack s1' N0,s2',M') -> 
            rollback (2::tid) (specStack nil N0) h (tAdd TRB t2) h' 
                     (tAdd T' (2::tid,specStack nil N0, s2', M'')) ->
            prog_step h T (tUnion TRB (tCouple t2 t1)) (OK h' T (tAdd T' (tid, unlocked nil, s2, fill E'(raise E))))
|CPopRead : forall TID t s1 s1' s2 M M' N T h x ds E d h' ds1 ds2, 
             s1 = unlocked (s1' ++ [rAct x M' E d]) -> ds = ds1 ++ [TID] ++ ds2 -> 
             ~ List.In TID ds2 -> heap_lookup x h = Some (sfull COMMIT ds COMMIT t N) ->
             h' = replace x (sfull COMMIT (ds1++ds2) COMMIT t N) h ->
             prog_step h T (tSingleton (TID, s1, s2, M)) 
                       (OK h' T (tSingleton (TID, unlocked s1', (rAct x M' E d)::s2, M)))
|CPopWrite : forall tid s1 s1' s2 M M' M'' T h h' x ds E d,
              s1 = unlocked (s1' ++ [wAct x M' E M'' d]) -> 
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
|CPopFork : forall h s1 s1' s2 tid M' M N T M'' E n d s1'', 
             s1 = unlocked(s1' ++ [fAct M' E M'' d n]) -> n = numForks' s2 ->
             prog_step h T (tCouple (tid, s1, s2, M) (n::tid, locked s1'', nil, N)) (OK h T 
                  (tCouple (tid, unlocked s1', fAct M' E M'' d n::s2, M)
                           (n::tid, unlocked s1'', nil, N)))
|CPopSpec : forall h s1 s1' s1'' s2 t tid M' M N T E d M'', 
             s1 = unlocked (s1' ++ [srAct t E M N d]) -> 
             prog_step h T (tCouple(tid, s1, s2, M')(2::tid,locked s1'',nil,M''))
                  (OK h T (tCouple(tid,unlocked s1',srAct t E M N d::s2,M')(2::tid,specStack s1'' N,nil,M'')))
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
         h' = Heap.extend x (sempty SPEC) h p ->
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


Ltac unfoldTac := 
  unfold tIn in *; unfold tUnion in *; unfold tSingleton in *; unfold tAdd in *; unfold tCouple in *.

Ltac invThreadEq := 
  match goal with
      |H:(?a,?b,?c,?d) = (?e,?f,?g,?h) |- _ => inv H
  end. 

Theorem monotonicActions : forall H tid H' T T' s1 s1' s2 s2' M M',
                             spec_multistep H T H' T' ->
                             tIn T (tid,s1,s2,M) -> tIn T' (tid,s1',s2',M') ->
                             alength s1 + length s2 <= alength s1' + length s2'. 
Proof.
  intros. genDeps{tid; s1; s1'; s2; s2'; M; M'}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,s1,s2,M)). econstructor. auto. 
   auto. assert(thread_lookup p2 tid (tid,s1',s2',M')). econstructor. auto. 
   auto. eapply uniqueThreadPool in H; eauto. inv H. omega. }
  {unfoldTac. invUnion. inv H1. 
   {assert(tIn (tUnion T t') (tid,s1,s2,M)). unfoldTac; invUnion. auto.
    eapply IHspec_multistep; eauto. }
   {inversion H; subst. 
    {inv H3. invThreadEq. eapply IHspec_multistep. invUnion. right. simpl; auto. eauto.
     inv H5. }
    {inv H3. invThreadEq. eapply IHspec_multistep in H2. Focus 2. invUnion. right. simpl. 
     left. eauto. destruct s1; simpl in *; omega. inv H1. }
    {inv H3. invThreadEq. eapply IHspec_multistep in H2. Focus 2. invUnion. right. simpl.
     eauto. destruct s1; simpl in *; omega. inv H4. }
    {inv H3. invThreadEq. eapply IHspec_multistep in H2. Focus 2. invUnion. right. simpl.
     eauto. destruct s1; simpl in *; omega. inv H4. }
    {inv H3. invThreadEq. eapply IHspec_multistep in H2. Focus 2. invUnion. right. simpl.
     eauto. destruct s1; simpl in *; omega. inv H1. }
    {inv H3. invThreadEq. eapply IHspec_multistep in H2. Focus 2. invUnion. right. simpl.
     eauto. destruct s1; simpl in *; omega. inv H1. }
   }
  }
Qed. 

Definition stackList s :=
  match s with
      |locked s' => s'
      |unlocked s' => s'
      |specStack s' N => s'
  end. 

Theorem consedActEq : forall H H' tid s1 s1' s1'' s1''' a b c s2 M M' T T',
                 spec_multistep H T H' T' -> tIn T (tid,s1,s2,M) -> tIn T' (tid,s1'',s2,M') ->
                 stackList s1 = s1'++[a;b] -> stackList s1'' = s1'''++[c;b] ->
                  a = c. 
Proof.
  intros. genDeps{s1';s1;s1'';s1''';s2;a;b;c;M;M';tid}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,s1,s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,s1'',s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. destruct s1; simpl in *; subst; 
   replace [a;b] with ([a]++[b]) in H4; auto; replace [c;b] with ([c]++[b]) in H4; auto; 
   repeat rewrite app_assoc in H4; apply app_inj_tail in H4; invertHyp; 
   apply lastElementEq in H; auto. }
  {unfoldTac; invUnion. inv H1. 
   {eapply IHspec_multistep; eauto. invUnion. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H5. inv H1. 
    {eapply IHspec_multistep; eauto. invUnion. right. simpl. eauto. }
    {eapply IHspec_multistep. Focus 2. eauto. Focus 2. invUnion. right. left. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {eapply IHspec_multistep. Focus 2. eauto. Focus 2. invUnion. right. left. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {eapply IHspec_multistep. Focus 2. eauto. Focus 2. invUnion. right. left. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {eapply IHspec_multistep. Focus 2. eauto. Focus 2. invUnion. right. left. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {eapply IHspec_multistep. Focus 2. eauto. Focus 2. invUnion. right. left. eauto. 
     eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {inv H. }
   }
  }
Qed.  

Theorem firstActEq : forall H H' tid s1 s1' a b s2 M M' T T' S S',
                 spec_multistep H T H' T' -> tIn T (tid,s1,s2,M) -> tIn T' (tid,s1',s2,M') ->
                 stackList s1 = S ++ [a] -> stackList s1' = S' ++ [b] ->
                  a = b. 
Proof.
  intros. genDeps{s1';s1;s2;a;b;S;S';M;M';tid}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,s1,s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,s1',s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. destruct s1; simpl in *; subst; 
   apply lastElementEq in H4; auto. }
  {unfoldTac. invUnion. inv H1. 
   {eapply IHspec_multistep; eauto. invUnion. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H5; try contradiction. inv H1. 
    {eapply IHspec_multistep;[idtac|idtac|eauto|eauto]. invUnion. right. simpl. eauto. 
     destruct s1; simpl in *; subst; eauto. }
    {eapply IHspec_multistep;[idtac|idtac|eauto|eauto]. invUnion. right. simpl. eauto. 
     destruct s1; simpl in *; subst; rewrite app_comm_cons; subst; eauto. }
    {eapply IHspec_multistep;[idtac|idtac|eauto|eauto]. invUnion. right. simpl. eauto. 
     destruct s1; simpl in *; subst; rewrite app_comm_cons; subst; eauto. }
    {eapply IHspec_multistep;[idtac|idtac|eauto|eauto]. invUnion. right. simpl. eauto. 
     destruct s1; simpl in *; subst; rewrite app_comm_cons; subst; eauto. }
    {eapply IHspec_multistep;[idtac|idtac|eauto|eauto]. invUnion. right. simpl. eauto. 
     destruct s1; simpl in *; subst; rewrite app_comm_cons; subst; eauto. }
    {eapply IHspec_multistep;[idtac|idtac|eauto|eauto]. invUnion. right. simpl. eauto. 
     destruct s1; simpl in *; subst; rewrite app_comm_cons; subst; eauto. }
   }
  }
Qed.  

Theorem nonEmptyStack : forall H H' tid s1 S S' s1' a b s2 M M' T T',
                 spec_multistep H T H' T' -> tIn T (tid,s1,s2,M) ->  tIn T' (tid,s1',s2,M') ->
                 stackList s1 = S ++ [a;b] -> stackList s1' = S' ++ [b] -> 
                 exists s, S' = s ++ [a]. 
Proof.
  intros. genDeps{s1';s1;s2;a;b;M;M';tid;S;S'}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,s1,s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,s1',s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. destruct s1; simpl in *; subst; 
   replace [a;b] with ([a]++[b]) in H4; auto; rewrite app_assoc in H4; 
   apply app_inj_tail in H4; invertHyp; eauto. }
  {unfoldTac. invUnion. inv H1. 
   {eapply IHspec_multistep; eauto. invUnion; eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H5; try contradiction. inv H1. 
    {eapply IHspec_multistep; eauto. invUnion. right. simpl; eauto. }
    {eapply IHspec_multistep. invUnion. right. simpl. left; eauto. Focus 2. 
     eauto. Focus 2. eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {eapply IHspec_multistep. invUnion. right. simpl. left; eauto. Focus 2. 
     eauto. Focus 2. eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {eapply IHspec_multistep. invUnion. right. simpl. left; eauto. Focus 2. 
     eauto. Focus 2. eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {eapply IHspec_multistep. invUnion. right. simpl. left; eauto. Focus 2. 
     eauto. Focus 2. eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
    {eapply IHspec_multistep. invUnion. right. simpl. left; eauto. Focus 2. 
     eauto. Focus 2. eauto. destruct s1; simpl in *; subst; rewrite app_comm_cons; eauto. }
   }
  }
Qed.  

Ltac solveSet := 
  unfoldTac; simpl;
  match goal with
      | |- In ?A (Union ?A ?T1 ?T2) ?x => invUnion;try solve[left; solveSet|right;solveSet]
      | |- ?a \/ ?b => try solve[left; solveSet|right; solveSet]
      |_ => eauto
  end. 

Ltac firstActTac H := eapply firstActEq in H;
                     [idtac|solveSet|solveSet|simpl;try rewrite app_nil_l; eauto|simpl;eauto].


Ltac heapsDisagree :=
  match goal with
      |H:heap_lookup ?x ?h = ?v, H':heap_lookup ?x ?h = ?v' |- _ => 
       solve[rewrite H in H'; inv H']
  end. 

Theorem spec_multistepWriteFull : forall x H H' T T' sc ds s t N N' s1 s2 tid E M M' M'' d,
                                    heap_lookup x H = Some(sfull sc ds s t N') ->
                                    spec_multistep H T H' T' -> tIn T (tid,unlocked nil,s2,M) ->
                                    tIn T' (tid,unlocked(s1++[wAct x M' E N d]), s2, M'') -> False. 
Proof.
  intros. genDeps{sc;ds;s;t;N;s2;M;M';M'';E;tid;s1;x}. induction H1; intros. 
  {assert(thread_lookup p2 tid (tid,unlocked nil, s2, M)). eauto. 
   assert(thread_lookup p2 tid (tid,unlocked(s1++[wAct x M' E N d]), s2, M'')). eauto. 
   eapply uniqueThreadPool in H; eauto. inv H. invertListNeq. }
  {unfoldTac; invUnion. inv H2.
   {eapply specStepFullIVar in H; eauto. invertHyp. eapply IHspec_multistep; eauto. 
    invUnion. eauto. }
   {copy H. apply specStepSingleton in H2. invertHyp. inv H4; try contradiction. inv H. 
    {eapply IHspec_multistep; eauto. invUnion; right; simpl; eauto. }
    {firstActTac H1. inv H1. }
    {firstActTac H1. inv H1. }
    {firstActTac H1. inv H1. rewrite H12 in H0. solveByInv. }
    {firstActTac H1. inv H1. }
    {firstActTac H1. inv H1. }
   }
  }
Qed. 

Ltac exMid a b := let n := fresh in
             assert(a=b\/a<>b) by apply classic; inv n.

Theorem specStepEmptyIVar : forall x H H' H'' T T' t t' M M' M'' N E d s s2 tid,
                              heap_lookup x H = Some(sempty COMMIT) -> 
                              spec_step H T (tSingleton t) H' T t' ->
                              spec_multistep H' (tUnion T t') H'' T' ->
                              tIn (tUnion T t') (tid, unlocked nil, s2, M) ->
                              tIn T' (tid, unlocked(s++[wAct x M' E N d]), s2, M'') -> 
                              heap_lookup x H' = Some(sempty COMMIT). 
Proof. 
  intros. inv H1; eauto. 
  {exMid x x0. 
   {heapsDisagree. }
   {rewrite lookupReplaceNeq; eauto. }
  }
  {exMid x x0. 
   {eapply spec_multistepWriteFull in H2; eauto. contradiction.
    erewrite HeapLookupReplace; eauto. }
   {rewrite lookupReplaceNeq; eauto. }
  }
  {exMid x x0. 
   {heapsDisagree. }
   {erewrite lookupExtendNeq; eauto. }
  }
Qed. 
 
Theorem smultiEmptyFull : forall H T H' T' x a b c d e,
                            spec_multistep H T H' T' ->
                            heap_lookup x H = Some(sfull a b c d e) ->
                            heap_lookup x H' = Some(sempty a) -> False. 
Proof.
  intros. genDeps{a; b; c; d; e}. induction H0; intros. 
  {rewrite H1 in H2. inv H2. }
  {inv H; eauto. 
   {exMid x x0. 
    {rewrite H3 in H1. inv H1. eapply IHspec_multistep; eauto. 
     erewrite HeapLookupReplace; eauto. }
    {eapply IHspec_multistep; eauto. rewrite lookupReplaceNeq; eauto. }
   }
   {exMid x x0. 
    {heapsDisagree. }
    {eapply IHspec_multistep; eauto. rewrite lookupReplaceNeq; eauto. }
   }
   {exMid x x0. 
    {heapsDisagree. }
    {eapply IHspec_multistep; eauto. erewrite lookupExtendNeq; eauto. }
   }
  }
Qed. 

Theorem specStepEmptyIVar' : forall x H H' H'' T T' t t' s,
                              heap_lookup x H = Some(sempty s) -> 
                              spec_step H T (tSingleton t) H' T t' ->
                              spec_multistep H' (tUnion T t') H'' T' ->
                              heap_lookup x H'' = Some(sempty s) ->
                              heap_lookup x H' = Some(sempty s). 
Proof. 
  intros. inv H1; eauto. 
  {exMid x x0. 
   {heapsDisagree. }
   {rewrite lookupReplaceNeq; eauto. }
  }
  {exMid x x0. 
   {eapply smultiEmptyFull in H2; eauto. contradiction. 
    erewrite HeapLookupReplace; eauto. rewrite H5 in H0. inv H0. eauto. }
   {rewrite lookupReplaceNeq; eauto. }
  }
  {exMid x x0. 
   {heapsDisagree. }
   {apply lookupExtendNeq; eauto. }
  }
Qed.  

Theorem specStepSomeIVar:  forall x H H' v T t t',
         spec_step H T t H' T t' ->
         heap_lookup x H = Some v ->
         exists v', heap_lookup x H' = Some v'. 
Proof. 
  intros. inversion H0; subst; try solve[econstructor; eauto]. 
  {exMid x x0. 
   {rewrite H1 in H2. inv H2. econstructor. eauto. erewrite HeapLookupReplace; eauto. }
   {rewrite lookupReplaceNeq; eauto. }
  }
  {exMid x x0. 
   {rewrite H2 in H1. inv H1. econstructor. erewrite HeapLookupReplace; eauto. }
   {rewrite lookupReplaceNeq; eauto. }
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
  {unfoldTac; invUnion. inv H2. 
   {eapply specStepSomeIVar in H; eauto. invertHyp. eapply IHspec_multistep; eauto. 
    invUnion. left; eauto. }
   {copy H. apply specStepSingleton in H2. invertHyp. inv H4. inv H. 
    {eapply IHspec_multistep; eauto. invUnion. right; simpl; eauto. }
    {firstActTac H1. inv H1. }
    {firstActTac H1. inv H1. }
    {firstActTac H1. inv H1. }
    {firstActTac H1. inv H1. heapsDisagree. }
    {firstActTac H1. inv H1. }
    {contradiction. }
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
  {exMid x x0. 
   {heapsDisagree. }
   {rewrite lookupReplaceNeq; eauto. }
  }
  {exMid x x0. 
   {heapsDisagree. }
   {rewrite lookupReplaceNeq; eauto. }
  }
  {exMid x x0. 
   {eapply spec_multistepNewSome in H2; eauto. 
    inv H2. rewrite lookupExtend. auto. }
   {erewrite <- lookupExtendNeq; eauto. }
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


