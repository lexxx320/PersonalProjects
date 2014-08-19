Require Import erasure.  
Require Import eraseRollbackIdempotent. 
Require Import NonSpecPureStep. 
Require Import stepWF. 
Require Import IndependenceCommon.

Hint Constructors pbasic_step. 

Theorem eraseLastAct : forall tid s a s2 M' M, 
                         actionTerm a M' ->
                         erasePool(tSingleton(tid,unlocked(s++[a]),s2,M)) = 
                         pSingle(eraseTerm M'). 
Proof.
  induction s; intros. 
  {simpl. inv H; auto. }
  {simpl. destruct (s++[a0])eqn:eq. 
   {invertListNeq. }
   {rewrite <- eq. rewrite getLastApp. inv H; auto. }
  }
Qed. 

Theorem eraseEraseTrm : forall tid s1 s2 M M', 
                          eraseTrm s1 M M' ->
                          erasePool(tSingleton(tid,unlocked s1,s2,M)) = (pSingle (eraseTerm M')). 
Proof.
  intros. destructLast s1. 
   {inv H; try invertListNeq. auto. }
   {invertHyp. inv H; try solve[invertListNeq]; apply lastElementEq in H1;
               subst; erewrite eraseLastAct; eauto; constructor. }
Qed. 

Theorem eEraseTrm : forall s1 M, exists M', eraseTrm s1 M M'. 
  intros. destructLast s1. 
  {econstructor. econstructor. }
  {invertHyp. destruct x; econstructor; econstructor. }
Qed. 

Ltac eraseTrmTac s1 M := assert(exists M', eraseTrm s1 M M') by apply eEraseTrm; invertHyp.             

Ltac consedActTac H :=
  eapply consedActEq in H;[idtac|solveSet|solveSet|rewrite app_nil_l; simpl;auto|
                           simpl; auto]. 

Theorem eraseTrmApp : forall x y M M',
                        eraseTrm(x++[y]) M M' -> actionTerm y M'. 
Proof.
  intros. inv H; try solve[invertListNeq]; 
  apply lastElementEq in H1; subst; constructor. 
Qed. 


Theorem simPureSteps : forall H H' H'' T T' PT s1 s2 tid M M' M'' a,
                eraseTrm s1 M' M'' ->
                spec_multistep H (tUnion T (tSingleton(tid,unlocked[a],s2,M)))
                               H' (tUnion T' (tSingleton(tid,unlocked(s1++[a]),s2,M'))) ->
                pmultistep H'' (pUnion PT (pSingle (eraseTerm M)))
                           (Some(H'', pUnion PT (pSingle (eraseTerm M'')))).
Proof.
  intros. dependent induction H1. 
  {apply UnionEqTID in x. invertHyp. inv H. destruct s1; inv H3. inv H0; try invertListNeq. 
   constructor. invertListNeq. }
  {startIndCase. destructThread x0. exMid H7 tid. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {eapply simBasicStep in H12. econstructor. eapply PBasicStep; eauto. 
     eapply IHspec_multistep; eauto. }
    {destructLast s1. 
     {eapply monotonicActions in H1; try solveSet. simpl in *; omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      apply eraseTrmApp in H0. inv H0. constructor. }
    }
    {destructLast s1. 
     {eapply monotonicActions in H1; try solveSet. simpl in *; omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      apply eraseTrmApp in H0. inv H0. constructor. }
    }
    {destructLast s1. 
     {eapply monotonicActions in H1; try solveSet. simpl in *; omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      apply eraseTrmApp in H0. inv H0. constructor. }
    }
    {destructLast s1. 
     {eapply monotonicActions in H1; try solveSet. simpl in *; omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      apply eraseTrmApp in H0. inv H0. constructor. }
    }
    {destructLast s1. 
     {eapply monotonicActions in H1; try solveSet. simpl in *; omega. }
     {invertHyp. rewrite <- app_assoc in H1. consedActTac H1. subst. 
      apply eraseTrmApp in H0. inv H0. constructor. }
    }
   }
   {apply UnionNeqTID in x; auto. invertHyp. copy H. eapply specSingleStepErase in H10; eauto. 
    invertHyp. eapply IHspec_multistep. eauto. Focus 2. eauto. rewrite H2. unfoldTac. 
    rewrite UnionSwap. eauto. }
  }
Qed. 

Theorem specStepRead : forall H H' TID x M ds M' E d s1' N t0 T T' s2,
   decompose M' E (get(fvar x)) -> 
   heap_lookup x H = Some(sfull COMMIT ds COMMIT t0 N) ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tSingleton(TID,unlocked(s1'++[rAct x M' E d]), s2, M))) ->
    exists H'' T'',
         spec_multistep H''
           (tUnion T''
              (tSingleton (TID, unlocked [rAct x M' E d], s2, fill E (ret N))))
           H' (tUnion T' (tSingleton (TID, unlocked (s1'++[rAct x M' E d]), s2, M))) /\
         eraseHeap H'' = eraseHeap H.
Proof.
  intros. generalize dependent ds. dependent induction H2; intros.
  {apply UnionEqTID in x. invertHyp. inv H2. invertListNeq. }
  {startIndCase. destructThread x1. exMid TID H9. 
   {apply UnionEqTID in x. invertHyp. inv H1; try solve[falseDecomp]. 
    {inv H15; falseDecomp. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H1; eauto. invertHyp. inv H7. 
     econstructor. econstructor. rewrite H15 in H3. inv H3. split. simpl in *. 
     proofsEq d d0. eassumption. erewrite eraseHeapDependentRead; eauto. }
   }
   {apply UnionNeqTID in x; auto. invertHyp. copy H1. eapply specStepFullIVar in H12; eauto. 
    invertHyp. eapply IHspec_multistep in H13; eauto. invertHyp. econstructor. 
    econstructor. split. eassumption. eapply specSingleStepErase in H1. invertHyp.
    rewrite H14. rewrite H15. auto. rewrite H4. unfoldTac. rewrite UnionSwap. eauto. }
  }
Qed. 

Theorem specStepWrite : forall H H' TID x M M' E ds s1' N T T' s2 t d,
   decompose M' E (put(fvar x) N) -> 
   heap_lookup x H = Some(sempty COMMIT) ->
   heap_lookup x H' = Some(sfull COMMIT ds SPEC t N) ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tSingleton(TID,unlocked(s1'++[wAct x M' E N d]), s2, M))) ->
    exists H'' T'',
         spec_multistep H''
           (tUnion T''
              (tSingleton (TID, unlocked [wAct x M' E N d], s2, fill E (ret unit))))
           H' (tUnion T' (tSingleton (TID, unlocked (s1'++[wAct x M' E N d]), s2, M))) /\
         eraseHeap H'' = eraseHeap H. 
Proof.
  intros. dependent induction H3; intros.
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x1. exMid TID H10. 
   {apply UnionEqTID in x. invertHyp. inv H4; try solve[falseDecomp]. 
    {inv H16; falseDecomp. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H4; eauto. invertHyp. inv H8. 
     proofsEq d d0. econstructor. econstructor. split. eassumption. 
     erewrite eraseHeapWrite; eauto. }
   }
   {apply UnionNeqTID in x; auto. invertHyp. copy H4. eapply specSingleStepErase in H4. 
    eapply specStepEmptyIVar in H13; eauto. invertHyp.
    eapply IHspec_multistep in H13; eauto. invertHyp. econstructor. econstructor. 
    split. eassumption. rewrite H16. auto. rewrite H5. unfoldTac. rewrite UnionSwap. 
    eauto. rewrite H5. solveSet. left. invUnion. right. simpl. auto. solveSet. }
  }
Qed. 

Ltac firstActTac H :=
       eapply firstActEq in H;[idtac|solveSet|solveSet
                               |rewrite app_nil_l; simpl; auto|simpl; auto]. 

Theorem specStepNewFull : forall H H' TID x M M' E ds s1' N T T' s2 t d,
   decompose M' E new -> 
   heap_lookup x H = None ->
   heap_lookup x H' = Some(sfull SPEC ds SPEC t N) ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]), s2, M))) ->
    exists H'' T'',
         spec_multistep H''
           (tUnion T''
              (tSingleton (TID, unlocked [nAct M' E d x], s2, fill E (ret (fvar x)))))
           H' (tUnion T' (tSingleton (TID, unlocked (s1'++[nAct M' E d x]), s2, M))) /\
         eraseHeap H'' = eraseHeap H.
Proof.
  intros. dependent induction H3; intros.
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x1. exMid TID H10. 
   {apply UnionEqTID in x. invertHyp. inv H4; try solve[falseDecomp]. 
    {inv H16; falseDecomp. }
    {copy d. copy d0. eapply uniqueCtxtDecomp in H4; eauto. invertHyp. proofsEq d d0. 
     exists (Heap.extend x (sempty SPEC) H p). econstructor. split. copy H3. 
     firstActTac H3. inv H3. eassumption. rewrite eraseHeapNew; eauto. }
   }
   {apply UnionNeqTID in x; auto. invertHyp. copy H4. eapply specSingleStepErase in H4. 
    eapply specStepNoneIVar in H13; eauto. eapply IHspec_multistep in H13; eauto. invertHyp. 
    econstructor. econstructor. split. eassumption. rewrite H15. auto. rewrite H5. 
    unfoldTac. rewrite UnionSwap. eauto. rewrite H5. solveSet. left. invUnion. right. simpl. 
    auto. solveSet. }
  }
Qed. 

Theorem specStepNewEmpty : forall H H' TID x M M' E s1' T T' s2 d,
   decompose M' E new ->
   heap_lookup x H = None ->
   heap_lookup x H' = Some(sempty SPEC) ->
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]), s2, M))) ->
    exists H'' T'',
         spec_multistep H''
           (tUnion T''
              (tSingleton (TID, unlocked [nAct M' E d x], s2, fill E (ret (fvar x)))))
           H' (tUnion T' (tSingleton (TID, unlocked (s1'++[nAct M' E d x]), s2, M))) /\
         eraseHeap H'' = eraseHeap H.
Proof.
  intros. dependent induction H3; intros.
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x1. exMid TID H10. 
   {apply UnionEqTID in x. invertHyp. inv H4; try solve[falseDecomp]. 
    {inv H16; falseDecomp. }
    {copy d. copy d0. eapply uniqueCtxtDecomp in H4; eauto. invertHyp. proofsEq d d0. 
     exists (Heap.extend x (sempty SPEC) H p). econstructor. split. copy H3. firstActTac H3. 
     inv H3. eassumption. erewrite eraseHeapNew; eauto. }
   }
   {apply UnionNeqTID in x; auto. invertHyp. copy H4. eapply specSingleStepErase in H4. 
    eapply specStepNoneIVar in H13; eauto. eapply IHspec_multistep in H13; eauto. invertHyp. 
    econstructor. econstructor. split. eassumption. rewrite H15. auto. rewrite H5. unfoldTac. 
    rewrite UnionSwap. eauto. rewrite H5. solveSet. left. invUnion. right. simpl. auto. solveSet. }
  }
Qed. 

Theorem eActTerm : forall a, exists M, actionTerm a M. 
Proof.
  intros. destruct a; repeat econstructor. 
Qed. 

Theorem eraseActTerm : forall tid s x s2 M M', 
                         actionTerm x M' ->
                         erasePool(tSingleton(tid,unlocked(s++[x]),s2,M)) =
                         (pSingle(eraseTerm M')).
Proof.
  intros. inv H; erewrite eraseLastAct; eauto; constructor. 
Qed. 

Fixpoint joinCtxts E1 E2 :=
  match E1 with
      |pbindCtxt E M => pbindCtxt (joinCtxts E E2) M
      | phandleCtxt E M => phandleCtxt (joinCtxts E E2) M
      | pappCtxt E M => pappCtxt (joinCtxts E E2) M
      | pappValCtxt E M => pappValCtxt (joinCtxts E E2) M
      | ppairCtxt E M => ppairCtxt (joinCtxts E E2) M
      | ppairValCtxt E M => ppairValCtxt (joinCtxts E E2) M
      | pfstCtxt E => pfstCtxt (joinCtxts E E2)
      | psndCtxt E => psndCtxt (joinCtxts E E2)
      | pspecRunCtxt E M => pspecRunCtxt (joinCtxts E E2) M
      | pspecJoinCtxt E M => pspecJoinCtxt (joinCtxts E E2) M
      | pholeCtxt => E2
  end. 

Theorem notPValPFill : forall E e, ~ pval e -> ~pval (pfill E e). 
Proof.
  induction E; intros; simpl; try solve[introsInv].
  {intros c. inv c. apply IHE in H. contradiction. }
  {intros c. inv c. apply IHE in H. contradiction. }
  {auto. }
Qed. 

Theorem pdecomposeNotPVal : forall t E e, pdecompose t E e -> E <> pholeCtxt -> ~pval t. 
Proof.
  intros. induction H; try solve[introsInv].
  {intros c. inv c. contradiction. }
  {introsInv. contradiction. }
Qed. 

Theorem pdecomposeFurther : forall E E' e e' e'',
                                  pctxtWF e E -> pdecompose e' E' e'' -> ~ pval e' ->
                                  pdecompose (pfill E e') (joinCtxts E E') e''.
Proof.
  induction E; intros. 
  {simpl. constructor. inv H. eapply notPValPFill. auto. inv H. eapply IHE; eauto. }
  {simpl. constructor. apply notPValPFill; auto. inv H. eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notPValPFill; eauto. }
  {simpl. auto. }
Qed. 


Theorem joinFill : forall E1 E2 e, pfill (joinCtxts E1 E2) e = pfill E1 (pfill E2 e). 
Proof.
  induction E1; intros; try solve[simpl; rewrite IHE1; eauto]. 
  simpl. auto. 
Qed. 

Ltac monoActs H :=
           eapply monotonicActions in H;[idtac|solveSet|solveSet]; eauto. 

Theorem simSpecJoinSteps : forall H H' e T T' N N0 N1 PT H'' M E s2 tid,
           pctxtWF e E ->
           spec_multistep H (tUnion T (tSingleton(tid,specStack nil N0, s2, N)))
                          H' (tUnion T' (tSingleton(tid,specStack nil N0, s2, M))) ->
           pmultistep H'' (pUnion PT (pSingle(pfill E (pspecJoin (pret N1) (eraseTerm N)))))
                      (Some(H'', pUnion PT (pSingle(pfill E (pspecJoin (pret N1) (eraseTerm M)))))).
Proof.
  intros. genDeps{E; e}. dependent induction H1; intros. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {startIndCase. destructThread x0. exMid H7 tid. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {apply simBasicStep in H12. inv H12. 
     {econstructor. eapply PBasicStep. eapply pbasicBeta. eapply pdecomposeFurther. 
      eauto. econstructor. constructor. Focus 2. eauto. Focus 2. introsInv. 
      apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. introsInv. 
      rewrite joinFill. simpl. rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicProjL. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. rewrite H. 
      eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicProjR. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicBind. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. 
      introsInv. eauto. introsInv.  rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicBindRaise. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicHandle. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicHandleRet. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pSpecJoinRaise. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pspecJoinDone. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H4. rewrite H4. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
    }
    {monoActs H1. simpl in *. omega. }
    {monoActs H1. simpl in *. omega. }
    {monoActs H1. simpl in *. omega. }
    {monoActs H1. simpl in *. omega. }
    {monoActs H1. simpl in *. omega. }
   }
   {apply UnionNeqTID in x. invertHyp. copy H. eapply specSingleStepErase in H10; eauto. invertHyp.
    eapply IHspec_multistep; eauto. rewrite H2. unfoldTac. rewrite UnionSwap. eauto. auto. }
  }
Qed.

Theorem simSpecJoinSteps' : forall H H' H'' e T T' PT s2 tid M M' s b M'' N1 E X,
                actionTerm b M'' -> pctxtWF e E -> 
                spec_multistep H (tUnion T (tSingleton(tid,specStack nil X,s2,M)))
                               H' (tUnion T' (tSingleton(tid,specStack(s++[b]) X,s2,M'))) ->
                pmultistep H'' (pUnion PT (pSingle (pfill E (pspecJoin (pret N1) (eraseTerm M)))))
                           (Some(H'', pUnion PT (pSingle (pfill E (pspecJoin (pret N1)(eraseTerm M'')))))).
Proof. 
  intros. genDeps{E; e}. dependent induction H2; intros. 
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x0. exMid tid H8. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {eapply simBasicStep in H14. inv H14. 
     {econstructor. eapply PBasicStep. eapply pbasicBeta. eapply pdecomposeFurther. 
      eauto. econstructor. constructor. Focus 2. eauto. Focus 2. introsInv.  
      apply pdecomposeEq in H5; subst. rewrite H5. apply notPValPFill. introsInv. 
      rewrite joinFill. simpl. rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicProjL. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H5. rewrite H5. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicProjR. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H5. rewrite H5. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicBind. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H5. rewrite H5. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicBindRaise. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H5. rewrite H5. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicHandle. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H5. rewrite H5. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pbasicHandleRet. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H5. rewrite H5. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pSpecJoinRaise. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H5. rewrite H5. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
     {econstructor. eapply PBasicStep. eapply pspecJoinDone. eapply pdecomposeFurther; eauto. 
      econstructor. constructor. apply pdecomposeEq in H5. rewrite H5. apply notPValPFill. 
      introsInv. eauto. introsInv. rewrite joinFill. simpl. 
      rewrite H. eapply IHspec_multistep; eauto. }
    }
    {firstActTac H2. subst. inv H0. constructor. }
    {firstActTac H2. subst. inv H0. constructor. }
    {firstActTac H2. subst. inv H0. constructor. }
    {firstActTac H2. subst. inv H0. constructor. }
    {firstActTac H2. subst. inv H0. constructor. }
   }
   {apply UnionNeqTID in x. invertHyp. copy H. eapply specSingleStepErase in H11; eauto. 
    invertHyp. eapply IHspec_multistep; eauto. rewrite H3. unfoldTac. 
    rewrite UnionSwap. eauto. auto. }
  }
Qed. 

Theorem wrapDistributeApp : forall s a N E e p, 
                              wrapActs(s++[a]) N E e p = wrapActs(s) N E e p++ wrapActs[a] N E e p.
Proof.
  induction s; intros. 
  {simpl. destruct a; auto. }
  {simpl. destruct a; auto; destruct a0; auto; rewrite IHs; auto. }
Qed. 

Theorem specStepFork : forall H H' TID M M' E s1' s1'' N T T' s2 n M'' d,
   decompose M' E (fork M'') -> 
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M')))
           H' (tUnion T' (tCouple(TID,unlocked(s1'++[fAct M' E M'' d n]), s2, M)
                                 (n::TID, locked s1'',nil, N))) ->
   exists H'' T'',
     spec_multistep H'' (tUnion T'' 
                                (tCouple (TID, unlocked[fAct M' E M'' d n], s2, fill E (ret unit))
                                         (n::TID, locked nil, nil, M'')))
                    H' (tUnion T' (tCouple(TID,unlocked(s1'++[fAct M' E M'' d n]), s2, M)
                                 (n::TID, locked s1'',nil, N))) /\ 
     eraseHeap H'' = eraseHeap H.
Proof.
  intros. dependent induction H1. 
  {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x.
   rewrite Union_associative in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x0. exMid TID H7. 
   {apply UnionEqTID in x. invertHyp. inv H; try solve[falseDecomp]. 
    {inv H13; falseDecomp. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H; eauto. invertHyp. inv H5. copy H1. 
     firstActTac H1. inv H1. proofsEq d d0. econstructor. econstructor. split; eauto. }
   }
   {apply UnionNeqTID in x. invertHyp. copy H. eapply specSingleStepErase in H10; eauto. 
    invertHyp. rewrite <- H12. eapply IHspec_multistep. eauto. rewrite H2. unfoldTac. 
    rewrite UnionSwap. eauto. eauto. auto. }
  }
Qed. 

Theorem simPureStepsCouple' : forall T' H H' H'' T PT s2 tid s1 M M' M'' N,
        eraseTrm s1 M' M'' -> 
        spec_multistep H (tUnion T (tSingleton(tid,locked[],s2,M)))
                       H' (tUnion T' (tSingleton(tid,locked(s1),s2,M'))) ->
        pmultistep H'' (pUnion PT (pCouple (eraseTerm M) N))
                   (Some (H'', pUnion PT (pCouple (eraseTerm M'') N))).
Proof.
  intros. dependent induction H1. 
  {apply UnionEqTID in x. invertHyp. inv H. inv H0; try invertListNeq. constructor. }
  {startIndCase. destructThread x0. exMid tid H7. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {apply simBasicStep in H13. unfold pUnion. rewrite pullOutL. 
     econstructor. eapply PBasicStep; eauto. unfold pUnion. rewrite <- pullOutL. eauto. }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *; omega. }
     {invertHyp. apply eraseTrmApp in H0. firstActTac H1. subst. inv H0. constructor. }
    }
   }
   {apply UnionNeqTID in x. invertHyp. eapply IHspec_multistep; eauto. rewrite H2. 
    unfoldTac. rewrite UnionSwap. eauto. auto. }
  }
Qed. 

Theorem simPureStepsCouple : forall T' H H' H'' T PT s2 tid s1 M M' a M'' N,
        eraseTrm s1 M' M'' -> 
        spec_multistep H (tUnion T (tSingleton(tid,unlocked[a],s2,M)))
                       H' (tUnion T' (tSingleton(tid,unlocked(s1++[a]),s2,M'))) ->
        pmultistep H'' (pUnion PT (pCouple (eraseTerm M) N))
                   (Some(H'', (pUnion PT (pCouple (eraseTerm M'') N)))).
Proof.
  intros. dependent induction H1. 
  {apply UnionEqTID in x. invertHyp. inv H. destruct s1. inv H3. inv H0; try invertListNeq. 
   constructor. simpl in *. inversion H3. invertListNeq. }
  {startIndCase. destructThread x0. exMid tid H7. 
   {apply UnionEqTID in x. invertHyp. inv H. 
    {apply simBasicStep in H13. unfold pUnion. rewrite pullOutL. 
     econstructor. eapply PBasicStep; eauto. unfold pUnion. rewrite <- pullOutL; eauto. }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *. omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. constructor. }
    }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *. omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. constructor. }
    }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *. omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. constructor. }
    }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *. omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. constructor. }
    }
    {destructLast s1. 
     {inv H0; try invertListNeq. monoActs H1. simpl in *. omega. }
     {invertHyp. apply eraseTrmApp in H0. consedActTac H1. Focus 2. rewrite <- app_assoc. 
      simpl. auto. subst. inv H0. constructor. }
    }
   }
   {apply UnionNeqTID in x; auto. invertHyp. eapply IHspec_multistep; eauto. 
    rewrite H2. unfoldTac. rewrite UnionSwap; eauto. }
  }
Qed. 

Theorem specStepSpec : forall H H' TID M M' E t s1' s1'' N T T' s2 s2' d M'',
   decompose t E (spec M N) -> 
   spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,t)))
           H' (tUnion T' (tCouple(TID,unlocked(s1'++[srAct t E M N d]), s2, M')
                                 (2::TID, locked s1'',s2', M''))) ->
   exists H'' T'',
     spec_multistep H'' (tUnion T'' 
                                (tCouple (TID, unlocked[srAct t E M N d], s2, fill E (specRun M N))
                                         (2::TID, locked nil, nil, N)))
                    H' (tUnion T' (tCouple(TID,unlocked(s1'++[srAct t E M N d]), s2, M')
                                 (2::TID, locked s1'',s2', M''))) /\ 
     eraseHeap H'' = eraseHeap H.
Proof.
  intros. dependent induction H1. 
  {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x.
   rewrite Union_associative in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x0. exMid TID H7. 
   {apply UnionEqTID in x. invertHyp. inv H; try solve[falseDecomp].  
    {inv H13; falseDecomp. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H; eauto. invertHyp. inv H5. 
     proofsEq d d0. econstructor. econstructor. split; eauto. }
   }
   {copy H. eapply specSingleStepErase in H2; eauto. invertHyp. 
    eapply IHspec_multistep in H0; eauto. invertHyp. econstructor. econstructor. 
    split. eauto. rewrite H11. eauto. apply UnionNeqTID in x. invertHyp. 
    rewrite H2. unfoldTac. rewrite UnionSwap. eauto. eauto. }
  }
Qed. 

Ltac actTermTac a := assert(exists M, actionTerm a M) by apply eActTerm; invertHyp.

Theorem eraseEmpty : forall tid s1 s2 M,
                       erasePool(tSingleton(tid,locked s1, s2, M)) = Empty_set ptrm. 
Proof.
  intros. simpl. auto. 
Qed. 

Theorem eraseEmptySpec : forall tid s1 N s2 M,
                       erasePool(tSingleton(tid,specStack s1 N, s2, M)) = Empty_set ptrm. 
Proof.
  intros. simpl. auto. 
Qed. 

Theorem eraseSingleton : forall t, 
                           erasePool(tSingleton t) = eraseThread t. 
Proof.
  intros. simpl. rewrite app_nil_r. auto.
Qed. 

Theorem eraseTwoActs' : forall a b c tid s2 M M',
                          actionTerm c M' ->
                          erasePool(tSingleton(tid,aCons a (unlocked(b++[c])),s2,M)) = 
                          pSingle(eraseTerm M').
Proof.
  intros. replace (aCons a (unlocked (b++[c]))) with (unlocked ((a::b) ++ [c])). 
  erewrite eraseLastAct; eauto. simpl. auto. 
Qed. 

Theorem AddUnion : forall A T t, Add A T t = Union A T (Single A t). 
reflexivity. 
Qed. 

Theorem specImpliesNonSpec : forall H H' T t t', 
                step H T t (OK H' T t') -> wellFormed H (tUnion T t) ->
                exists PH' pt', pmultistep (eraseHeap H) (pUnion (erasePool T) (erasePool t))
                                           (Some(PH', (pUnion (erasePool T) pt'))) /\
                                eraseHeap H' = PH' /\ erasePool t' = pt'. 
Proof.  
  intros. inv H0. 
  {exists (eraseHeap H'). econstructor. split; auto. destruct s1. 
   {inv H1. simpl in *. constructor. }
   {destructLast l. 
    {inv H1. repeat erewrite erasePoolSingleton; eauto. apply simBasicStep in H6. 
     econstructor. eapply PBasicStep; eauto. constructor. }
    {invertHyp. inv H1. actTermTac x. repeat erewrite eraseLastAct; eauto. constructor. }
   }
   {inv H1. simpl. constructor. }
  }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1. destruct s1. 
   {simpl. constructor. }
   {destructLast l. 
    {simpl. constructor. }
    {invertHyp. unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. actTermTac x. 
     erewrite eraseLastAct; eauto. rewrite eraseEmpty. unfold pUnion.
     rewrite union_empty_r. erewrite eraseTwoActs'; eauto. constructor. }
   }
   {simpl. constructor. }
  }
  {exists (eraseHeap H). destruct s1. 
   {econstructor. split. simpl. constructor. erewrite eraseHeapDependentRead; eauto. }
   {destructLast l. 
    {econstructor. split. simpl. constructor. erewrite eraseHeapDependentRead; eauto. }
    {invertHyp. econstructor. split. constructor. split. erewrite eraseHeapDependentRead; eauto. 
     inv H1. actTermTac x0. erewrite eraseTwoActs'; eauto. erewrite eraseLastAct; eauto. }
   }
   {econstructor. split. simpl. constructor. erewrite eraseHeapDependentRead; eauto. }
  }
  {exists (eraseHeap H). econstructor. split. constructor. split. erewrite eraseHeapWrite; auto.
   inv H1. destruct s1; auto. 
   {destructLast l; auto. invertHyp. actTermTac x0. erewrite eraseTwoActs'; eauto. 
    erewrite eraseLastAct; eauto. }
  }  
  {exists (eraseHeap H). eapply rollbackIdempotent in H7; eauto. 
   invertHyp. inv H1. econstructor. split. constructor. split. 
   erewrite eraseHeapWrite; auto. unfoldTac. repeat rewrite AddUnion. 
   repeat rewrite eraseUnionComm. rewrite <- H0. simpl. apply decomposeEq in d. 
   subst. auto. }
  {exists (eraseHeap H). econstructor. split. constructor. split. 
   rewrite eraseHeapNew. auto. inv H1. destruct s1; auto. 
   {destructLast l. 
    {copy d. apply decomposeEq in H0. subst. simpl. auto. }
    {invertHyp. actTermTac x0. erewrite eraseTwoActs'; eauto. erewrite eraseLastAct; eauto. }
   }
  }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1. unfoldTac. rewrite coupleUnion. 
   rewrite eraseUnionComm. destruct s1.
   {simpl. constructor. }
   {destructLast l. 
    {simpl. constructor. }
    {invertHyp. actTermTac x. erewrite eraseLastAct; eauto.
     erewrite eraseTwoActs'; eauto. simpl. constructor. }
   }
   {simpl. constructor. }
  }
  {inv H1. unfoldTac. rewrite coupleUnion in H0. 
   repeat rewrite unspecUnionComm in H0. econstructor. econstructor. split; auto. 
   rewrite coupleUnion. rewrite eraseUnionComm. rewrite eraseEmptySpec. unfold pUnion. 
   rewrite union_empty_r. repeat rewrite Union_associative in H0. econstructor. 
   eapply pSpecRun. copy p. erewrite <- decomposeErase in H; eauto. simpl. auto. 
   copy p. apply decomposeWF in H. rewrite eraseCtxtWF in H. simpl in H. copy p. 
   rewrite <- decomposeErase in H1; eauto. simpl in H1. destructLast s1. 
   {simpl. rewrite eraseFill. unfoldTac. rewrite UnionSwap in H0.
    rewrite Union_associative in H0. rewrite UnionSwap in H0.
    rewrite spec_multi_unused in H0. eapply simSpecJoinSteps; eauto. simpl in *.
    eassumption. }
   {unfoldTac. rewrite UnionSwap in H0. rewrite Union_associative in H0. rewrite UnionSwap in H0. 
    rewrite spec_multi_unused in H0. invertHyp. rewrite wrapDistributeApp. destruct x.
    {simpl (wrapActs [rAct x t E0 d] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps';[idtac|eauto|simpl in *; eauto]. constructor. }
    {simpl (wrapActs [wAct x t E0 M0 d] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps';[idtac|eauto|simpl in *; eauto]. constructor. }
    {simpl (wrapActs [nAct t E0 d i] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps'; [idtac|eauto|simpl in *; eauto]. constructor. }
    {simpl (wrapActs [fAct t E0 M0 d n] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps';[idtac|eauto|simpl in *; eauto]. constructor. }
    {simpl (wrapActs [srAct t E0 M0 N d] N1 E (specRun (ret N1) N0)(decomposeWF t0 E (specRun (ret N1) N0) p)).
     erewrite eraseLastAct; eauto. rewrite eraseFill. 
     eapply simSpecJoinSteps'; [idtac|eauto|simpl in *; eauto]. constructor. }
   }
  }
  {exists (eraseHeap H). eapply rollbackIdempotent in H10; eauto. 
   invertHyp. inv H1. econstructor. split. unfoldTac. rewrite coupleUnion. 
   repeat rewrite eraseUnionComm. unfold pUnion. rewrite Union_associative. eapply pmulti_step. 
   simpl. eapply pSpecRunRaise. eapply decomposeErase in H4; eauto. simpl. auto. 
   unfold pUnion.  rewrite <- Union_associative. 
   constructor. split; auto. unfoldTac. rewrite AddUnion. rewrite eraseUnionComm. 
   repeat rewrite AddUnion in H0. repeat rewrite eraseUnionComm in H0. simpl in H0. 
   unfold pUnion in H0. repeat rewrite union_empty_r in H0. rewrite <- H0.
   simpl. rewrite eraseFill; eauto. }
  {exists (eraseHeap H). econstructor. split. Focus 2. split; auto. 
   erewrite eraseHeapDependentRead. auto. eauto. inv H1. eraseTrmTac s1' M. 
   erewrite eraseLastAct; eauto. econstructor. eapply PGet; eauto. 
   eapply lookupEraseCommitFull; eauto. copy d. erewrite <- decomposeErase in H0; eauto. 
   rewrite unspecUnionComm in H2. erewrite unspecLastActPool in H2. Focus 2. constructor. 
   eapply specStepRead in H2; eauto. invertHyp. eapply simPureSteps in H0; eauto.
   rewrite eraseFill in H0. simpl in H0. erewrite eraseEraseTrm; eauto. 
   eapply unspecHeapLookupFull; eauto. }
  {exists (replace x (pfull (eraseTerm M'')) (eraseHeap H)). econstructor. split. 
   Focus 2. split; eauto. erewrite eraseHeapCommitWrite; eauto. inv H1. 
   erewrite eraseLastAct. Focus 2. constructor. rewrite unspecUnionComm in H2. 
   erewrite unspecLastActPool in H2. Focus 2. constructor. eraseTrmTac s1' M. 
   erewrite eraseEraseTrm; eauto. eapply specStepWrite in H2; eauto. invertHyp. 
   eapply simPureSteps in H0; eauto. rewrite eraseFill in H0. simpl in H0. 
   econstructor. eapply PPut; eauto. copy d. erewrite <- decomposeErase in H2; eauto.
   simpl. auto. eapply lookupEraseSpecFull; eauto. eassumption. 
   eapply lookupUnspecSpecFullEmpty; eauto. }
  {inv H1. assert(heap_lookup i (eraseHeap H) = None). 
   eapply lookupEraseSpecNone; eauto. exists (Heap.extend i pempty (eraseHeap H) H0). 
   econstructor. split. Focus 2. split; eauto. eapply eraseHeapCommitNewFull; eauto. 
   erewrite eraseLastAct. Focus 2. constructor. econstructor.
   eapply PNew with(x:=i)(p:=H0); eauto. copy d. erewrite <- decomposeErase in H1; eauto. 
   rewrite unspecUnionComm in H2. erewrite unspecLastActPool in H2. Focus 2. constructor. 
   eraseTrmTac s1' M. eapply specStepNewFull in H2; eauto. invertHyp. 
   eapply simPureSteps in H1; eauto. rewrite eraseFill in H1.
   erewrite eraseEraseTrm; eauto. eapply lookupUnspecSpecNone; eauto. }
  {inv H1. assert(heap_lookup i (eraseHeap H) = None). eapply lookupEraseSpecNoneEmpty; eauto. 
   exists (Heap.extend i pempty (eraseHeap H) H0). econstructor. split. Focus 2. split; eauto. 
   eapply eraseHeapCommitNewEmpty; eauto. erewrite eraseLastAct. Focus 2. constructor. 
   econstructor. eapply PNew with (x:=i)(p:=H0); eauto. copy d.
   erewrite <- decomposeErase in H1; eauto. eraseTrmTac s1' M. erewrite eraseEraseTrm; eauto. 
   rewrite unspecUnionComm in H2. erewrite unspecLastActPool in H2. Focus 2. constructor. 
   eapply specStepNewEmpty in H2; eauto. invertHyp. eapply simPureSteps in H1; eauto. 
   rewrite eraseFill in H1. eassumption. eapply lookupUnspecSpecEmptyNone; eauto. }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1.
   unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. rewrite eraseEmpty. 
   unfold pUnion. rewrite union_empty_r. erewrite eraseLastAct. Focus 2. constructor. 
   econstructor. eapply pFork. copy d. erewrite <- decomposeErase in H; eauto. 
   simpl. auto. rewrite coupleUnion in H0. repeat rewrite unspecUnionComm in H0. 
   rewrite unspecEmpty in H0. erewrite unspecLastActPool in H0. Focus 2. constructor. 
   unfoldTac. rewrite union_empty_r in H0. rewrite <- coupleUnion in H0. 
   eapply specStepFork in H0; eauto. invertHyp. rewrite eraseUnspecHeapIdem in H1. 
   rewrite <- H1. eraseTrmTac s1' M. eraseTrmTac s1'' N. unfoldTac.
   repeat rewrite coupleUnion in H. repeat rewrite Union_associative in H. 
   repeat rewrite coupleUnion. rewrite eraseUnionComm.
   repeat erewrite eraseEraseTrm; eauto. unfold pUnion. repeat rewrite <- coupleUnion. 
   copy H. eapply simPureStepsCouple' with(H'':=eraseHeap x)(PT:=erasePool T)
    (N:=pfill (eraseCtxt E)(pret punit)) in H; eauto. unfold pCouple. rewrite couple_swap. 
   eapply pmulti_trans. eassumption. rewrite UnionSwap in H0. rewrite <- Union_associative in H0. 
   rewrite UnionSwap in H0. rewrite Union_associative in H0.
   eapply simPureStepsCouple in H0; eauto. rewrite eraseFill in H0; eauto.
   unfold pCouple in *. rewrite couple_swap in H0. eauto. }
  {exists (eraseHeap H'). econstructor. split; auto. inv H1. unfoldTac. 
   rewrite coupleUnion in *. repeat rewrite unspecUnionComm in H0.
   rewrite unspecEmpty in H0. unfoldTac. rewrite union_empty_r in H0. 
   repeat rewrite eraseUnionComm. rewrite eraseEmpty. erewrite eraseLastAct. Focus 2. 
   constructor. unfold pUnion. rewrite union_empty_r. econstructor. 
   eapply pSpec. copy d. rewrite <- decomposeErase in H; eauto. simpl. auto. 
   rewrite <- coupleUnion in H0. erewrite unspecLastActPool in H0. Focus 2. constructor. 
   eapply specStepSpec in H0; eauto. invertHyp. eraseTrmTac s1' M'. rewrite coupleUnion. 
   rewrite eraseUnionComm. erewrite eraseEraseTrm; eauto. simpl. unfoldTac.
   flipCouplesIn H.  repeat rewrite coupleUnion in H. repeat rewrite Union_associative in H. 
   eapply simPureSteps in H; eauto. rewrite eraseFill in H. eassumption. }
Qed. 

Theorem specImpliesNonSpecMulti : forall H H' T T', 
                multistep H T (Some(H', T')) -> wellFormed H T -> 
                exists PH' PT', pmultistep (eraseHeap H) (erasePool T) (Some(PH',PT')) /\
                                eraseHeap H' = PH' /\ erasePool T' = PT'. 
Proof.  
  intros. depInd H0; intros.  
  {econstructor. econstructor. split. constructor. auto. }
  {copy H0. eapply specImpliesNonSpec in H0; eauto. invertHyp.
   copy H3. eapply stepWF in H3; auto. eapply IHmultistep in H3; eauto. 
   invertHyp. econstructor. econstructor. split; eauto. eapply pmulti_trans.
   rewrite eraseUnionComm. eassumption. rewrite <- eraseUnionComm. auto. }
Qed. 




