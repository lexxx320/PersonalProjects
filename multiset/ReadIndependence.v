Require Import erasure. 
Require Import IndependenceCommon. 

Theorem readFastForward : forall H T H' T' ds TID x M' E t0 s2 d s1' M N,
         heap_lookup x H = Some(sfull COMMIT ds COMMIT t0 N) ->
         decompose M' E (get (fvar x)) -> ~List.In TID ds -> 
         spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M'))) H'
                        (tUnion T' (tSingleton(TID,unlocked(s1'++[rAct x M' E d]),s2,M))) ->
         exists H'' T'' ,
           spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M'))) H''
                         (tUnion T'' (tSingleton(TID,unlocked [rAct x M' E d],s2,fill E (ret N)))) /\
           spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked [rAct x M' E d],s2,fill E(ret N))))
                          H' (tUnion T' (tSingleton(TID,unlocked(s1'++[rAct x M' E d]),s2,M)))  /\
           exists ds',
           spec_multistep H T (replace x (sfull COMMIT ds' COMMIT t0 N)H'') T'' /\ 
           heap_lookup x H'' = Some(sfull COMMIT (TID::ds') COMMIT t0 N) /\ ~ List.In TID ds'.
Proof.
  intros. genDeps{ds; t0; N}. dependent induction H3; intros. 
  {apply UnionEqTID in x. invertHyp. inv H3. invertListNeq. }
  {startIndCase. destructThread x1. exMid TID H10. 
   {apply UnionEqTID in x. invertHyp. econstructor. econstructor. split. econstructor. 
    eapply SGet; eauto. constructor. split. inv H0; try solve[falseDecomp]. 
    {inv H16; falseDecomp. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H0; eauto. invertHyp. inv H8. 
     proofsEq d d0. rewrite H16 in H2. inv H2. eauto. }
    {exists ds. split. rewrite replaceOverwrite. rewrite replaceSame; eauto. 
     constructor. erewrite HeapLookupReplace; eauto. }
   }
   {copy H0. eapply specStepFullIVar' in H5; eauto. inv H5. 
    {eapply IHspec_multistep in H12; eauto. invertHyp. apply UnionNeqTID in x. invertHyp. 
     exists x1. exists x2. split. rewrite H17. unfoldTac. rewrite UnionSwap. 
     econstructor. eapply specStepChangeUnused. eassumption. unfoldTac. rewrite UnionSwap. 
     eassumption. split. eassumption. exists x3. split. rewrite H17. econstructor.
     eapply specStepChangeUnused. eauto. eauto. eauto. auto. apply UnionNeqTID in x. 
     invertHyp. rewrite H5. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap; auto. auto. }
     {eapply IHspec_multistep in H12; eauto. apply UnionNeqTID in x; auto. invertHyp. 
      exists x1. exists x2. split. rewrite H17. unfoldTac. rewrite UnionSwap. 
      econstructor. eapply specStepChangeUnused. eassumption. unfoldTac. rewrite <- UnionSwap. 
      eassumption. split. eassumption. exists x3. split. rewrite H17. econstructor. 
      eapply specStepChangeUnused. eauto. eauto. split. 
      eauto. auto. apply UnionNeqTID in x. invertHyp. rewrite H5. rewrite UnionSubtract. 
      unfoldTac. rewrite UnionSwap. eauto. auto. introsInv. apply H8; auto. contradiction. }
   }
  }
Qed. 

Theorem monotonicReaders : forall H T H' T' ds ds' x t0 N,
         heap_lookup x H = Some(sfull COMMIT ds COMMIT t0 N) ->
         heap_lookup x H' = Some(sfull COMMIT ds' COMMIT t0 N) -> 
         spec_multistep H T H' T' -> exists z, ds' = z ++ ds. 
Proof.
  intros. genDeps{ds; ds'; x; t0; N}. induction H2; intros. 
  {rewrite H1 in H0. inv H0. exists nil. auto. }
  {copy H. apply specStepSingleton in H3. invertHyp. destruct x0. destruct p. 
   destruct p. copy H. eapply specStepFullIVar' in H; eauto. inv H. 
   {eapply IHspec_multistep in H4; eauto. }
   {inv H3.
    {rewrite H4 in H0. inversion H0; invertListNeq. }
    {rewrite H4 in H0. inversion H0; invertListNeq. }
    {destruct (beq_nat x0 x) eqn:eq. apply beq_nat_true in eq. subst.
     eapply IHspec_multistep in H4. invertHyp. exists (x0++[t1]). rewrite <- app_assoc.  
     simpl. eauto. eauto. apply beq_nat_false in eq. rewrite lookupReplaceNeq in H4; auto. 
     rewrite H4 in H0. inversion H0; invertListNeq. }
    {destruct (beq_nat x0 x) eqn:eq. apply beq_nat_true in eq. subst. rewrite H13 in H0. 
     inv H0. apply beq_nat_false in eq. rewrite lookupReplaceNeq in H4; eauto. rewrite H4 in H0. 
     inversion H0. invertListNeq. }
    {destruct (beq_nat x0 x) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H in H0. 
     inv H0. apply beq_nat_false in eq. erewrite lookupExtendNeq in H4; eauto. inversion H4. 
     invertListNeq. }
    {eauto. }
   }
  }
Qed. 

Theorem stepWithoutReader : forall H T H' T' ds1 ds2 ds1' t t0 N x,
                              heap_lookup x H = Some(sfull COMMIT (ds1 ++ [t]++ds2) COMMIT t0 N) ->
                              heap_lookup x H' = Some(sfull COMMIT (ds1' ++ [t]++ds2) COMMIT t0 N) ->
                              spec_multistep H T H' T' ->
                              spec_multistep (replace x (sfull COMMIT (ds1 ++ ds2) COMMIT t0 N) H) T
                                             (replace x (sfull COMMIT (ds1'++ds2) COMMIT t0 N) H') T'. 
Proof.
  intros. genDeps{ds1;ds2;ds1';x;t;t0;N}. induction H2; intros. 
  {rewrite H1 in H0. inv H0. apply app_inv_tail in H2. subst. constructor. }
  {inversion H; subst.  
   {econstructor. eapply SBasicStep; eauto. eauto. }
   {econstructor. eapply SFork; eauto. eauto. }
   {destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq. subst. 
    rewrite H3 in H0. inv H0. econstructor. eapply SGet with (x:=x0); auto. 
    erewrite HeapLookupReplace; eauto. lookupTac. simpl in *. repeat rewrite app_comm_cons in H0. 
    eapply IHspec_multistep in H0; eauto. rewrite replaceOverwrite. rewrite replaceOverwrite in H0. 
    eauto. apply beq_nat_false in eq. lookupTac. eapply IHspec_multistep in H4; eauto. 
    econstructor. eapply SGet with(x:=x0); auto. rewrite lookupReplaceNeq; eauto. 
    rewrite lookupReplaceSwitch; eauto. }
   {destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq. subst. rewrite H0 in H3. inv H3. 
    apply beq_nat_false in eq. lookupTac. eapply IHspec_multistep in H4; eauto. econstructor. 
    eapply SPut with(x:=x0); auto. rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch;eauto. }
   {destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H3 in H0. 
    inv H0. apply beq_nat_false in eq. lookupTac. eapply IHspec_multistep in H3; eauto. econstructor. 
    eapply SNew with(x:=x0); auto. erewrite extendReplaceSwitch; eauto. }
   {econstructor. eapply SSpec; eauto. eauto. }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto.
Qed. 

Theorem readSimPureSteps : forall H T H' T' TID x M' t0 E M'' d N N' N'' s2 s1' ds1 ds1' ds2,
       eraseTrm s1' N' N'' -> 
       heap_lookup x H = Some(sfull COMMIT (ds1++[TID]++ds2) COMMIT t0 M'') ->       
       heap_lookup x H' = Some(sfull COMMIT (ds1'++[TID]++ds2) COMMIT t0 M'') -> 
       spec_multistep H (tUnion T (tSingleton(TID,unlocked[rAct x M' E d],s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[rAct x M' E d]),s2,N'))) ->
       exists H'' T'',
         spec_multistep H (tUnion T (tSingleton(TID,unlocked[rAct x M' E d],s2,N))) 
                        H'' (tUnion T'' (tSingleton(TID,unlocked[rAct x M' E d],s2,N''))) /\
         spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked[rAct x M' E d],s2,N''))) 
                        H' (tUnion T' (tSingleton(TID,unlocked(s1'++[rAct x M' E d]),s2,N'))) /\
         exists ds1'',
         spec_multistep (replace x (sfull COMMIT (ds1++ds2) COMMIT t0 M'') H) T 
                        (replace x (sfull COMMIT (ds1''++ds2) COMMIT t0 M'')H'') T'' /\
         heap_lookup x H'' = Some(sfull COMMIT (ds1''++[TID]++ds2) COMMIT t0 M'').
Proof.
  intros. genDeps{ds1;ds2;t0;M'';ds1'}. dependent induction H3; intros. 
  {apply UnionEqTID in x. invertHyp. rewrite H2 in H1. inv H1. inv H. 
   destruct s1'; inv H4. inv H0; try solve[invertListNeq]. exists H'. exists T'. 
   split. constructor. split. constructor. exists ds1. split. constructor. 
   apply app_inv_tail in H5. subst. auto. invertListNeq. }
  {startIndCase. destructThread x1. exMid H10 TID. 
   {apply UnionEqTID in x. invertHyp. inv H1. 
    {eapply IHspec_multistep in H4;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. invertHyp. 
     econstructor. econstructor. split. econstructor. eapply SBasicStep; eauto. eassumption. 
     split. eauto. econstructor. split. eauto. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists h'. exists T. 
     split. constructor. split. simpl. econstructor. eapply SFork; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists H. exists T. 
     split. constructor. split. simpl. econstructor. eapply SGet; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists H. exists T. 
     split. constructor. split. simpl. econstructor. eapply SPut; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists H. exists T. 
     split. constructor. split. simpl. econstructor. eapply SNew; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists h'. exists T. 
     split. constructor. split. simpl. econstructor. eapply SSpec; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
   }
   {apply UnionNeqTID in x; auto. invertHyp. copy H1. eapply specStepFullIVar' in H1; eauto. 
    inversion H1. 
    {copy H14. eapply IHspec_multistep in H14; eauto. invertHyp. econstructor. econstructor. 
     split. rewrite H12. unfoldTac. rewrite UnionSwap. econstructor. eapply specStepChangeUnused. 
     eauto. unfoldTac. rewrite UnionSwap. eassumption. split; eauto. exists x2. split. 
     eapply spec_multi_trans. Focus 2. eassumption. eapply stepWithoutReader; eauto. 
     rewrite H12. econstructor. eapply specStepChangeUnused; eauto. constructor. eauto. 
     rewrite H5. unfoldTac. rewrite UnionSubtract. rewrite UnionSwap. auto. }
    {copy H14. rewrite app_comm_cons in H14. eapply IHspec_multistep in H14; eauto. invertHyp. 
     econstructor. econstructor. split. rewrite H12. unfoldTac. rewrite UnionSwap. econstructor. 
     eapply specStepChangeUnused. eauto. unfoldTac. rewrite UnionSwap. eassumption. split; eauto. 
     exists x2. split. eapply spec_multi_trans. Focus 2. eassumption. eapply stepWithoutReader; eauto. 
     rewrite H12. econstructor. eapply specStepChangeUnused; eauto. constructor. eauto. 
     rewrite H5. unfoldTac. rewrite UnionSubtract. rewrite UnionSwap. auto. }
   }
  }
Qed. 

Theorem readSimActionSteps : forall H T H' T' TID x M' E M'' d N N' t0 H'' T'' N'' s2 s1 s1' ds1 ds1' ds2 a,
       eraseTrm (s1'++[a]) N' N'' ->
       heap_lookup x H = Some(sfull COMMIT (ds1++[TID]++ds2) COMMIT t0 M'') ->       
       heap_lookup x H' = Some(sfull COMMIT (ds1'++[TID]++ds2) COMMIT t0 M'') -> 
       spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked [rAct x M' E d],s2,N'')))
                      H (tUnion T (tSingleton(TID,unlocked(s1++[rAct x M' E d]),s2,N))) ->
       spec_multistep H (tUnion T (tSingleton(TID,unlocked(s1++[rAct x M' E d]),s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[a]++[rAct x M' E d]),s2,N'))) ->
       spec_multistep (replace x (sfull COMMIT (ds1++ds2) COMMIT t0 M'') H)
                      (tUnion T (tSingleton(TID,unlocked s1,rAct x M' E d::s2,N))) 
                      (replace x (sfull COMMIT (ds1'++ds2) COMMIT t0 M'') H')
                      (tUnion T' (tSingleton(TID,unlocked (s1'++[a]), rAct x M' E d::s2,N'))).
Proof.
  intros. genDeps{ds1; ds2; ds1'}. dependent induction H4; intros. 
  {apply UnionEqTID in x. invertHyp. inv H.
   replace[a;rAct x0 M' E d] with ([a]++[rAct x0 M' E d]) in H6; auto. 
   rewrite app_assoc in H6. apply app_inj_tail in H6. invertHyp. rewrite H2 in H1. 
   inv H1. apply app_inv_tail in H6. subst. constructor. }
  {startIndCase. destructThread x1. exMid TID H11. 
   {apply UnionEqTID in x. invertHyp. inversion H1; subst. 
    {copy H3. eapply stackNonNil in H3. destruct s1. exfalso. apply H3. auto. 
     econstructor. eapply SBasicStep; eauto. constructor. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SBasicStep; eauto. constructor. 
     eauto. intros c. subst. apply eraseTrmApp in H0. inv H0; inv H17; falseDecomp. }
    {econstructor. eapply SFork; eauto. unfoldTac. rewrite coupleUnion. rewrite Union_associative. 
     rewrite <- UnionSwap. eapply IHspec_multistep; eauto. Focus 2. 
     rewrite <- Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     unfold numForks. simpl. simpl. eauto. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite <- plus_comm. simpl. rewrite plus_comm. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SFork; eauto. rewrite <- Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. simpl. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite plus_comm. simpl. rewrite plus_comm. constructor. }
    {destruct(beq_nat x x0) eqn:eq. 
     {apply beq_nat_true in eq. subst. rewrite H5 in H17. inv H17. econstructor. 
      eapply SGet with(x:=x0); eauto. erewrite HeapLookupReplace; eauto. lookupTac. simpl in *. 
      rewrite app_comm_cons in H6. eapply IHspec_multistep in H6; eauto. rewrite replaceOverwrite. 
      rewrite replaceOverwrite in H6. eassumption. eapply spec_multi_trans. eassumption. econstructor. 
      eapply SGet with(x:=x0); eauto. constructor. simpl. eauto. }
     {apply beq_nat_false in eq. apply neqSym in eq. lookupTac. eapply IHspec_multistep in H6; eauto. 
      econstructor. eapply SGet with(x:=x); auto. rewrite lookupReplaceNeq; eauto. 
      rewrite lookupReplaceSwitch; auto. eassumption. eapply spec_multi_trans. eassumption. 
      econstructor. eapply SGet with(x:=x); eauto. constructor. simpl. eauto. }
    }
    {destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq. subst. rewrite H17 in H5. 
     inv H5. apply beq_nat_false in eq. apply neqSym in eq. lookupTac.
     eapply IHspec_multistep in H6; eauto. econstructor. eapply SPut with(x:=x). 
     rewrite lookupReplaceNeq; eauto. auto. rewrite lookupReplaceSwitch; auto. simpl. 
     eassumption. eapply spec_multi_trans. eassumption. econstructor. eapply SPut with(x:=x). 
     eauto. auto. constructor. simpl. reflexivity. }
    {destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H6 in H5. 
     inv H5. apply beq_nat_false in eq. apply neqSym in eq. lookupTac.
     eapply IHspec_multistep in H6; eauto. econstructor. eapply SNew with(x:=x). 
     auto. erewrite extendReplaceSwitch; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SNew with(x:=x); eauto. constructor. simpl. auto. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite coupleUnion. rewrite Union_associative. 
     rewrite <- UnionSwap. eapply IHspec_multistep; eauto. Focus 2. rewrite <- Union_associative. 
     rewrite <- coupleUnion.  rewrite couple_swap. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SSpec; eauto. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. constructor. }
   }
   {apply UnionNeqTID in H7; auto. invertHyp. copy H1. eapply specStepFullIVar' in H1; eauto. 
    inversion H1. 
    {copy H14. eapply IHspec_multistep in H14; eauto. eapply spec_multi_trans. Focus 2. 
     eassumption. eapply stepWithoutReader; eauto. rewrite H13. unfoldTac. rewrite UnionSwap. 
     econstructor. eapply specStepChangeUnused. eauto. unfoldTac. rewrite UnionSwap. 
     constructor. eapply spec_multi_trans. eassumption. rewrite H13. unfoldTac. 
     rewrite UnionSwap. econstructor. eapply specStepChangeUnused. eauto. unfoldTac. 
     rewrite UnionSwap. constructor. rewrite H6. rewrite UnionSubtract. unfoldTac. 
     rewrite UnionSwap. eauto. }
    {copy H14. rewrite app_comm_cons in H14. eapply IHspec_multistep in H14; eauto. 
     eapply spec_multi_trans. Focus 2. 
     eassumption. eapply stepWithoutReader; eauto. rewrite H13. unfoldTac. rewrite UnionSwap. 
     econstructor. eapply specStepChangeUnused. eauto. unfoldTac. rewrite UnionSwap. 
     constructor. eapply spec_multi_trans. eassumption. rewrite H13. unfoldTac. 
     rewrite UnionSwap. econstructor. eapply specStepChangeUnused. eauto. unfoldTac. 
     rewrite UnionSwap. constructor. rewrite H6. rewrite UnionSubtract. unfoldTac. 
     rewrite UnionSwap. eauto. }
   }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 
     
