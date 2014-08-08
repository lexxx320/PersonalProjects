Require Import erasure. 
Require Import IndependenceCommon. 

Ltac takeTStep :=
  match goal with
      |H:?T = ?x |- spec_multistep ?H (tUnion ?T ?T') ?H' ?T'' =>
       rewrite H; unfoldTac; rewrite UnionSwap; 
       econstructor;[eapply specStepChangeUnused; eassumption|idtac]; unfoldTac; 
       rewrite <- UnionSwap                                          
      |H:?T = ?x |- spec_multistep ?H (tUnion ?T ?T') ?H' ?T'' =>
       rewrite H; unfoldTac; rewrite UnionSwap
      |H:?T = ?x |- spec_multistep ?H (tUnion ?T ?T') ?H' ?T'' =>
       rewrite H
  end. 

Theorem helper : forall H T H' T' ds ds' x M' TID,
                   heap_lookup x H = Some(sfull COMMIT ds SPEC TID M') ->
                   heap_lookup x H' = Some(sfull COMMIT ds' SPEC TID M') ->
                   spec_multistep H T H' T' ->
                   spec_multistep (replace x (sfull COMMIT ds COMMIT TID M') H) T
                                  (replace x (sfull COMMIT ds' COMMIT TID M') H') T'. 
Proof.  
  intros. genDeps{x; ds; ds'; TID; M'}. induction H2; intros. 
  {rewrite H1 in H0. inv H0. constructor. }
  {inversion H; subst. 
   {econstructor. eapply SBasicStep; eauto. eauto. }
   {econstructor. eapply SFork; eauto. eauto. }
   {destruct (beq_nat x0 x) eqn:eq. 
    {apply beq_nat_true in eq. subst. rewrite H0 in H3. inv H3. econstructor. 
     eapply SGet with(x:=x); auto. erewrite HeapLookupReplace; eauto. 
     lookupTac. eapply IHspec_multistep in H3; eauto. rewrite replaceOverwrite. 
     rewrite replaceOverwrite in H3. eauto. }
    {apply beq_nat_false in eq. apply neqSym in eq. lookupTac.
     eapply IHspec_multistep in H4; eauto. econstructor. eapply SGet with(x:=x0); eauto. 
     rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; auto. eauto. }
   }
   {destruct(beq_nat x0 x) eqn:eq. apply beq_nat_true in eq. subst. rewrite H0 in H3. 
    inv H3. apply beq_nat_false in eq. apply neqSym in eq. lookupTac.
    eapply IHspec_multistep in H4; eauto. econstructor. eapply SPut with(x:=x0); eauto. 
    rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. }
   {destruct(beq_nat x0 x) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H0 in H3. 
    inv H3. apply beq_nat_false in eq. apply neqSym in eq. lookupTac.
    eapply IHspec_multistep in H3; eauto. econstructor. eapply SNew with(x:=x0); eauto. 
    erewrite extendReplaceSwitch; eauto. }
   {econstructor. eapply SSpec; eauto. eapply IHspec_multistep; eauto. }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 

Theorem writeFastForward : forall H T H' T' TID x M' E M'' s2 d s1' M,
         heap_lookup x H = Some(sempty COMMIT) -> decompose M' E (put (fvar x) M'') ->
         spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M'))) H' 
                        (tUnion T' (tSingleton(TID,unlocked(s1'++[wAct x M' E M'' d]),s2,M))) ->
         exists H'' T'' ,
           spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M'))) H''
                         (tUnion T'' (tSingleton(TID,unlocked [wAct x M' E M'' d],s2,fill E (ret unit)))) /\
           spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked [wAct x M' E M'' d],s2,fill E (ret unit))))
                          H' (tUnion T' (tSingleton(TID,unlocked(s1'++[wAct x M' E M'' d]),s2,M)))  /\
           spec_multistep (replace x (sfull COMMIT nil COMMIT TID M'') H) T 
                          (replace x (sfull COMMIT nil COMMIT TID M'')H'') T'' /\ 
           heap_lookup x H'' = Some(sfull COMMIT nil SPEC TID M'').
Proof.
  intros. dependent induction H2. 
  {apply UnionEqTID in x. invertHyp. inv H2. invertListNeq. }
  {startIndCase. destructThread x1. exMid TID H9.
   {apply UnionEqTID in H5. invertHyp. econstructor. econstructor. split. 
    econstructor. eapply SPut; eauto. constructor. split. inv H3; try solve[falseDecomp].  
    {inv H15. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H3; eauto. invertHyp. inv H6. 
     proofsEq d d0. rewrite H14 in H0. inv H0. eauto. }
    {split. rewrite replaceOverwrite. constructor. erewrite HeapLookupReplace; eauto. }
   } 
   {apply UnionNeqTID in H5; auto. invertHyp. copy H3. eapply specStepEmptyIVar in H3; eauto.
     Focus 2. rewrite H4. solveSet. left. invUnion. right; simpl. eauto. Focus 2. solveSet. 
    copy H3. eapply IHspec_multistep in H3; eauto. invertHyp. econstructor. econstructor. split.
    rewrite H11; unfoldTac; rewrite UnionSwap; econstructor. eapply specStepChangeUnused. 
    eauto. unfoldTac. rewrite UnionSwap. eassumption. split; eauto. split; eauto. 
    Focus 2. rewrite H4. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap. eauto.
    rewrite H11. clear H11 H4. inv H5. 
    {econstructor. eapply SBasicStep;eauto.  eauto. }
    {econstructor. eapply SFork; eauto. eauto. }
    {varsEq x3 x0. heapsDisagree. econstructor. eapply SGet; eauto.
     erewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. }
    {varsEq x3 x0. erewrite HeapLookupReplace in H12; eauto. inv H12. econstructor. 
     eapply SPut. rewrite lookupReplaceNeq; eauto. auto. rewrite lookupReplaceSwitch. 
     eauto. auto. }
    {varsEq x3 x0. heapsDisagree. econstructor. eapply SNew; eauto. 
     erewrite extendReplaceSwitch; eauto. }
    {econstructor. eapply SSpec; eauto. eauto. }
   }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 

Theorem writeSimPureSteps : forall H T H' T' TID x M' E M'' d N N' N'' s2 s1' ds ds',
       eraseTrm s1' N' N'' -> 
       heap_lookup x H = Some(sfull COMMIT ds SPEC TID M'') ->       
       heap_lookup x H' = Some(sfull COMMIT ds' SPEC TID M'') -> 
       spec_multistep H (tUnion T (tSingleton(TID,unlocked[wAct x M' E M'' d],s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[wAct x M' E M'' d]),s2,N'))) ->
       exists H'' T'',
         spec_multistep H (tUnion T (tSingleton(TID,unlocked[wAct x M' E M'' d],s2,N))) 
                        H'' (tUnion T'' (tSingleton(TID,unlocked[wAct x M' E M'' d],s2,N''))) /\
         spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked[wAct x M' E M'' d],s2,N''))) 
                        H' (tUnion T' (tSingleton(TID,unlocked(s1'++[wAct x M' E M'' d]),s2,N'))) /\
         exists ds'',
         spec_multistep (replace x (sfull COMMIT ds COMMIT TID M'') H) T 
                        (replace x (sfull COMMIT ds'' COMMIT TID M'')H'') T'' /\
         heap_lookup x H'' = Some(sfull COMMIT ds'' SPEC TID M'').
Proof.
  intros. genDeps{N'';ds; ds'}. dependent induction H3; intros.
  {apply UnionEqTID in x. invertHyp. inv H. destruct s1'; inv H5. inv H0; try invertListNeq. 
   rewrite H2 in H1. inv H1. repeat econstructor. eauto. invertListNeq. }
  {startIndCase. destructThread x1. exMid TID H10. 
   {apply UnionEqTID in H6. invertHyp. inv H0. 
    {eapply IHspec_multistep in H1;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. invertHyp. 
     econstructor. econstructor. split. econstructor. eapply SBasicStep; eauto. eassumption. 
     split. eassumption. econstructor. split. eassumption. eassumption. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H4. inv H4. exists h'. 
     exists T. split. constructor. split. simpl in *. econstructor. eapply SFork; eauto. 
     eassumption. econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H4. inv H4. 
     exists H. exists T. split. constructor. split. simpl in *. econstructor. 
     eapply SGet; eauto. eassumption. econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H4. inv H4.  
     exists H. exists T. split. constructor. split. simpl in *. econstructor.
     eapply SPut; eauto. eassumption. econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H4. inv H4.  
     exists H. exists T. split. constructor. split. simpl in *. econstructor.
     eapply SNew; eauto. eassumption. econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H4. inv H4. 
     exists h'. exists T. split. constructor. split. simpl in *. econstructor. 
     eapply SSpec; eauto. eassumption. econstructor. split. constructor. eauto. }
   }
   {copy H0. eapply specStepFullIVar in H0; eauto. invertHyp. apply UnionNeqTID in x. invertHyp. 
    copy H12. eapply IHspec_multistep in H12; eauto. invertHyp. econstructor. econstructor. 
    split. rewrite H13. unfoldTac; rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused. eauto. unfoldTac. rewrite UnionSwap. eassumption. 
    split; eauto. econstructor. split. eapply spec_multi_trans. Focus 2. eassumption.  
    eapply helper. eauto. eauto. rewrite H13. econstructor. eapply specStepChangeUnused. 
    eauto. constructor. eauto. rewrite H0. rewrite UnionSubtract. unfoldTac. 
    rewrite UnionSwap. eauto. auto. }
  }
Qed. 

Theorem writeSimActionSteps : forall H T H' T' TID x M' E M'' d N N' H'' T'' N'' s2 s1 s1' ds ds' a,
                                eraseTrm (s1'++[a]) N' N'' ->
       heap_lookup x H = Some(sfull COMMIT ds SPEC TID M'') ->       
       heap_lookup x H' = Some(sfull COMMIT ds' SPEC TID M'') -> 
       spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked [wAct x M' E M'' d],s2,N'')))
                      H (tUnion T (tSingleton(TID,unlocked(s1++[wAct x M' E M'' d]),s2,N))) ->
       spec_multistep H (tUnion T (tSingleton(TID,unlocked(s1++[wAct x M' E M'' d]),s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[a]++[wAct x M' E M'' d]),s2,N'))) ->
       spec_multistep (replace x (sfull COMMIT ds COMMIT TID M'') H)
                      (tUnion T (tSingleton(TID,unlocked s1,wAct x M' E M'' d::s2,N))) 
                      (replace x (sfull COMMIT ds' COMMIT TID M'') H')
                      (tUnion T' (tSingleton(TID,unlocked (s1'++[a]), wAct x M' E M'' d::s2,N'))).
Proof.
  intros. genDeps{ds;ds'}. dependent induction H4; intros. 
  {apply UnionEqTID in x. invertHyp. inv H.
   replace[a;wAct x0 M' E M'' d] with ([a]++[wAct x0 M' E M'' d]) in H6; auto. 
   rewrite app_assoc in H6. apply app_inj_tail in H6. invertHyp. rewrite H2 in H1. 
   inv H1. constructor. }
  {startIndCase. destructThread x1. exMid TID H11. 
   {apply UnionEqTID in H7. invertHyp. inversion H1; subst. 
    {copy H3. eapply stackNonNil in H3. destruct s1. exfalso. apply H3. auto. 
     econstructor. eapply SBasicStep; eauto. constructor. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SBasicStep; eauto. constructor. 
     eauto. intros c. subst. apply eraseTrmApp in H0. inv H0; inv H16; falseDecomp. }
    {econstructor. eapply SFork; eauto. unfoldTac. rewrite coupleUnion. rewrite Union_associative. 
     rewrite <- UnionSwap. eapply IHspec_multistep; eauto. Focus 2. 
     rewrite <- Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     unfold numForks. simpl. simpl. eauto. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite <- plus_comm. simpl. rewrite plus_comm. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SFork; eauto. rewrite <- Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. simpl. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite plus_comm. simpl. rewrite plus_comm. constructor. }
    {varsEq x0 x1. 
     {rewrite H5 in H16. inv H16. econstructor. eapply SGet with(x:=x1); eauto. 
      erewrite HeapLookupReplace; eauto. lookupTac. 
      eapply IHspec_multistep in H6; eauto. rewrite replaceOverwrite. rewrite replaceOverwrite in H6. 
      eassumption. eapply spec_multi_trans. eassumption. econstructor. eapply SGet with(x:=x1); eauto. 
      constructor. simpl. eauto. }
     {lookupTac. eapply IHspec_multistep in H7; eauto. 
      econstructor. eapply SGet with(x:=x1); auto. rewrite lookupReplaceNeq; eauto. 
      rewrite lookupReplaceSwitch; auto. eassumption. eapply spec_multi_trans. eassumption. 
      econstructor. eapply SGet with(x:=x1); eauto. constructor. simpl. eauto. }
    }
    {varsEq x0 x1. heapsDisagree. lookupTac. eapply IHspec_multistep in H7; eauto. 
     econstructor. eapply SPut with(x:=x1). rewrite lookupReplaceNeq; eauto. auto. 
     rewrite lookupReplaceSwitch; auto. simpl. eassumption. eapply spec_multi_trans.
     eassumption. econstructor. eapply SPut with(x:=x1).  eauto. auto. 
     constructor. simpl. reflexivity. }
    {varsEq x0 x1. heapsDisagree. lookupTac. eapply IHspec_multistep in H7; eauto. 
     econstructor. eapply SNew with(x:=x1). auto. erewrite extendReplaceSwitch; eauto.
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew with(x:=x1); eauto. 
     constructor. simpl. auto. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite coupleUnion. rewrite Union_associative. 
     rewrite <- UnionSwap. eapply IHspec_multistep; eauto. Focus 2. rewrite <- Union_associative. 
     rewrite <- coupleUnion.  rewrite couple_swap. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SSpec; eauto. rewrite <- Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. constructor. }
   }
   {apply UnionNeqTID in H7; auto. copy H1. eapply specStepFullIVar in H1; eauto. invertHyp. 
    copy H13. eapply IHspec_multistep in H13; eauto. eapply spec_multi_trans. Focus 2. eassumption. 
    eapply helper; eauto. unfoldTac. rewrite UnionSwap. rewrite H14. rewrite UnionSwap. 
    econstructor. eapply specStepChangeUnused. eauto. constructor. eapply spec_multi_trans. 
    eassumption. rewrite H14. unfoldTac. rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused; eauto. unfoldTac. rewrite UnionSwap. constructor. 
    rewrite H1. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap; eauto. }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto.
Qed. 






