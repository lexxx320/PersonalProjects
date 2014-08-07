Require Import erasure. 
Require Import IndependenceCommon. 
Require Import Coq.Logic.Classical. 

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
  {startIndCase. eqIn H5. inv H6.  
   {copy H0. destruct x1. destruct p. destruct p. eapply specStepFullIVar' in H6; eauto. inv H6. 
    {eapply IHspec_multistep in H9; eauto. invertHyp. Focus 2. proveUnionEq x. exists x1.
     exists x2. split. apply pullOut in H8. rewrite H8. unfoldTac. rewrite UnionSwap. 
     econstructor. eapply specStepChangeUnused. eassumption. unfoldTac. rewrite <- UnionSwap. 
     eassumption. split. eassumption. exists x3. split. apply pullOut in H8. rewrite H8. 
     econstructor. eapply specStepChangeUnused. eauto. eauto. eauto. }
    {assert(t1=TID \/ t1 <> TID). apply classic. inv H6. 
     {apply UnionEqTID in x. invertHyp. 
      exists (replace x0 (sfull COMMIT (TID::ds) COMMIT t0 N) H). exists T. split. econstructor. 
      eapply SGet; eauto. constructor. split. 
      inversion H0; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
      {inv H10; falseDecomp. }
      {falseDecomp. rewrite H10 in H2. inv H2. simpl in *. assert(d=d0). apply proof_irrelevance. 
       subst. eassumption. }
      exists ds. split. rewrite replaceOverwrite. rewrite replaceSame; eauto. constructor. 
      split. erewrite HeapLookupReplace; eauto. assumption. }
     {eapply IHspec_multistep in H9; eauto. Focus 2. proveUnionEq x. invertHyp. 
      exists x1. exists x2. split. apply pullOut in H8. rewrite H8. unfoldTac. rewrite UnionSwap. 
      econstructor. eapply specStepChangeUnused. eassumption. unfoldTac. rewrite <- UnionSwap. 
      eassumption. split. eassumption. exists x3. split. apply pullOut in H8. 
      rewrite H8. econstructor. eapply specStepChangeUnused. eauto. eauto. split. 
      eauto. auto. intros c. inv c. apply H10; auto. contradiction. }
    }
   }
   {inv H8. exists (replace x0 (sfull COMMIT (TID::ds) COMMIT t0 N) H). exists T. 
    split. econstructor. eapply SGet; eauto. constructor. split.
    inv H0; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
    {inv H8; falseDecomp. }
    {falseDecomp. rewrite H8 in H2. inv H2. apply UnionEqTID in x. invertHyp. simpl in *. 
     assert(d=d0). apply proof_irrelevance. subst. eassumption. }
    exists ds. split. rewrite replaceOverwrite. rewrite replaceSame; eauto. 
    constructor. erewrite HeapLookupReplace; eauto. }
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
   {inv H3; unfoldTac; invertHyp; invThreadEq. 
    {rewrite H4 in H0. inversion H0; invertListNeq. }
    {rewrite H4 in H0. inversion H0; invertListNeq. }
    {destruct (beq_nat x0 x) eqn:eq. apply beq_nat_true in eq. subst.
     eapply IHspec_multistep in H4. invertHyp. exists (x0++[t1]). rewrite <- app_assoc.  
     simpl. eauto. eauto. apply beq_nat_false in eq. rewrite lookupReplaceNeq in H4; auto. 
     rewrite H4 in H0. inversion H0; invertListNeq. }
    {destruct (beq_nat x0 x) eqn:eq. apply beq_nat_true in eq. subst. rewrite H5 in H0. 
     inv H0. apply beq_nat_false in eq. rewrite lookupReplaceNeq in H4; eauto. rewrite H4 in H0. 
     inversion H0. invertListNeq. }
    {destruct (beq_nat x0 x) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H in H0. 
     inv H0. apply beq_nat_false in eq. erewrite lookupExtendNeq in H4; eauto. inversion H4. 
     invertListNeq. }
    {eauto. }
   }
  }
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
  {startIndCase. eqIn H5. inv H6. 
   {copy H1. clear H1. inversion H6; subst; unfoldTac; invertHyp. 
    {eapply IHspec_multistep in H4;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. Focus 2.
     proveUnionEq x. invertHyp. econstructor. econstructor. split. takeTStep. eassumption. 
     split. eassumption. econstructor. split. apply pullOut in H8. rewrite H8. 
     econstructor. eapply SBasicStep; eauto. eassumption. eauto. }
    {eapply IHspec_multistep in H4;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. Focus 2.
     proveUnionEq x. invertHyp. econstructor. econstructor. split. takeTStep. eassumption. 
     split. eassumption. econstructor. split. apply pullOut in H8. rewrite H8. 
     econstructor. eapply SFork; eauto. eassumption. eauto. }
    {destruct (beq_nat x2 x0) eqn:eq. apply beq_nat_true in eq. subst. lookupTac. 
     rewrite H9 in H4. inv H4. simpl in *. rewrite app_comm_cons in H1.   
     eapply IHspec_multistep in H1; eauto. Focus 2. proveUnionEq x. invertHyp. 
     econstructor. econstructor. split. takeTStep. eassumption. split. eassumption. econstructor. 
     split. apply pullOut in H8. rewrite H8. econstructor. eapply SGet with(x:=x0); eauto. 
     erewrite HeapLookupReplace; eauto. rewrite replaceOverwrite. rewrite replaceOverwrite in H11. 
     eassumption. eauto. apply beq_nat_false in eq. apply neqSym in eq. lookupTac. 
     eapply IHspec_multistep in H1; eauto. Focus 2. proveUnionEq x. invertHyp. econstructor. 
     econstructor. split. takeTStep. eassumption. split. eassumption. econstructor. split. 
     apply pullOut in H8; rewrite H8. econstructor. eapply SGet with(x:=x2); eauto. 
     rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch. eassumption. auto. 
     eauto. }
    {destruct (beq_nat x0 x2)eqn:eq. apply beq_nat_true in eq. subst. rewrite H9 in H4. 
     inv H4. apply beq_nat_false in eq. lookupTac. eapply IHspec_multistep in H1; eauto. 
     Focus 2. proveUnionEq x. invertHyp. econstructor. econstructor. split. takeTStep. 
     eassumption. split. eassumption. econstructor. split. apply pullOut in H8; rewrite H8. 
     econstructor. eapply SPut with(x:=x2); eauto. rewrite lookupReplaceNeq; eauto. 
     rewrite lookupReplaceSwitch; eauto. eauto. }
    {destruct (beq_nat x0 x2) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H1 in H4. 
     inv H4. apply beq_nat_false in eq. lookupTac. eapply IHspec_multistep in H1; eauto.
     invertHyp. econstructor. econstructor. split. takeTStep. eauto. split. eauto. 
     econstructor. split. apply pullOut in H8. rewrite H8. econstructor. eapply SNew with (x:=x2); auto. 
     erewrite extendReplaceSwitch; eauto. eauto. proveUnionEq x. }
    {eapply IHspec_multistep in H4;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. Focus 2.
     proveUnionEq x. invertHyp. econstructor. econstructor. split. takeTStep. eassumption. 
     split. eassumption. econstructor. split. apply pullOut in H8. rewrite H8. 
     econstructor. eapply SSpec; eauto. eauto. eauto. }
   } 
   {inv H8. apply UnionEqTID in x. invertHyp. inversion H1; subst; unfoldTac; invertHyp; invThreadEq. 
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
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
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
  {copy x. copy H1. apply specStepSingleton in H1. invertHyp. unfoldSetEq H6.
   assert(tIn(tUnion T0(tSingleton x1)) x1). apply Union_intror. constructor. 
   apply H1 in H6. inv H6.  
   {copy H9. apply pullOut in H9. rewrite H9. clear H9. copy H7. destruct x1. destruct p.  
    destruct p. copy H9. eapply specStepFullIVar' in H9; eauto. inv H9.  
    {eapply spec_multi_trans. eapply spec_multi_unused. eapply stepWithoutReader; eauto. 
     eapply smulti_step. eapply specStepChangeUnused. eassumption. constructor. 
     eapply IHspec_multistep in H11; eauto. eapply spec_multi_trans. eassumption. 
     apply pullOut in H6. rewrite H6. unfoldTac. rewrite UnionSwap. econstructor. 
     eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap. 
     rewrite subtractSingle. constructor. proveUnionEq x. }
    {inversion H10; subst; unfoldTac; invertHyp; invThreadEq. 
     {rewrite H5 in H11. inversion H11. invertListNeq. }
     {rewrite H5 in H11. inversion H11. invertListNeq. }
     {destruct (beq_nat x0 x1) eqn:eq. apply beq_nat_true in eq. subst. rewrite H12 in H5. 
      inv H5. copy H11. repeat rewrite app_comm_cons in H5. eapply IHspec_multistep in H5; eauto.
      rewrite UnionSwap. econstructor. eapply SGet with(x:=x1); eauto. erewrite HeapLookupReplace; eauto. 
      rewrite replaceOverwrite. rewrite replaceOverwrite in H5. simpl in *. unfoldTac. 
      rewrite <- UnionSwap. eassumption. eapply spec_multi_trans. eassumption. apply pullOut in H6.
      rewrite H6. rewrite UnionSwap. econstructor. eapply SGet with(x:=x1); eauto. 
      rewrite <- UnionSwap. simpl. rewrite subtractSingle. constructor. proveUnionEq x. 
      apply beq_nat_false in eq. rewrite lookupReplaceNeq in H11. rewrite H11 in H5. 
      inversion H5. invertListNeq. auto. }
     {destruct (beq_nat x0 x1) eqn:eq. apply beq_nat_true in eq. subst. rewrite H12 in H5. 
      inv H5. rewrite lookupReplaceNeq in H11. rewrite H11 in H5. inversion H5. invertListNeq. 
      apply beq_nat_false in eq. auto. }
     {destruct (beq_nat x0 x1) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H9 in H5. 
      inv H5. apply beq_nat_false in eq. erewrite lookupExtendNeq in H11; eauto. 
      inversion H11. invertListNeq. }
     {rewrite H5 in H11. inversion H11. invertListNeq. }
    }
   }
   {inv H9. apply UnionEqTID in x. invertHyp. inv H6. 
    inversion H7; subst; unfoldTac; invertHyp; invThreadEq.  
    {copy H3. eapply stackNonNil in H3. destruct s1. exfalso. apply H3. auto. 
     econstructor. eapply SBasicStep; eauto. constructor. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SBasicStep; eauto. constructor. 
     eauto. intros c. subst. apply eraseTrmApp in H0. inv H0; inv H10; falseDecomp. }
    {econstructor. eapply SFork; eauto. unfoldTac. rewrite coupleUnion. rewrite <- Union_associative. 
     rewrite <- UnionSwap. eapply IHspec_multistep; eauto. Focus 2. 
     rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     unfold numForks. simpl. simpl. eauto. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite <- plus_comm. simpl. rewrite plus_comm. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SFork; eauto. rewrite Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. simpl. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite plus_comm. simpl. rewrite plus_comm. constructor. }
    {destruct(beq_nat x x0) eqn:eq. 
     {apply beq_nat_true in eq. subst. rewrite H5 in H10. inv H10. econstructor. 
      eapply SGet with(x:=x0); eauto. erewrite HeapLookupReplace; eauto. lookupTac. simpl in *. 
      rewrite app_comm_cons in H6. eapply IHspec_multistep in H6; eauto. rewrite replaceOverwrite. 
      rewrite replaceOverwrite in H6. eassumption. eapply spec_multi_trans. eassumption. econstructor. 
      eapply SGet with(x:=x0); eauto. constructor. simpl. eauto. }
     {apply beq_nat_false in eq. apply neqSym in eq. lookupTac. eapply IHspec_multistep in H6; eauto. 
      econstructor. eapply SGet with(x:=x); auto. rewrite lookupReplaceNeq; eauto. 
      rewrite lookupReplaceSwitch; auto. eassumption. eapply spec_multi_trans. eassumption. 
      econstructor. eapply SGet with(x:=x); eauto. constructor. simpl. eauto. }
    }
    {destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq. subst. rewrite H10 in H5. 
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
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite coupleUnion. rewrite <- Union_associative. 
     rewrite <- UnionSwap. eapply IHspec_multistep; eauto. Focus 2. rewrite Union_associative. 
     rewrite <- coupleUnion.  rewrite couple_swap. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SSpec; eauto. rewrite Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. constructor. }
   }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 