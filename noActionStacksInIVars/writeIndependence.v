Require Import SfLib.            
Require Import NonSpec.   
Require Import Spec.  
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import hetList. 
Require Import Coq.Program.Equality. 
Require Import unspec. 
Require Import sets. 
Require Import classifiedStep. 
Require Import Coq.Sets.Powerset_facts.  
Require Import Heap.  
Require Import IndependenceCommon. 

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
  {copy x. copy H3. apply specStepSingleton in H5. invertHyp. copy x. unfoldSetEq x.
   assert(tIn (tUnion T0 (tSingleton x1)) x1). apply Union_intror. constructor.
   apply H6 in H8. inv H8. 
   {copy H3. eapply specStepEmptyIVar in H3; eauto. Focus 3. apply Union_intror. constructor.
    eapply IHspec_multistep in H1. Focus 2. eassumption. Focus 2. auto. Focus 3. auto. 
    invertHyp. exists x. exists x2.  split. copy H9. apply pullOut in H12. rewrite H12. 
    unfoldTac. rewrite UnionSwap. econstructor. eapply specStepChangeUnused. eauto. 
    unfoldTac. rewrite <- UnionSwap. eassumption. split. eassumption. split.
    apply pullOut in H9. rewrite H9. clear H9. inv H8; unfoldTac; invertHyp.
    {econstructor. eapply SBasicStep; eauto. auto. }
    {econstructor. eapply SFork. auto. eauto. }
    {destruct (beq_nat x3 x0) eqn:eq. apply beq_nat_true in eq. subst. 
     erewrite HeapLookupReplace in H3; eauto. inv H3. econstructor. eapply SGet with(x:=x3). 
     apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. auto.  
     rewrite lookupReplaceSwitch. unfoldTac. eassumption. apply beq_nat_false in eq. auto. }
    {destruct (beq_nat x3 x0) eqn:eq. apply beq_nat_true in eq. subst.
     erewrite HeapLookupReplace in H3; eauto. inv H3. econstructor. eapply SPut with(x:=x3). 
     apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. auto. 
     rewrite lookupReplaceSwitch. eassumption. apply beq_nat_false in eq. auto. }
    {destruct (beq_nat x3 x0)eqn:eq. apply beq_nat_true in eq. subst. rewrite lookupExtend in H3. 
     inv H3. econstructor. eapply SNew with(x:=x3). auto. 
     erewrite extendReplaceSwitch; eauto. apply beq_nat_false in eq. auto. }
    {econstructor. eapply SSpec; eauto. eassumption. }
    auto. apply UnionSingletonEq in H4. rewrite H4. unfoldTac. rewrite UnionSwap. auto. auto. 
    apply UnionSingletonEq in H4. rewrite H4. constructor. apply Union_intror. constructor. auto. 
   }
   {inv H9. apply UnionEqTID in H4. invertHyp. clear H4 H9 H10. 
    exists (replace x0 (sfull COMMIT nil SPEC TID M'') H). 
    exists T. split. econstructor. 
    eapply SPut. eauto. auto. simpl. constructor. split. inv H3; unfoldTac; invertHyp; invThreadEq. 
    {inv H8; copy d; eapply uniqueCtxtDecomp in H; eauto; invertHyp; inv H8. }
    {copy d. copy d0. eapply uniqueCtxtDecomp in H; eauto. invertHyp. inv H8. }
    {copy d. copy d0. eapply uniqueCtxtDecomp in H3; eauto. invertHyp. solveByInv. }
    {copy d. copy d0. eapply uniqueCtxtDecomp in H3; eauto. invertHyp. inv H10. copy H2. 
     rewrite H0 in H8. inv H8. assert(d=d0). apply proof_irrelevance. subst. eassumption. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H3; eauto. invertHyp. solveByInv. }
    {copy d; copy d0. eapply uniqueCtxtDecomp in H; eauto. invertHyp. solveByInv. }
    split. rewrite replaceOverwrite. constructor. erewrite HeapLookupReplace; eauto. }
  }
  Grab Existential Variables. apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. 
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
   {copy x. copy H0. apply specStepSingleton in H6. invertHyp. unfoldSetEq H5. 
   assert(tIn (tUnion T0(tSingleton x1)) x1). apply Union_intror. constructor. apply H6 in H5. 
   inv H5.  
   {copy H8. apply pullOut in H8. rewrite H8. clear H8. 
    inversion H0; subst; unfoldTac; invertHyp. 
    {eapply IHspec_multistep in H1;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. Focus 2.
     proveUnionEq x. invertHyp. exists x1. exists x2. split. rewrite UnionSwap. econstructor. 
     eapply specStepChangeUnused. eassumption. unfoldTac. rewrite <- UnionSwap. eassumption. 
     split. eassumption. exists x3. split. econstructor. eapply SBasicStep; eauto. eassumption. 
     eauto. }
    {eapply IHspec_multistep in H1;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. Focus 2.
     proveUnionEq x. invertHyp. exists x1. exists x2. split. rewrite UnionSwap. econstructor. 
     eapply specStepChangeUnused. eassumption. unfoldTac. rewrite <- UnionSwap. eassumption. 
     split. eassumption. exists x3. split. econstructor. eapply SFork; eauto. eassumption. 
     eauto. }
    {destruct (beq_nat x2 x0) eqn:eq. 
     {apply beq_nat_true in eq. subst. rewrite H9 in H1. inv H1. lookupTac.
      eapply IHspec_multistep in H1; eauto. Focus 2. proveUnionEq x.  
      invertHyp. exists x1. exists x2. split. rewrite UnionSwap. econstructor. eapply SGet. 
      eauto. auto. unfoldTac. rewrite <- UnionSwap. eassumption. split. eauto. exists x3. split. 
      econstructor. eapply SGet with (x:=x0). erewrite HeapLookupReplace; eauto. auto. 
      rewrite replaceOverwrite. rewrite replaceOverwrite in H11. eapply H11. eassumption. }
     {apply beq_nat_false in eq. rewrite neqSym in eq. lookupTac. eapply IHspec_multistep in H8; eauto. 
      Focus 2. proveUnionEq x. invertHyp. exists x1. exists x3. split. rewrite UnionSwap. econstructor.
      eapply SGet with(x:=x2). eassumption. auto. unfoldTac. rewrite <- UnionSwap. eassumption. 
      split. eassumption. exists x4. split. econstructor. eapply SGet with(x:=x2). 
      rewrite lookupReplaceNeq. eauto. auto. auto. rewrite lookupReplaceSwitch. eassumption. 
      auto. eauto. }
    }
    {destruct (beq_nat x2 x0) eqn:eq. apply beq_nat_true in eq. subst. rewrite H9 in H1. 
     inv H1. apply beq_nat_false in eq. rewrite neqSym in eq. lookupTac.
     eapply IHspec_multistep in H8; eauto. Focus 2. proveUnionEq x. invertHyp. exists x1. 
     exists x3. split. rewrite UnionSwap. econstructor. eapply SPut; eauto. unfoldTac. 
     rewrite <- UnionSwap. eassumption. split. eassumption. exists x4. split. econstructor. 
     eapply SPut with(x:=x2); eauto. rewrite lookupReplaceNeq. eauto. auto. 
     rewrite lookupReplaceSwitch; auto. eassumption. eauto. }
    {destruct (beq_nat x2 x0) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H8 in H1. 
     inv H1. apply beq_nat_false in eq. rewrite neqSym in eq. lookupTac. 
     eapply IHspec_multistep in H8; eauto. Focus 2. proveUnionEq x. invertHyp. exists x1. 
     exists x3. split. rewrite UnionSwap. econstructor. eapply SNew; eauto. unfoldTac. 
     rewrite <- UnionSwap. eassumption. split. eassumption. exists x4. split. econstructor. 
     eapply SNew with(x:=x2); eauto. erewrite extendReplaceSwitch; eauto. eauto. 
    }
    {eapply IHspec_multistep in H1;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. Focus 2.
     proveUnionEq x. invertHyp. exists x1. exists x2. split. rewrite UnionSwap. econstructor. 
     eapply specStepChangeUnused. eassumption. unfoldTac. rewrite <- UnionSwap. eassumption. 
     split. eassumption. exists x3. split. econstructor. eapply SSpec. eauto. eauto. 
    }
   }
   {inv H8. apply UnionEqTID in x. invertHyp. inv H0; unfoldTac; invertHyp; invThreadEq. 
    {eapply IHspec_multistep in H1;[idtac|eauto|eauto|eauto|eauto|eauto|eauto]. invertHyp. 
     exists x. exists x1. split. econstructor. eapply SBasicStep; eauto. eassumption. 
     split. eassumption. exists x2. split. assumption. eassumption. }
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
   }
   Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 


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
  {copy x. copy H1. apply specStepSingleton in H1. invertHyp. unfoldSetEq H6.
   assert(tIn(tUnion T0(tSingleton x1)) x1). apply Union_intror. constructor. 
   apply H1 in H6. inv H6.  
   {copy H9. apply pullOut in H9. rewrite H9. clear H9. copy H7. destruct x1. destruct p.  
    destruct p. copy H9. eapply specStepFullIVar in H9; eauto. inv H9. 
    {eapply spec_multi_trans. eapply spec_multi_unused. eapply helper. eauto. eapply H11. 
     eapply smulti_step. eapply specStepChangeUnused. eassumption. constructor. 
     eapply IHspec_multistep in H11; eauto. eapply spec_multi_trans. eassumption. 
     apply pullOut in H6. rewrite H6. unfoldTac. rewrite UnionSwap. econstructor. 
     eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap. 
     rewrite subtractSingle. constructor. proveUnionEq x. }
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
      eapply SGet with(x:=x0); eauto. erewrite HeapLookupReplace; eauto. lookupTac. 
      eapply IHspec_multistep in H6; eauto. rewrite replaceOverwrite. rewrite replaceOverwrite in H6. 
      eassumption. eapply spec_multi_trans. eassumption. econstructor. eapply SGet with(x:=x0); eauto. 
      constructor. simpl. eauto. }
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



