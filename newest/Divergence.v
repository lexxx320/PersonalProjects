Require Import erasure.    
Require Import progStepImpliesSpec. 
Require Import progStepWF. 
Require Import nonspeculativeImpliesSpeculative. 

(*Definitions*)
CoInductive ParDiverge : pHeap -> pPool -> Prop :=
|divergeStep : forall T1 T2 T2' H H',
                 pstep H T1 T2 (pOK H' T1 T2') -> 
                 ParDiverge H' (pUnion T1 T2') -> ParDiverge H (pUnion T1 T2)
.

CoInductive ParDiverge' : pHeap -> pPool -> Prop :=
|divergeStep' : forall H H' T T',
                 pstepPlus H T H' T' -> ParDiverge' H' T' -> ParDiverge' H T. 

Theorem ParDivergeEq : forall H T, ParDiverge H T <-> ParDiverge' H T. 
Proof. 
  intros. split; intros. 
  {genDeps{T; H}. cofix. intros. inv H0. econstructor. econstructor. eauto. 
   constructor. eapply ParDivergeEq; eassumption. }
  {genDeps{T; H}. cofix CH. intros. inv H0. inv H2. inv H4. 
   {econstructor. eassumption. eapply CH. eauto. }
   {assert(ParDiverge' H'0 (pUnion T t0)). econstructor. econstructor. 
    eassumption. eassumption. assumption. econstructor. eassumption. 
    eapply CH. rewrite <- H2. eauto. }
  }
Qed. 

Theorem eActTerm : forall x, exists M, actionTerm x M. 
Proof.
  intros. destruct x; repeat econstructor. 
Qed. 

Ltac actTermTac x := assert(exists M, actionTerm x M) by apply eActTerm; invertHyp. 

Theorem getLastApp : forall (T:Type) a c (b:T),
                       last(a++[b]) c = b.
Proof.
  induction a; intros. 
  {simpl. auto. }
  {simpl. destruct (a0++[b]) eqn:eq. 
   {invertListNeq. }
   {rewrite <- eq. eauto. }
  }
Qed. 

Theorem unspecLastActPool : forall tid s a s2 M' M, 
                         actionTerm a M' ->
                         unspecPool(tSingleton(tid,unlocked(s++[a]),s2,M)) = 
                         tSingleton(tid,unlocked nil,s2,M'). 
Proof.
  induction s; intros. 
  {simpl. inv H; auto. }
  {simpl. destruct (s++[a0])eqn:eq. 
   {invertListNeq. }
   {rewrite <- eq. rewrite getLastApp. inv H; auto. }
  }
Qed. 

Theorem actionTrmConsSame'' : forall a M' N s1 s2 tid,
                             actionTerm a M' -> 
                             unspecPool(tSingleton(tid,unlocked s1,s2,M')) = 
                             unspecPool(tSingleton(tid,aCons a (unlocked s1),s2,N)). 
Proof.
  induction s1; intros. 
  {simpl. inv H; auto.  }
  {simpl. destruct s1. auto. erewrite getLastNonEmpty; eauto. }
Qed. 

Theorem actionTrmConsSame' : forall a M' N s1 s2 tid,
                             actionTerm a M' -> 
                             unspecPool(tSingleton(tid,s1,s2,M')) = 
                             unspecPool(tSingleton(tid,aCons a s1,s2,N)). 
Proof.
  intros. destruct s1; auto. apply actionTrmConsSame''. auto. 
Qed. 

Theorem unspecEmpty : forall tid s1 s2 M, 
                unspecPool(tSingleton(tid,locked s1,s2,M)) = (Empty_set thread).
Proof.
  intros. simpl. auto. 
Qed. 

Ltac sswfHelper := eapply spec_multi_trans;[eassumption|econstructor].

Hint Constructors actionTerm spec_multistep. 

Theorem specStepWF : forall H T H' t t',
                       wellFormed H (tUnion T t) -> spec_step H T t H' T t' ->
                       wellFormed H' (tUnion T t'). 
Proof.
  intros. inv H1. 
  {inv H0. econstructor. rewrite unspecUnionComm in *. destruct s1. 
   {simpl in *. sswfHelper; auto. eapply SBasicStep; eauto. }
   {destructLast l. inv H3. invertHyp. actTermTac x. erewrite unspecLastActPool in *; eauto. 
    sswfHelper; eauto. eapply SBasicStep; eauto. }
   {simpl in *. sswfHelper; eauto. eapply SBasicStep; eauto. }
  }
  {unfoldTac. inv H0. econstructor. rewrite coupleUnion. repeat rewrite unspecUnionComm in *.
   destruct b. 
   {simpl in *. sswfHelper. eapply SFork; eauto. constructor. }
   {erewrite <- actionTrmConsSame'. rewrite unspecEmpty. unfoldTac. rewrite union_empty_r. 
    sswfHelper. eapply SFork; eauto. constructor. auto. }
   {simpl in *.  sswfHelper. eapply SFork; eauto. constructor. }
  }
  {inv H0. econstructor. rewrite unspecUnionComm in *. destruct b. 
   {simpl in *. erewrite unspecHeapRBRead; eauto. sswfHelper. eapply SGet; eauto. constructor. }
   {erewrite unspecHeapRBRead; eauto. erewrite <- actionTrmConsSame'; auto. sswfHelper. 
    eapply SGet; eauto. constructor. }
   {simpl in *. erewrite unspecHeapRBRead; eauto. sswfHelper. eapply SGet; eauto. constructor. }
  }
  {inv H0. constructor. rewrite unspecHeapAddWrite; auto. rewrite unspecUnionComm in *.
   destruct b. 
   {simpl in *. sswfHelper. eapply SPut; eauto. constructor. }
   {erewrite <- actionTrmConsSame'; eauto. sswfHelper. eapply SPut; eauto. constructor. }
   {simpl in *. sswfHelper. eapply SPut; eauto. constructor. }
  }
  {inv H0. constructor. rewrite unspecHeapExtend. rewrite unspecUnionComm in *. destruct b. 
   {sswfHelper. eapply SNew; eauto. constructor. }
   {erewrite <- actionTrmConsSame'; eauto. sswfHelper. eapply SNew; eauto. constructor. }
   {sswfHelper. eapply SNew; eauto. constructor. }
  }
  {inv H0. constructor. unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
   rewrite unspecEmpty. unfoldTac. rewrite union_empty_r. destruct b. 
   {sswfHelper. eapply SSpec; eauto. constructor. }
   {erewrite <- actionTrmConsSame'; eauto. sswfHelper. eapply SSpec; eauto. constructor. }
   {sswfHelper. eapply SSpec; eauto. constructor. }
  }
Qed. 

Theorem specMultiWF : forall H T H' T', wellFormed H T -> spec_multistep H T H' T' ->
                                        wellFormed H' T'. 
Proof.
  intros. induction H1. 
  {auto. }
  {eapply specStepWF in H; eauto. }
Qed. 

Theorem pstepDiffUnused : forall H H' T T' t t',
                            pstep H T t (pOK H' T t') ->
                            pstep H T' t (pOK H' T' t'). 
Proof.
  intros. Hint Constructors pstep. inv H0; eauto. 
Qed. 

Theorem pstepSingleton : forall H T1 T2 H' T2', 
                           pstep H T1 T2 (pOK H' T1 T2') -> exists t, T2 = Single ptrm t. 
Proof.
  intros. inv H0; eauto. 
Qed.
 
CoInductive SpecDiverge : sHeap -> pool-> Prop :=
|specDiverge : forall T1 T2 T2' H H' H'' T,
                 spec_multistep H T H' (tUnion T1 T2) -> 
                 prog_step H' T1 T2 (OK H'' T1 T2') -> 
                 SpecDiverge H'' (tUnion T1 T2') -> SpecDiverge H T.

Theorem SpecDivergeParDiverge' : forall H T,
                wellFormed H T -> 
                SpecDiverge H T -> ParDiverge' (eraseHeap H) (erasePool T). 
Proof.
  cofix CH. intros. inv H1. copy H3. apply specMultiWF in H3; auto. 
  eapply spec_multistepErase in H1. invertHyp. rewrite H6. rewrite H2.
  rewrite eraseUnionComm in *. copy H4. apply prog_specImpliesNonSpec in H4; auto. 
  invertHyp.  apply prog_stepWF in H1; auto. rewrite eraseUnionComm in *. 
  econstructor. eassumption. eapply CH. eauto. eauto. 
Qed. 

Theorem SpecDivergeParDiverge : forall H T,
              wellFormed H T -> 
              SpecDiverge H T -> ParDiverge (eraseHeap H) (erasePool T). 
Proof.
  intros. apply SpecDivergeParDiverge' in H1. rewrite ParDivergeEq. auto. auto. 
Qed. 

Theorem ParDivergeSpecDiverge : forall H T H' T',
                                  ParDiverge H T -> specHeap H H' -> speculate T T' ->
                                  heapWF H -> PoolWF T -> SpecDiverge H' T'. 
Proof.
  cofix CH. intros. inv H0. inversion H6; subst. 
  {apply specUnionComm in H2. invertHyp. inv H0. inv H8. unfoldTac. rewrite Union_associative. 
   econstructor. constructor. eapply CBasicStep. eapply simBasicStep. eauto. eapply CH; eauto. 
   apply poolWFComm in H4. simpl in H4. invertHyp. eapply basicStepGather in H11; eauto. 
   unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto.  
   constructor. constructor. auto. eapply pstepWF in H6; eauto. invertHyp. auto. }
  {copy H10. apply specUnionComm in H2. invertHyp. inv H2. inv H9.
   eapply gatherDecomp in H; eauto. invertHyp. unfoldTac. rewrite Union_associative.
   econstructor. eapply smulti_step. eapply SSpec with(M:=specTerm M)(N:=specTerm N)(E:=specCtxt E). 
   constructor. eapply CPopSpec. rewrite app_nil_l. simpl. auto. eapply CH; eauto.  
   unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto.
   rewrite couple_swap. rewrite coupleUnion. repeat rewrite Union_associative. 
   replace (specRun(specTerm M)(specTerm N)) with (specTerm(pspecRun M N)); auto.  
   rewrite <- specFill. constructor. constructor. rewrite <- Union_associative. 
   apply gatherFill; auto. inv H. constructor; auto. eapply pstepWF in H6; auto.
   invertHyp. auto. }
  {copy H10. apply specUnionComm in H2. invertHyp. inv H2. inv H9. 
   eapply gatherDecomp in H; eauto. invertHyp. inv H. unfoldTac. 
   repeat rewrite <- Union_associative. rewrite listToSingle. rewrite <- coupleUnion. 
   rewrite couple_swap. repeat rewrite Union_associative. econstructor. constructor. 
   eapply CSpecJoin with (N0:=specTerm M)
                          (M:=specTerm M)(N1:=specTerm N)(E:=specCtxt E); eauto. 
   simpl. eapply CH; eauto. unfoldTac. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. rewrite (Union_associative thread x0).
   rewrite (Union_associative thread (Union thread x0 T0)). 
   replace (specJoin(ret(specTerm N)) (specTerm M)) with (specTerm (pspecJoin (pret N) M)); auto. 
   rewrite <- specFill. constructor. constructor. rewrite <- Union_associative. 
   apply gatherFill. auto. constructor; auto. eapply pstepWF in H6; eauto. invertHyp. auto. }
  {copy H10. apply specUnionComm in H2. invertHyp. inv H2. inv H9. 
   eapply gatherDecomp in H; eauto. invertHyp. inv H. unfoldTac. 
   repeat rewrite <- Union_associative. rewrite listToSingle. rewrite <- coupleUnion. 
   repeat rewrite Union_associative. rewrite <- Union_associative. econstructor. constructor.
   apply decomposeSpec in H10.
   eapply CSpecRB with (E:=specTerm N)(E':=specCtxt E)(N0:=specTerm M). eassumption. 
   auto. auto. eapply RBDone. unfold tAdd. unfold Add. unfoldTac. unfold In. 
   apply in_app_iff. right. simpl. left; eauto. eauto. eapply CH; eauto. 
   unfoldTac. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. replace (raise (specTerm N)) with (specTerm (praise N)); auto. rewrite <- specFill.
   apply gatherSourceProg in H13. Focus 2. apply poolWFComm in H4. simpl in H4. invertHyp.
   apply ptrmDecomposeWF in H10; auto. inv H10. auto. subst. unfold Add. simpl. 
   rewrite Union_associative. constructor. constructor. apply gatherFill; auto. 
   eapply pstepWF in H6; auto. invertHyp. auto. }
  {copy H10. apply specUnionComm in H2. invertHyp. inv H2. inv H9. 
   eapply gatherDecomp in H; eauto. invertHyp. inv H. copy H10. rewrite poolWFComm in H4. 
   simpl in H4. invertHyp. apply ptrmDecomposeWF in H10; auto. simpl in H10. 
   unfoldTac. rewrite Union_associative. econstructor. eapply smulti_step. 
   eapply SFork with (M:=specTerm M)(E:=specCtxt E). eauto. constructor. eapply CPopFork. 
   rewrite app_nil_l. simpl. auto. auto. eapply CH; eauto. unfoldTac. rewrite <- Union_associative. 
   apply specUnionComm'. auto. copy H8. apply gatherSourceProg in H8; auto. rewrite H8. 
   rewrite union_empty_r. rewrite coupleUnion. unfold pCouple. unfold Couple. simpl. 
   replace (ret unit) with (specTerm (pret punit)); auto. rewrite <- specFill. constructor. 
   rewrite <- union_empty_l. constructor. constructor. subst. eauto. 
   rewrite <- union_empty_r. apply gatherFill. auto. repeat constructor. 
   eapply pstepWF in H6; auto. invertHyp. auto. rewrite poolWFComm. simpl. split; auto. }
  {copy H12. apply specUnionComm in H2. invertHyp. inv H2. inv H9. copy H11. 
   eapply specHeapLookupFull in H11; eauto. invertHyp. 
   eapply gatherDecomp in H; eauto. invertHyp. unfoldTac. rewrite Union_associative. 
   econstructor. eapply smulti_step.
   eapply SGet with (N:=specTerm M)(E:=specCtxt E). eauto. auto. constructor. eapply CPopRead. 
   rewrite app_nil_l. simpl; auto. rewrite app_nil_r. rewrite app_nil_l. auto. introsInv. 
   erewrite HeapLookupReplace; eauto. auto. rewrite replaceOverwrite. rewrite replaceSame. 
   eapply CH; eauto. unfoldTac. rewrite Union_associative. repeat rewrite <- Union_associative. 
   apply specUnionComm'. auto. inv H. inv H10. simpl. 
   replace (ret(specTerm M)) with (specTerm(pret M)); auto. rewrite <- specFill. 
   constructor. constructor. rewrite <- union_empty_r. apply gatherFill. auto. constructor.
   gatherTac M. copy H9. apply gatherSourceProg in H9; eauto. subst. auto.
   eapply lookupSourceProg; eauto. eapply pstepWF in H6; auto. invertHyp. auto. auto. }
  {apply specUnionComm in H2. invertHyp. inv H2. inv H10. copy H8. 
   eapply gatherDecomp in H8; eauto. invertHyp. rewrite poolWFComm in H4. simpl in H4. 
   invertHyp. unfoldTac. rewrite Union_associative. econstructor. eapply smulti_step.
   eapply SPut with (N:=specTerm M)(E:=specCtxt E).
   eapply specHeapLookupEmpty; eauto. auto. constructor.  
   eapply CPopWrite. rewrite app_nil_l. simpl; auto. erewrite HeapLookupReplace; eauto. 
   eapply specHeapLookupEmpty; eauto. auto. rewrite replaceOverwrite. eapply CH; eauto. 
   Focus 2. unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto. 
   inv H8. inv H15. unfoldTac. simpl in *. copy H2. apply ptrmDecomposeWF in H8; auto. inv H8. 
   eapply gatherSourceProg in H17; eauto. subst. rewrite union_empty_r in *.  
   replace (ret unit) with (specTerm (pret punit)); auto. rewrite <- specFill. constructor. 
   constructor. rewrite <- union_empty_r. apply gatherFill. auto. repeat constructor. 
   apply specHeapReplaceFull; auto. apply pstepWF in H6; auto. invertHyp; auto. 
   rewrite poolWFComm. simpl. auto. apply pstepWF in H6; auto. invertHyp. auto. 
   rewrite poolWFComm. simpl. auto. }
  {apply specUnionComm in H2. invertHyp. inv H2. inv H9. copy H11. unfoldTac. rewrite Union_associative. 
   eapply gatherDecomp in H11; eauto. invertHyp. rewrite poolWFComm in H4. simpl in H4. 
   invertHyp. econstructor. eapply smulti_step. copy p. eapply specHeapLookupNone in H10; eauto.
   eapply SNew with (E:=specCtxt E)(x:=x). auto. constructor. 
   eapply CPopNewEmpty.  rewrite app_nil_l. simpl; auto. rewrite lookupExtend. auto. 
   auto. erewrite replaceExtendOverwrite; eauto. eapply CH; eauto. Focus 2.  unfoldTac.
   rewrite <- Union_associative. apply specUnionComm'. auto. 
   replace (ret(fvar x)) with (specTerm(pret(pfvar x))); auto. rewrite <- specFill. 
   constructor. constructor. apply gatherFill; auto. constructor. inv H8. constructor. 
   apply specHeapExtend; auto. eapply pstepWF in H6; auto. invertHyp. auto. 
   rewrite poolWFComm. simpl. auto. eapply pstepWF in H6; auto. invertHyp. auto. 
   rewrite poolWFComm. simpl. auto. }
  Grab Existential Variables. 
  {eapply specHeapLookupNone; eauto. }
  {apply decomposeSpec in H2. auto. }
  {eapply specHeapLookupNone; eauto. }
  {apply decomposeSpec in H2. auto. }
  {apply decomposeSpec in H12. auto. }
  {apply decomposeSpec in H. auto. }
  {apply decomposeSpec in H10; auto. }
  {apply decomposeSpec in H10; auto. }
Qed. 













