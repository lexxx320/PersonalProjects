Require Import erasure. 
Require Import IndependenceCommon. 
Require Import stepWF. 
Require Import nonspeculativeImpliesSpeculative. 

Inductive prog_multistep : sHeap -> pool -> option (sHeap * pool) -> Prop :=
|prog_multi_refl : forall H T, prog_multistep H T (Some (H, T))
|prog_multi_step : forall H H' c T t t',
                prog_step H T t (OK H' T t') -> prog_multistep H' (tUnion T t') c ->
                prog_multistep H (tUnion T t) c
|prog_smulti_error : forall H T t, 
                  prog_step H T t Error -> prog_multistep H (tUnion T t) None. 

Inductive stepPlus : sHeap -> pool -> option (sHeap * pool) -> Prop :=
| plus_step : forall (H H' : sHeap) c (T t t' : pool),
                 prog_step H T t (OK H' T t') ->
                 prog_multistep H' (tUnion T t') c -> stepPlus H (tUnion T t) c
| plus_error : forall (H : sHeap) (T t : pool),
                   prog_step H T t Spec.Error -> stepPlus H (tUnion T t) None.

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' T H,
        pstep PH PT pt (pOK PH' PT pt') -> 
        speculate (pUnion PT pt) T -> PoolWF (pUnion PT pt) -> heapWF PH -> specHeap PH H ->
        exists T' H', stepPlus H T (Some(H', T')) /\
                   speculate (pUnion PT pt') T' /\ specHeap PH' H'. 
Proof.
  intros. inv H0. 
  {apply specUnionComm in H1. invertHyp. inv H1. inv H7. econstructor. econstructor. 
   split. unfoldTac. rewrite Union_associative. econstructor. 
   eapply simBasicStep in H9. eapply CBasicStep. eauto. constructor. split; auto. 
   apply poolWFComm in H2. simpl in H2. invertHyp. eapply basicStepGather in H9; eauto. 
   unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto. 
   constructor. constructor. auto. }
  {copy H9. apply specUnionComm in H1. invertHyp. inv H1. inv H8.
   eapply gatherDecomp in H0; eauto. invertHyp. econstructor. econstructor. split. 
   unfoldTac. rewrite Union_associative. econstructor.
   eapply CSpec with(M:=specTerm M)(N:=specTerm N)(E:=specCtxt E). 
   eapply multi_step. eapply PopSpec. rewrite app_nil_l. simpl. auto. constructor. 
   split. unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto.
   rewrite couple_swap. rewrite coupleUnion. repeat rewrite Union_associative. 
   replace (specRun(specTerm M)(specTerm N)) with (specTerm(pspecRun M N)); auto.  
   rewrite <- specFill. constructor. constructor. rewrite <- Union_associative. 
   apply gatherFill; auto. inv H0. constructor; auto. auto. }
  {copy H9. apply specUnionComm in H1. invertHyp. inv H1. inv H8. 
   eapply gatherDecomp in H0; eauto. invertHyp. inv H0. unfoldTac. 
   repeat rewrite <- Union_associative. rewrite listToSingle. rewrite <- coupleUnion. 
   rewrite couple_swap. repeat rewrite Union_associative. econstructor. econstructor. split.
   econstructor. eapply SpecJoin with (N0:=specTerm M)
                          (M:=specTerm M)(N1:=specTerm N)(E:=specCtxt E); eauto. 
   simpl. constructor. split. unfoldTac. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. rewrite (Union_associative thread x0).
   rewrite (Union_associative thread (Union thread x0 T1)). 
   replace (specJoin(ret(specTerm N)) (specTerm M)) with (specTerm (pspecJoin (pret N) M)); auto. 
   rewrite <- specFill. constructor. constructor. rewrite <- Union_associative. 
   apply gatherFill. auto. constructor; auto. auto. }
  {copy H9. apply specUnionComm in H1. invertHyp. inv H1. inv H8. 
   eapply gatherDecomp in H0; eauto. invertHyp. inv H0. unfoldTac. 
   repeat rewrite <- Union_associative. rewrite listToSingle. rewrite <- coupleUnion. 
   repeat rewrite Union_associative. rewrite <- Union_associative. econstructor. econstructor. split.  
   econstructor. apply decomposeSpec in H9.
   eapply SpecRB with (E:=specTerm N)(E':=specCtxt E)(N0:=specTerm M). eassumption. 
   auto. auto. eapply RBDone. unfold tAdd. unfold Add. unfoldTac. unfold In. 
   apply in_app_iff. right. simpl. left; eauto. eauto.
   constructor. split. unfoldTac. repeat rewrite <- Union_associative. apply specUnionComm'. 
   auto. replace (raise (specTerm N)) with (specTerm (praise N)); auto. rewrite <- specFill.
   apply gatherSourceProg in H12. Focus 2. apply poolWFComm in H2. simpl in H2. invertHyp.
   apply ptrmDecomposeWF in H9; auto. inv H9. auto. subst. unfold Add. simpl. 
   rewrite Union_associative. constructor. constructor. apply gatherFill; auto. auto. }
  {copy H9. apply specUnionComm in H1. invertHyp. inv H1. inv H8. 
   eapply gatherDecomp in H0; eauto. invertHyp. inv H0. copy H9. rewrite poolWFComm in H2. 
   simpl in H2. invertHyp. apply ptrmDecomposeWF in H9; auto. simpl in H9. 
   unfoldTac. rewrite Union_associative. econstructor. econstructor. split. econstructor. 
   eapply Fork with (M:=specTerm M)(E:=specCtxt E). eauto. eapply multi_step. eapply PopFork. 
   rewrite app_nil_l. simpl. auto. auto. constructor. unfoldTac. rewrite <- Union_associative. 
   split. apply specUnionComm'. auto. copy H7. apply gatherSourceProg in H7; auto. rewrite H7. 
   rewrite union_empty_r. rewrite coupleUnion. unfold pCouple. unfold Couple. simpl. 
   replace (ret unit) with (specTerm (pret punit)); auto. rewrite <- specFill. constructor. 
   rewrite <- union_empty_l. constructor. constructor. subst. eauto. 
   rewrite <- union_empty_r. apply gatherFill. auto. repeat constructor. auto. }
  {copy H11. apply specUnionComm in H1. invertHyp. inv H1. inv H8. copy H10. 
   eapply specHeapLookupFull in H10; eauto. invertHyp. 
   eapply gatherDecomp in H0; eauto. invertHyp. 
   econstructor. econstructor. split. unfoldTac. rewrite Union_associative. econstructor. 
   eapply Get with (N:=specTerm M)(E:=specCtxt E). eauto. auto. eapply multi_step. eapply PopRead. 
   rewrite app_nil_l. simpl; auto. rewrite app_nil_r. rewrite app_nil_l. auto. introsInv. 
   erewrite HeapLookupReplace; eauto. auto. rewrite replaceOverwrite. rewrite replaceSame. 
   constructor. eauto. unfoldTac. rewrite Union_associative. repeat rewrite <- Union_associative. 
   split. apply specUnionComm'. auto. inv H0. inv H9. simpl. 
   replace (ret(specTerm M)) with (specTerm(pret M)); auto. rewrite <- specFill. 
   constructor. constructor. rewrite <- union_empty_r. apply gatherFill. auto. constructor.
   gatherTac M. copy H8. apply gatherSourceProg in H8; eauto. subst. auto. Focus 2. auto.
   eapply lookupSourceProg; eauto. } 
  {apply specUnionComm in H1. invertHyp. inv H1. inv H8. copy H7. 
   eapply gatherDecomp in H7; eauto. invertHyp. rewrite poolWFComm in H2. simpl in H2. 
   invertHyp. econstructor. econstructor. split. unfoldTac. rewrite Union_associative. 
   econstructor. eapply Put with (N:=specTerm M)(E:=specCtxt E).
   simpl in *. eauto. eapply specHeapLookupEmpty; eauto. auto. eapply multi_step. 
   eapply PopWrite. rewrite app_nil_l. simpl; auto. erewrite HeapLookupReplace; eauto. 
   eapply specHeapLookupEmpty; eauto. auto. rewrite replaceOverwrite. constructor. 
   split. unfoldTac. rewrite <- Union_associative. apply specUnionComm'. auto. 
   inv H6. inv H13. unfoldTac. simpl in *. copy H1. apply ptrmDecomposeWF in H6; auto. inv H6. 
   eapply gatherSourceProg in H15; eauto. subst. rewrite union_empty_r in *.  
   replace (ret unit) with (specTerm (pret punit)); auto. rewrite <- specFill. constructor. 
   constructor. rewrite <- union_empty_r. apply gatherFill. auto. repeat constructor. 
   apply specHeapReplaceFull; auto. }
  {apply specUnionComm in H1. invertHyp. inv H1. inv H7. copy H10. 
   eapply gatherDecomp in H10; eauto. invertHyp. rewrite poolWFComm in H2. simpl in H2. 
   invertHyp. econstructor. econstructor. split. unfoldTac. rewrite Union_associative. 
   econstructor. copy p. eapply specHeapLookupNone in H8; eauto.
   eapply New with (E:=specCtxt E)(x:=x). auto. eapply multi_step. 
   eapply PopNewEmpty.  rewrite app_nil_l. simpl; auto. rewrite lookupExtend. auto. 
   auto. erewrite replaceExtendOverwrite; eauto. constructor. unfoldTac.
   rewrite <- Union_associative. apply specUnionComm'. auto. 
   replace (ret(fvar x)) with (specTerm(pret(pfvar x))); auto. rewrite <- specFill. 
   constructor. constructor. apply gatherFill; auto. constructor. inv H6. constructor. 
   apply specHeapExtend; auto. }
  Grab Existential Variables. 
  {eapply specHeapLookupNone; eauto. }
  {apply decomposeSpec in H1. auto. }
  {eapply specHeapLookupNone; eauto. }
  {apply decomposeSpec in H1; auto. }
  {apply decomposeSpec in H11. auto. }
  {apply decomposeSpec in H0. auto. }
  {apply decomposeSpec in H9; auto. }
  {apply decomposeSpec in H9; auto. }
Qed. 

Theorem nonspecImpliesSpecStar : forall PH PH' PT H PT' T,
        pmultistep PH PT (Some(PH', PT')) -> 
        speculate PT T -> PoolWF PT -> heapWF PH -> specHeap PH H ->
        exists T' H', multistep H T (Some(H', T')) /\
                   speculate PT' T' /\ specHeap PH' H'. 
Proof.
  intros. remember (Some(PH',PT')). genDeps{H; T}. induction H0; intros.  
  {inv Heqo. eauto. }
  {intros. subst. copy H0. eapply nonspecImpliesSpec in H0; eauto. invertHyp.
   copy H7. apply pstepWF in H7; auto. invertHyp. 
   eapply IHpmultistep in H10; eauto. invertHyp. econstructor. econstructor. split.
   inv H8. eapply multi_step. eauto. eapply multi_trans; eauto. eauto. }
  {inv Heqo. }
Qed. 









