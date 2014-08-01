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

Theorem newFastForward : forall H T H' T' TID x M' E s2 d s1' p M,
         heap_lookup x H = None -> decompose M' E new ->
         spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M'))) H' 
                        (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,M))) ->
         exists H'' T'',
           spec_multistep H (tUnion T (tSingleton(TID,unlocked nil,s2,M'))) H''
                         (tUnion T'' (tSingleton(TID,unlocked [nAct M' E d x],s2,fill E (ret (fvar x))))) /\
           spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked [nAct M' E d x],s2,fill E (ret (fvar x)))))
                          H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,M)))  /\
           spec_multistep (extend x (sempty COMMIT) H p) T 
                          (replace x (sempty COMMIT) H'') T'' /\ 
           heap_lookup x H'' = Some(sempty SPEC).
Proof.
  intros. dependent induction H2. 
  {apply UnionEqTID in x. invertHyp. inv H2. invertListNeq. }
  {startIndCase. eqIn H4. inv H5. 
   {copy H3. eapply specStepNoneIVar in H3; eauto. Focus 3. apply Union_intror. constructor.
    Focus 2. apply UnionSingletonEq in x. rewrite x. constructor. apply Union_intror. constructor. 
    auto. eapply IHspec_multistep with(p:=H3)in H1. Focus 2. eassumption. Focus 2. auto. Focus 3. auto. 
    invertHyp. exists x2. exists x3. split. copy H7. apply pullOut in H10. rewrite H10. 
    unfoldTac. rewrite UnionSwap. econstructor. eapply specStepChangeUnused. eauto. 
    unfoldTac. rewrite <- UnionSwap. eassumption. split. eassumption. split.
    apply pullOut in H7. rewrite H7. clear H7. inv H5; unfoldTac; invertHyp.
    {econstructor. eapply SBasicStep; eauto. proofsEq p H3. eassumption. }
    {econstructor. eapply SFork. auto. proofsEq p H3. eauto. }
    {destruct (beq_nat x4 x0) eqn:eq. apply beq_nat_true in eq. subst. rewrite H0 in H10.
     inv H10. apply beq_nat_false in eq. econstructor. eapply SGet with(x:=x4); auto. 
     erewrite lookupExtendNeq; eauto. erewrite <- extendReplaceSwitch; eauto. }
    {destruct (beq_nat x4 x0) eqn:eq. apply beq_nat_true in eq. subst.
     rewrite H0 in H10. inv H10. apply beq_nat_false in eq. econstructor. eapply SPut with(x:=x4). 
     erewrite lookupExtendNeq; eauto. auto. erewrite <- extendReplaceSwitch; eauto. }
    {destruct (beq_nat x4 x0)eqn:eq. apply beq_nat_true in eq. subst. 
     copy H3. erewrite lookupExtend in H5. inv H5. apply beq_nat_false in eq. 
     econstructor. eapply SNew with(x:=x4). auto. erewrite extendExtendSwitch. eassumption. }
    {econstructor. eapply SSpec; eauto. proofsEq p H3. eassumption. }
    auto. proveUnionEq x.
   }
   {inv H7. apply UnionEqTID in x. invertHyp. clear H5 H7 H9. econstructor. 
    exists T. split. econstructor. eapply SNew with (x:=x0)(p:=p). eauto. simpl. constructor.
    split. inv H3; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
    {inv H7; falseDecomp. }
    {simpl in *. copy H2. firstActTac H2. inv H2. proofsEq d d0. proofsEq p p0. eassumption. }
    split. erewrite replaceExtendOverwrite. constructor. rewrite lookupExtend. auto. 
   }
  }
  Grab Existential Variables. eapply lookupExtendNeq; eauto.  
Qed. 

Theorem stepReplaceEmpty : forall H T t H' t' x,
                             heap_lookup x H = Some(sempty SPEC) -> 
                             heap_lookup x H' = Some(sempty SPEC) ->
                             spec_step H T t H' T t' -> 
                             spec_step (replace x (sempty COMMIT) H) T t 
                                       (replace x (sempty COMMIT) H') T t'. 
Proof.
  intros. inv H2; auto.
  {destruct (beq_nat x0 x) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H3 in H0. inv H0. }
   {eapply SGet with(x:=x0). apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. 
    rewrite lookupReplaceSwitch. auto. apply beq_nat_false in eq. auto. }
  }
  {destruct (beq_nat x0 x) eqn:eq. 
   {apply beq_nat_true in eq. subst. erewrite HeapLookupReplace in H1; eauto. inv H1. }
   {apply beq_nat_false in eq. eapply SPut. erewrite lookupReplaceNeq; eauto. 
    erewrite lookupReplaceSwitch; eauto. }
  }
  {destruct (beq_nat x0 x) eqn:eq. 
   {apply beq_nat_true in eq. subst. copy p. rewrite H2 in H0. inv H0. }
   {apply beq_nat_false in eq. eapply SNew; eauto. erewrite extendReplaceSwitch; eauto. }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 

Theorem smultiReplaceEmpty : forall H T T' H' x,
                             heap_lookup x H = Some(sempty SPEC) -> 
                             heap_lookup x H' = Some(sempty SPEC) ->
                             spec_multistep H T H' T' -> 
                             spec_multistep (replace x (sempty COMMIT) H) T 
                                       (replace x (sempty COMMIT) H') T'. 
Proof.
  intros. induction H2. 
  {constructor. }
  {copy H. apply specStepSingleton in H3. invertHyp. copy H. 
   eapply specStepEmptyIVar' in H; eauto. eapply stepReplaceEmpty in H3; eauto. 
   econstructor. eauto. auto. }
Qed. 

Theorem newSimPureStepsEmpty : forall H T H' T' TID x M' E d N N' N'' s2 s1',
       eraseTrm s1' N' N'' -> 
       heap_lookup x H = Some(sempty SPEC) ->       
       heap_lookup x H' = Some(sempty SPEC)-> 
       spec_multistep H (tUnion T (tSingleton(TID,unlocked[nAct M' E d x],s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,N'))) ->
       exists H'' T'',
         spec_multistep H (tUnion T (tSingleton(TID,unlocked[nAct M' E d x],s2,N))) 
                        H'' (tUnion T'' (tSingleton(TID,unlocked[nAct M' E d x],s2,N''))) /\
         spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked[nAct M' E d x],s2,N''))) 
                        H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,N'))) /\
         spec_multistep (replace x (sempty COMMIT) H) T 
                        (replace x (sempty COMMIT)H'') T'' /\
         heap_lookup x H'' = Some(sempty SPEC).
Proof.
  intros. dependent induction H3. 
  {apply UnionEqTID in x. invertHyp. inv H. destruct s1'; inv H5; try invertListNeq. 
   inv H0; try invertListNeq. repeat econstructor. eauto. }
  {startIndCase. eqIn H5. inv H6. 
   {copy H4. eapply specStepEmptyIVar' in H4; eauto. copy H4. 
    eapply IHspec_multistep in H4;[idtac|eauto|idtac|auto|proveUnionEq x|auto|auto].
    Focus 2. auto. invertHyp. econstructor. econstructor. split. takeTStep. eassumption.  
    split. assumption. split. Focus 2. auto. eapply stepReplaceEmpty in H6; eauto. 
    apply pullOut in H8. rewrite H8. econstructor. eapply specStepChangeUnused. eauto. 
    assumption. }
   {inv H8. apply UnionEqTID in x. invertHyp. clear H6 H8 H10. 
    inversion H4; unfoldTac; invertHyp; invThreadEq. 
    {eapply IHspec_multistep in H1;[idtac|eauto|idtac|auto|auto|auto|auto]; auto. 
     invertHyp. econstructor. econstructor. split. econstructor. eapply SBasicStep; eauto.
     eassumption. split; auto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. 
     do 4 econstructor. simpl in *. econstructor. eapply SFork; eauto. eassumption. 
     split. constructor. auto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. 
     do 4 econstructor. simpl in *. destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq.
     subst. rewrite H8 in H1. inv H1. apply beq_nat_false in eq. econstructor. 
     eapply SGet with(x:=x); eauto. simpl in *. eassumption. split. constructor. auto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. 
     do 4 econstructor. simpl in *. destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq.
     subst. eapply smultiEmptyFull in H6; eauto. contradiction. erewrite HeapLookupReplace; eauto. 
     rewrite H8 in H1. inv H1. auto. apply beq_nat_false in eq. econstructor. 
     eapply SPut with(x:=x); eauto. simpl in *. eassumption. split. constructor. auto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. 
     do 4 econstructor. simpl in *. destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq.
     subst. copy p. rewrite H0 in H1. inv H1. apply beq_nat_false in eq. econstructor. 
     eapply SNew with(x:=x); eauto. simpl in *. eassumption. split. constructor. auto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. 
     do 4 econstructor. econstructor. eapply SSpec; eauto. simpl in *. eassumption. 
     split. constructor. auto. }
   }
  }
Qed.

Theorem newSimActionStepsEmpty : forall H T H' T' TID x M' E d N N' H'' T'' N'' s2 s1 s1' a,
       eraseTrm (s1'++[a]) N' N'' ->
       heap_lookup x H = Some(sempty SPEC) ->       
       heap_lookup x H' = Some(sempty SPEC) -> 
       spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked [nAct M' E d x],s2,N'')))
                      H (tUnion T (tSingleton(TID,unlocked(s1++[nAct M' E d x]),s2,N))) ->
       spec_multistep H (tUnion T (tSingleton(TID,unlocked(s1++[nAct M' E d x]),s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[a]++[nAct M' E d x]),s2,N'))) ->
       spec_multistep (replace x (sempty COMMIT) H)
                      (tUnion T (tSingleton(TID,unlocked s1,nAct M' E d x::s2,N))) 
                      (replace x (sempty COMMIT) H')
                      (tUnion T' (tSingleton(TID,unlocked (s1'++[a]), nAct M' E d x::s2,N'))).
Proof.
  intros. dependent induction H4; intros. 
  {apply UnionEqTID in x. invertHyp. inv H.
   replace[a;nAct M' E d x0] with ([a]++[nAct M' E d x0]) in H6; auto. 
   rewrite app_assoc in H6. apply app_inj_tail in H6. invertHyp. rewrite H2 in H1. 
   inv H1. constructor. }
  {startIndCase. eqIn H6. inv H7.   
   {copy H9. apply pullOut in H9. rewrite H9. clear H9. copy H5. eapply specStepEmptyIVar' in H5; eauto. 
    copy H5. eapply IHspec_multistep in H5;[idtac|eauto|idtac|auto|auto|auto|auto|auto]; auto.
    takeTStep. eapply stepReplaceEmpty. auto. eapply H10. eapply specStepChangeUnused. 
    eauto. unfoldTac. rewrite <- UnionSwap. eassumption. eapply spec_multi_trans. eassumption. 
    takeTStep. repeat rewrite subtractSingle. constructor. proveUnionEq x.
    rewrite subtractSingle. auto. }
   {inv H9. apply UnionEqTID in x. invertHyp. inv H7. copy H5. eapply specStepEmptyIVar' in H5; eauto.  
    inversion H7; subst; unfoldTac; invertHyp; invThreadEq.  
    {copy H3. eapply stackNonNil in H3; eauto. destruct s1. exfalso. apply H3. auto. 
     econstructor. eapply SBasicStep; eauto. constructor. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eauto. econstructor. eapply SBasicStep; eauto. constructor.
     intros c. subst. apply eraseTrmApp in H0. inv H0; inv H12; falseDecomp. }
    {econstructor. eapply SFork; eauto. simpl. unfoldTac. rewrite coupleUnion. 
     rewrite <- Union_associative. rewrite UnionSwap. eapply IHspec_multistep; eauto. 
     Focus 2. rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     unfold numForks. simpl. simpl. eauto. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite <- plus_comm. simpl. rewrite plus_comm. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SFork; eauto. rewrite Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. simpl. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite plus_comm. simpl. rewrite plus_comm. constructor. }
    {destruct(beq_nat x x0) eqn:eq. 
     {apply beq_nat_true in eq. subst. rewrite H1 in H12. inv H12. }
     {apply beq_nat_false in eq. apply neqSym in eq. lookupTac.
      eapply IHspec_multistep in H10;[idtac|eauto|idtac|auto|auto|auto|auto|auto]; auto.
      econstructor. eapply SGet with(x:=x); auto. rewrite lookupReplaceNeq; eauto. 
      rewrite lookupReplaceSwitch; auto. eassumption. eapply spec_multi_trans. eassumption. 
      econstructor. eapply SGet with(x:=x); eauto. constructor. simpl. eauto. }
    }
    {destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq. subst. rewrite H12 in H1. 
     inv H1. eapply smultiEmptyFull in H4; eauto. contradiction. erewrite HeapLookupReplace; eauto. 
     apply beq_nat_false in eq. apply neqSym in eq. lookupTac.
     eapply IHspec_multistep in H10;[idtac|eauto|idtac|auto|auto|auto|auto|auto]; auto.
     econstructor. eapply SPut with(x:=x). 
     rewrite lookupReplaceNeq; eauto. auto. rewrite lookupReplaceSwitch; auto. simpl. 
     eassumption. eapply spec_multi_trans. eassumption. econstructor. eapply SPut with(x:=x). 
     eauto. auto. constructor. simpl. reflexivity. }
    {destruct (beq_nat x x0) eqn:eq. apply beq_nat_true in eq. subst. copy p. rewrite H10 in H1. 
     inv H1. apply beq_nat_false in eq. apply neqSym in eq. lookupTac.
     eapply IHspec_multistep in H10;[idtac|eauto|idtac|auto|auto|auto|auto|auto]; auto.
     econstructor. eapply SNew with(x:=x). 
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

Theorem smultiFullIVar : forall T' x H H' ds tid M T S sc,
         spec_multistep H T H' T' ->
         heap_lookup x H = Some(sfull sc ds S tid M) ->
         exists ds', heap_lookup x H' = 
                     Some(sfull sc ds' S tid M). 
Proof.
  intros. genDeps{sc; ds; S; tid; M}. induction H0; intros.  
  {eauto. }
  {eapply specStepFullIVar in H; eauto. invertHyp. eauto. }
Qed. 
  

Theorem specStepEmptyIVarOr : forall x H H' H'' T T' t t' s s' ds M t0,
                              heap_lookup x H = Some(sempty s) -> 
                              spec_step H T (tSingleton t) H' T t' ->
                              spec_multistep H' (tUnion T t') H'' T' ->
                              heap_lookup x H'' = Some(sfull s ds s' t0 M) ->
                              (heap_lookup x H' = Some(sempty s) \/
                               exists ds', heap_lookup x H' = Some(sfull s ds' s' t0 M)). 
Proof. 
  intros. inversion H1; subst; eauto. 
  {unfold tSingleton in *; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H5 in H0. inv H0. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. }
  }
  {unfold tSingleton in *; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H5 in H0. inv H0.
    eapply smultiFullIVar in H2; eauto. Focus 2. erewrite HeapLookupReplace; eauto. 
    invertHyp. rewrite H3 in H0. inv H0. right. exists nil. erewrite HeapLookupReplace; eauto. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; eauto. }
  }
  {unfold tSingleton in *; invertHyp. destruct (beq_nat x x0)eqn:eq. 
   {apply beq_nat_true in eq. subst. copy p. rewrite H4 in H0. inv H0. }
   {apply beq_nat_false in eq. left. apply lookupExtendNeq; auto. }
  }
Qed. 

Theorem newSimPureStepsFull' : forall H T H' T' TID x M' E d M'' t0 ds ds' N N' N'' s2 s1',
       eraseTrm s1' N' N'' -> 
       heap_lookup x H = Some(sfull SPEC ds SPEC t0 M'') ->
       heap_lookup x H' = Some(sfull SPEC ds' SPEC t0 M'')-> 
       spec_multistep H (tUnion T (tSingleton(TID,unlocked[nAct M' E d x],s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,N'))) ->
       exists H'' T'',
         spec_multistep H (tUnion T (tSingleton(TID,unlocked[nAct M' E d x],s2,N))) 
                        H'' (tUnion T'' (tSingleton(TID,unlocked[nAct M' E d x],s2,N''))) /\
         spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked[nAct M' E d x],s2,N''))) 
                        H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,N'))) /\
         exists ds'',
         spec_multistep (replace x (sfull COMMIT ds SPEC t0 M'') H) T 
                        (replace x (sfull COMMIT ds'' SPEC t0 M'')H'') T'' /\
          heap_lookup x H'' = Some(sfull SPEC ds'' SPEC t0 M''). 
Proof.
  intros. genDeps{ds; ds'}. dependent induction H3; intros. 
  {apply UnionEqTID in x. invertHyp. inv H. destruct s1'; inv H5; try invertListNeq. 
   inv H0; try invertListNeq. rewrite H1 in H2. inv H2. do 6 econstructor. constructor. 
   eauto. }
  {startIndCase. eqIn H5. inv H6. 
   {copy H4. destruct x1. destruct p. destruct p. copy H1. eapply specStepFullIVar' in H1; eauto. inv H1. 
    {copy H10. eapply IHspec_multistep in H10; eauto. Focus 2. proveUnionEq x. invertHyp. 
     econstructor. econstructor. split. takeTStep. eauto. split; eauto. econstructor. 
     split. Focus 2. eauto. apply pullOut in H8. rewrite H8. clear H8. 
     inversion H9; unfoldTac; invertHyp; invThreadEq. 
     {econstructor. eapply SBasicStep; eauto. eauto. }
     {econstructor. eapply SFork; eauto. eauto. }
     {varsEq x4 x0. rewrite H12 in H4. inv H4. erewrite HeapLookupReplace in H1; eauto. 
      inversion H1. invertListNeq. econstructor. eapply SGet; eauto.
      rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. }
     {varsEq x4 x0. heapsDisagree. econstructor. eapply SPut; eauto. 
      rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. }
     {varsEq x4 x0. copy p. heapsDisagree. econstructor. eapply SNew; eauto. 
      erewrite extendReplaceSwitch; eauto. }
     {econstructor. eapply SSpec; eauto. eauto. }
    }
    {inversion H9; unfoldTac; invertHyp; invThreadEq. 
     {rewrite H10 in H4. inversion H4. invertListNeq. }
     {rewrite H10 in H4. inversion H4; invertListNeq. }
     {varsEq x1 x0. 
      {lookupTac. rewrite H11 in H4. inv H4. eapply IHspec_multistep in H1; eauto. 
       Focus 2. proveUnionEq x. invertHyp. econstructor. econstructor. split. 
       takeTStep. eauto. split; eauto. econstructor. split. apply pullOut in H8. 
       rewrite H8. econstructor. eapply SGet; eauto. erewrite HeapLookupReplace; eauto.
       rewrite replaceOverwrite. rewrite replaceOverwrite in H13. eauto. eauto. }
      {rewrite lookupReplaceNeq in H10; eauto. rewrite H10 in H4. inversion H4. invertListNeq. }
     }
     {varsEq x1 x0. heapsDisagree. rewrite lookupReplaceNeq in H10. rewrite H10 in H4. 
      inversion H4; invertListNeq. auto. }
     {varsEq x1 x0. heapsDisagree. erewrite lookupExtendNeq in H10; eauto. inversion H10. 
      invertListNeq. }
     {rewrite H10 in H4. inversion H4; invertListNeq. }
    }
   }
   {inv H8. apply UnionEqTID in x. invertHyp. inversion H1; unfoldTac; invertHyp; invThreadEq. 
    {eapply IHspec_multistep in H4;[idtac|eauto|idtac|eauto|eauto|eauto|eauto]. Focus 2. auto.
     invertHyp. econstructor. econstructor. split. econstructor. eapply SBasicStep; eauto. 
     eauto. split; auto. econstructor. split. eauto. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     econstructor. eapply SFork; eauto. eassumption. econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     econstructor. eapply SGet; eauto. eassumption. econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     econstructor. eapply SPut; eauto. eassumption. econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     econstructor. eapply SNew; eauto. eassumption. econstructor. split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     econstructor. eapply SSpec; eauto. eassumption. econstructor. split. constructor. eauto. }
   }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 

Theorem newSimPureStepsFull : forall H T H' T' TID x M' E d M'' t0 ds' N N' N'' s2 s1',
       eraseTrm s1' N' N'' -> 
       heap_lookup x H = Some(sempty SPEC) ->
       heap_lookup x H' = Some(sfull SPEC ds' SPEC t0 M'')-> 
       spec_multistep H (tUnion T (tSingleton(TID,unlocked[nAct M' E d x],s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,N'))) ->
       (exists H'' T'',
         spec_multistep H (tUnion T (tSingleton(TID,unlocked[nAct M' E d x],s2,N))) 
                        H'' (tUnion T'' (tSingleton(TID,unlocked[nAct M' E d x],s2,N''))) /\
         spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked[nAct M' E d x],s2,N''))) 
                        H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,N'))) /\
         spec_multistep (replace x (sempty COMMIT) H) T 
                        (replace x (sempty COMMIT)H'') T'' /\
          heap_lookup x H'' = Some(sempty SPEC)) \/
       (exists H'' T'' ds'',
         spec_multistep H (tUnion T (tSingleton(TID,unlocked[nAct M' E d x],s2,N))) 
                        H'' (tUnion T'' (tSingleton(TID,unlocked[nAct M' E d x],s2,N''))) /\
         spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked[nAct M' E d x],s2,N''))) 
                        H' (tUnion T' (tSingleton(TID,unlocked(s1'++[nAct M' E d x]),s2,N'))) /\
         spec_multistep (replace x (sempty COMMIT) H) T 
                        (replace x (sfull COMMIT ds'' SPEC t0 M'')H'') T'' /\
          heap_lookup x H'' = Some(sfull SPEC ds'' SPEC t0 M'')). 
Proof.
  intros. dependent induction H3. 
  {rewrite H1 in H2. inv H2. }
  {startIndCase. eqIn H5. inv H6. 
   {copy H4. eapply specStepEmptyIVarOr in H4; eauto. inv H4. 
    {copy H9. eapply IHspec_multistep in H9; eauto. Focus 2. proveUnionEq x. inv H9. 
     {invertHyp. left. econstructor. econstructor. split. takeTStep. eassumption. 
      split. assumption. split. apply pullOut in H8. rewrite H8. econstructor. 
      eapply stepReplaceEmpty. assumption. eapply H4. eapply specStepChangeUnused. 
      eassumption. eauto. eauto. }
     {invertHyp. right. econstructor. econstructor. econstructor. split. takeTStep. eauto. 
      split; eauto. split. Focus 2. eauto. apply pullOut in H8. rewrite H8. clear H8. 
      inversion H6; subst; unfoldTac; invertHyp. 
      {econstructor. eapply SBasicStep; eauto. auto. }
      {econstructor. eapply SFork; eauto. eauto. }
      {varsEq x5 x0. heapsDisagree. econstructor. eapply SGet; eauto. 
       rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. }
      {varsEq x5 x0. erewrite HeapLookupReplace in H4; eauto. inv H4. econstructor. 
       eapply SPut; eauto. rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. }
      {varsEq x5 x0. heapsDisagree. econstructor. eapply SNew; eauto.
       erewrite extendReplaceSwitch; eauto. }
      {econstructor. eapply SSpec; eauto. eauto. }
     }
    }
    {invertHyp. apply UnionSingletonEq in x; auto. rewrite x in H3. unfoldTac. rewrite UnionSwap in H3. 
     eapply newSimPureStepsFull' in H3; eauto. invertHyp. right. econstructor. econstructor. econstructor. 
     split. takeTStep. eauto. split; eauto. split.
     inversion H6; unfoldTac; invertHyp; try solve[heapsDisagree]. 
     {varsEq x5 x0. heapsDisagree. erewrite lookupReplaceNeq in H4; eauto. heapsDisagree. }
     {varsEq x5 x0. erewrite HeapLookupReplace in H4; eauto. inv H4. apply pullOut in H8. 
      rewrite H8. econstructor. eapply SPut; eauto. erewrite HeapLookupReplace; eauto. 
      rewrite replaceOverwrite. rewrite replaceOverwrite in H11. eauto. 
      rewrite lookupReplaceNeq in H4; eauto. heapsDisagree. }
     {varsEq x5 x0. heapsDisagree. erewrite lookupExtendNeq in H4; eauto. inv H4. }
     eauto. 
    }
   }
   {inv H8. apply UnionEqTID in x. invertHyp. inversion H4; unfoldTac; invertHyp; invThreadEq. 
    {eapply IHspec_multistep in H1;[idtac|eauto|idtac|auto|auto|auto|auto]. Focus 2. auto. 
     inv H1. 
     {invertHyp. left. econstructor. econstructor. split. econstructor. eapply SBasicStep; eauto. 
      eassumption. split; auto. }
     {right. invertHyp. econstructor. econstructor. econstructor. split. econstructor.
      eapply SBasicStep; eauto. eauto. eauto. }
    }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     constructor. split. simpl in *. econstructor. eapply SFork; eauto. eassumption. 
     split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     constructor. split. simpl in *. econstructor. eapply SGet; eauto. eassumption. 
     split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     constructor. split. simpl in *. econstructor. eapply SPut; eauto. eassumption. 
     split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     constructor. split. simpl in *. econstructor. eapply SNew; eauto. eassumption. 
     split. constructor. eauto. }
    {copy H3. nonEmptyStackTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. do 4 econstructor. 
     constructor. split. simpl in *. econstructor. eapply SSpec; eauto. eassumption. 
     split. constructor. eauto. }
   }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 


Theorem stepReplaceSpecFull : forall H T H' t t' ds ds' x M' TID,
                   heap_lookup x H = Some(sfull SPEC ds SPEC TID M') ->
                   heap_lookup x H' = Some(sfull SPEC ds' SPEC TID M') ->
                   spec_step H T t H' T t' ->
                   spec_step (replace x (sfull COMMIT ds SPEC TID M') H) T t
                                  (replace x (sfull COMMIT ds' SPEC TID M') H') T t'. 
Proof. 
  intros. inv H2. 
  {rewrite H0 in H1. inv H1. eauto. }
  {rewrite H0 in H1. inv H1; eauto. }
  {varsEq x x0. rewrite H0 in H3. inv H3. erewrite HeapLookupReplace in H1; eauto. inv H1.
   eapply SGet; eauto. erewrite HeapLookupReplace; eauto. repeat rewrite replaceOverwrite. 
   auto. eapply SGet; eauto. rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. 
   erewrite lookupReplaceNeq in H1; eauto. rewrite H0 in H1. inv H1. auto. }
  {varsEq x x0. heapsDisagree. rewrite lookupReplaceNeq in H1; eauto. rewrite H1 in H0. 
   inv H0. eapply SPut; eauto. rewrite lookupReplaceNeq; eauto.
   rewrite lookupReplaceSwitch; eauto. }
  {varsEq x x0. heapsDisagree. eapply SNew; eauto. erewrite extendReplaceSwitch; eauto. 
   erewrite lookupExtendNeq in H1; eauto. inv H1. auto. }
  {rewrite H0 in H1; inv H1; eauto. }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto.
Qed. 

Theorem smultiReplaceSpecFull : forall H T H' T' ds ds' x M' TID,
                   heap_lookup x H = Some(sfull SPEC ds SPEC TID M') ->
                   heap_lookup x H' = Some(sfull SPEC ds' SPEC TID M') ->
                   spec_multistep H T H' T' ->
                   spec_multistep (replace x (sfull COMMIT ds SPEC TID M') H) T
                                  (replace x (sfull COMMIT ds' SPEC TID M') H') T'. 
Proof.
  intros. genDeps{ds; ds'}. induction H2; intros. 
  {rewrite H1 in H0. inv H0. constructor. }
  {copy H. eapply specStepFullIVar in H; eauto. invertHyp. 
   eapply stepReplaceSpecFull in H3; eauto. econstructor. eassumption.
   eapply IHspec_multistep; eauto. }
Qed. 

Theorem smultiReplaceEmptyFull : forall H T H' T' ds' x M' TID,
                   heap_lookup x H = Some(sempty SPEC) ->
                   heap_lookup x H' = Some(sfull SPEC ds' SPEC TID M') ->
                   spec_multistep H T H' T' ->
                   spec_multistep (replace x (sempty COMMIT) H) T
                                  (replace x (sfull COMMIT ds' SPEC TID M') H') T'. 
Proof.
  intros. genDeps{ds'}. induction H2; intros.  
  {rewrite H1 in H0. inv H0. }
  {copy H. apply specStepSingleton in H. invertHyp. copy H3. 
   eapply specStepEmptyIVarOr in H3; eauto. inv H3. 
   {econstructor. eapply stepReplaceEmpty; eauto. eauto. }
   {invertHyp. inversion H; unfoldTac; invertHyp; try solve[heapsDisagree]. 
    {varsEq x2 x. heapsDisagree. rewrite lookupReplaceNeq in H3; eauto. 
     heapsDisagree. } 
    {varsEq x2 x. rewrite H5 in H0. inv H0. econstructor. eapply SPut with(d:=d); eauto. 
     erewrite HeapLookupReplace; eauto. rewrite replaceOverwrite. 
     copy H2. eapply smultiFullIVar in H2. Focus 2. erewrite HeapLookupReplace; eauto. 
     invertHyp. rewrite H4 in H1. inv H1. lookupTac. eapply smultiReplaceSpecFull in H0. 
     Focus 2. eassumption. Focus 2. eassumption. rewrite replaceOverwrite in H0.
     eassumption. rewrite lookupReplaceNeq in H3; eauto. heapsDisagree. }
    {varsEq x2 x. heapsDisagree. erewrite lookupExtendNeq in H3; eauto. inv H3. }
   }
  }
Qed. 

Theorem newSimActionStepsFullFull : forall H T H' T' TID x ds ds' t0 M'' M' E d N N' H'' T'' N'' s2 s1 s1' a,
       eraseTrm (s1'++[a]) N' N'' ->
       heap_lookup x H = Some(sfull SPEC ds SPEC t0 M'') ->       
       heap_lookup x H' = Some(sfull SPEC ds' SPEC t0 M'') -> 
       spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked [nAct M' E d x],s2,N'')))
                      H (tUnion T (tSingleton(TID,unlocked(s1++[nAct M' E d x]),s2,N))) ->
       spec_multistep H (tUnion T (tSingleton(TID,unlocked(s1++[nAct M' E d x]),s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[a]++[nAct M' E d x]),s2,N'))) ->
       spec_multistep (replace x (sfull COMMIT ds SPEC t0 M'') H)
                      (tUnion T (tSingleton(TID,unlocked s1,nAct M' E d x::s2,N))) 
                      (replace x (sfull COMMIT ds' SPEC t0 M'') H')
                      (tUnion T' (tSingleton(TID,unlocked (s1'++[a]), nAct M' E d x::s2,N'))).
Proof.
  intros. genDeps{ds; ds'}. dependent induction H4; intros. 
  {apply UnionEqTID in x. invertHyp. inv H. 
   replace [a; nAct M' E d x0] with ([a]++[nAct M' E d x0]) in H6; auto. 
   rewrite app_assoc in H6. apply app_inj_tail in H6. invertHyp. inv H5. rewrite H1 in H2. 
   inv H2. constructor. }
  {startIndCase. eqIn H6. inv H7. 
   {copy H1. copy H7. eapply specStepFullIVar in H7; eauto. invertHyp.
    eapply stepReplaceSpecFull in H1; eauto. takeTStep. eapply IHspec_multistep; eauto.
    eapply spec_multi_trans. eassumption. rewrite H9. rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused. eauto. unfoldTac. rewrite UnionSwap. rewrite subtractSingle. 
    constructor. proveUnionEq x. rewrite H9. apply Union_intror. constructor. }
   {inv H9. apply UnionEqTID in x. invertHyp. inversion H1; unfoldTac; invertHyp; invThreadEq. 
    {copy H3. eapply stackNonNil in H3. destruct s1. exfalso. apply H3. auto. 
     econstructor. eapply SBasicStep; eauto. constructor. eapply IHspec_multistep; eauto. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SBasicStep; eauto. constructor. 
     eauto. intros c. subst. apply eraseTrmApp in H0. inv H0; inv H12; falseDecomp. }
    {econstructor. eapply SFork; eauto. simpl. unfoldTac. rewrite coupleUnion. 
     rewrite <- Union_associative. rewrite UnionSwap. eapply IHspec_multistep; eauto. 
     Focus 2. rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     unfold numForks. simpl. simpl. eauto. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite <- plus_comm. simpl. rewrite plus_comm. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SFork; eauto. rewrite Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. simpl. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
     rewrite plus_comm. simpl. rewrite plus_comm. constructor. }
    {varsEq x x0. 
     {rewrite H12 in H5. inv H5. econstructor. eapply SGet; eauto. 
      erewrite HeapLookupReplace; eauto. rewrite replaceOverwrite. lookupTac.
      eapply IHspec_multistep in H5; eauto. rewrite replaceOverwrite in H5. eauto. 
      eapply spec_multi_trans. eauto. econstructor. eapply SGet; eauto. constructor.
      simpl. auto. }
     {apply neqSym in H10. lookupTac. eapply IHspec_multistep in H13; eauto. 
      econstructor. eapply SGet; eauto. rewrite lookupReplaceNeq; eauto. 
      rewrite lookupReplaceSwitch. eassumption. auto. eapply spec_multi_trans. eassumption. 
      econstructor. eapply SGet; eauto. simpl. constructor. simpl.  auto. }
    }
    {varsEq x0 x. heapsDisagree. lookupTac. eapply IHspec_multistep in H13; eauto. 
     econstructor. eapply SPut; eauto. rewrite lookupReplaceNeq; eauto. 
     rewrite lookupReplaceSwitch; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SPut; eauto. constructor. simpl. auto. }
    {varsEq x0 x. heapsDisagree. lookupTac. eapply IHspec_multistep in H12; eauto. 
     econstructor. eapply SNew; eauto. erewrite extendReplaceSwitch; eauto.
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. constructor. 
     simpl; auto. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite coupleUnion. rewrite <- Union_associative. 
     rewrite <- UnionSwap. eapply IHspec_multistep; eauto. Focus 2. rewrite Union_associative. 
     rewrite <- coupleUnion.  rewrite couple_swap. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SSpec; eauto. rewrite Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. constructor. }
   }
  } 
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto.
Qed. 

Theorem newSimActionStepsEmptyFull : forall H T H' T' TID x ds' t0 M'' M' E d N N' H'' T'' N'' s2 s1 s1' a,
       eraseTrm (s1'++[a]) N' N'' ->
       heap_lookup x H = Some(sempty SPEC) ->       
       heap_lookup x H' = Some(sfull SPEC ds' SPEC t0 M'') -> 
       spec_multistep H'' (tUnion T'' (tSingleton(TID,unlocked [nAct M' E d x],s2,N'')))
                      H (tUnion T (tSingleton(TID,unlocked(s1++[nAct M' E d x]),s2,N))) ->
       spec_multistep H (tUnion T (tSingleton(TID,unlocked(s1++[nAct M' E d x]),s2,N))) H'
                      (tUnion T' (tSingleton(TID,unlocked(s1'++[a]++[nAct M' E d x]),s2,N'))) ->
       spec_multistep (replace x (sempty COMMIT) H)
                      (tUnion T (tSingleton(TID,unlocked s1,nAct M' E d x::s2,N))) 
                      (replace x (sfull COMMIT ds' SPEC t0 M'') H')
                      (tUnion T' (tSingleton(TID,unlocked (s1'++[a]), nAct M' E d x::s2,N'))).
Proof.
  intros. genDeps{ds'}. dependent induction H4; intros. 
  {rewrite H1 in H2. inv H2. }
  {startIndCase. eqIn H6. inv H7. 
   {copy H1. copy H2. eapply specStepEmptyIVarOr in H2; eauto. inv H2. 
    {copy H11. eapply IHspec_multistep in H11; eauto. Focus 3. proveUnionEq x.
     takeTStep. eapply stepReplaceEmpty; eauto. eapply specStepChangeUnused. eassumption. 
     unfoldTac. rewrite UnionSwap. eassumption. eapply spec_multi_trans. eassumption. 
     apply pullOut in H9. rewrite H9. unfoldTac. rewrite UnionSwap. econstructor. 
     eapply specStepChangeUnused. eassumption. rewrite subtractSingle. unfoldTac. 
     rewrite UnionSwap. constructor. }
    {invertHyp. inversion H10; unfoldTac; invertHyp; try solve[heapsDisagree]. 
     {varsEq x3 x0. heapsDisagree. rewrite lookupReplaceNeq in H2; auto. heapsDisagree. }
     {varsEq x3 x0. copy H2. erewrite HeapLookupReplace in H11; eauto. inv H11. 
      apply UnionSingletonEq in x; auto. rewrite x in H4. rewrite UnionSwap in H4. 
      eapply newSimActionStepsFullFull in H4; eauto. Focus 2. eapply spec_multi_trans. 
      eassumption. takeTStep. rewrite subtractSingle. constructor. takeTStep. 
      eapply SPut; eauto. erewrite HeapLookupReplace; eauto. rewrite replaceOverwrite. 
      rewrite replaceOverwrite in H4. unfoldTac. rewrite UnionSwap. eassumption. 
      rewrite lookupReplaceNeq in H2; auto. heapsDisagree. }
     {varsEq x3 x0. heapsDisagree. erewrite lookupExtendNeq in H2; eauto. inv H2. }
    }
   }
   {inv H9. apply UnionEqTID in x. invertHyp. copy H1. copy H2. 
    eapply specStepEmptyIVarOr in H12; eauto. inv H12.
    {inversion H2; unfoldTac; invertHyp; invThreadEq. 
     {copy H3. eapply stackNonNil in H3. destruct s1. exfalso. apply H3. auto. 
      econstructor. eapply SBasicStep; eauto. constructor. eapply IHspec_multistep; eauto. 
      eapply spec_multi_trans. eassumption. econstructor. eapply SBasicStep; eauto. constructor. 
      eauto. intros c. subst. apply eraseTrmApp in H0. inv H0; inv H14; falseDecomp. }
     {econstructor. eapply SFork; eauto. simpl. unfoldTac. rewrite coupleUnion. 
      rewrite <- Union_associative. rewrite UnionSwap. eapply IHspec_multistep; eauto. 
      Focus 2. rewrite Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
      unfold numForks. simpl. simpl. eauto. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
      rewrite <- plus_comm. simpl. rewrite plus_comm. reflexivity. eapply spec_multi_trans. 
      eassumption. econstructor. eapply SFork; eauto. rewrite Union_associative. rewrite <- coupleUnion. 
      rewrite couple_swap. simpl. rewrite numForksDistribute. simpl. rewrite <- plus_assoc. 
      rewrite plus_comm. simpl. rewrite plus_comm. constructor. }
     {varsEq x0 x. heapsDisagree. econstructor. eapply SGet; eauto. 
      rewrite lookupReplaceNeq; eauto. lookupTac. eapply IHspec_multistep in H15; eauto.
      rewrite lookupReplaceSwitch; auto. eassumption. eapply spec_multi_trans. eassumption. 
      econstructor. eapply SGet; eauto. simpl. constructor. reflexivity. } 
     {varsEq x0 x. erewrite HeapLookupReplace in H13; eauto. inv H13. econstructor. 
      eapply SPut; eauto. rewrite lookupReplaceNeq; eauto. lookupTac.
      eapply IHspec_multistep in H15; eauto. rewrite lookupReplaceSwitch; auto. eassumption. 
      eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. simpl. 
      constructor. reflexivity. }
     {varsEq x0 x. heapsDisagree. econstructor. eapply SNew; eauto. lookupTac.
      eapply IHspec_multistep in H14; eauto. erewrite extendReplaceSwitch; eauto. 
      eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. simpl. 
      constructor. reflexivity. }
    {econstructor. eapply SSpec; eauto. unfoldTac. rewrite coupleUnion. rewrite <- Union_associative. 
     rewrite <- UnionSwap. eapply IHspec_multistep; eauto. Focus 2. rewrite Union_associative. 
     rewrite <- coupleUnion.  rewrite couple_swap. reflexivity. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SSpec; eauto. rewrite Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. constructor. }
    }
    {invertHyp. inversion H2; unfoldTac; invertHyp; invThreadEq; try solve[heapsDisagree]. 
     {varsEq x1 x0. erewrite HeapLookupReplace in H12; eauto. inv H12. heapsDisagree. 
      rewrite lookupReplaceNeq in H12; eauto. heapsDisagree. }
     {varsEq x1 x0. erewrite HeapLookupReplace in H12; eauto. inv H12. 
      simpl in *. rewrite app_comm_cons in H4. eapply newSimActionStepsFullFull in H4; eauto. 
      econstructor. eapply SPut; eauto. erewrite HeapLookupReplace; eauto. rewrite replaceOverwrite. 
      rewrite replaceOverwrite in H4. eassumption. erewrite HeapLookupReplace; eauto. 
      eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. 
      constructor. rewrite lookupReplaceNeq in H12; eauto. heapsDisagree. }
     {varsEq x1 x0. heapsDisagree. erewrite lookupExtendNeq in H12; eauto. inv H12. }
    }
   }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 















