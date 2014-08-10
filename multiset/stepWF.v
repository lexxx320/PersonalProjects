Require Import erasure. 
Require Import specIndependence. 
Require Import writeIndependence. 
Require Import IndependenceCommon. 
Require Import ReadIndependence. 
Require Import newIndependence.  
Require Import ForkIndependence.
Require Import PopSpecInd. 

Ltac rewriteEmpty xs := 
      match xs with
          |HNil => unfold tUnion; try rewrite union_empty_l; try rewrite union_empty_r
          |HCons ?x ?xs' => unfold tUnion in x; try rewrite union_empty_l in x; 
                          try rewrite union_empty_r in x; rewriteEmpty xs'
      end. 

Theorem rollbackWF : forall H H' T TR TR' tidR acts,
                       wellFormed H (tUnion T TR) ->
                       rollback tidR acts H TR H' TR' ->
                       wellFormed H' (tUnion T TR'). 
Admitted. 

Ltac foldTac := fold Add in *; fold tAdd in *; fold tUnion in *; fold tSingleton in *; fold tCouple in *.

Ltac invertDecomp :=
  match goal with
    |H:(?a,?b,?c,?d)=(?e,?f,?g,?h) |- _ => inv H
    |H:?x = ?y |- _ => solve[inv H]
    |H:decompose ?M ?E ?e,H':decompose ?M' ?E' ?e' |- _=>
     eapply uniqueCtxtDecomp in H; eauto; invertHyp
  end. 

Theorem appCons : forall (T:Type) x (y:T) z,
                    x ++ [y;z] = (x ++ [y]) ++ [z]. 
Proof. 
  intros. rewrite <- app_assoc. simpl. auto. Qed. 


Ltac monoActs H := 
  eapply monotonicActions in H;[idtac|apply InL; constructor|apply InL; constructor]. 


Theorem listTailEq : forall (T:Type) a (b:T) c d e,
                       ~List.In b c -> ~List.In b e -> a ++ [b] ++ c = d ++ b::e -> c = e. 
Proof.
  induction a; intros. 
  {simpl in *. destruct d. simpl in *. inv H1. auto. inv H1. exfalso. apply  H. 
   apply in_or_app. right. simpl. left. auto. }
  {destruct d. inv H1. exfalso. apply H0. apply in_or_app. right. 
   simpl. auto. inv H1. eapply IHa; eauto. }
Qed.   

Theorem raw_unspecHeapCommitNewFull : forall x ds t N H S,
                                   unique ivar_state S H -> 
                                   raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                   raw_unspecHeap (raw_replace x (sfull COMMIT ds SPEC t N) H) =
                                   raw_extend x (sempty COMMIT) (raw_unspecHeap H).
Proof.
  intros. apply heapExtensionality. genDeps{S; N; t; ds; x; H}. induction H; intros. 
  {inv H1. } 
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. simpl. destruct (beq_nat x0 x) eqn:eq2; auto. }
   {simpl. destruct (beq_nat x0 x) eqn:eq2; eauto.
    {destruct i0. destruct s. erewrite IHlist. rewrite eq2. auto. 
     auto. inv H0;  eauto. apply beq_nat_true in eq2. subst. simpl. rewrite eq. inv H0.
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. eauto. 
     destruct s. inv H0. eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. 
     eauto. destruct s0. apply beq_nat_true in eq2. subst. simpl. rewrite eq. inv H0. 
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. eauto. 
     simpl. apply beq_nat_true in eq2. subst. rewrite eq. inv H0. 
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. auto. }
    {destruct i0. destruct s. inv H0. eapply IHlist with(x0:=x0)in H1; eauto. 
     rewrite eq2 in H1. auto. simpl. destruct (beq_nat x0 i)eqn:eq3; auto. 
     inv H0. eapply IHlist with(x0:=x0)in H1. rewrite eq2 in H1. auto. eauto.
     destruct s. inv H0. eapply IHlist with(x0:=x0) in H1. rewrite eq2 in H1. auto. 
     eauto. destruct s0. simpl. destruct (beq_nat x0 i) eqn:eq3; auto. 
     eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. auto. inv H0; eauto. 
     simpl. destruct (beq_nat x0 i); auto. eapply IHlist with(x0:=x0) in H1. 
     rewrite eq2 in H1. auto. inv H0; eauto. }
   }
  }
Qed.
 
Theorem unspecHeapCommitNewFull : forall x ds t N H p,
                                   heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                   unspecHeap (replace x (sfull COMMIT ds SPEC t N) H) =
                                   Heap.extend x (sempty COMMIT) (unspecHeap H) p.
Proof.
  intros. destruct H. simpl in *. apply rawHeapsEq. eapply raw_unspecHeapCommitNewFull; eauto. 
Qed.
 
Theorem raw_eraseHeapCommitNewEmpty : forall x S H,
                                   unique ivar_state S H -> 
                                   raw_heap_lookup x H = Some(sempty SPEC) ->
                                   raw_unspecHeap (raw_replace x (sempty COMMIT) H) =
                                   raw_extend x (sempty COMMIT) (raw_unspecHeap H).
Proof.
  intros. apply heapExtensionality. genDeps{S; x; H}. induction H; intros. 
  {inv H1. }
  {simpl in H1. simpl. destruct a. destruct (beq_nat x i)eqn:eq. 
   {inv H1. destruct (beq_nat x0 x) eqn:eq2. simpl. rewrite eq2. auto. simpl. rewrite eq2. 
    auto. }
   {simpl. destruct i0. 
    {destruct s. 
     {destruct (beq_nat x0 x) eqn:eq2. 
      {simpl in *. inv H0. eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. 
       auto. }
      {erewrite IHlist. simpl. rewrite eq2. auto. eauto. inv H0; eauto. }
     }
     {simpl. destruct(beq_nat x0 i)eqn:eq2. 
      {apply beq_nat_true in eq2. subst. rewrite beq_nat_sym in eq. rewrite eq. auto. }
      {destruct(beq_nat x0 x) eqn:eq3.
       {eapply IHlist with(x0:=x0) in H1. simpl in *. rewrite eq3 in H1. auto. inv H0; eauto. }
       {erewrite IHlist; eauto. simpl. rewrite eq3. auto. inv H0; eauto. }
      }
     }
    }
    {destruct s. 
     {destruct (beq_nat x0 x)eqn:eq2. 
      {eapply IHlist with(x0:=x0) in H1. simpl in *. rewrite eq2 in H1. auto. inv H0; eauto. }
      {erewrite IHlist; eauto. simpl. rewrite eq2. auto. inv H0; eauto. }
     }
     {destruct s0. 
      {destruct (beq_nat x0 x) eqn:eq2. 
       {simpl. apply beq_nat_true in eq2. subst. rewrite eq.
        eapply IHlist with(x0:=x) in H1; eauto. simpl in *. rewrite <- beq_nat_refl in H1. auto. 
        inv H0; eauto. }
       {simpl. destruct (beq_nat x0 i); auto. erewrite IHlist; eauto. simpl. rewrite eq2. auto. 
        inv H0; eauto. }
      }
      {simpl. destruct (beq_nat x0 i) eqn:eq2. 
       {apply beq_nat_true in eq2. subst. rewrite beq_nat_sym in eq. rewrite eq. auto. }
       {destruct (beq_nat x0 x) eqn:eq3. 
        {simpl in *. eapply IHlist with(x0:=x0) in H1. rewrite eq3 in H1. eauto. inv H0; eauto. }
        {erewrite IHlist; eauto. simpl. rewrite eq3. auto. inv H0; eauto. }
       }
      }
     }
    }
   }
  }
Qed. 

Theorem eraseHeapCommitNewEmpty : forall x H p,
                                   heap_lookup x H = Some(sempty SPEC) ->
                                   unspecHeap (replace x (sempty COMMIT) H) =
                                   Heap.extend x (sempty COMMIT) (unspecHeap H) p.
Proof.
  intros. destruct H. simpl in *. apply rawHeapsEq. eapply raw_eraseHeapCommitNewEmpty; eauto. 
Qed.

Theorem uniqueLookupNone : forall (T:Type) x H S, 
                            unique T S H -> Ensembles.In (AST.id) S x ->
                            raw_heap_lookup x H = None. 
Proof.
  induction H; intros. 
  {auto. }
  {inv H0. simpl. assert(x <> m). intros c. subst. contradiction.
   apply beq_nat_false_iff in H0. rewrite H0. eapply IHlist; eauto.
   constructor. auto. }
Qed. 

Theorem raw_lookupCreatedSpecFull : forall x H ds t0 N s S,
                                  unique ivar_state S H -> 
                                  raw_heap_lookup x H = Some(sfull SPEC ds s t0 N) ->
                                  raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof. 
  induction H; intros. 
  {inv H0; inv H1. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. inv H1. apply unspecUnique in H7; eapply uniqueLookupNone; eauto;
    apply beq_nat_true in eq; subst; apply Ensembles.Union_intror; constructor. }
   {inv H0. destruct i0. destruct s0. eauto. simpl. rewrite eq. eauto. 
    destruct s0; eauto. destruct s1; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupCreatedSpecFull : forall x H ds t0 N s,
                                  heap_lookup x H = Some(sfull SPEC ds s t0 N) ->
                                  heap_lookup x (unspecHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupCreatedSpecFull; eauto. 
Qed. 

Theorem raw_lookupCreatedSpecEmpty : forall x H S,
                                  unique ivar_state S H -> 
                                  raw_heap_lookup x H = Some(sempty SPEC) -> 
                                  raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof. 
  induction H; intros. 
  {inv H0; inv H1. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. inv H1; apply unspecUnique in H7; eapply uniqueLookupNone; eauto;
    apply beq_nat_true in eq; subst; apply Ensembles.Union_intror; constructor. }
   {inv H0. destruct i0. destruct s. eauto. simpl. rewrite eq. eauto. 
    destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupCreatedSpecEmpty : forall x H,
                                  heap_lookup x H = Some(sempty SPEC) ->
                                  heap_lookup x (unspecHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupCreatedSpecEmpty; eauto. 
Qed. 


Theorem PopSpecFastForward : forall H T H' T' tid s1' s1'' N M M' M'' N'' E s2 d,
  decompose M' E (spec M'' N'') -> 
  spec_multistep H (tUnion T (tSingleton(tid,unlocked nil, s2, M')))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[srAct M' E M'' N'' d]),s2,M)
                                       (2::tid,locked s1'',nil,N))) ->
  exists H'' T'',
    spec_multistep H (tUnion T (tSingleton(tid,unlocked nil,s2,M')))
                   H'' (tUnion T'' (tCouple(tid,unlocked[srAct M' E M'' N'' d],s2,fill E (specRun M'' N''))
                                          (2::tid,locked nil,nil,N''))) /\
    spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[srAct M' E M'' N'' d],s2,fill E (specRun M'' N'')) 
                                           (2::tid,locked nil,nil,N'')))
                   H'(tUnion T' (tCouple(tid,unlocked(s1'++[srAct M' E M'' N'' d]),s2,M)
                                       (2::tid,locked s1'',nil,N))) /\
    spec_multistep H T H'' T''. 
Proof.
  intros. dependent induction H1. 
  {unfoldTac. rewrite coupleUnion in x. rewrite Union_associative in x. 
   rewrite UnionSwap in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x0. exMid tid H7. 
   {apply UnionEqTID in x. invertHyp. econstructor. econstructor. split. 
    econstructor. eapply SSpec; eauto. simpl. constructor. split; try constructor. 
    inv H; try solve[falseDecomp]. 
    {inv H13; falseDecomp. }
    {simpl in *. copy d0. eapply uniqueCtxtDecomp in H0; eauto. invertHyp. 
     inv H4. proofsEq d d0. eassumption. }
   }
   {apply UnionNeqTID in x. invertHyp. eapply IHspec_multistep in H0; eauto. 
    invertHyp. econstructor. econstructor. split. takeTStep. eassumption. 
    split; eauto. takeTStep. econstructor. eapply specStepChangeUnused; eauto. 
    eauto. rewrite H2. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap; eauto.
    auto. }
  }
Qed. 


Theorem unspecSpecSame : forall tid hd tl s2 M M',
                           unspecPool(tSingleton(tid,unlocked(hd::tl),s2,M)) = 
                           unspecPool(tSingleton(tid,unlocked(hd::tl),s2,M')). 
Proof.
  induction tl; intros; auto. 
Qed. 

Theorem unspecSpecSame' : forall tid hd a tl s2 M M',
            unspecPool(tSingleton(tid,aCons a (unlocked(hd::tl)),s2,M)) = 
            unspecPool(tSingleton(tid,unlocked(hd::tl),s2,M')). 
Proof.
  induction tl; intros; auto. 
  {simpl. destruct tl. auto. erewrite getLastNonEmpty. eauto. }
Qed. 

Theorem unspecEmpty : forall tid s1 s2 M, 
                unspecPool(tSingleton(tid,locked s1,s2,M)) = (Empty_set thread).
Proof.
  intros. simpl. auto. 
Qed. 

Theorem AddUnion : forall (A:Type) T (e:A),
                     Add T e = Union T (Single e). 
Proof.
  intros. reflexivity. 
Qed. 

Theorem stepWF : forall H T t H' t', 
                   wellFormed H (tUnion T t) -> step H T t (OK H' T t') ->
                   wellFormed H' (tUnion T t'). 
Proof.
  intros. inversion H1; subst.      
  {destruct s1.  
   {inv H0. econstructor; eauto. rewrite unspecUnionComm in *. 
    simpl in *. unfoldTac. rewrite union_empty_r in *. eapply spec_multi_trans; eauto.
    econstructor. eapply SBasicStep. eauto. constructor. constructor. } 
   {destruct l. 
    {inv H0. econstructor; eauto. rewrite unspecUnionComm in *. simpl in *. 
     apply spec_multi_unused in H2. rewrite spec_multi_unused. auto. }
    {inv H0. econstructor; eauto. rewrite unspecUnionComm in *. 
     erewrite unspecSpecSame. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SBasicStep; eauto. constructor. constructor. }
   }
   {inv H0. constructor; auto. rewrite unspecUnionComm in *. simpl in *. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SBasicStep; eauto. 
    constructor. constructor. }
  }
  {inv H0. econstructor; eauto. destruct s1.
   {simpl. unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. 
    simpl in *. eapply spec_multi_trans. eassumption. econstructor. eapply SFork. 
    auto. unfoldTac. unfold Couple. simpl. constructor. }
   {destruct l. 
    {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
     simpl in *. eapply spec_multi_trans. eassumption. econstructor. 
     eapply SFork; eauto. unfoldTac. unfold Couple. simpl. constructor. }
    {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
     rewrite unspecEmpty. erewrite unspecSpecSame'. unfoldTac. 
     rewrite union_empty_r. eapply spec_multi_trans. eassumption. econstructor. 
     eapply SFork; eauto. unfoldTac. unfold Couple. constructor. }
   }
   {simpl. unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. 
    simpl in *. eapply spec_multi_trans. eassumption. econstructor. eapply SFork. 
    auto. constructor. }
  }
  {inv H0. econstructor; eauto. erewrite unspecHeapRBRead; eauto. destruct s1.  
   {rewrite unspecUnionComm in *. simpl in *. eapply spec_multi_trans. eassumption. 
    econstructor. eapply SGet; eauto. constructor. }
   {destruct l.
    {unfoldTac. rewrite unspecUnionComm in *. simpl. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SGet; eauto. constructor. }
    {rewrite unspecUnionComm in *. erewrite unspecSpecSame'. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SGet; eauto. constructor. }
   }
   {rewrite unspecUnionComm in *. simpl in *. eapply spec_multi_trans. eassumption. 
    econstructor. eapply SGet; eauto. constructor. }
  }
  {inv H0. econstructor; eauto. erewrite unspecHeapAddWrite; eauto. destruct s1.  
   {rewrite unspecUnionComm in *. simpl in *. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SPut; eauto. constructor. }
   {destruct l. 
    {rewrite unspecUnionComm in *. simpl in *. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SPut; eauto. constructor. }
    {rewrite unspecUnionComm in *. erewrite unspecSpecSame'. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SPut; eauto. constructor. }
   }
   {rewrite unspecUnionComm in *. simpl in *. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SPut; eauto. constructor. }
  }   
  {copy H5. unfoldTac. rewrite AddUnion in H0. rewrite Union_associative in H0. 
   rewrite wfFrame in H0. eapply rollbackWF in H7; eauto. Focus 2. simpl. auto. 
   econstructor; eauto. uCons (wAct x t0 E N d) (@nil action). 
   rewrite unspecHeapAddWrite; auto. inv H7. rewrite AddUnion. 
   rewrite Union_associative. eapply spec_multi_trans. rewrite  unspecUnionComm. 
   rewrite spec_multi_unused. eassumption. simpl. econstructor. eapply SPut; eauto. 
   constructor. }
  {inv H0. econstructor; eauto. erewrite unspecHeapExtend; eauto. destruct s1. 
   {rewrite unspecUnionComm in *. simpl in *. eapply spec_multi_trans. eassumption. 
    copy d. apply decomposeEq in H0; subst. econstructor. eapply SNew; eauto. 
    constructor. }
   {destruct l. 
    {rewrite unspecUnionComm in *. simpl in *. copy d. apply decomposeEq in H0;subst. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. 
     constructor. }
    {copy d. apply decomposeEq in H0; subst. rewrite unspecUnionComm in *. 
     erewrite unspecSpecSame'. eapply spec_multi_trans. eassumption. econstructor. 
     eapply SNew; eauto. constructor. }
   }
   {rewrite unspecUnionComm in *. simpl in *.  eapply spec_multi_trans. eassumption. 
    copy d. apply decomposeEq in H0; subst. econstructor. eapply SNew; eauto. 
    constructor. }
  }   
  {inv H0. econstructor; eauto. destruct s1.  
   {unfoldTac. rewrite unspecUnionComm in *. simpl in *. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SSpec; eauto. constructor. }
   {destruct l.
    {rewrite unspecUnionComm in *. simpl in *. copy d. apply decomposeEq in H. 
     subst. eapply spec_multi_trans. eassumption. econstructor. eapply SSpec; eauto. 
     constructor. }
    {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *.
     rewrite unspecEmpty. unfoldTac. rewrite union_empty_r. 
     erewrite unspecSpecSame'. eapply spec_multi_trans. eassumption. econstructor. 
     eapply SSpec. constructor. }
   }
   {rewrite unspecUnionComm in *. simpl in *. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SSpec; eauto. constructor. }
  }  
  {inv H0. econstructor; eauto. unfoldTac. rewrite couple_swap in H2. 
   rewrite coupleUnion in H2. repeat rewrite unspecUnionComm in *. unfoldTac.
   repeat rewrite Union_associative in H2. simpl in H2.
   rewrite spec_multi_unused in H2. destructLast s1. 
   {simpl. rewrite spec_multi_unused. eapply simSpecJoin in H2. eauto. }
   {invertHyp. eraseTrmTac (x0++[x]) M. copy H0. 
    eapply wrapEraseTrm with(N:=N1)(E:=E)(N':=(specRun(ret N1) N0))in H0.
    erewrite unspecEraseTrm; eauto. eapply specFastForward in H2; eauto. 
    invertHyp. eapply spec_multi_trans. eapply simTSteps in H3. eapply H3. 
    eapply simSpecJoin' in H4. simpl in *.
    eauto. eauto. constructor. introsInv. }
  }
  {copy H13. unfoldTac. rewrite AddUnion. rewrite Union_associative. 
   rewrite wfFrame. Focus 2. simpl. auto. rewrite AddUnion in H0. 
   rewrite Union_associative in H0. rewrite wfFrame in H0. Focus 2. simpl. auto. 
   eapply rollbackWF; eauto. }
  {inv H0. econstructor; eauto. rewrite unspecUnionComm in *. simpl in *.  
   rewrite spec_multi_unused in H2. rewrite spec_multi_unused. auto. }
  {inv H0. econstructor; eauto. erewrite unspecHeapRBRead; eauto. 
   rewrite unspecUnionComm in *. 
(*pick up here*)

erewrite unspecSingleton in H4. Focus 2. unspecThreadTac. 
   auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2. apply unspecEraseTrm; eauto. 
   eapply readFastForward in H4. Focus 2. eapply unspecHeapLookupFull; eauto. Focus 2. eauto. 
   Focus 2. intros c. inv c. invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. 
   eassumption. copy H3. eapply monotonicReaders in H3; eauto. invertHyp.
   apply listTailEq in H9; auto. subst.  eapply readSimPureSteps in H7; eauto. Focus 2. 
   rewrite app_nil_l. simpl. eassumption. invertHyp. eapply spec_multi_trans.
   rewrite spec_multi_unused. eassumption. destructLast s1'. 
   {inv H2; try solve[invertListNeq]. rewrite spec_multi_unused. rewrite spec_multi_unused in H7. 
    eapply stepWithoutReader; eauto. }
   {invertHyp. eapply readSimActionSteps; eauto. constructor. simpl. rewrite <- app_assoc in H7. 
    simpl in *. auto. }
  }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapCommitCreateFull; eauto.
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. unspecThreadTac. 
   auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2.  apply unspecEraseTrm; eauto.
   eapply writeFastForward in H4; eauto. Focus 2. eapply lookupUnspecEmpty; eauto.
   invertHyp. eapply spec_multi_trans. eapply spec_multi_unused. eassumption. 
   eapply writeSimPureSteps in H3; eauto. invertHyp. eapply spec_multi_trans. 
   rewrite spec_multi_unused. eassumption. destructLast s1'. 
   {simpl in *. inv H2; try solve[invertListNeq]. eapply helper; eauto. rewrite spec_multi_unused. 
    rewrite spec_multi_unused in H3. assumption. }
   {invertHyp. eapply writeSimActionSteps; eauto. eauto. constructor. simpl. rewrite <- app_assoc in H3. 
    simpl in *. assumption. }
  }                   
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapCommitNewFull; eauto. 
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. 
   unspecThreadTac. auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2. 
   apply unspecEraseTrm; eauto. eapply newFastForward in H4; eauto. Focus 2. 
   eapply lookupCreatedSpecFull; eauto. invertHyp. eapply spec_multi_trans.
   rewrite spec_multi_unused. eassumption. eapply newSimPureStepsFull in H3; eauto. 
   inv H3.  
   {invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. eassumption. 
    destructLast s1'. 
    {inv H2; try invertListNeq. simpl in *. rewrite spec_multi_unused. 
     rewrite spec_multi_unused in H5. clear H4. eapply smultiReplaceEmptyFull; eauto. }
    {invertHyp. eapply newSimActionStepsEmptyFull; eauto.  constructor. 
     rewrite <- app_assoc in H5. simpl in *. assumption. }
   }
   {invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. eassumption. 
    destructLast s1'. 
    {inv H2; try invertListNeq. rewrite spec_multi_unused. rewrite spec_multi_unused in H3. 
     clear H4. eapply smultiReplaceSpecFull; eauto. }
    {invertHyp. eapply newSimActionStepsFullFull; eauto. constructor.  rewrite <- app_assoc in H3.
     simpl in *. eassumption. }
   }
  }
  {inv H0. inv H3. econstructor; eauto. erewrite eraseHeapCommitNewEmpty; eauto. 
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. 
   unspecThreadTac. auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2. 
   apply unspecEraseTrm; eauto. eapply newFastForward in H4; eauto. Focus 2. 
   eapply lookupCreatedSpecEmpty; eauto. invertHyp. eapply spec_multi_trans.
   rewrite spec_multi_unused. eassumption. eapply newSimPureStepsEmpty in H3; eauto. 
   invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. eassumption. 
   destructLast s1'. 
   {simpl in *. inv H2; try invertListNeq. rewrite spec_multi_unused.
    rewrite spec_multi_unused in H3. eapply smultiReplaceEmpty; eauto. }
   {invertHyp. eapply newSimActionStepsEmpty; eauto. constructor. rewrite <- app_assoc in H3. 
    simpl in *. assumption. }
  }
  {inv H0. inv H2. econstructor; eauto. unfoldTac. rewrite coupleUnion in *. 
   repeat rewrite unspecUnionComm in *. eraseTrmTac s1' M. rUnspecAll. 
   Focus 2. unspecThreadTac; eauto. Focus 3. unspecThreadTac; eauto. 
   Focus 2. apply unspecEraseTrm; eauto. eraseTrmTac s1'' N. rUnspecAll. Focus 2. 
   apply unspecEraseTrm. eauto. unfoldTac. rewrite union_empty_r in H3. 
   rewrite <- coupleUnion in H3. eapply forkFastForward in H3; eauto. invertHyp.
   eapply spec_multi_trans. erewrite spec_multi_unused. eassumption. 
   repeat rewrite <- coupleUnion. eapply forkCatchup' in H3; eauto. invertHyp. 
   destructLast s1'. 
   {destructLast s1''. 
    {inv H2;inv H0; try invertListNeq. rewrite spec_multi_unused. simpl in *.  
      unfoldTac. rewrite spec_multi_unused in H6. assumption. }
    {invertHyp. inv H0; try invertListNeq. unfoldTac. flipCouples. flipCouplesIn H6.  
      repeat rewrite coupleUnion in *. repeat rewrite <- Union_associative in *. 
      rewrite spec_multi_unused. rewrite spec_multi_unused in H6. apply eraseTrmApp in H2. 
      eapply forkSimActStepsLocked; eauto. constructor. constructor. }
   }
   {invertHyp. destructLast s1''. 
    {inv H2; try invertListNeq. unfoldTac. repeat rewrite coupleUnion in *. 
     repeat rewrite <- Union_associative in *. rewrite spec_multi_unused. 
     rewrite spec_multi_unused in H6. eapply forkSimActStepsUnlocked; eauto. 
     constructor. rewrite <- app_assoc in H6. simpl in *. auto. }
    {invertHyp. eapply forkSimActSteps; eauto. constructor. constructor. 
     rewrite <- app_assoc in H6. simpl in *. assumption. }
   }
  }
  {inv H0. inv H2. econstructor; eauto. unfoldTac. rewrite coupleUnion in *.  
   repeat rewrite unspecUnionComm in *. eraseTrmTac s1' M'. rUnspecAll. 
   Focus 2. unspecThreadTac; eauto. Focus 3. unspecThreadTac; eauto. 
   Focus 2. apply unspecEraseTrm; eauto. eraseTrmTac s1'' M''. rUnspecAll. 
   unfoldTac. rewrite union_empty_r in H3. rewrite <- coupleUnion in H3. 
   eapply PopSpecFastForward in H3; eauto. invertHyp.
   eapply spec_multi_trans. erewrite spec_multi_unused. eassumption. 
   repeat rewrite <- coupleUnion. unfoldTac. flipCouplesIn H3. 
   repeat rewrite coupleUnion in H3. repeat rewrite <- Union_associative in H3. 
   eapply forkCatchupL in H3; eauto. Focus 2. simpl. auto. Focus 2. simpl. auto. 
   invertHyp. eapply ind in H6; eauto. invertHyp. clear H3. unfoldTac. 
   rewrite Union_associative in H7. rewrite <- coupleUnion in H7. flipCouplesIn H7. 
   destructLast s1'. 
   {inv H0; try invertListNeq. rewrite couple_swap in H7.  rewrite coupleUnion in H7. 
    rewrite <- Union_associative in H7. rewrite spec_multi_unused in H7. flipCouples.  
    repeat rewrite coupleUnion. repeat rewrite <- Union_associative. rewrite spec_multi_unused. 
    apply simSpecStackSteps. assumption. }
   {invertHyp. eapply specSimActSteps; eauto. constructor. rewrite <- app_assoc in H7. 
    simpl in *. rewrite Union_associative in H7. rewrite <- coupleUnion in H7. 
    rewrite couple_swap in H7. flipCouplesIn H7. assumption. }
  }
  Grab Existential Variables. eapply lookupCreatedSpecEmpty; eauto. 
  eapply lookupCreatedSpecFull; eauto. 
Qed. 