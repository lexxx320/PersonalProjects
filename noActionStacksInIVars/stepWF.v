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
Require Import specIndependence. 
Require Import writeIndependence. 
Require Import IndependenceCommon. 

Ltac eUnspec :=
  match goal with
    | |-spec_multistep ?H ?t ?H' (tUnion ?T' (tSingleton ?t')) =>
        assert(exists t'', unspecThread t' t'') by apply unspecThreadTotal; invertHyp
    | H:spec_multistep ?H ?t ?H' (tUnion ?T' (tSingleton ?t')) |- _ =>
        assert(exists t'', unspecThread t' t'') by apply unspecThreadTotal; invertHyp
  end. 

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

Ltac rUnspec := erewrite unspecSingleton; eauto.
Ltac rUnspecIn H := erewrite unspecSingleton in H; eauto.
Ltac rUnspecAll := erewrite unspecSingleton in *; eauto. 

Ltac invertDecomp :=
  match goal with
    |H:(?a,?b,?c,?d)=(?e,?f,?g,?h) |- _ => inv H
    |H:?x = ?y |- _ => solve[inv H]
    |H:decompose ?M ?E ?e,H':decompose ?M' ?E' ?e' |- _=>
     eapply uniqueCtxtDecomp in H; eauto; invertHyp
  end. 

Axiom UnionSingletonCoupleEq : forall T T' a b c, 
                 tUnion T (tSingleton a) = tUnion T' (tCouple b c) -> 
                 tIn T' a -> T = tUnion (Subtract thread T' a) (tCouple b c).

Axiom CoupleUnionAx : forall T T' t1 t2,
                        tUnion T (tSingleton t1) = tUnion T' (tCouple t1 t2) -> 
                        T = tUnion T' (tSingleton t2).

Ltac actEqTac H :=
  eapply firstActEq in H;[idtac|apply Union_intror; rewrite app_nil_l; constructor|
                          apply Union_intror; constructor]. 

Theorem forkFastForward : forall H T H' T' tid s1' s1'' N M M' M'' n E s2 d,
  decompose M' E (fork M'') -> n = numForks' s2 ->   
  spec_multistep H (tUnion T (tSingleton(tid,unlocked nil, s2, M')))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,M)
                                       (n::tid,locked s1'',nil,N))) ->
  exists H'' T'',
    spec_multistep H (tUnion T (tSingleton(tid,unlocked nil,s2,M')))
                   H'' (tUnion T'' (tCouple(tid,unlocked[fAct M' E M'' d n],s2,fill E (ret unit))
                                          (n::tid,locked nil,nil,M''))) /\
    spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[fAct M' E M'' d n],s2,fill E (ret unit)) (n::tid,locked nil,nil,M'')))
                   H'(tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,M)
                                       (n::tid,locked s1'',nil,N))) /\
    spec_multistep H T H'' T''. 
Proof.
  intros. dependent induction H2. 
  {unfoldTac. rewrite coupleUnion in x. rewrite <- Union_associative in x. 
   rewrite UnionSwap in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq H1. copy H. apply specStepSingleton in H1. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x0)) x0). apply Union_intror. constructor. 
   apply H3 in H1. inv H1. 
   {eapply IHspec_multistep in H0. Focus 4. auto. Focus 2. auto. Focus 2. 
    apply UnionSingletonEq in x; auto.  
    rewrite x. unfoldTac. rewrite UnionSwap. auto. invertHyp. exists x1. exists x2.
    split; auto. apply pullOut in H5. unfoldTac. rewrite H5. rewrite UnionSwap. 
    econstructor. eapply specStepChangeUnused. eauto. unfoldTac. 
    rewrite <- UnionSwap. eauto. split. auto. copy H5. apply pullOut in H5. 
    rewrite H5. econstructor. eapply specStepChangeUnused. eauto. eauto. }
   {inv H5. apply UnionEqTID in x. invertHyp. clear H1 H5 H7. inversion H; subst. 
    {unfoldTac; invertHyp; invThreadEq.
     inv H5; eapply uniqueCtxtDecomp in H0; eauto; invertHyp; solveByInv. }
    {unfoldTac; invertHyp; invThreadEq. copy d0. eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H6. exists h'. exists T. split. econstructor. 
     eapply SFork; eauto. simpl. constructor. split. simpl in *. assert(d=d0). 
     apply proof_irrelevance. subst. assumption. constructor. }
    {unfoldTac; invertHyp; invThreadEq. copy d0; eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H7. }
    {unfoldTac; invertHyp; invThreadEq. copy d0; eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H7. }
    {unfoldTac; invertHyp; invThreadEq. copy d0; eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H6. }
    {unfoldTac; invertHyp; invThreadEq. copy d0; eapply uniqueCtxtDecomp in H0; eauto.
     invertHyp. inv H6. }
   }
  }
Qed.

Theorem appCons : forall (T:Type) x (y:T) z,
                    x ++ [y;z] = (x ++ [y]) ++ [z]. 
Proof. 
  intros. rewrite <- app_assoc. simpl. auto. Qed. 

Theorem eraseTrmActTerm : forall x a M M',
                            eraseTrm (x++[a]) M M' ->
                            actionTerm a M'. 
Proof.
  intros. destruct a; inv H; try solve[invertListNeq]; 
  apply lastElementEq in H1; inv H1; constructor. 
Qed. 
 
Theorem forkCatchup' : forall H T H' T' x x0 tid s1' s1'' s2 e1 e1' e2 e2' M' M'' n E d  S S',
    eraseTrm s1' e1' x -> eraseTrm s1'' e2' x0 -> n = numForks' s2 -> S = [] \/ S' = [] ->
    spec_multistep H (tUnion T (tCouple(tid,unlocked(S++[fAct M' E M'' d n]), s2, e1)
                                       (n::tid,locked S',nil,e2)))
                   H' (tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) -> 
    exists H'' T'',
      spec_multistep H (tUnion T (tCouple(tid,unlocked(S++[fAct M' E M'' d n]),s2,e1)
                                         (n::tid,locked nil,nil,e2)))
                     H'' (tUnion T'' (tCouple(tid,unlocked(S++[fAct M' E M'' d n]),s2,x)
                                             (n::tid,locked S',nil,x0))) /\
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked(S++[fAct M' E M'' d n]),s2,x)
                                             (n::tid,locked S',nil,x0)))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) /\
      spec_multistep H T H'' T''. 
Proof.
  intros. genDeps{x;x0}. dependent induction H4; intros.
  {unfoldTac. repeat rewrite coupleUnion in x. 
   repeat rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. inv H3. 
   {apply UnionEqTID in H. invertHyp. inv H. destruct s1'; inv H6. Focus 2. invertListNeq. 
    inv H0; try solve[invertListNeq]. simpl. 


Theorem forkCatchup : forall H T H' T' x x0 tid s1' s1'' s2 e1 e1' e2 e2' M' M'' n E d,
    eraseTrm s1' e1' x -> eraseTrm s1'' e2' x0 -> n = numForks' s2 -> 
    spec_multistep H (tUnion T (tCouple(tid,unlocked[fAct M' E M'' d n], s2, e1)
                                       (n::tid,locked nil,nil,e2)))
                   H' (tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) -> 
    exists H'' T'',
      spec_multistep H (tUnion T (tCouple(tid,unlocked[fAct M' E M'' d n],s2,e1)
                                         (n::tid,locked nil,nil,e2)))
                     H'' (tUnion T'' (tCouple(tid,unlocked[fAct M' E M'' d n],s2,x)
                                             (n::tid,locked nil,nil,x0))) /\
      spec_multistep H'' (tUnion T'' (tCouple(tid,unlocked[fAct M' E M'' d n],s2,x)
                                             (n::tid,locked nil,nil,x0)))
                 H' (tUnion T' (tCouple(tid,unlocked(s1'++[fAct M' E M'' d n]),s2,e1')
                                         (n::tid,locked s1'',nil,e2'))) /\
      spec_multistep H T H'' T''. 
Proof.
  intros. genDeps{x;x0}. dependent induction H3; intros.
  {unfoldTac. repeat rewrite coupleUnion in x. 
   repeat rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. 
   inv H3. apply UnionEqTID in H. invertHyp. inv H. destruct s1'; inv H5. 
   inv H0; try invertListNeq. inv H1; try invertListNeq. exists h. exists T'. 
   split. constructor. split. constructor. constructor. invertListNeq. }
  {copy x. copy H. apply specStepSingleton in H4. invertHyp. copy x. unfoldSetEq x.
   assert(tIn (tUnion T0 (tSingleton x2)) x2). apply Union_intror. constructor.
   apply H5 in H7. inv H7. 
   {eapply IHspec_multistep in H0; eauto. invertHyp. exists x. exists x3. 
    split. copy H8. apply pullOut in H9. rewrite H9. unfoldTac. rewrite UnionSwap. 
    econstructor. eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap.
    eauto. split. auto. copy H8. apply pullOut in H9. rewrite H9. econstructor. 
    eapply specStepChangeUnused. eauto. auto. apply UnionSingletonCoupleEq in H2. 
    rewrite H2. unfoldTac. rewrite UnionSwap. auto. auto. }
   {inv H8. unfoldTac. rewrite coupleUnion in H2. rewrite <- Union_associative in H2.
    rewrite UnionSwap in H2. apply UnionEqTID in H2. invertHyp. 
    inv H; unfoldTac; invertHyp; invThreadEq. 
    {eapply IHspec_multistep in H0. invertHyp. exists x. exists x2. 
     split. rewrite coupleUnion. rewrite <- Union_associative. rewrite UnionSwap. 
     econstructor. eapply SBasicStep. eauto. constructor. unfoldTac. 
     rewrite <- UnionSwap. rewrite Union_associative. rewrite <- coupleUnion. 
     eauto. split. eassumption. assumption.  auto. rewrite Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. auto. auto. auto. }
    {simpl in *. copy H3. eapply consedActEq in H3. Focus 2. apply Union_intror. simpl. 
     rewrite app_nil_l. constructor. Focus 2. apply Union_intror. constructor. 
     invertHyp. copy H0. apply eraseTrmActTerm in H0. inv H0. 

Theorem raw_replaceSame : forall (T:Type) H x (v:T),
                        raw_heap_lookup x H = Some v -> raw_replace x v H = H. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i)eqn:eq. 
   {inv H0. apply beq_nat_true in eq. subst. auto. }
   {rewrite IHlist; eauto. }
  }
Qed. 

Theorem replaceSame : forall (T: Type) H x (v:T),
                        heap_lookup x H = Some v -> replace x v H = H. 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. eapply raw_replaceSame; eauto. 
Qed. 
 
Theorem specStepFullIVar' : forall x H H' ds TID s1 s2 N S tid M T t' sc,
       spec_step H T (tSingleton(TID,s1,s2,N)) H' T t' ->
       heap_lookup x H = Some (sfull sc ds S tid M) ->
       (heap_lookup x H' = Some (sfull sc ds S tid M) \/
        heap_lookup x H' = Some(sfull sc (TID::ds) S tid M)). 
Proof.
  intros. inv H0; unfoldTac; invertHyp; invThreadEq; eauto. 
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H3 in H1. inv H1. 
    right. erewrite HeapLookupReplace; eauto. }
   {rewrite lookupReplaceNeq. eauto. intros c. subst. apply beq_nat_false in eq. apply eq. 
    auto. }
  }
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H3 in H1. inv H1. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; auto. }
  }
  {destruct H; simpl in *. destruct h. 
   {inv H1. } 
   {assert(x<>x0). intros c. subst. rewrite p in H1. inv H1. 
    rewrite <- beq_nat_false_iff in H. rewrite H. left; eauto. }
  }
Qed.

Ltac startIndCase :=
  match goal with
    |H:spec_step ?a ?b ?c ?d ?e ?f,H':tUnion ?T ?t = tUnion ?T' ?t' |- _ =>
     let n := fresh
     in let n' := fresh
        in copyAs H n; copyAs H' n'; apply specStepSingleton in n; invertHyp;
           unfoldSetEq n'
  end. 
Ltac eqIn H := 
  match type of H with
      |forall x, In ?X (tUnion ?T (tSingleton ?x1)) x -> ?a => 
       let n := fresh 
       in assert(n:In X (tUnion T (tSingleton x1)) x1) by (apply Union_intror; constructor);apply H in n
  end. 
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

Ltac takeTStep :=
  match goal with
      |H:In thread ?T ?t |- _ => apply pullOut in H; rewrite H; unfoldTac; rewrite UnionSwap;
                                 econstructor;[eapply specStepChangeUnused; eassumption|idtac];
                                 unfoldTac; rewrite <- UnionSwap
      |H:In thread ?T ?t |- _ => apply pullOut in H; rewrite H; unfoldTac; rewrite UnionSwap;
                                 econstructor
      |H:In thread ?T ?t |- _ => apply pullOut in H; rewrite H; 
                                 econstructor;[eapply specStepChangeUnused; eassumption|idtac]
  end.

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

Ltac consedActTac H :=
  eapply consedActEq in H;[idtac|apply Union_intror; rewrite app_nil_l; constructor|apply Union_intror; constructor].


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
    {copy H3. consedActTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists h'. exists T. 
     split. constructor. split. simpl. econstructor. eapply SFork; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
    {copy H3. consedActTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists H. exists T. 
     split. constructor. split. simpl. econstructor. eapply SGet; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
    {copy H3. consedActTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists H. exists T. 
     split. constructor. split. simpl. econstructor. eapply SPut; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
    {copy H3. consedActTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists H. exists T. 
     split. constructor. split. simpl. econstructor. eapply SNew; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
    {copy H3. consedActTac H3. invertHyp. apply eraseTrmApp in H0. inv H0. exists h'. exists T. 
     split. constructor. split. simpl. econstructor. eapply SSpec; eauto. eassumption. 
     econstructor. split. constructor. eauto. }
   }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq; eauto. 
Qed. 

Theorem listTailEq : forall (T:Type) a (b:T) c d e,
                       ~List.In b c -> ~List.In b e -> a ++ [b] ++ c = d ++ b::e -> c = e. 
Proof.
  induction a; intros. 
  {simpl in *. destruct d. simpl in *. inv H1. auto. inv H1. exfalso. apply  H. 
   apply in_or_app. right. simpl. left. auto. }
  {destruct d. inv H1. exfalso. apply H0. apply in_or_app. right. 
   simpl. auto. inv H1. eapply IHa; eauto. }
Qed.   

Theorem stepWF : forall H T t H' t', 
                   wellFormed H (tUnion T t) -> step H T t (OK H' T t') ->
                   wellFormed H' (tUnion T t'). 
Proof.
  intros. inversion H1; subst.      
  {destruct s1.  
   {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. 
    rUnspecAll. unfoldTac. rewrite union_empty_r in *. eapply spec_multi_trans; eauto. 
    econstructor. eapply SBasicStep. eauto. constructor. constructor. } 
   {destruct l. 
    {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. rUnspecAll. 
     apply spec_multi_unused in H3. rewrite spec_multi_unused. auto. }
    {inversion H0; subst. inversion H2; subst. econstructor; eauto. 
    rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. econstructor. 
    eauto. rewriteEmpty HNil. eapply SBasicStep; eauto. constructor. constructor. 
    uCons a l. eapply unspecTwoActs. eauto. }
   }
   {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. rUnspecAll. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SBasicStep; eauto.
    constructor. constructor. }
  }
  {inv H0. inv H2. econstructor; eauto. destruct s1.
   {simpl. unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans.
    eassumption. econstructor. eapply SFork. auto. rewrite <- coupleUnion. simpl. constructor. }
   {destruct l. 
    {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
     erewrite unspecSingleton;try unspecThreadTac; auto. erewrite unspecSingleton; eauto. 
     unfold tUnion. rewrite union_empty_r. eapply spec_multi_trans. copy d. apply decomposeEq in H. subst. 
     erewrite unspecSingleton in H3; eauto. copy d. apply decomposeEq in H. rewrite <- H.  
     econstructor. auto. unfold tUnion. eapply SFork; eauto. rewrite <- coupleUnion. unfoldTac. 
     constructor. simpl. copy d. apply decomposeEq in H; subst. eapply unspecFork.
     rewrite app_nil_l. auto. }
   {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    assert(exists t', unspecThread (tid, unlocked(a :: l), s2, t0) t'). 
    apply unspecThreadTotal. invertHyp. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton; eauto. unfold tUnion. rewrite union_empty_r. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. 
    econstructor. eapply SFork. auto. rewrite <- coupleUnion. constructor. uCons a l.
    rewrite unspecTwoActs'. eauto. }
   }
   {simpl. unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans.
    eassumption. econstructor. eapply SFork. auto. rewrite <- coupleUnion. constructor. }
  }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapRBRead; eauto. destruct s1.  
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. unfoldTac. rewrite union_empty_r in *. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. constructor. }
   {destruct l.
    {unfoldTac. rewrite unspecUnionComm in *. simpl. rUnspecAll. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SGet; eauto. constructor. eapply unspecRead. 
     rewrite app_nil_l. auto. }
   {rewrite unspecUnionComm in *. eUnspec. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton in H4. Focus 2. uCons a l. rewrite <- unspecTwoActs'. eauto. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. constructor. }
   }
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SGet; eauto. constructor. }
  }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapAddWrite; eauto. destruct s1.  
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. unfoldTac. rewrite union_empty_r in *. 
    eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. constructor. }
   {destruct l. 
    {unfold tUnion in *. rewrite unspecUnionComm in *. simpl. rUnspecAll. Focus 2. 
     unspecThreadTac. rewrite app_nil_l; auto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SPut; eauto. constructor. }
    {rewrite unspecUnionComm in *. eUnspec. rUnspecAll. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SPut; eauto. constructor. uCons a l.
     rewrite <- unspecTwoActs'. eauto. uCons a l. rewrite <- unspecTwoActs'; eauto. }
   }
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SPut; eauto. constructor. }
  }   
  {copy H5. unfoldTac. rewrite <- Union_associative in H0. rewrite wfFrame in H0. 
   eapply rollbackWF in H7; eauto. Focus 2. unfold commitPool. intros. inv H3; auto.
   econstructor; eauto. uCons (wAct x t0 E N d) (@nil action). rewrite unspecHeapAddWrite; auto.
   inv H7. inv H8. rewrite unspecUnionComm in H9. repeat rewrite unspecUnionComm. simpl. 
   erewrite unspecSingleton. Focus 2. unspecThreadTac. rewrite app_nil_l. auto. 
   unfoldTac. rewrite <- Union_associative. rewrite <- spec_multi_unused in H9. 
   eapply spec_multi_trans. eassumption. econstructor. eapply SPut; eauto. 
   simpl. rewrite <- Union_associative. constructor. }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapExtend; eauto. destruct s1. 
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. unfoldTac. rewrite union_empty_r in *. 
    eapply spec_multi_trans. eassumption. copy d. apply decomposeEq in H0; subst. 
    econstructor. eapply SNew; eauto. constructor. }
   {destruct l. 
    {unfold tUnion in *. rewrite unspecUnionComm in *. simpl. rUnspecAll. Focus 2. 
     unspecThreadTac. rewrite app_nil_l; auto. copy d. apply decomposeEq in H0; subst. 
     eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. constructor. }
    {copy d. apply decomposeEq in H0; subst. rewrite unspecUnionComm in *. eUnspec. 
     rUnspecAll. eapply spec_multi_trans. eassumption. econstructor. eapply SNew; eauto. 
     constructor. uCons a l. rewrite <- unspecTwoActs'. eauto. uCons a l. 
     rewrite <- unspecTwoActs'; eauto. }
   }
   {rewrite unspecUnionComm in *. simpl. rUnspecAll. 
    eapply spec_multi_trans. eassumption. copy d. apply decomposeEq in H0; subst. 
    econstructor. eapply SNew; eauto. constructor. }
  }   
  {inv H0. inv H2. econstructor; eauto. destruct s1.  
   {unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. simpl. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SSpec; eauto. rewrite <- coupleUnion. constructor. }
   {destruct l.
    {unfold tCouple. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
     erewrite unspecSingleton. Focus 2. eapply unspecSpecret. rewrite app_nil_l. simpl. auto. 
     copy d. apply decomposeEq in H. subst. auto. erewrite unspecSingleton; eauto. unfoldTac. 
     rewrite union_empty_r.  erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. 
     eassumption. econstructor. eapply SSpec; eauto. unfold tUnion. rewrite <- coupleUnion. 
     constructor. }
    {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. foldTac. eUnspec. 
     erewrite unspecSingleton in H3; eauto. repeat erewrite unspecSingleton; eauto. unfoldTac. 
     rewrite union_empty_r. eapply spec_multi_trans. eassumption. econstructor. eapply SSpec. 
     rewrite <- coupleUnion. constructor. uCons a l. rewrite unspecTwoActs'. eauto. }
   }
   {unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. simpl. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans. 
    eassumption. econstructor. eapply SSpec; eauto. rewrite <- coupleUnion. constructor. }
  }  
  {inv H0. inv H2. econstructor; eauto. unfoldTac. rewrite couple_swap in H3. 
   rewrite coupleUnion in H3. repeat rewrite unspecUnionComm in *. 
   erewrite unspecSingleton in H3; eauto. erewrite unspecSingleton in H3; eauto. 
   unfoldTac. repeat rewrite <- Union_associative in H3. rewrite spec_multi_unused in H3. 
   destructLast s1. 
   {simpl. erewrite unspecSingleton; eauto. rewrite spec_multi_unused. unfoldTac. 
    eapply simSpecJoin in H3. eauto. }
   {invertHyp. eraseTrmTac (x0++[x]) M. copy H0. 
    eapply wrapEraseTrm with(N:=N1)(E:=E)(N':=(specRun(ret N1) N0))in H0.
    erewrite unspecSingleton. Focus 2. apply unspecEraseTrm; eauto.
    eapply specFastForward in H3; eauto. invertHyp. eapply spec_multi_trans. 
    eapply simTSteps in H2. eassumption. eapply simSpecJoin' in H4. simpl in *.
    eauto. eauto. constructor. introsInv. }
  }
  {copy H13. unfoldTac. rewrite <- Union_associative. rewrite wfFrame. Focus 2. 
   unfold commitPool. intros. inv H3. auto. rewrite <- Union_associative in H0. 
   rewrite wfFrame in H0. Focus 2. unfold commitPool; intros. inv H3. auto.
   eapply rollbackWF; eauto. }
  {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. rUnspecAll. 
   rewrite spec_multi_unused in H3. rewrite spec_multi_unused. auto. }
  {inv H0. inv H3. econstructor; eauto. erewrite unspecHeapRBRead; eauto. 
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. unspecThreadTac. 
   auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2. apply unspecEraseTrm; eauto. 
   eapply readFastForward in H4. Focus 2. eapply unspecHeapLookupFull; eauto. Focus 2. eauto. 
   Focus 2. intros c. inv c. invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. 
   eassumption. copy H3. eapply monotonicReaders in H3; eauto. invertHyp.
   apply listTailEq in H9; auto. subst.  eapply readSimPureSteps in H7; eauto. Focus 2. 
   rewrite app_nil_l. simpl. eassumption. invertHyp. eapply spec_multi_trans.
   rewrite spec_multi_unused. eassumption. 
   
   admit. }
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
  {admit. }
  {admit. }
  {inv H0. inv H2. econstructor; eauto. unfoldTac. rewrite coupleUnion in *. 
   repeat rewrite unspecUnionComm in *. eraseTrmTac s1' M. rUnspecAll. 
   Focus 2. unspecThreadTac; eauto. Focus 3. unspecThreadTac; eauto. 
   Focus 2. apply unspecEraseTrm; eauto. eraseTrmTac s1'' N. rUnspecAll. Focus 2. 
   apply unspecEraseTrm. eauto. unfoldTac. rewrite union_empty_r in H3. 
   rewrite <- coupleUnion in H3. eapply forkFastForward in H3; eauto. invertHyp.
   eapply spec_multi_trans. erewrite spec_multi_unused. eassumption. 
   repeat rewrite <- coupleUnion. eapply forkCatchup in H3; eauto. 
   invertHyp. eapply spec_multi_trans. rewrite spec_multi_unused. eassumption. 
   
   




  




aldsfhlasdkjhfasd