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
(*Require Import ForkIndependence. *)

Axiom uniqueTP : forall T1 T2 t, tIn (tUnion T1 T2) t -> tIn T1 t -> tIn T2 t -> False. 

Theorem unionEq : forall T1 T2 T2', tUnion T1 T2 = tUnion T1 T2' -> T2 = T2'.  
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
   assert(tIn (tUnion T1 T2) x). apply Union_intror. auto. copy H. apply H1 in H.
   inversion H; subst. eapply uniqueTP in H0; eauto. inversion H0. auto. }
  {apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
   assert(tIn (tUnion T1 T2') x). apply Union_intror. auto. copy H. apply H2 in H3. 
   inversion H3; subst. eapply uniqueTP in H0; eauto. inversion H0. auto. }
Qed. 

Hint Constructors Union Couple. 

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

Hint Constructors spec_step. 

Theorem UnionEqTID : forall T T' tid s1 s2 M s1' s2' M',
                       tUnion T (tSingleton(tid,s1,s2,M)) = tUnion T' (tSingleton(tid,s1',s2',M')) ->
                       T = T' /\ s1 = s1' /\ s2 = s2' /\ M = M'. 
Proof. 
  intros. unfoldSetEq H. assert(tIn (tUnion T (tSingleton(tid,s1,s2,M)))(tid,s1,s2,M)). 
  apply Union_intror. constructor. copy H.  apply H0 in H. inversion H.  
  {assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1,s2,M)). 
   econstructor. econstructor. eauto. auto. 
   assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1',s2',M')). 
   econstructor. apply Union_intror. constructor. auto. eapply uniqueThreadPool in H5; eauto. 
   inv H5. repeat constructor; auto. eqSets. 
   {assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H5. apply H0 in H5. 
    inversion H5; subst. auto. inv H8. exfalso. eapply uniqueTP; eauto. constructor. }
   {assert(tIn (tUnion T' (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H5. 
    apply H1 in H5. inversion H5; subst. auto. inv H8. exfalso. eapply uniqueTP; eauto. 
    constructor. }
  }
  {subst. inv H3. repeat constructor; auto. eqSets. 
   {assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H4. apply H0 in H4. 
    inversion H4; subst. auto. inv H6. exfalso. eapply uniqueTP; eauto. constructor. }
   {assert(tIn (tUnion T' (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H4. 
    apply H1 in H4. inversion H4; subst. auto. inv H6. exfalso. eapply uniqueTP; eauto. 
    constructor. }
  }
Qed. 

Ltac foldTac := fold Add in *; fold tAdd in *; fold tUnion in *; fold tSingleton in *; fold tCouple in *.

Ltac rUnspec := erewrite unspecSingleton; eauto.
Ltac rUnspecIn H := erewrite unspecSingleton in H; eauto.
Ltac rUnspecAll := erewrite unspecSingleton in *; eauto. 

Inductive eraseTrm : list action -> trm -> trm -> Prop :=
|eraseTrmNil : forall M, eraseTrm nil M M
|eraseTrmRead : forall x t E d s M, eraseTrm (s++[rAct x t E d]) M t
|eraseTrmWrite : forall x t E M d N s, eraseTrm (s++[wAct x t E M d]) N t
|eraseTrmNew : forall x t E d s M, eraseTrm (s++[nAct t E d x]) M t
|eraseTrmFork : forall t E M d N s, eraseTrm (s++[fAct t E M d]) N t
|eraseTrmSR : forall t E M N d M' s, eraseTrm (s++[srAct t E M N d]) M' t. 

Theorem unspecEraseTrm : forall tid s1 s2 M M', 
                          eraseTrm s1 M M' ->
                          unspecThread(tid,unlocked s1,s2,M) (tSingleton(tid,unlocked nil,s2,M')). 
Proof.
  intros. destructLast s1. 
   {inv H; try invertListNeq. auto. }
   {invertHyp. inv H; try solve[invertListNeq]; apply lastElementEq in H1;
   subst; unspecThreadTac; auto. }
Qed. 

Theorem eEraseTrm : forall s1 M, exists M', eraseTrm s1 M M'. 
  intros. destructLast s1. 
  {econstructor. econstructor. }
  {invertHyp. destruct x; econstructor; econstructor. }
Qed. 

Ltac eraseTrmTac s1 M := assert(exists M', eraseTrm s1 M M') by apply eEraseTrm; invertHyp.  

Theorem EqJMeq : forall (T:Type) (x y:T), x = y -> JMeq x y.
Proof.
  intros. subst. auto. Qed. 

Axiom UnionSingletonEq : forall T T' a b, 
                 tUnion T (tSingleton a) = tUnion T' (tSingleton b) -> 
                 tIn T' a -> T = tUnion (Subtract thread T' a) (tSingleton b).

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


Theorem simSpecJoin : forall H T H' T' tid s1 s2 M' M'',
                        spec_multistep H (tUnion T (tSingleton(tid,s1,s2,M'))) H' 
                                       (tUnion T' (tSingleton(tid,s1,s2,M''))) ->
                        spec_multistep H T H' T'. 
Proof.
  intros. dependent induction H0. 
  {unfoldTac. apply UnionEqTID in x. invertHyp. constructor. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H4. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor.
   apply H2 in H4. inv H4. 
   {copy H5. apply pullOut in H5. rewrite H5. econstructor. eapply specStepChangeUnused. 
    eauto. eapply IHspec_multistep. Focus 2. auto. apply UnionSingletonEq in H1. rewrite H1. 
    unfoldTac. rewrite UnionSwap. auto. auto. }
   {inv H5. inv H. 
    {unfoldTac; invertHyp. inv H4. eapply IHspec_multistep; eauto. apply UnionEqTID in H1. 
     invertHyp. auto. }
     {unfoldTac; invertHyp. inv H7. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
     {unfoldTac; invertHyp. inv H4. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
     {unfoldTac; invertHyp. inv H4. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
     {unfoldTac; invertHyp. inv H4. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
     {unfoldTac; invertHyp. inv H7. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
    }
  }
Qed. 

Theorem wrapDistributeApp : forall s a N E e p, 
                              wrapActs(s++[a]) N E e p = wrapActs(s) N E e p++ wrapActs[a] N E e p.
Proof.
  induction s; intros. 
  {simpl. destruct a; auto. }
  {simpl. destruct a; auto; destruct a0; auto; rewrite IHs; auto. }
Qed. 

Theorem wrapEraseTrm : forall s M M' N N' E p,
                         eraseTrm s M M' -> 
                         eraseTrm (wrapActs s N E N' p) 
                                  (fill E (specJoin (ret N) M)) (fill E (specJoin (ret N) M')). 
Proof.
  intros. inv H; try solve[rewrite wrapDistributeApp; constructor]. 
  {simpl. constructor. }
Qed. 


Ltac specActEq H := 
  eapply firstSpecActEq in H; [idtac|apply Union_intror; rewrite app_nil_l; constructor|
                               apply Union_intror; constructor]. 

Theorem eraseTrmApp : forall x a M M', 
                        eraseTrm (x ++ [a]) M M' -> actionTerm a M'. 
Proof.
  intros. inv H; try solve[apply lastElementEq in H1; subst; constructor].
  invertListNeq. 
Qed. 

Theorem specFastForward : forall H T H' T' tid x0 x s2' N N0 M M' M'',
             eraseTrm (x0++[x]) N M' ->                                                
             spec_multistep H (tUnion T (tSingleton(tid,specStack nil N0, s2', M)))
                            H' (tUnion T' (tSingleton(tid,specStack(x0++[x]) N0, s2', M''))) ->
             exists H'' T'',
               spec_multistep H (tUnion T (tSingleton(tid,specStack nil N0, s2', M))) 
                              H'' (tUnion T'' (tSingleton(tid,specStack nil N0, s2', M'))) /\
               spec_multistep H'' (tUnion T'' (tSingleton(tid, specStack nil N0, s2', M')))
                              H' (tUnion T' (tSingleton(tid,specStack(x0++[x]) N0, s2',M''))). 
Proof.
  intros. dependent induction H1. 
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy x. unfoldSetEq H2. copy H. apply specStepSingleton in H2. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x2)) x2). apply Union_intror. constructor. apply H3 in H2. 
   inv H2. 
   {eapply IHspec_multistep in H0. Focus 3. auto. Focus 2. apply UnionSingletonEq in x; auto.  
    rewrite x. unfoldTac. rewrite UnionSwap. auto. invertHyp. exists x3. exists x4. split; auto.
    apply pullOut in H5. unfoldTac. rewrite H5. rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap. eauto. }
   {inv H5. apply UnionEqTID in x. invertHyp. clear H2 H5 H7. inversion H; subst. 
    {unfoldTac; invertHyp. inv H2. eapply IHspec_multistep in H0. Focus 3. 
     auto. Focus 2. auto. invertHyp. exists x. exists x2. split; eauto. econstructor. 
     eapply SBasicStep; eauto. assumption. }
    {unfoldTac; invertHyp. inv H7. copy H1. specActEq H1. subst. 
     apply eraseTrmApp in H0. inv H0.  exists h'. exists T. split. constructor. 
     econstructor. eapply SFork. eauto. }
    {unfoldTac; invertHyp. inv H2. copy H1. specActEq H1. subst. exists h. exists T. 
     apply eraseTrmApp in H0. inv H0. split. constructor. econstructor. 
     eauto. eauto. }
    {unfoldTac; invertHyp. inv H2. copy H1. specActEq H1. subst. exists h. exists T. 
     apply eraseTrmApp in H0. inv H0. split. constructor. econstructor. 
     eauto. eauto. }
    {unfoldTac; invertHyp. inv H2. copy H1. specActEq H1. subst. exists h. exists T. 
     apply eraseTrmApp in H0. inv H0. split. constructor. econstructor. 
     eauto. eauto. }
    {unfoldTac; invertHyp. inv H7. copy H1. specActEq H1. subst. apply eraseTrmApp in H0. 
     inv H0. exists h'. exists T. split. constructor. econstructor. eauto. eauto. }
   }
  }
Qed. 

Ltac monoActs H :=
  eapply monotonicActions in H;[idtac|apply Union_intror; constructor|apply Union_intror;constructor].

Theorem simTSteps : forall H T H' T' tid s1 s2 s1' s2' N M M' tid',
                      spec_multistep H (tUnion T (tSingleton(tid,s1,s2,M)))
                                     H' (tUnion T' (tSingleton(tid,s1,s2,M'))) ->
                      spec_multistep H (tUnion T (tSingleton(tid',s1',s2',N)))
                                     H' (tUnion T' (tSingleton(tid',s1',s2',N))). 
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H4. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
   apply H2 in H4. inv H4. 
   {copy H5. apply pullOut in H5. rewrite H5. unfoldTac. rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap.
    eapply IHspec_multistep; eauto. apply UnionSingletonEq in H1. rewrite H1.
    rewrite UnionSwap. eauto. auto. }
   {inv H5. inv H; unfoldTac; invertHyp; invThreadEq.   
    {eapply IHspec_multistep; eauto. apply UnionEqTID in H1. invertHyp. eauto. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
   }
  }
Qed. 

Fixpoint joinCtxts E1 E2 :=
  match E1 with
      | bindCtxt E M => bindCtxt (joinCtxts E E2) M
      | handleCtxt E M => handleCtxt (joinCtxts E E2) M
      | appCtxt E M => appCtxt (joinCtxts E E2) M
      | appValCtxt E M => appValCtxt (joinCtxts E E2) M
      | pairCtxt E M => pairCtxt (joinCtxts E E2) M
      | pairValCtxt E M => pairValCtxt (joinCtxts E E2) M
      | fstCtxt E => fstCtxt (joinCtxts E E2)
      | sndCtxt E => sndCtxt (joinCtxts E E2)
      | specRunCtxt E M => specRunCtxt (joinCtxts E E2) M
      | specJoinCtxt E M => specJoinCtxt (joinCtxts E E2) M
      | holeCtxt => E2
  end. 

Theorem notValFill : forall E e, ~ val e -> ~val (fill E e). 
Proof.
  induction E; intros; simpl; try solve[introsInv].
  {intros c. inv c. apply IHE in H. contradiction. }
  {intros c. inv c. apply IHE in H. contradiction. }
  {auto. }
Qed. 

Theorem decomposeNotVal : forall t E e, decompose t E e -> E <> holeCtxt -> ~val t. 
Proof.
  intros. induction H; try solve[introsInv].
  {intros c. inv c. contradiction. }
  {introsInv. contradiction. }
Qed. 

Theorem decomposeFurther : forall E E' e e' e'',
                                  ctxtWF e E -> decompose e' E' e'' -> ~ val e' ->
                                  decompose (fill E e') (joinCtxts E E') e''.
Proof.
  induction E; intros. 
  {simpl. constructor. inv H. eapply notValFill. auto. inv H. eapply IHE; eauto. }
  {simpl. inv H. constructor. auto. apply notValFill; auto. eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {simpl. auto. }
Qed. 


Theorem joinFill : forall E1 E2 e, fill (joinCtxts E1 E2) e = fill E1 (fill E2 e). 
Proof.
  induction E1; intros; try solve[simpl; rewrite IHE1; eauto]. 
  simpl. auto. 
Qed. 

Theorem simBasicStepFill : forall E e M M',
                             ctxtWF e E -> basic_step M M' ->
                             basic_step (fill E M) (fill E M'). 
Admitted. 

Theorem simSpecJoin' : forall H T H' T' tid tid' s2 s2' M M' s1 s1' N0 N1 E e p,              
        spec_multistep H (tUnion T (tSingleton(tid,specStack s1 N0, s2, M)))
                       H' (tUnion T' (tSingleton(tid,specStack s1' N0, s2, M'))) -> ~val e ->
        spec_multistep H (tUnion T (tSingleton(tid',unlocked (wrapActs s1 N1 E e p),s2',fill E (specJoin(ret N1)M))))
           H' (tUnion T' (tSingleton(tid',unlocked(wrapActs s1' N1 E e p),s2',fill E (specJoin(ret N1)M')))).
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. inv H. constructor. }
  {copy x. unfoldSetEq H2. copy H. apply specStepSingleton in H2. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x0)) x0). apply Union_intror. constructor. 
   apply H3 in H2. inv H2. 
   {copy H5. apply pullOut in H5. rewrite H5. unfoldTac. rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap.
    eapply IHspec_multistep; eauto. apply UnionSingletonEq in x; auto.  rewrite x. 
    rewrite UnionSwap. auto. }
   {inv H5. apply UnionEqTID in x. invertHyp. inv H; unfoldTac; invertHyp; invThreadEq.  
    {inv H8. 
     {econstructor. eapply SBasicStep; auto. eapply basicBeta.  

Theorem decomposeFill : forall e e' e'' E E', 
                          ctxtWF e E -> decompose e' E' e'' -> ~val e'' ->
                          decompose (fill E e') (joinCtxts E E') e''. 
Proof.
  intros. induction H. 
  {simpl. 











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
    eassumption. econstructor. eapply SFork. rewrite <- coupleUnion. constructor. }
   {destruct l. 
    {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
     erewrite unspecSingleton;try unspecThreadTac; auto. erewrite unspecSingleton; eauto. 
     unfold tUnion. rewrite union_empty_r. eapply spec_multi_trans. copy d. apply decomposeEq in H. subst. 
     erewrite unspecSingleton in H3; eauto. copy d. apply decomposeEq in H. rewrite <- H.  
     econstructor. auto. unfold tUnion. eapply SFork. rewrite <- coupleUnion. unfoldTac. 
     constructor. simpl. copy d. apply decomposeEq in H; subst. eapply unspecFork.
     rewrite app_nil_l. auto. }
   {unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
    assert(exists t', unspecThread (tid, unlocked(a :: l), s2, t0) t'). 
    apply unspecThreadTotal. invertHyp. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton; eauto. unfold tUnion. rewrite union_empty_r. 
    erewrite unspecSingleton in H3; eauto. eapply spec_multi_trans. eassumption. 
    econstructor. eapply SFork. rewrite <- coupleUnion. constructor. uCons a l.
    rewrite unspecTwoActs'. eauto. }
   }
   {simpl. unfoldTac. rewrite coupleUnion in *. repeat rewrite unspecUnionComm in *. 
    repeat rUnspecAll. unfoldTac. repeat rewrite union_empty_r in *. eapply spec_multi_trans.
    eassumption. econstructor. eapply SFork. rewrite <- coupleUnion. constructor. }
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
   eapply rollbackWF in H5; eauto. Focus 2. unfold commitPool. intros. inv H3; auto.
   econstructor; eauto. uCons (wAct x t0 E N d) (@nil action). rewrite unspecHeapAddWrite; auto. 
   inv H5. inv H6. rewrite unspecUnionComm in H7. repeat rewrite unspecUnionComm. simpl. 
   erewrite unspecSingleton. Focus 2. unspecThreadTac. rewrite app_nil_l. auto. 
   unfoldTac. rewrite <- Union_associative. erewrite <- spec_multi_unused in H7. 
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
    eapply simTSteps in H2. eassumption. eapply simSpecJoin' in H4. simpl in *. eauto. }
  }
  {copy H13. unfoldTac. rewrite <- Union_associative. rewrite wfFrame. Focus 2. 
   unfold commitPool. intros. inv H3. auto. rewrite <- Union_associative in H0. 
   rewrite wfFrame in H0. Focus 2. unfold commitPool; intros. inv H3. auto.
   eapply rollbackWF; eauto. }
  {inv H0. inv H2. econstructor; eauto. rewrite unspecUnionComm in *. rUnspecAll. 
   rewrite spec_multi_unused in H3. rewrite spec_multi_unused. auto. }
  {inversion H0; subst. inversion H3; subst. econstructor; eauto. erewrite unspecHeapRBRead; eauto. 
   rewrite unspecUnionComm in *. erewrite unspecSingleton in H4. Focus 2. 
   unspecThreadTac; auto. eraseTrmTac s1' M. erewrite unspecSingleton. Focus 2. 
   eapply unspecEraseTrm; eauto. eapply specStepRead in H4; eauto. Focus 2. 
   eapply lookupUnspecFull; eauto. invertHyp. rewrite unspecUnspecHeap in H2. 
   rewrite unspecUnspecPool in H7. rewrite <- H2. inv H7. 
   
  {inv H0. inv H2. econstructor; eauto. unfoldTac. rewrite coupleUnion in *.
   repeat rewrite unspecUnionComm in *. erewrite unspecSingleton in H3. Focus 2. 
   eapply unspecFork; auto. erewrite unspecSingleton in H3. Focus 2. 
   eapply unspecLocked; eauto. unfoldTac. rewrite union_empty_r in H3. 
   rewrite <- coupleUnion in H3. apply forkInd' in H3. unfoldTac. rewrite coupleUnion in H3. 
   rewrite unspecUnionComm in H3. eauto. }

                    

a;lkhdj



