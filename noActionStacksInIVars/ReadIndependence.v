Require Import SfLib.       
Require Import NonSpec.  
Require Import Spec.  
Require Import AST. 
Require Import hetList. 
Require Import Coq.Program.Equality. 
Require Import unspec. 
Require Import sets. 
Require Import erasure.  
Require Import Heap. 
Require Import classifiedStep. 
Require Import Coq.Sets.Ensembles. 
Require Import Coq.Sets.Powerset_facts. 

Theorem EqJMeq : forall (T:Type) (x y:T), x = y -> JMeq x y.
Proof.
  intros. subst. auto. Qed. 

Axiom UnionSingletonEq : forall T T' a b, tUnion T (tSingleton a) = tUnion T' (tSingleton b) -> 
                                          tIn T' a -> T = tUnion (Subtract thread T' a) (tSingleton b).

Axiom uniqueTP : forall T1 T2 t, tIn (tUnion T1 T2) t -> tIn T1 t -> tIn T2 t -> False. 

Ltac cleanup :=
  match goal with
      |H: ?x = ?x |- _ => clear H; cleanup
      |H: ?x = ?y |- _ => inv H
  end. 

Theorem specMultiHeapDepRead : forall H H' T T' x ds t N TID,
                               heap_lookup x H = Some(sfull nil ds nil t N) -> 
                               spec_multistep (replace x (sfull nil (Add tid ds TID) nil t N) H)
                                              T H' T' ->
                               spec_multistep H T (replace x (sfull nil (Add tid ds TID) nil t N) H) T'.
Proof. 
  intros. dependent induction H1. 
  {

(*  intros. dependent induction H1. 
  {admit. }
  {copy H2. apply specStepSingleton in H2. invertHyp. inversion H3; subst. 
   {unfoldTac; invertHyp. econstructor. eapply SBetaRed; eauto. eauto. }
   {unfoldTac; invertHyp. econstructor. eapply SProjL; eauto. eauto. }
   {unfoldTac; invertHyp. econstructor. eapply SProjR; eauto. eauto. }
   {unfoldTac; invertHyp. econstructor. eapply SBind; eauto. eauto. }
   {unfoldTac; invertHyp. econstructor. eapply SBindRaise; eauto. eauto. }
   {unfoldTac; invertHyp. econstructor. eapply SHandle; eauto. eauto. }
   {unfoldTac; invertHyp. econstructor. eapply SHandleRet; eauto. eauto. }
   {unfoldTac; invertHyp. econstructor. eapply SFork; eauto. eauto. }
   {unfoldTac; invertHyp. destruct (beq_nat x x1) eqn:eq. 
    {apply beq_nat_true in eq. subst. copy H0. erewrite HeapLookupReplace in H4; eauto. 
     inv H4. econstructor. eapply SGet; eauto. simpl. eapply IHspec_multistep.
     erewrite HeapLookupReplace; eauto. apply EqJMeq. unfoldTac. 
     rewrite Union_associative. rewrite (Union_commutative tid (Singleton tid TID)).
     rewrite <- Union_associative. repeat rewrite replaceOverwrite. reflexivity. }
    {econstructor. eapply SGet with(x:=x1). eauto. auto. simpl. rewrite lookupReplaceNeq.  
     eauto. intros c. subst. apply beq_nat_false_iff in eq. apply eq. auto. 
     auto. simpl. eapply IHspec_multistep with (x0:=x1). *)
     Admitted. 

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

Theorem monotonicActions : forall H tid H' T T' s1 s1' s2 s2' M M',
                             spec_multistep H T H' T' ->
                             tIn T (tid,s1,s2,M) -> tIn T' (tid,s1',s2',M') ->
                             length s1 + length s2 <= length s1' + length s2'. 
Proof.
  intros. genDeps{tid; s1; s1'; s2; s2'; M; M'}. dependent induction H0. 
  {intros. assert(thread_lookup p2 tid (tid,s1,s2,M)). econstructor. auto. 
   auto. assert(thread_lookup p2 tid (tid,s1',s2',M')). econstructor. auto. 
   auto. eapply uniqueThreadPool in H; eauto. inv H. omega. }
  {intros. inversion H1; subst. 
   {assert(tIn (tUnion T t') (tid,s1,s2,M)). constructor; auto. eapply IHspec_multistep in H4. 
    eauto. eauto. }
   {inversion H; subst. 
    {inv H3. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {inv H3. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {inv H3. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {inv H3. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {inv H3. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {inv H3. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {inv H3. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {inv H3. eapply IHspec_multistep with(s4 := (fAct M E M0 d::s1))(s3:=s2) in H2. 
     simpl in H2. omega. apply Union_intror. apply Couple_l. }
    {inv H3. eapply IHspec_multistep with(s4:=rAct x M E d::s1)(s3:=s2) in H2. 
     simpl in H2. omega. apply Union_intror. constructor. }
    {inv H3. eapply IHspec_multistep with(s4:=wAct x M E N d::s1)(s3:=s2) in H2. 
     simpl in H2. omega. apply Union_intror. constructor. }
    {inv H3. eapply IHspec_multistep with(s4:=nAct M E d x::s1)(s3:=s2) in H2. 
     simpl in H2. omega. apply Union_intror. constructor. }
    {inv H3. eapply IHspec_multistep with(s4:=srAct M E M0 N d::s1)(s3:=s2) in H2. 
     simpl in H2. omega. apply Union_intror. constructor. }
   }
  }
Qed. 

Theorem specMultiPureThrowout : forall H H' T T' tid s1 s2 M M',
                                  spec_multistep H (tUnion T (tSingleton(tid,s1,s2,M))) H'
                                                 (tUnion T' (tSingleton(tid,s1,s2,M'))) ->
                                  spec_multistep H T H' T'. 
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {copy H. apply specStepSingleton in H. invertHyp. copy x. unfoldSetEq x. 
   assert(tIn (tUnion T0 (tSingleton x0)) x0). apply Union_intror. constructor. apply H2 in H4. 
   inversion H4; subst. 
   {copy H5. apply pullOut in H5. rewrite H5. econstructor. eapply specStepChangeUnused. eauto. 
    eapply IHspec_multistep; eauto. apply EqJMeq. apply UnionSingletonEq in H; auto.
    rewrite H. unfoldTac. rewrite Union_associative. rewrite (Union_commutative thread _ t'). 
    rewrite <- Union_associative. auto. }
   {inv H5. apply UnionEqTID in H. invertHyp. 
    inversion H1; subst; try solve[unfoldTac; invertHyp; cleanup; eauto].
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions with (s1' := s1) in H0.
     Focus 2. apply Union_intror. apply Couple_l. simpl in H0. Focus 2. 
     apply Union_intror. constructor. omega. }
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions in H0. Focus 2. 
     apply Union_intror; constructor. Focus 2. apply Union_intror. constructor. 
     simpl in H0. omega. }
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions in H0. Focus 2. 
     apply Union_intror; constructor. Focus 2. apply Union_intror. constructor. 
     simpl in *. omega. }
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions in H0. Focus 2. 
     apply Union_intror; constructor. Focus 2. apply Union_intror. constructor. 
     simpl in *. omega. }
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions in H0. Focus 2. 
     apply Union_intror; constructor. Focus 2. apply Union_intror. constructor. 
     simpl in *. omega. }
   }
  }
Qed.  

Theorem eqUnspec : forall T, T = unspecPoolAux T -> commitPool T. 
Proof. 
  intros. unfold commitPool. intros. unfoldSetEq H. apply H1 in H0. inv H0. inv H3; inv H4; auto. 
Qed. 

Theorem readInd : forall H H' t0 N TID s2 M M' x E d ds ds'' T T' s,
                    heap_lookup x H = Some(sfull nil ds nil t0 N) ->
                    heap_lookup x H' = Some(sfull nil ds'' nil t0 N) ->
                    spec_multistep H
                                   (tUnion T (tSingleton (TID,nil,s2,M))) H'
                                   (tUnion T' (tSingleton(TID,s++[rAct x M' E d], s2, M))) ->
                    exists ds', spec_multistep H
                                   (tUnion T (tSingleton(TID,nil,rAct x M' E d::s2,M)))
                                   (replace x (sfull nil ds' nil t0 N) H')
                                   (tUnion T' (tSingleton(TID,s,rAct x M' E d::s2,M))) /\ Included tid ds' ds.
Proof.
  intros. genDeps{ds; ds''}. dependent induction H2; intros. 
  {apply UnionEqTID in x. invertHyp. invertListNeq. }
  {copy H0. apply specStepSingleton in H0. invertHyp. copy x. unfoldSetEq x. 
   assert(tIn (tUnion T0 (tSingleton x1)) x1). apply Union_intror. constructor. 
   apply H5 in H7. inversion H7; subst. 
   {eapply specStepCommitFullIVar in H4; eauto. invertHyp. eapply IHspec_multistep in H9; eauto.
    



generalize dependent ds. dependent induction H1. 
  {erewrite unspecSingleton in x. Focus 2. eapply unspecRead; auto. apply UnionEqTID in x. 
   invertHyp. invertListNeq. }
  {intros. destruct s. 
   {simpl in *. erewrite unspecSingleton; eauto. erewrite unspecSingleton in x. 
    Focus 2. eapply unspecRead; auto. unfoldSetEq x. copy H0. apply specStepSingleton in H0.
    invertHyp. assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
    apply H3 in H0. inversion H0; subst. 
    {copy H6. apply pullOut in H6. rewrite H6. eapply specStepCommitFullIVar in H5; eauto. invertHyp. 
     eapply IHspec_multistep with (s:=nil)in H8; eauto. unfoldTac. rewrite Union_associative. 



Theorem readInd : forall H t0 N TID s2 M M' x E d ds T T' s,
                    heap_lookup x H = Some(sfull nil ds nil t0 N) ->
                    spec_multistep (unspecHeap H)
                                   (tUnion T (unspecPoolAux(tSingleton (TID,s++[rAct x M' E d],s2,M)))) H
                                   (tUnion T' (tSingleton(TID,s++[rAct x M' E d], s2, M))) ->
                    spec_multistep (unspecHeap H) 
                                   (tUnion T (unspecPoolAux(tSingleton(TID,s,rAct x M' E d::s2,M))))
                                   (replace x (sfull nil (Subtract tid ds TID) nil t0 N) H)
                                   (tUnion T' (tSingleton(TID,s,rAct x M' E d::s2,M))).
Proof.
  intros. generalize dependent ds. dependent induction H2. 
  {erewrite unspecSingleton in x. Focus 2. eapply unspecRead; auto. apply UnionEqTID in x. 
   invertHyp. invertListNeq. }
  {intros. destruct s. 
   {simpl in *. erewrite unspecSingleton; eauto. erewrite unspecSingleton in x. 
    Focus 2. eapply unspecRead; auto. unfoldSetEq x. copy H. apply specStepSingleton in H.
    invertHyp. assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
    apply H3 in H. inversion H; subst. 
    {copy H6. apply pullOut in H6. rewrite H6. eapply specStepCommitFullIVar in H0; eauto. invertHyp. 
     eapply IHspec_multistep with (s:=nil)in H8; eauto. unfoldTac. rewrite Union_associative. 
     rewrite (Union_commutative thread (Singleton thread x)). rewrite <- Union_associative. 
     econstructor. eapply specStepChangeUnused. eauto. unfoldTac. rewrite Union_associative.  
     rewrite (Union_commutative thread _ t'). rewrite <- Union_associative. 
     erewrite unspecSingleton in H8; eauto. unfoldTac. replace ds with x1. eassumption. 
     admit. 


econstructor. eapply specStepChangeUnused. 
     eassumption. eauto. eauto. apply EqJMeq. eapply UnionSingletonEq in H0; auto. 
     rewrite H0. unfoldTac. repeat rewrite Union_associative. rewrite (Union_commutative thread t'). 
     auto. }
    {inv H7. inversion H3; subst; try solve[unfoldTac; invertHyp; inv H7]. 
     {unfoldTac; invertHyp. inv H10. copy d; copy d0. eapply uniqueCtxtDecomp in H; eauto. 
      inv H. inv H9. }
     {unfoldTac; invertHyp. inv H7. copy d; copy d0. eapply uniqueCtxtDecomp in H7; eauto. 
      inv H7. inv H11. eapply lookupDeterministic in H2; eauto. inv H2.
      
      
      
      eapply specMultiHeapDepRead; eauto. eapply specMultiPureThrowout. assert(d=d0). 
     apply proof_irrelevance. subst. apply UnionEqTID in H0. invertHyp. eauto. }
    {unfoldTac; invertHyp. copy d; copy d0. inv H7.  eapply uniqueCtxtDecomp in H9; eauto. 
     inv H9. inv H11. }
    {unfoldTac; invertHyp. copy d; copy d0. inv H7.  eapply uniqueCtxtDecomp in H8; eauto. 
     inv H8. inv H11. }
    {unfoldTac; invertHyp. copy d; copy d0. inv H10. eapply uniqueCtxtDecomp in H; eauto. 
     inv H. inv H9. }
   }
  }
Qed. 