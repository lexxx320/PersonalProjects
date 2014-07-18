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

Definition alength l :=
  match l with
      |locked l' => length l'
      |unlocked l' => length l'
  end. 

Theorem monotonicActions : forall H tid H' T T' s1 s1' s2 s2' M M',
                             spec_multistep H T H' T' ->
                             tIn T (tid,s1,s2,M) -> tIn T' (tid,s1',s2',M') ->
                             alength s1 + length s2 <= alength s1' + length s2'. 
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
    {inv H3. eapply IHspec_multistep with(s4 := aCons (fAct M E M0 d)s1)(s3:=s2) in H2. 
     destruct s1; simpl in *; omega. apply Union_intror. apply Couple_l. }
    {inv H3. eapply IHspec_multistep with(s4:=aCons (rAct x M E d)s1)(s3:=s2) in H2. 
     destruct s1; simpl in *; omega. apply Union_intror. constructor. }
    {inv H3. eapply IHspec_multistep with(s4:=aCons (wAct x M E N d)s1)(s3:=s2) in H2. 
     destruct s1; simpl in *; omega. apply Union_intror. constructor. }
    {inv H3. eapply IHspec_multistep with(s4:=aCons(nAct M E d x)s1)(s3:=s2) in H2. 
     destruct s1; simpl in *; omega.  apply Union_intror. constructor. }
    {inv H3. eapply IHspec_multistep with(s4:=aCons(srAct M E M0 N d)s1)(s3:=s2) in H2.
     destruct s1; simpl in *; omega. apply Union_intror. constructor. }
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
     apply Union_intror. constructor. destruct s1; simpl in *; omega. }
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions in H0. Focus 2. 
     apply Union_intror; constructor. Focus 2. apply Union_intror. constructor. 
     simpl in H0. destruct s1; simpl in *; omega. }
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions in H0. Focus 2. 
     apply Union_intror; constructor. Focus 2. apply Union_intror. constructor. 
     simpl in *. destruct s1; simpl in *; omega. }
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions in H0. Focus 2. 
     apply Union_intror; constructor. Focus 2. apply Union_intror. constructor. 
     simpl in *. destruct s1; simpl in *; omega. }
    {unfoldTac; invertHyp; cleanup. eapply monotonicActions in H0. Focus 2. 
     apply Union_intror; constructor. Focus 2. apply Union_intror. constructor. 
     simpl in *. destruct s1; simpl in *; omega. }
   }
  }
Qed.  

Theorem eqUnspec : forall T, T = unspecPoolAux T -> commitPool T. 
Proof. 
  intros. unfold commitPool. intros. unfoldSetEq H. apply H1 in H0. inv H0. inv H3; inv H4; auto. 
Qed. 

Theorem forkInd : forall H H' TID s2 M N E d T T' s t,
                    spec_multistep H
                                   (tUnion T (tSingleton (TID,unlocked nil,s2,t))) H'
                                   (tUnion T' (tSingleton(TID,(unlocked(s++[fAct M E N d])), s2, M))) ->
                    spec_multistep H
                                   (tUnion T (tSingleton(TID,unlocked nil,fAct M E N d::s2,t))) H'
                                   (tUnion T' (tSingleton(TID,unlocked s,fAct M E N d::s2,M))).
Proof.
Admitted. 

Theorem unspecUnlocked : forall tid s1 s2 M t', 
                   unspecThread (tid,unlocked s1,s2,M) t' ->
                   exists M',  t' = tSingleton (tid, unlocked nil, s2, M'). 
Proof.
  intros. inv H; eauto. 
Qed. 

Theorem forkInd' : forall H H' T T' tid M M' M'' N s1 s1' s2 s2' E d,
                    spec_multistep H (tUnion T (tSingleton(tid, unlocked [], s2, M'))) H'
                                   (tUnion T' (tCouple(tid, unlocked(s1 ++ [fAct M' E M'' d]), s2, M)
                                                      (1 :: tid, locked s1', s2', N))) ->
                    spec_multistep H (tUnion T (unspecPoolAux (tCouple (tid,unlocked s1',fAct M' E M'' d::s2, M)
                                                                       (1::tid,unlocked s1', s2', N))))
                                   H' (tUnion T' (tCouple(tid,unlocked s1,fAct M' E M'' d::s2, M)
                                                         (1::tid,unlocked s1', s2', N))).
Proof.
  intros. 
Admitted. 
(*
Theorem forkInd'' : forall H N TID s2 M E d T T' s,
                    spec_multistep (unspecHeap H)
                                   (tUnion T (unspecPoolAux(tSingleton (TID,unlocked(s++[fAct M E N d]),s2,M)))) H
                                   (tUnion T' (tSingleton(TID,unlocked(s++[fAct M E N d]), s2, M))) ->
                    spec_multistep (unspecHeap H) 
                                   (tUnion T (unspecPoolAux(tSingleton(TID,unlocked s,fAct M E N d::s2,M))))
                                   H (tUnion T' (tSingleton(TID,unlocked s,fAct M E N d::s2,M))).
Proof.
  intros. erewrite unspecSingleton in H0. Focus 2. unspecThreadTac. auto.  
  assert(exists t', unspecThread(TID,unlocked s,fAct M E N d::s2, M) t'). apply unspecThreadTotal. 
  invertHyp. copy H2. apply unspecUnlocked in H2. invertHyp. erewrite unspecSingleton; eauto. 
  






asdlkfh*)