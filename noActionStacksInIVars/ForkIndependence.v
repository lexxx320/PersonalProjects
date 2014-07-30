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

Theorem unspecUnlocked : forall tid s1 s2 M t', 
                   unspecThread (tid,unlocked s1,s2,M) t' ->
                   exists M',  t' = tSingleton (tid, unlocked nil, s2, M'). 
Proof.
  intros. inv H; eauto. 
Qed. 


Ltac eqIn H :=  unfoldTac; 
  match type of H with
    | forall x, In ?X (Union ?X ?T (Singleton ?X ?t)) x -> ?z => 
            assert(In X (Union X T (Singleton X t)) t) by (apply Union_intror; constructor)
  end. 
            

Theorem specStepDiffUnused : forall H T H' T' t t',
                               spec_step H T t H' T t' ->
                               spec_step H T' t H' T' t'. 
Proof.
  intros. inv H0; auto. 
  {eapply SGet; eauto. }{eapply SPut; eauto. }
Qed. 

Theorem decomposeNeq : forall M E E' e e', decompose M E e -> decompose M E' e' -> e <> e' ->
                                           False. 
Proof.
  intros. eapply uniqueCtxtDecomp in H; eauto. invertHyp. apply H1. auto.
Qed. 

Ltac invert := 
  match goal with
    |H:?x = ?x |- _ => clear H; invert
    |H:?x = ?y |- _ => inv H; subst; match goal with
                                       |H':?x = ?y |- _ => fail
                                       |_ => idtac
                                     end 
  end. 

Theorem forkInd' : forall M M' M'' E N N' h h' T T' s1 s1' s2 d tid,
      spec_multistep h (tUnion T (tCouple(tid,unlocked[fAct M' E N d], s2, M)
                                         (1::tid,locked nil, nil, N)))
                     h' (tUnion T' (tCouple(tid,unlocked(s1++[fAct M' E N d]), s2, M'')
                                           (1::tid,locked s1', nil, N'))) ->
      exists h'' T'',
      spec_multistep h (tUnion T (tCouple(tid,unlocked[fAct M' E N d], s2, M)
                                         (1::tid,locked nil, nil, N)))
                     h'' (tUnion T'' (unspecPoolAux(tCouple (tid,unlocked s1,s2,M'')
                                                            (1::tid,locked s1', nil, N')))) /\
      spec_multistep h'' (tUnion T''(unspecPoolAux(tCouple (tid,unlocked s1,s2,M'')
                                                            (1::tid,locked s1', nil, N'))))
                     h' (tUnion T' (tCouple(tid,unlocked(s1++[fAct M' E N d]), s2, M'')
                                           (1::tid,locked s1', nil, N'))). 
Admitted. 

Theorem forkInd : forall H H' T T' tid M M' M'' N s1 s1' s2 E d,
                    spec_multistep H (tUnion T (tSingleton(tid, unlocked [], s2, M'))) H'
                                   (tUnion T' (tCouple(tid, unlocked(s1 ++ [fAct M' E M'' d]), s2, M)
                                                      (1 :: tid, locked s1', nil, N))) ->
                    spec_multistep H (tUnion T (unspecPoolAux (tCouple (tid,unlocked s1,fAct M' E M'' d::s2, M)
                                                                       (1::tid,unlocked s1', nil, N))))
                                   H' (tUnion T' (tCouple(tid,unlocked s1,fAct M' E M'' d::s2, M)
                                                         (1::tid,unlocked s1', nil, N))).
Proof.
  intros. dependent induction H0. 
  {unfoldTac. rewrite couple_swap in x. rewrite coupleUnion in x. 
   rewrite <- Union_associative in x. apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {copy H. apply specStepSingleton in H1. invertHyp. copy x. unfoldSetEq x. eqIn H2. 
   apply H2 in H4. inversion H4; subst. 
   {copy H5. apply pullOut in H5. rewrite Union_commutative. rewrite H5. rewrite <- Union_associative. 
    econstructor. eapply specStepDiffUnused. eauto. unfoldTac. rewrite Union_associative.  
    rewrite (Union_commutative thread _ t'). rewrite Union_commutative.
    eapply IHspec_multistep; eauto. apply UnionSingletonEq in H1; auto. rewrite H1. 
    apply EqJMeq. unfoldTac. rewrite Union_associative. rewrite (Union_commutative thread t').
    rewrite Union_associative. rewrite (Union_commutative thread t'). auto. }
   {inv H5. apply UnionEqTID in H1. invertHyp. cleanup. inversion H; subst; try solve[
     unfoldTac; invertHyp; invert; 
     match goal with
       |H:decompose ?M ?E ?e,H':decompose ?M ?E' ?e' |- _ => 
        assert(CONTRA:e <> e') by introsInv
     end; eapply decomposeNeq in CONTRA; eauto; contradiction].                                                   
    {inv H5; unfoldTac; invertHyp; inv H1; 
     match goal with
       |H:decompose ?M ?E ?e,H':decompose ?M ?E' ?e' |- _ => 
        assert(CONTRA:e <> e') by introsInv
     end; eapply decomposeNeq in CONTRA; eauto; contradiction. }
    {unfoldTac; invertHyp. invert. simpl in *. copy d; copy d0. eapply uniqueCtxtDecomp in H1; eauto.  
     invertHyp. inv H7. assert(d=d0) by apply proof_irrelevance. subst. apply forkInd' in H0. 
     invertHyp. 



apply EqJMeq. fold tUnion. unfoldTac. 
    rewrite (Union_commutative thread t'). rewrite Union_associative. eapply UnionSingletonEq. 

    

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