Require Import NonSpec.   
Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import SfLib.  
Require Import unspec. 
Require Import sets. 
Require Import SpecLib. 
Require Import classifiedStep. 
Require Import hetList. 
Require Import Coq.Program.Equality. 
Require Import Heap. 
Require Import Coq.Sets.Powerset_facts. 

(*
Theorem passThroughAct : forall a M M' T T' tid s1 s2 H H',
                           actionTerm a M' ->
                           splitMultistep H T (unspecPoolAux (tSingleton(tid,a::s1,s2,M)))
                                          (OK H' T' (tSingleton(tid,a::s1,s2,M))) ->
                           exists T'' H'', 
                             splitMultistep H T (unspecPoolAux (tSingleton(tid,a::s1,s2,M)))
                                            (OK H'' T'' (tSingleton(tid,s1,s2,M'))). 
Admitted.  
*)

Theorem spec_multi_trans : forall H H' H'' T T' T'',
                        spec_multistep H T H' T' ->
                        spec_multistep H' T' H'' T'' ->
                        spec_multistep H T H'' T''.  
Proof.
  intros. genDeps {H''; T''}. induction H0; intros.  
  {auto. }
  {apply IHspec_multistep in H1. econstructor. eauto. auto. }
Qed. 

Ltac eqIn H := unfoldTac; 
  match type of H with
      |forall x, Ensembles.In ?X (Union ?X ?T (Singleton ?X ?t)) x -> ?y =>
       assert(Ensembles.In X(Union X T (Singleton X t)) t) by (apply Union_intror; constructor)
  end.

Axiom uniqueTP : forall T1 T2 t, tIn (tUnion T1 T2) t -> tIn T1 t -> tIn T2 t -> False. 

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

Theorem eqUnspec : forall T, T = unspecPoolAux T -> commitPool T. 
Proof. 
  intros. unfold commitPool. intros. unfoldSetEq H. apply H1 in H0. inv H0. inv H3; inv H4; auto. 
Qed. 

Theorem passThroughAct : forall a M M' T s1 s2 H H' tid,
                           actionTerm a M' -> unspecHeap H H' ->
                           spec_multistep H' (tUnion (unspecPoolAux T) (unspecPoolAux (tSingleton(tid,a::s1,s2,M))))
                                          H (tUnion T (tSingleton(tid,a::s1,s2,M))) ->
                           exists T'' H'', 
                             spec_multistep H' (tUnion (unspecPoolAux T) (unspecPoolAux (tSingleton(tid,a::s1,s2,M))))
                                            H'' (tUnion T'' (tSingleton(tid,s1,s2,M'))) /\
                             spec_multistep H'' (tUnion T'' (tSingleton(tid,s1,s2,M')))
                                            H (tUnion T (tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H2.  
  {rewrite <- unspecUnionComm in x. symmetry in x. apply eqUnspec in x. unfold commitPool in x. 
   assert(tIn (tUnion T (tSingleton(tid,a::s1,s2,M))) (tid,a::s1,s2,M)). apply Union_intror. 
   constructor. apply x in H. inv H. }
  {copy H. apply specStepSingleton in H. invertHyp. unfoldSetEq x. eqIn H.
   apply H in H5. inversion H5; subst. 
   {admit. }
   {inv H6. inv H7. inv H10. inv H6. erewrite unspecSingleton; eauto. 
Admitted. 

Theorem rollbackWF : forall H H' T TR TR' tidR acts,
                       wellFormed H (tUnion T TR) ->
                       rollback tidR acts H TR H' TR' ->
                       wellFormed H' (tUnion T TR'). 
Proof.
  intros. induction H1. 
  {auto. }
  {subst. inversion H0; subst. inversion H3; subst. apply IHrollback. destruct s1'. 
   {econstructor; eauto. eapply unspecHeapAddReader; eauto. unfoldTac.
    repeat rewrite unspecUnionComm in H7. unfoldTac. repeat rewrite <- Union_associative in H7.
    rewrite <- unspecUnionComm in H7. eapply passThroughAct in H7. invertHyp. 
    repeat rewrite unspecUnionComm. unfoldTac. repeat rewrite <- Union_associative.
    rewrite unspecUnionComm in H. eapply spec_multi_trans. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton; eauto. erewrite unspecSingleton in H. Focus 2. 
    eapply unspecRead; eauto. Focus 2. constructor. Focus 2. auto. eapply spec_multi_trans. 
    eassumption. 
   












