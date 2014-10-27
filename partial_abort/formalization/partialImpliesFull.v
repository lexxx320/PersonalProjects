Require Export semantics. 
Require Export hetList. 
Require Export Coq.Program.Equality. 

Theorem f_multi_L : forall C H T1 T2 T1' C' H', 
                      f_multistep C H T1 C' H' T1' ->
                      f_multistep C H (Par T1 T2) C' H' (Par T1' T2). 
Proof.
  intros. induction H0.
  {constructor. }
  {econstructor. eapply f_parLStep. eassumption. eassumption. }
Qed. 

Theorem f_multi_R : forall C H T1 T2 T2' C' H', 
                      f_multistep C H T2 C' H' T2' ->
                      f_multistep C H (Par T1 T2) C' H' (Par T1 T2'). 
Proof.
  intros. induction H0.
  {constructor. }
  {econstructor. eapply f_parRStep. eassumption. eassumption. }
Qed. 

Ltac solveByInv :=
  match goal with
      |H:_ |- _ => solve[inv H]
  end. 

Theorem validateDeterministic : forall S L H S' S'' H' H'' L' L'' res res', 
                                  validate S L H S' H' L' res ->
                                  validate S L H S'' H'' L'' res' ->
                                  L' = L'' /\ res = res'. 
Proof.
  intros. genDeps {{ S''; H''; L''; res' }}. induction H0; intros. 
  {inv H1. auto. }
  {inv H3; auto. apply IHvalidate in H13. invertHyp. inv H3. 
   eapply lookupDeterministic in H15; eauto. invertHyp. omega. }
  {inv H1. 
   {apply IHvalidate in H13. invertHyp. inv H2. }
   {apply IHvalidate in H11; eauto. }
   {apply IHvalidate in H5; eauto. invertHyp. solveByInv. }
   {apply IHvalidate in H11; eauto. invertHyp. solveByInv. }
  }
  {inv H3. 
   {eapply lookupDeterministic in H1; eauto. invertHyp. omega. }
   {apply IHvalidate in H13; eauto. invertHyp. solveByInv. }
   {eapply lookupDeterministic in H1; eauto. }
  }
  {inv H1. eapply IHvalidate in H11; eauto. invertHyp. solveByInv. 
   eapply IHvalidate in H12; eauto. }
Qed. 


Theorem validateValidate : forall S L H S' H' L' e, 
                             validate S L H S' H' L' (abort e) ->
                             exists H'', validate S L' H S' H'' L' (commit). 
Proof.
  intros. remember (abort e). induction H0; try solve[inv Heqv]. 
  {inv Heqv. assert(abort e = abort e) by auto. apply IHvalidate in H1. invertHyp. 
   exists x0. auto. }
  {exists H'. assumption. }
Qed. 

Fixpoint numThreads T :=
  match T with
      |Single _ => 1
      |Par T1 T2 => plus (numThreads T1) (numThreads T2)
  end. 

Theorem numThreadsMonotonic_step : forall C H T C' H' T', 
                                 f_step C H T C' H' T' ->
                                 numThreads T <= numThreads T'. 
Proof.
  intros. induction H0; try solve[simpl; omega]. 
Qed. 

Theorem numThreadsMonotonic : forall C H T C' H' T', 
                                 f_multistep C H T C' H' T' ->
                                 numThreads T <= numThreads T'. 
Proof.
  intros. induction H0. 
  {omega. }
  {apply numThreadsMonotonic_step in H0. omega. }
Qed. 

Definition stampLE (S1 S2: option (stamp * term)) :=
  match S1, S2 with
      |Some(S1', _), Some(S2', _) => S1' <= S2'
      |None, Some _ => True
      |None, None => True
      |Some _, None => False
  end. 

Theorem asdf : forall C H H' e e' e0 S L C', 
                 f_multistep C H (Single(None, nil, e)) C' H' (Single(Some(S,e0), L, e')) ->
                 S >= C. 
Proof.
  intros. dependent induction H0. 

Theorem threadStampMonotonic : forall C H S S' e C' H' L L' e' e0, 
                                 f_threadWF C H (S, L, e) ->
                                 f_step C H (Single(S, L, e)) 
                                             C' H' (Single(Some(S', e0), L', e')) ->
                                 stampLE S (Some(S', e0)).
Proof.
  intros. inv H1; simpl; eauto. 
  {inv H0; omega. }
Qed. 

Theorem numThreadsGT1 : forall T, numThreads T >= 1. 
Proof.
  induction T; auto. simpl. omega. 
Qed. 

Theorem threadStampMonotonic' : forall C H S S' e C' H' L L' e' e0, 
                                 f_threadWF C H (S, L, e) ->
                                 f_multistep C H (Single(S, L, e)) 
                                             C' H' (Single(Some(S', e0), L', e')) ->
                                 stampLE S (Some(S', e0)).
Proof.
  intros. dependent induction H1. 
  {destruct S'; simpl; auto. }
  {destruct T'. 
   {destruct t. destruct p. destruct o. 
    {destruct p. copy H2. eapply threadStampMonotonic in H2; auto. 
     assert(stampLE (Some(n, t0)) (Some(S', e0))). eapply IHf_multistep; eauto.
     eapply f_stepWF in H3; eauto. Focus 2. constructor. intros. inv H4. 
     auto. inv H3. eapply H5. constructor. destruct S. simpl in *. destruct p. omega. 
     simpl. auto. }
    {



admit. }
   {eapply numThreadsMonotonic in H1. simpl in *. assert(numThreads T'1 >= 1). 
    apply numThreadsGT1. assert(numThreads T'2 >= 1). apply numThreadsGT1. omega. }
  }
Qed. 

 
Theorem threadStampMonotonic' : forall C H S S' e C' H' L L' e' e0, 
                                 f_threadWF C H (S, L, e) ->
                                 f_multistep C H (Single(S, L, e)) 
                                             C' H' (Single(Some(S', e0), L', e')) ->
                                 stampLE S (Some(S', e0)).
Proof.
  intros. dependent induction H1. 
  {destruct S'; simpl; auto. }
  {destruct T'. 
   {destruct t. destruct p. destruct o. 
    {destruct p. copy H2. eapply threadStampMonotonic in H2; auto. 
     assert(stampLE (Some(n, t0)) (Some(S', e0))). eapply IHf_multistep; eauto.
     eapply f_stepWF in H3; eauto. Focus 2. constructor. intros. inv H4. 
     auto. inv H3. eapply H5. constructor. destruct S. simpl in *. destruct p. omega. 
     simpl. auto. }
    {



admit. }
   {eapply numThreadsMonotonic in H1. simpl in *. assert(numThreads T'1 >= 1). 
    apply numThreadsGT1. assert(numThreads T'2 >= 1). apply numThreadsGT1. omega. }
  }
Qed. 






copy H2. inv H2; eauto.   
   {destruct S'; simpl; auto. }
   {eapply f_stepWF in H3. Focus 2. constructor. intros. inv H. auto. 
    eapply IHf_multistep. inv H3. eapply H2. constructor. auto. auto. }
   {eapply f_stepWF in H3. Focus 2. constructor. intros. inv H. auto. 
    eapply IHf_multistep. inv H3. eapply H2; eauto. constructor. auto. auto. }
   {eapply f_stepWF in H3. Focus 2. constructor. intros. inv H. auto. 
    assert(stampLE(Some(C, e2)) (Some(S', e0))). eapply IHf_multistep. inv H3. eapply H2. 
    constructor. auto. auto. simpl in *. inv H0. omega. omega. }
   {eapply f_stepWF in H3. Focus 2. constructor. intros. inv H. auto. 
    eapply IHf_multistep. inv H3. eapply H2; eauto. constructor. auto. auto. }
   {destruct S'; simpl; auto. }
   {simpl. eapply asdf in H1. inv H0; omega. 
 


admit. }
   {simpl. destruct S'; auto. }
   {eapply f_stepWF in H3. Focus 2. constructor. intros. inv H. auto. 
    eapply IHf_multistep. inv H3. eapply H2; eauto. constructor. auto. auto. }
   {eapply f_stepWF in H3. Focus 2. constructor. intros. inv H. auto. 
    eapply IHf_multistep. inv H3. eapply H2; eauto. constructor. auto. auto. }
  }
Qed. 

Theorem startTXStampGT : forall H H' C S e0 L  e' C' e,
                           f_multistep C H (Single(None, nil, e)) 
                                       C' H' (Single(Some(S,e0), L, e')) ->
                           C > S -> False. 
Proof.
  intros. dependent induction H0. copy H0. inv H0; eauto.
  {apply numThreadsMonotonic in H1. simpl in H1. omega. }
  {eapply f_stepWF in H3; eauto. Focus 2. constructor. intros. inv H. constructor. 
   eapply threadStampMonotonic in H1. simpl in H1. omega. inv H3.  eapply H0. constructor. }
Qed. 
 
Theorem f_multiDiffStamp : forall C C' S' S e0 e e' L' L H, 
                  f_multistep C H (Single(Some(S, e0), L, e)) 
                              C H (Single(Some(S, e0), L', e')) -> C' >= C -> C > S ->
                  (exists H', validate S L H S' H'  L commit) ->
                  f_multistep (plus 1 C') H (Single(Some(C', e0), L, e)) 
                              (plus 1 C') H (Single(Some(C', e0), L', e')). 
Proof. 
  intros. generalize dependent C'. dependent induction H0; intros. 
  {constructor. }
  {inv H0. 
   {econstructor. eapply f_readStep; eauto. omega. eapply IHf_multistep; eauto. invertHyp. 
    econstructor. eapply validateCommitRead; eauto. }
   {econstructor. eapply f_readInDomainStep; eauto. omega. eapply IHf_multistep; eauto. }
   {invertHyp. eapply validateDeterministic in H15; eauto. invertHyp. solveByInv. }
   {econstructor. eapply f_writeStep; eauto. intros c. inv c.
    eapply IHf_multistep; eauto. invertHyp. econstructor. eapply validateWrite. eauto. }
   {apply startTXStampGT in H1. solveByInv. omega. }
   {econstructor. eapply f_atomicIdemStep; eauto. intros c. inv c. eauto. }
   {econstructor. eapply f_betaStep; eauto. eauto. }
  }
Qed. 

Theorem partialImpliesFull : forall C H T C' H' T', 
                               p_step C H T C' H' T' -> f_poolWF C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0. 
  {apply f_wfPar_l in H1. apply IHp_step in H1. 
   eapply f_multi_L. eassumption. }
  {eapply f_wfPar_r in H1. apply IHp_step in H1. 
   eapply f_multi_R. eassumption. }
  {econstructor. eapply f_forkStep; eauto. constructor. }
  {econstructor. eapply f_readStep; eauto. constructor. }
  {econstructor. eapply f_readInDomainStep; eauto. constructor. }
  {inv H1. InTac. inv INHYP.
   {eapply validateDeterministic in H0; eauto. invertHyp. solveByInv. }
   {copy H0. eapply validateDeterministic in H0; eauto. invertHyp. inv H4. 
    econstructor. eapply f_abortStep; eauto. copy H8. eapply validateValidate in H0. 
    invertHyp. eapply validateDeterministic in H8; eauto. invertHyp. inv H5. 
    eapply f_multiDiffStamp; eauto. repeat econstructor. }
  }
  {econstructor. eapply f_writeStep; eauto. constructor. }
  {econstructor. eapply f_allocStep; eauto. constructor. }
  {econstructor. eapply f_commitStep; eauto. constructor. }
  {econstructor. eapply f_atomicStep; eauto. constructor. }
  {econstructor. eapply f_atomicIdemStep; eauto. constructor. }
  {econstructor. eapply f_betaStep; eauto. constructor. }
  Grab Existential Variables. constructor. 
Qed. 
 
Theorem partialImpliesFullMulti : forall C H T C' H' T', 
                                    p_multistep C H T C' H' T' -> f_poolWF C H T ->
                                    f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0. constructor. eapply partialImpliesFull in H0; eauto. 
  copy H0. eapply f_multistepWF in H3; eauto. apply IHp_multistep in H3. 
  eapply f_multi_trans; eauto. 
Qed. 


Definition initPool P :=
  match P with
      |Single(None, nil, e) => True
      |_ => False
  end. 

Fixpoint Finished P :=
  match P with
      |Single(None, nil, v) => value v
      |Single _ => False
      |Par T1 T2 => Finished T1 /\ Finished T2
  end. 

Theorem partialImpliesFullTopLevel : forall C H T C' H' T', 
                                       initPool T ->
                                       p_multistep C H T C' H' T' -> Finished T' ->
                                       f_multistep C H T C' H' T'. 
Proof.
  intros. eapply partialImpliesFullMulti in H1; auto. unfold initPool in H0.
  destruct T. destruct t. destruct p. destruct o. inv H0. destruct l. 
  constructor. intros. inv H3. constructor. solveByInv. solveByInv. 
Qed. 

















