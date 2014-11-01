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

Definition getStamp (t:thread) :=
  match t with
      (s, _, _) => s
  end. 

Theorem threadStampMonotonic : forall C H S' e C' H' L' e' e0, 
                                 f_multistep C H (Single(None, nil, e)) 
                                             C' H' (Single(Some(S', e0), L', e')) ->
                                 S' >= C.
Proof.  
  intros. dependent induction H0. inv H0; eauto. 
  {eapply IHf_multistep. eapply numThreadsMonotonic in H1. 
   simpl in H1. omega. auto. }
  {exfalso. apply H12. auto. }
  {assert(S' >= 1+C). eapply IHf_multistep; eauto. omega. }
  {


Admitted. 

Theorem threadStampMonotonic' : forall C H S' e C' H' e0' L' e' e0 S L, 
                                 f_multistep C H (Single(Some(S, e0), L, e)) 
                                             C' H' (Single(Some(S', e0'), L', e')) ->
                                 S' >= S.
Proof. 
Admitted. 

Theorem startTXStampGT : forall H H' C S e0 L  e' C' e,
                           f_multistep C H (Single(None, nil, e)) 
                                       C' H' (Single(Some(S,e0), L, e')) ->
                           C > S -> stampMonotonic C H -> False. 
Proof.
  intros. dependent induction H0. copy H0. inv H0; eauto.
  {apply numThreadsMonotonic in H1. simpl in H1. omega. } 
  {eapply threadStampMonotonic in H1. omega. }
  {eapply threadStampMonotonic' in H1. omega. }
Qed. 

Theorem f_multiDiffStamp : forall C C' S' S e0 e e' L' L H, 
                  f_multistep C H (Single(Some(S, e0), L, e)) 
                              C H (Single(Some(S, e0), L', e')) -> C' >= C -> C > S ->
                  (exists H', validate S L H S' H'  L commit) -> stampMonotonic C H ->
                  f_multistep (plus 1 C') H (Single(Some(C', e0), L, e)) 
                              (plus 1 C') H (Single(Some(C', e0), L', e')). 
Proof. 
  intros. generalize dependent C'. dependent induction H0; intros. 
  {constructor. }
  {inv H0. 
   {econstructor. eapply f_readStep; eauto. omega. eapply IHf_multistep; eauto. invertHyp. 
    econstructor. eapply validateCommitRead; eauto. }
   {econstructor. eapply f_readInDomainStep; eauto. omega. eapply IHf_multistep; eauto. }
   {invertHyp. eapply validateDeterministic in H16; eauto. invertHyp. solveByInv. }
   {econstructor. eapply f_writeStep; eauto. intros c. inv c.
    eapply IHf_multistep; eauto. invertHyp. econstructor. eapply validateWrite. eauto. }
   {apply startTXStampGT in H1. solveByInv. omega. eapply validateMonotonic; eauto. }
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
   {copy H0. eapply validateDeterministic in H0. Focus 2. eapply H9. invertHyp. 
    inv H5. econstructor. eapply f_abortStep; eauto. eapply f_multiDiffStamp; eauto. 
    econstructor. constructor. }
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

Theorem partialImpliesFullTopLevel : forall C T C' H' T', 
                                       initPool T ->
                                       p_multistep C nil T C' H' T' -> Finished T' ->
                                       f_multistep C nil T C' H' T'. 
Proof.
  intros. eapply partialImpliesFullMulti in H0; auto. unfold initPool in H.
  destruct T. destruct t. destruct p. destruct o. solveByInv. destruct l. 
  constructor. constructor. intros. inv H2. constructor. solveByInv. solveByInv. 
Qed. 

















