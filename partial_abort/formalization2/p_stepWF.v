Require Export f_stepWF.   

Theorem p_stampHeapMonotonic : forall C H T C' H' T',
                               p_step C H T C' H' T' -> 
                               C' >= C /\ (exists H'', H' = H'' ++ H /\ Forall (fun x => getStamp x = C) H''). 
Proof.
  intros. induction H0; try invertHyp; split; eauto; try solve[exists nil; auto]. 
  {exists [(l,v,C)]. simpl. split; auto.  }
  {copy H0. apply validateHeapMonotonic in H0. invertHyp. exists x. split; auto. 
   eapply validateStampGE in H2. auto. }
Qed. 

Theorem validateNewerStamp : forall S S' C  L H H', 
                            validate S L H S' (commit H') -> C > S ->
                            validate C L H S' (commit H').
Proof.
  intros. dependent induction H0. 
  {constructor. }
  {eapply validateCommitRead; eauto. omega. }
  {eapply validateWrite; eauto. }
Qed. 

Theorem trans_multiNewerStamp : forall S e0 e e' L L' H C,
                                  trans_multistep H (Some (S, e0), L, e)
                                                  (Some (S, e0), L', e') -> C > S ->
                                  trans_multistep H (Some (C, e0), L, e)
                                                  (Some (C, e0), L', e').
Proof.
  intros. dependent induction H0. 
  {constructor. }
  {inv H0. 
   {econstructor. eapply t_readStep; eauto.  eauto. }
   {econstructor. eapply t_readInDomainStep; eauto. eauto. }
   {econstructor. eapply t_writeStep; eauto. intros c. inv c.  eauto. }
   {econstructor. eapply t_atomicIdemStep; eauto. intros c. inv c.  eauto. }
   {econstructor. eapply t_betaStep ;eauto. intros c. inv c. eauto. }
  }
Qed. 


Theorem logWFApp : forall L L', logWF(L++L') -> logWF L'. 
Proof.
  induction L; intros; auto. inv H; eauto.
Qed. 

Theorem p_stepWF : forall C H T C' H' T', 
                   poolWF C H T ->
                   p_step C H T C' H' T' -> 
                   poolWF C' H' T'. 
Proof.
  intros. induction H1.
  {inv H0. InTac. invertHyp. constructor. auto. intros. inv H5. 
   split. Focus 2. eapply trans_stepWF; eauto.
   erewrite <- trans_stepStampSame; eauto. }
  {copy H0. apply wfPar_l in H0. apply IHp_step in H0. 
   apply wfPar_r in H2. apply wfParConj. assumption. constructor. inv H0.
   assumption. intros. inv H2. apply H6 in H3. copy H1. 
   eapply p_stampHeapMonotonic in H1. invertHyp. split. Focus 2. 
   eapply thread_wf_Extension; eauto. destruct (getThreadStamp t); auto. 
   simpl in *. omega. }
  {copy H0. apply wfPar_r in H0. apply IHp_step in H0. 
   apply wfPar_l in H2. apply wfParConj; auto. constructor. inv H0.
   assumption. intros. inv H2. apply H6 in H3. copy H1. 
   eapply p_stampHeapMonotonic in H1. invertHyp. split. Focus 2.
   eapply thread_wf_Extension; eauto. destruct (getThreadStamp t); auto. simpl in *. 
   omega. }
  {constructor. inv H0. auto. intros. inv H2. inv H6. split; simpl; auto.
   constructor. inv H6. split; simpl; auto. constructor. }
  {constructor. inv H0. eapply monotonicWeakening. Focus 2. eauto. omega. 
   intros. inv H0. inv H2. copy H1. eapply abortLogPostfix in H1. invertHyp. split.
   simpl. auto. InTac. invertHyp. simpl in H1. inv H2. 
   {eapply validateSameAns in H0; eauto. inv H0. }
   {eapply abortSameAns in H0; eauto. invertHyp. copy H8.  
    apply validateValidate in H8. invertHyp. copy H2. 
    eapply validateNewerStamp in H2; eauto. econstructor. eauto. 
    eapply logWFApp; eauto. eapply trans_multiNewerStamp; eauto. }
  }
  {constructor. inv H0. eapply monotonicWeakening. Focus 2. eauto. omega. 
   intros. inv H2. split; auto. simpl. omega. repeat econstructor. }
  {constructor. inv H0. constructor. omega. auto. intros. inv H0. inv H3. split. 
   simpl. auto. constructor. }
  {inv H0. constructor. eapply validateMonotonic; eauto. intros. inv H0. 
   split. simpl. auto. constructor. }
  {econstructor. inv H0. eapply monotonicWeakening;[idtac|eauto]. omega. intros. 
   inv H2. split. simpl. auto. econstructor. constructor. econstructor. constructor. }
  {constructor. inv H0. auto. intros. inv H2. split. simpl. auto. constructor. }
  Grab Existential Variables. constructor.  constructor.
Qed. 

Theorem p_multistepWF : forall C H T C' H' T', 
                   poolWF C H T ->
                   p_multistep C H T C' H' T' -> 
                   poolWF C' H' T'. 
Proof.
  intros. induction H1. auto. eapply p_stepWF in H1; auto. 
Qed. 
























