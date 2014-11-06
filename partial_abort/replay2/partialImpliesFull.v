Require Export stepPreservesRewind. 

Theorem replayCommit : forall S L H L' S' H' e0 e e', 
                         replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                         validate S L' H S' (commit H') -> 
                         exists H'', validate S L H S' (commit H'').
Proof.
  intros. dependent induction H0. 
  {eauto. }
  {inv H0; eauto. 
   {eapply IHreplay in H2;[idtac|eauto|eauto]. invertHyp. inv H0. eauto. }
   {eapply IHreplay in H2;[idtac|eauto|eauto]. invertHyp. inv H0. eauto. }
   {eapply IHreplay in H2;[idtac|eauto|eauto]. invertHyp. inv H0. eauto. }
  }
Qed. 

Theorem replayFMulti : forall H S C C' e0 L e L' e' H' S', 
                         replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                         validate S L' H S' (commit H') ->
                         f_multistep C' H (Single(Some(C,e0),L,e)) C' H 
                                     (Single(Some(C,e0),L',e')). 
Proof.
  intros. dependent induction H0. 
  {constructor. }
  {inv H0. 
   {econstructor. eapply f_transStep. eapply t_readStep; eauto. eauto. }
   {eapply replayCommit in H1; eauto. invertHyp. inv H0. lookupSame. omega. }
   {econstructor. eapply f_transStep. eapply t_readInDomainStep; eauto. eauto. }
   {econstructor. eapply f_transStep. eapply t_writeStep; eauto. intros c. 
    inv c. eauto. }
   {econstructor. eapply f_transStep. eapply t_atomicIdemStep; eauto. intros c. 
    inv c. eauto. }
   {econstructor. eapply f_transStep. eapply t_betaStep; eauto. intros c. 
    inv c. eauto. }
  }
Qed. 

Theorem partialImpliesFull : forall C H T C' H' T', 
                               p_step C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0.
  {econstructor. eapply f_transStep. eauto. constructor. }
  {inv H1. apply IHp_step in H4. apply f_multi_L. auto. }
  {inv H1. apply IHp_step in H5. apply f_multi_R. auto. }
  {inv H1. econstructor. eapply f_forkStep; eauto. constructor. }
  {copy H0. inv H1. eapply abortRewind in H2; eauto. copy H0. 
   apply validateValidate in H1. invertHyp. econstructor.
   eapply f_abortStep; eauto. rewrite rewindIFFReplay in H2.
   eapply replayFMulti; eauto. }
  {econstructor. eapply f_allocStep; eauto. constructor. }
  {econstructor. eapply f_commitStep; eauto. constructor. }
  {econstructor. eapply f_atomicStep; eauto. constructor. }
  {econstructor. eapply f_betaStep; eauto. constructor. }
Qed. 

Theorem partialImpliesFullMulti : forall C H T C' H' T', 
                               p_multistep C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0. 
  {constructor. }
  {copy H0. apply p_stepRewind in H0; auto. apply IHp_multistep in H0.
   eapply partialImpliesFull in H3; eauto. eapply f_multi_trans; eauto. }
Qed. 



