Require Export semantics.   

Theorem validateHeapExtensionC : forall S L H S' H' new C, 
                  Forall (fun x : location * term * stamp => getStamp x = C) new ->
                  S < C ->
                  validate S L H S' H' L commit ->
                  (exists Hnew, validate S L (new++H) S' (Hnew++new++H) L commit) \/
                  (exists Lnew e, validate S L (new++H) S' (new++H) Lnew (abort e) /\
                             postfix Lnew L).
Proof.
  intros. remember commit. induction H2; try solve[inv Heqv]; clear Heqv. 
  {left. exists nil. constructor. }
  {copy H1. apply IHvalidate in H1; auto. inv H1.
   {invertHyp. eapply LookupExtensionGE in H2. Focus 2. eauto. inv H2. 
    {left. exists x. eapply validateCommitRead; eauto. }
    {invertHyp. right. exists L0. exists (fill E (get (loc l))). split.
     eapply validateAbortRead; eauto. omega. unfold postfix. exists [readItem l E]. auto. }
   }
   {invertHyp. right. exists x. exists x0. split. eapply validateAbortPropogate. eauto. 
    unfold postfix in *. invertHyp. exists (readItem l E :: x1). auto. }
  }
  {copy H1. apply IHvalidate in H1; auto. inv H1. 
   {invertHyp. left. exists ((l, v, S')::x). simpl. eapply validateWrite. auto. }
   {invertHyp. right. exists x. exists x0. split. eapply validateAbortPropogate. auto. 
    unfold postfix in *. invertHyp. exists (writeItem l v::x1). auto. }
  }
Qed. 

Theorem validateHeapExtensionA : forall S L H S' new L' C e, 
                  Forall (fun x : location * term * stamp => getStamp x = C) new ->
                  S < C ->
                  validate S L H S' H L' (abort e) ->
                  validate S L (new++H) S' (new++H) L' (abort e) \/
                  (exists Lnew e', validate S L (new++H) S' (new++H) Lnew (abort e') /\
                             postfix Lnew L').
Proof.
  intros. remember (abort e). induction H2; try solve[inv Heqv]. 
  {apply IHvalidate in H1; auto. inv H1. 
   {left. eapply validateAbortPropogate. auto. }
   {invertHyp. right. exists x0. exists x1. split; auto. eapply validateAbortPropogate. auto. }
  }
  {eapply validateHeapExtensionC in H3. inv H3. 
   {invertHyp. left. eapply LookupExtensionGE in H4. Focus 2. eauto. inv H4. 
    {eapply validateAbortRead; eauto. }
    {invertHyp. eapply validateAbortRead; eauto. omega. }
   }
   {invertHyp. right. exists x. exists x0. split. eapply validateAbortPropogate; auto. auto. }
   eauto. auto. 
  }
Qed. 

Theorem trans_multistepLogMonotonic : forall H act L L' e e' S,
                                        trans_multistep H (S, L,e) (S,L',e') ->
                                        In act L -> In act L'. 
Proof.
  intros. dependent induction H0; auto. inv H0. 
  {eapply IHtrans_multistep; auto. simpl. right. auto. }
  {eapply IHtrans_multistep; auto. }
  {eapply IHtrans_multistep; auto. simpl. right. auto. }
  {eapply IHtrans_multistep; auto. }
  {eapply IHtrans_multistep; auto. }
Qed. 
Theorem lookupSame : forall H' H l S S' C v v', 
              Forall (fun x0 : location * term * stamp => getStamp x0 = C) H' ->
              lookup H l = Some(v, S) -> S' < C -> S < C ->
              lookup (H'++H) l = Some(v',S') -> v' = v /\ S' = S. 
Proof.
  induction H'; intros. 
  {simpl in H4. eapply lookupDeterministic in H1; eauto. }
  {simpl in *. destruct a. destruct p. destruct (eq_nat_dec l l0). 
   {inv H4. inv H0. simpl in *. omega. }
   {inv H0. simpl in H8. eauto. }
  }
Qed. 

Theorem lookupValid : forall L H H' H'' l v S E S' S'0 C,
              lookup H l = Some(v, S'0) ->
              validate S L (H'++H) S' H'' L commit -> S < C -> S'0 < C ->
              Forall (fun x0 : location * term * stamp => getStamp x0 = C) H' ->
              In (readItem l E) L ->
              lookup (H'++H) l = Some(v,S'0).
Proof.
  induction L; intros. 
  {inv H5. }
  {inv H5. 
   {inv H1. eapply lookupSame in H0. Focus 2. eauto. Focus 3. auto. Focus 3. 
    eauto. invertHyp. auto. omega. }
   {inv H1; eapply IHL; eauto. }
  }
Qed. 

Theorem trans_multiHeapExt : forall H H' S e0 e L S' L' e' C, 
                 trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                 (exists x, validate S L' (H'++H) S' x L' commit) ->
                 Forall (fun x0 : location * term * stamp => getStamp x0 = C) H' ->
                 S < C ->
                 trans_multistep (H'++H) (Some(S,e0),L,e) (Some(S,e0),L',e').
Proof.
  intros. dependent induction H0.  
  {constructor. }
  {inv H0. 
   {copy H1. eapply trans_multistepLogMonotonic in H0. Focus 2. simpl. left. auto.
    invertHyp. eapply lookupValid in H12; eauto. econstructor.
    eapply t_readStep; eauto. eauto. omega. }
   {econstructor. eapply t_readInDomainStep; eauto. eauto. }
   {econstructor. eapply t_writeStep; eauto. eapply IHtrans_multistep; eauto. }
   {econstructor. eapply t_atomicIdemStep; eauto. eauto. }
   {econstructor. eapply t_betaStep; eauto. eauto. }
  }
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

Theorem thread_wf_Extension : forall H H' t C, 
                 threadWF H t -> optLT (getThreadStamp t) C ->
                 Forall (fun x0 : location * term * stamp => getStamp x0 = C) H' ->
                 threadWF (H'++H) t. 
Proof. 
  intros. inv H0.  
  {constructor. } 
  {simpl in H1. eapply validateHeapExtensionC in H3; eauto. inv H3. 
   {invertHyp. econstructor. eauto. eapply trans_multiHeapExt; eauto. }
   {invertHyp. copy H3. eapply validateValidate in H0. 
    copy H3. apply abortLogPostfix in H6. invertHyp. 
    assert(trans_multistep H (Some (S, e0), [], e0) (Some (S, e0), x, x0)).
    admit. eapply threadWFInvalid. eauto. eapply trans_multiHeapExt; eauto. }
  }
  {simpl in H1. copy H3. eapply validateHeapExtensionA in H3; eauto. inv H3. 
   {eapply threadWFInvalid. eauto. copy H5. eapply validateValidate in H3. invertHyp. 
    eapply trans_multiHeapExt; eauto. }
   {invertHyp. eapply threadWFInvalid. eauto. copy H0. apply abortLogPostfix in H5. 
    invertHyp. copy H0. apply validateValidate in H5. invertHyp.
    admit. }
  }
Qed. 

Theorem trans_stepWF : forall H t t', 
                  threadWF H t -> trans_step H t t' -> threadWF H t'.
Proof.
  intros. inv H1. 
  {inv H0. 
   {econstructor. eapply validateCommitRead; eauto.  eapply trans_multistep_trans. 
    eassumption. econstructor. eapply t_readStep; eauto. constructor. }
   {eapply threadWFInvalid. eapply validateAbortPropogate; eauto. auto. }
  }
  {inv H0. econstructor; eauto. eapply trans_multistep_trans. eassumption. 
   econstructor. eapply t_readInDomainStep; eauto. constructor. 
   eapply threadWFInvalid. eauto.  eapply trans_multistep_trans. eassumption. 
   econstructor. }
  {inv H0. exfalso. apply H3. auto. 
   {econstructor. econstructor. eauto. eapply trans_multistep_trans. eauto. 
    econstructor. eapply t_writeStep; eauto. constructor. }
   {eapply threadWFInvalid. eapply validateAbortPropogate. eauto. auto. }
  }
  {inv H0. exfalso. apply H3. auto. 
   {econstructor. eauto. eapply trans_multistep_trans. eauto. econstructor. 
    eapply t_atomicIdemStep; eauto. constructor. }
   {eapply threadWFInvalid; eauto. }
  }
  {inv H0. exfalso. apply H3. auto. 
   {econstructor. eauto. eapply trans_multistep_trans. eauto. econstructor. 
    eapply t_betaStep; eauto. constructor. }
   {eapply threadWFInvalid; eauto. }
  }
Qed. 

Theorem trans_stepStampSame : forall H t t', trans_step H t t' -> 
                                      getThreadStamp t = getThreadStamp t'. 
Proof.
  intros. inv H0; auto. Qed. 

Theorem f_stepWF : forall C H T C' H' T', 
                   poolWF C H T ->
                   f_step C H T C' H' T' -> 
                   poolWF C' H' T'. 
Proof.
  intros. induction H1.
  {inv H0. InTac. invertHyp. constructor. auto. intros. inv H5. 
   split. Focus 2. eapply trans_stepWF; eauto.
   erewrite <- trans_stepStampSame; eauto. }
  {copy H0. apply wfPar_l in H0. apply IHf_step in H0. 
   apply wfPar_r in H2. apply wfParConj. assumption. constructor. inv H0.
   assumption. intros. inv H2. apply H6 in H3. copy H1. 
   eapply stampHeapMonotonic in H1. invertHyp. split. Focus 2. 
   eapply thread_wf_Extension; eauto. destruct (getThreadStamp t); auto. 
   simpl in *. omega. }
  {copy H0. apply wfPar_r in H0. apply IHf_step in H0. 
   apply wfPar_l in H2. apply wfParConj; auto. constructor. inv H0.
   assumption. intros. inv H2. apply H6 in H3. copy H1. 
   eapply stampHeapMonotonic in H1. invertHyp. split. Focus 2.
   eapply thread_wf_Extension; eauto. destruct (getThreadStamp t); auto. simpl in *. 
   omega. }
  {constructor. inv H0. auto. intros. inv H2. inv H6. split; simpl; auto.
   constructor. inv H6. split; simpl; auto. constructor. }
  {constructor. inv H0. eapply monotonicWeakening. Focus 2. eauto. omega. 
   intros. inv H0. inv H2. copy H1. eapply abortLogPostfix in H1.
   econstructor. simpl. auto. econstructor. constructor. constructor. }
  {constructor. inv H0. constructor. omega. auto. intros. inv H0. inv H3. split. 
   simpl. auto. constructor. }
  {inv H0. constructor. eapply validateMonotonic; eauto. intros. inv H0. 
   split. simpl. auto. constructor. }
  {econstructor. inv H0. eapply monotonicWeakening;[idtac|eauto]. omega. intros. 
   inv H2. split. simpl. auto. econstructor. constructor. econstructor. }
  {constructor. inv H0. auto. intros. inv H2. split. simpl. auto. constructor. }
  Grab Existential Variables. constructor. constructor. 
Qed. 

Theorem f_multistepWF : forall C H T C' H' T', 
                   poolWF C H T ->
                   f_multistep C H T C' H' T' -> 
                   poolWF C' H' T'. 
Proof.
  intros. induction H1. auto. eapply f_stepWF in H1; auto. 
Qed. 
























