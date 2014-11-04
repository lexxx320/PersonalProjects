Require Export p_stepWF. 
 
Inductive OK H : thread -> thread -> Prop :=
|noTXOk : forall e, OK H (None,nil,e) (None,nil,e)
|commitCommitOK : forall S L L' S' H' H'' e0 e e',
                    validate S L H S' (commit H') ->
                    validate S L' H S' (commit H'') ->
                    trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                    OK H (Some(S,e0),L,e) (Some(S,e0),L',e')
|commitAbortOK : forall S L L'  S' H' e0 e e' L'' e'',
                    validate S L H S' (commit H') -> 
                    validate S L' H S' (abort e'' L'') -> postfix L L' ->
                    OK H (Some(S,e0),L,e) (Some(S,e0),L',e')
|abortAbortOK : forall S L L' S' eAbort eAbort' LAbort LAbort' e0 e e',
                    validate S L H S' (abort eAbort LAbort) ->
                    validate S L' H S' (abort eAbort' LAbort') ->
                    OK H (Some(S,e0),L,e) (Some(S,e0),L',e')   
.

Inductive poolOK H : pool -> pool -> Prop :=
|SingleOK : forall t t', OK H t t' -> poolOK H (Single t) (Single t')
|ParOk : forall T1 T1' T2 T2', poolOK H T1 T1' -> poolOK H T2 T2' ->
                          poolOK H (Par T1 T2) (Par T1' T2'). 
Theorem transMultiLogPostfix : forall H S e0 L L' e e',
                              trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                              postfix L L'. 
Proof.
  intros. dependent induction H0.
  {unfold postfix. exists nil. auto. }
  {inv H0; eauto.  
   {assert(postfix (readItem l E::L) L'). eapply IHtrans_multistep; eauto. 
    unfold postfix in *. invertHyp. exists (x++[readItem l E]). 
    rewrite <- app_assoc. simpl. auto. }
   {assert(postfix (writeItem l v::L) L').  eapply IHtrans_multistep; eauto. 
    unfold postfix in *. invertHyp. exists (x++[writeItem l v]). 
    rewrite <- app_assoc. simpl. auto. }
  }
Qed. 

Theorem fillGet : forall E l, decompose (fill E (get(loc l))) E (get(loc l)). 
Proof.
  intros. induction E; intros; eauto; try solve[simpl;constructor; auto]. 
Qed. 

Theorem multistepAbortCommit : forall H H' L L' C C' eAbort LAbort e0 e e' S, 
                                 validate S L H C (abort eAbort LAbort) ->
                                 validate S L' H C' (commit H') -> 
                                 trans_multistep H (Some (S, e0), L, e)
                                                 (Some (S, e0), L', e') -> 
                                 False. 
Proof.
  intros. dependent induction H2. 
  {eapply validateSameAns; eauto. }
  {inv H3; eauto.  
   {eapply IHtrans_multistep. Focus 3. eauto. Focus 3. eauto.
    eapply validateAbortPropogate. auto. auto. }
   {eapply IHtrans_multistep. Focus 3. eauto. Focus 3. eauto.
    eapply validateAbortPropogate. auto. auto. }
  }
Qed. 

Theorem abortNewTermIsGet : forall S L H C e L',
                              validate S L H C (abort e L') ->
                              exists l E, decompose e E (get (loc l)).
Proof.
  intros. dependent induction H0. 
  {invertHyp. econstructor. eauto. }
  {exists l. exists E. apply fillGet. }
Qed. 

Theorem multistepPostfix : forall S e0 L L' H L'' C C' eAbort LAbort H' e e',
                             trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                             trans_multistep H (Some(S,e0),L,e) (Some(S,e0),LAbort, eAbort) ->
                             validate S L' H C (commit H') ->
                             validate S L'' H C' (abort eAbort LAbort) ->
                             postfix L' LAbort.
Proof.
  intros. dependent induction H0. 
  {eapply transMultiLogPostfix; eauto. }
  {inv H2. 
   {copy H4. eapply abortNewTermIsGet in H4. invertHyp.
    inv H0; decompSame; invertEq. 
    {


Theorem asdf : forall H,
                 trans_multistep H (Some (S, e0), L, e) (Some (S, e0), L', e') ->
                 validate S L' H C (commit H') ->
                 validate S L'' H C (abort eAbort LAbort



admit. }
   {eapply trans_stepDeterministic in H0; eauto. subst. 
    inv H5; eapply IHtrans_multistep; eauto. }
  }
Qed. 


Theorem trans_stepOK : forall H t t' pt, 
                         OK H t pt -> trans_step H t t' -> threadWF H t -> threadWF H pt ->
                         (exists pt', trans_step H pt pt' /\ OK H t' pt') \/
                         OK H t' pt. 
Proof.
  intros. inv H0. 
  {inv H1; exfalso; apply H8; auto. }
  {inv H6. 
   {left. econstructor. split. eauto. inv H1; eapply commitCommitOK; eauto; try solve[constructor]. 
    {eapply validateCommitRead; eauto. }
    {eapply validateCommitRead; eauto. }
    {eapply validateWrite; eauto. }
    {eapply validateWrite; eauto. }
   }
   {eapply trans_stepDeterministic in H1; eauto. subst. right.
    inv H0; eapply commitCommitOK; eauto.  
    {eapply validateCommitRead; eauto. }
    {eapply validateWrite; eauto. }
   }
  }
  {right. inv H1; eapply commitAbortOK; eauto. 
   {eapply validateCommitRead; eauto. }
   {inv H2. Focus 2. eapply validateSameAns in H4; eauto. contradiction. 
    inv H3. eapply validateSameAns in H5; eauto. contradiction.
    eapply abortSameAns in H5; eauto. invertHyp.
    assert(trans_multistep H (Some (S, e0), [], e0) (Some (S, e0), readItem l E::L, fill E v)). 
    eapply trans_multistep_trans. eapply H11. econstructor. eapply t_readStep; eauto.
    constructor. copy H2. eapply multistepPostfix in H2; eauto. Focus 2.
    eapply validateCommitRead; eauto. assert(postfix L'' L').
    apply abortLogPostfix in H1; eauto. unfold postfix in *. invertHyp. exists (x++x1). 
    rewrite app_assoc. auto. }
   {eapply validateWrite; eauto. }
   {inv H2. Focus 2. eapply validateSameAns in H4; eauto. contradiction. 
    inv H3. eapply validateSameAns in H5; eauto. contradiction.
    eapply abortSameAns in H5; eauto. invertHyp.
    assert(trans_multistep H (Some (S, e0), [], e0) (Some (S, e0), writeItem l v::L, fill E unit)). 
    eapply trans_multistep_trans. eapply H12. econstructor. eapply t_writeStep; eauto.
    constructor. copy H2. eapply multistepPostfix in H2; eauto. Focus 2.
    eapply validateWrite; eauto. assert(postfix L'' L').
    apply abortLogPostfix in H1; eauto. unfold postfix in *. invertHyp. exists (x++x1). 
    rewrite app_assoc. auto. }
  }
  {right. inv H1; eapply abortAbortOK; eauto. 
   {eapply validateAbortPropogate; eauto. }
   {eapply validateAbortPropogate; eauto. }
  }
Qed. 

Theorem p_multi_L : forall C H T1 T2 T1' C' H', 
                      p_multistep C H T1 C' H' T1' ->
                      p_multistep C H (Par T1 T2) C' H' (Par T1' T2). 
Proof.
  intros. induction H0.
  {constructor. }
  {econstructor. eapply p_parLStep. eassumption. eassumption. }
Qed. 

Theorem p_multi_R : forall C H T1 T2 T2' C' H', 
                      p_multistep C H T2 C' H' T2' ->
                      p_multistep C H (Par T1 T2) C' H' (Par T1 T2'). 
Proof.
  intros. induction H0.
  {constructor. }
  {econstructor. eapply p_parRStep. eassumption. eassumption. }
Qed. 

Theorem inconsistentTraces : forall H S e0 L e L' C C' e' H' L'' e'' eAbort v E LAbort,
                               trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                               trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L'',e'') ->
                               validate S L' H C (commit H') -> decompose e' E (inatomic v) ->
                               validate S L'' H C' (abort eAbort LAbort) -> False. 
Proof.
  intros. dependent induction H0. 
  {inv H1. 
   {eapply validateSameAns in H4; eauto. }
   {inv H0; decompSame; invertEq. }
  }
  {inv H0. 
   {eapply IHtrans_multistep; eauto. inv H2. 
    {eapply multistepAbortCommit in H1; eauto. contradiction.
     eapply validateAbortPropogate; eauto. }
    {inv H0; decompSame; invertEq. rewrite H13 in H17. inv H17. eauto. 
     rewrite H16 in H12. inv H12. }
   }
   {eapply IHtrans_multistep; eauto. inv H2. 
    {eapply multistepAbortCommit in H1; eauto. contradiction. }
    {inv H0; decompSame; invertEq. rewrite H12 in H14. inv H14.
     rewrite H12 in H14. inv H14. auto. } 
   }
   {eapply IHtrans_multistep; eauto. inv H2. 
    {eapply multistepAbortCommit in H1; eauto. contradiction.
     eapply validateAbortPropogate; eauto. }
    {inv H0; decompSame; invertEq. auto. }
   }
   {eapply IHtrans_multistep; eauto. inv H2. 
    {eapply multistepAbortCommit in H1; eauto. contradiction. }
    {inv H0; decompSame; invertEq. auto. }
   }
   {eapply IHtrans_multistep; eauto. inv H2. 
    {eapply multistepAbortCommit in H1; eauto. contradiction. }
    {inv H0; decompSame; invertEq. auto. }
   }
  }
Qed. 


Theorem poolOKExtension : forall H H' T T' C C',
                            poolWF C H T -> poolWF C H T' -> C' >= C ->
                            poolOK H T T' -> 
                            Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                            poolOK (H'++H) T T'. 
Proof. 
  intros. induction H3.  
  {inv H3. 
   {repeat constructor. }
   {inv H1. InTac. invertHyp. simpl in H1. eapply validateHeapExtensionC in H5; eauto. 
    inv H5. 
    {invertHyp. eapply validateHeapExtensionC in H6; eauto. inv H6. 
     {invertHyp. constructor. eapply commitCommitOK; eauto.
      eapply trans_multiHeapExt; eauto. }
     {invertHyp. 




admit. }
    }
    {eapply validateHeapExtensionC in H6; eauto. inv H6. 
     {invertHyp. (*abort/commit*)admit. }
     {constructor. invertHyp. eapply abortAbortOK; eauto. }
    }
   }
   {inv H1. InTac. invertHyp. simpl in H1. eapply validateHeapExtensionC in H5; eauto. inv H5. 
    {admit. }
    {invertHyp. eapply validateHeapExtensionA in H7; eauto. inv H7. 
     {constructor. eapply abortAbortOK; eauto. 


(*commit/abort*)

admit. }
   {inv H1. InTac. invertHyp. simpl in H1. eapply validateHeapExtensionA in H5; eauto. 
    eapply validateHeapExtensionA in H6; eauto. inv H5; inv H6; constructor.
    {eapply abortAbortOK; eauto. }
    {invertHyp. eapply abortAbortOK; eauto. }
    {invertHyp. eapply abortAbortOK; eauto. }
    {invertHyp. eapply abortAbortOK; eauto. }
   }
  }
  {constructor. eapply IHpoolOK1. apply wfPar_l in H0. auto. apply wfPar_l in H1.
   auto. eapply IHpoolOK2. apply wfPar_r in H0. auto. apply wfPar_r in H1. auto. }
Qed. 

Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
                               poolOK H T PT -> poolWF C H T -> poolWF C H PT ->
                               f_step C H T C' H' T' ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolOK H' T' PT'. 
Proof.
  intros. generalize dependent PT. induction H3; intros.  
  {inv H2. eapply trans_stepOK in H0; eauto. inv H0. 
   {invertHyp. exists (Single x). split. econstructor. eapply p_transStep. eauto. 
    constructor. constructor. auto. }
   {econstructor. split. constructor. constructor. auto. }
  }
  {inv H0. copy H1. eapply wfPar_l in H1. eapply IHf_step in H6; auto. invertHyp. 
   econstructor. split. eapply p_multi_L. eassumption. constructor. auto.
   copy H3. eapply stampHeapMonotonic in H3; auto. invertHyp. copy H2. inv H2. 
   eapply poolOKExtension; eauto. apply wfPar_r in H0. auto. apply wfPar_r in H3. 
   auto. apply wfPar_l in H2. auto. }
  {inv H0. eapply wfPar_r in H1. eapply IHf_step in H8; auto. invertHyp. 
   econstructor. split. eapply p_multi_R. eassumption. constructor. auto. admit. 
   auto. apply wfPar_r in H2. auto. }
  {inv H2. inv H5. econstructor. split. eapply p_multi_step.
   eapply p_forkStep; eauto. constructor. repeat constructor. }
  {inv H2. inv H5. 
   {eapply validateSameAns in H0; eauto. contradiction. }
   {eapply validateSameAns in H0; eauto. contradiction. }
   {eapply abortSameAns in H0; eauto. invertHyp. inv H3. InTac.
    invertHyp. simpl in H0. inv H3. eapply validateSameAns in H10; eauto. contradiction. 
    eapply abortSameAns in H10; eauto. invertHyp. econstructor. split. econstructor. 
    eapply p_abortStep; eauto. constructor. constructor. copy H7. 
    eapply validateValidate in H7. invertHyp. eapply commitCommitOK. 
    constructor. eauto. eapply validateNewerStamp. eauto. omega. 
    eapply trans_multiNewerStamp; eauto. }
  }
  {inv H3. inv H6. econstructor. split. econstructor. eapply p_allocStep; eauto. 
   constructor. constructor. constructor. }
  {inv H3. inv H6. 
   {inv H12. 
    {econstructor. split. econstructor. eapply p_commitStep; eauto. constructor.
     repeat constructor.  }
    {inv H3; decompSame; invertEq. }
   }
   {inv H1. InTac. invertHyp. inv H3. Focus 2. 
    eapply validateSameAns in H0; eauto. contradiction. eapply inconsistentTraces in H11; eauto. 
    contradiction. }
   {eapply validateSameAns in H0; eauto. contradiction. }
  }
  {inv H2. inv H5. econstructor. split. econstructor. apply p_atomicStep; eauto. 
   constructor. constructor. eapply commitCommitOK with (S' := C); constructor. }
  {inv H2. inv H5. econstructor. split. eapply p_multi_step.
   eapply p_betaStep; eauto. constructor. repeat constructor. }
Qed. 


