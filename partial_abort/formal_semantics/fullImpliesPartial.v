Require Export stepPreservesRewind. 
 
Inductive OK H : thread -> thread -> Prop :=
|noTXOK : forall e, OK H (None, nil, e) (None, nil, e)
|inTXOKValid : forall S e0 L L' S' e e' H', 
                 validate S L H S' (commit H') ->
                 replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                 OK H (Some(S,e0),L,e) (Some(S,e0),L',e')
|inTXInvalid : forall S L L' eA S' eA' e LA LA' e0 e', 
                 validate S L H S' (abort eA LA) -> 
                 validate S L' H S' (abort eA' LA') ->
                 OK H (Some(S,e0),L,e) (Some(S,e0),L',e'). 

Inductive poolOK H : pool -> pool -> Prop := 
|SingleOK : forall t t', OK H t t' -> poolOK H (Single t) (Single t')
|ParOK : forall T1 T2 T1' T2', 
           poolOK H T1 T1' -> poolOK H T2 T2' -> poolOK H (Par T1 T2) (Par T1' T2'). 

Theorem replayInvalid : forall H S e0 L e L' e' S' eA LA, 
                          replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                          validate S L H S' (abort eA LA) ->
                          exists eA' LA', validate S L' H S' (abort eA' LA').
Proof.
  intros. dependent induction H0; eauto. 
  {inv H0; eauto. 
   {assert(validate S (readItem l E v::L) H S' (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
   {assert(validate S (readItem l E v::L) H S' (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
   {assert(validate S (writeItem l v::L) H S' (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
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
 
Theorem validateSameAns : forall L S H S' S'' e L' H', 
                                  validate S L H S' (abort L' e) ->
                                  validate S L H S'' (commit H') ->
                                  False. 
Proof.
  induction L; intros. 
  {inv H0. }
  {inv H0; inv H1; eauto. eapply lookupDeterministic in H11; eauto. invertHyp. omega. }
Qed. 
                    
Theorem replayValidPortion : forall S L H S' e' L' e0 e, 
                               rewind H (Some(S,e0),nil,e0) (Some(S,e0),L,e) ->
                               validate S L H S' (abort e' L') ->
                               rewind H (Some(S,e0),nil,e0) (Some(S,e0),L',e').
Proof.
  intros. dependent induction H0. 
  {inv H1. }
  {inv H0; eauto. 
   {inv H2. 
    {eapply IHrewind; eauto. }
    {lookupSame. omega. }
   }
   {inv H2. 
    {eapply IHrewind; eauto. }
    {eapply decomposeEq in H10. subst. auto. }
   }
   {inv H2. eauto. }
  }
Qed. 

Theorem validateValidate : forall S L H S' L' e, 
                             validate S L H S' (abort e L') ->
                             exists H'', validate S L' H S' (commit H''). 
Proof.
  intros. dependent induction H0. 
  {invertHyp. exists x0. auto. }
  {exists H'. assumption. }
Qed. 

Theorem LookupExtensionGE : forall H' H l v S C,
                   lookup H l = Some(v, S) -> 
                   Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                   lookup (H'++H) l = Some(v,S) \/ 
                   exists S' v', lookup (H'++H) l = Some(v',S') /\ S' >= C. 
Proof.
  induction H'; intros; auto. simpl in *. destruct a. destruct p.
  destruct (eq_nat_dec l l0). 
  {subst. right. inv H1. repeat econstructor. }
  {eapply IHH' in H0; eauto. inv H1. auto. }
Qed.

Theorem validateHeapExtensionC : forall S L H S' H' new C, 
                  Forall (fun x : location * term * stamp => getStamp x = C) new ->
                  S < C ->
                  validate S L H S' (commit H') ->
                  (exists Hnew, validate S L (new++H) S' (commit (Hnew++new++H))) \/
                  (exists Lnew e, validate S L (new++H) S' (abort e Lnew) /\
                             postfix Lnew L).
Proof.
  intros. dependent induction H2. 
  {left. exists nil. constructor. }
  {copy H1. apply IHvalidate in H1; auto. inv H1.
   {invertHyp. eapply LookupExtensionGE in H3. Focus 2. eauto. inv H3. 
    {left. exists x. eapply validateCommitRead; eauto. }
    {invertHyp. right. exists L. exists (fill E (get (loc l))). split.
     eapply validateAbortRead; eauto. omega. unfold postfix. exists [readItem l E v]. auto. }
   }
   {invertHyp. right. exists x. exists x0. split. eapply validateAbortPropogate. eauto. 
    unfold postfix in *. invertHyp. exists (readItem l E v :: x1). auto. }
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
                  validate S L H S' (abort e L') ->
                  validate S L (new++H) S' (abort e L') \/
                  (exists Lnew e', validate S L (new++H) S' (abort e' Lnew) /\
                             postfix Lnew L').
Proof.
  intros. dependent induction H2. 
  {apply IHvalidate in H1; auto. inv H1. 
   {left. eapply validateAbortPropogate. auto. }
   {invertHyp. right. exists x0. exists x1. split; auto. eapply validateAbortPropogate. auto. }
  }
  {eapply validateHeapExtensionC in H2. inv H2. 
   {invertHyp. left. eapply LookupExtensionGE in H3. Focus 2. eauto. inv H3. 
    {eapply validateAbortRead; eauto. }
    {invertHyp. eapply validateAbortRead; eauto. omega. }
   }
   {invertHyp. right. exists x. exists x0. split. eapply validateAbortPropogate; auto. auto. }
   eauto. auto. 
  }
Qed. 

Theorem OKExtension : forall H H' S t e0 L e C, 
                        OK H t (Some(S,e0),L,e) -> S < C ->
                        Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                        OK (H'++H) t (Some(S,e0),L,e).
Proof.
  intros. inv H0. 
  {eapply validateHeapExtensionC in H6; eauto. inv H6. 
   {invertHyp. eapply inTXOKValid; eauto. eapply replayHeapExtension; eauto. }
   {invertHyp. eapply replayHeapExtension in H9; eauto.
    eapply replayInvalid in H9; eauto. invertHyp. eapply inTXInvalid; eauto. }
  }
  {eapply validateHeapExtensionA in H6; eauto.
   eapply validateHeapExtensionA in H9; eauto.
   inv H6; inv H9; try invertHyp; eapply inTXInvalid; eauto. }
Qed. 

Theorem poolOKExtension : forall H H' T1 T2 C,
                            poolOK H T1 T2 -> 
                            Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                            poolRewind C H T2 ->
                            poolOK (H'++H) T1 T2.
Proof.
  intros. induction H0. 
  {constructor. inv H2. 
   {inv H0. constructor. }
   {eapply OKExtension; eauto. }
  }
  {inv H2. constructor; auto. } 
Qed. 
 
Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
                               f_step C H T C' H' T' -> poolOK H T PT ->
                               poolRewind C H PT -> 
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolOK H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {inv H1. inv H4. 
   {inv H0; exfalso; apply H7; auto. }
   {inv H3. 
    {econstructor. split. eapply p_multi_step. eapply p_transStep; eauto. 
     constructor. constructor.
     inv H0; try solve[eapply inTXOKValid; eauto; constructor]. 
     {destruct (lt_dec S'0 S). 
      {eapply inTXOKValid. eapply validateCommitRead; eauto. constructor. }
      {eapply inTXInvalid; eapply validateAbortRead; eauto; omega. }
     }
     {eapply inTXOKValid. eapply validateWrite; eauto. constructor. }
    }
    {inv H0. 
     {inv H4; decompSame; invertEq; lookupSame. destruct(lt_dec S'0 S). 
      {lookupSame. econstructor. split. constructor. constructor. 
       eapply inTXOKValid. eapply validateCommitRead; eauto. auto. }
      {lookupSame. omega. }
      {lookupSame. econstructor. split. constructor.
       eapply replayInvalid in H5. Focus 2. eapply validateAbortRead; eauto. 
       invertHyp. constructor. eapply inTXInvalid; eauto.
       eapply validateAbortRead; eauto. }
     }
     {inv H4; decompSame; invertEq; lookupSame. econstructor. split.
      constructor. constructor. eapply inTXOKValid; eauto. }
     {inv H4; decompSame; invertEq. econstructor. split. constructor. 
      constructor. eapply inTXOKValid; eauto. eapply validateWrite; eauto. }
     {inv H4; decompSame; invertEq. econstructor. split.
      constructor. constructor. eapply inTXOKValid; eauto. }
     {inv H4; decompSame; invertEq. econstructor. split.
      constructor. constructor. eapply inTXOKValid; eauto. }
    }
   }
   {econstructor. split. constructor. constructor. 
    inv H0; eapply inTXInvalid; eauto; eapply validateAbortPropogate; eauto. }
  }
  {eapply f_stampHeapMonotonic in H0. invertHyp. inv H1. eapply IHf_step in H6. 
   invertHyp. econstructor. split. eapply p_multi_L. eauto. constructor. auto.
   inv H2. eapply poolOKExtension; eauto. inv H2. auto. }
  {eapply f_stampHeapMonotonic in H0. invertHyp. inv H1. eapply IHf_step in H8. 
   invertHyp. econstructor. split. eapply p_multi_R. eauto. constructor. inv H2. 
   eapply poolOKExtension; eauto. auto. auto. inv H2. auto. }
  {inv H1. inv H4. econstructor. split. eapply p_multi_step.
   eapply p_forkStep; eauto. constructor. repeat constructor. }
  {inv H1. inv H4. 
   {eapply validateSameAns in H0; eauto. contradiction. }
   {econstructor. split. econstructor. eapply p_abortStep; eauto.
    constructor. constructor. inv H2. eapply replayValidPortion in H4; eauto. 
    eapply inTXOKValid. constructor. rewrite <- rewindIFFReplay. copy H0. 
    eapply validateValidate in H9. invertHyp. eapply rewindDiffStamp; eauto. }
  }
  {inv H2. inv H5. econstructor. split. econstructor.
   eapply p_allocStep; eauto. constructor. repeat constructor. }
  {inv H2. inv H5. 
   {inv H10. 
    {econstructor. split. econstructor. eapply p_commitStep; eauto. 
     constructor. repeat constructor. }
    {inv H2; decompSame; invertEq. }
   }
   {eapply validateSameAns in H0; eauto. contradiction. }
  }
  {inv H1. inv H4. econstructor. split. econstructor. 
   eapply p_atomicStep; eauto. constructor. constructor. 
   eapply inTXOKValid. constructor. constructor. }
  {inv H1. inv H4. econstructor. split. eapply p_multi_step. 
   eapply p_betaStep; eauto. constructor. repeat constructor. }
  Grab Existential Variables. constructor. constructor. 
Qed. 

Theorem multistepPreservesRewind : forall C H T C' H' T',
                                poolRewind C H T -> p_multistep C H T C' H' T' ->
                                poolRewind C' H' T'. 
Proof.
  intros. induction H1. auto. apply IHp_multistep.
  eapply p_stepRewind; eauto. 
Qed. 

Theorem fullImpliesPartialMulti : forall C H T C' H' T' PT, 
                               f_multistep C H T C' H' T' -> poolOK H T PT ->
                               poolRewind C H PT ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolOK H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {exists PT. split. constructor. auto. }
  {copy H0. eapply fullImpliesPartial in H0; eauto. invertHyp. 
   copy H0. apply multistepPreservesRewind in H5; auto. 
   eapply IHf_multistep in H6; eauto. invertHyp. exists x0. split. 
   eapply p_multi_trans; eauto. auto. }
Qed. 







