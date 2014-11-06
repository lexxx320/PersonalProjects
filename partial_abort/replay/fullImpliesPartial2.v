Require Export semantics_rewind. 
 
Inductive replay_step H : thread -> thread -> Prop :=
|r_readStepValid : forall S L E l t v e0 S', 
                lookup H l = Some(v, S') -> S > S' ->
                decompose t E (get (loc l)) -> logLookup L l = None ->
                replay_step H (Some(S, e0), L, t) (Some(S, e0), readItem l E v::L, fill E v)
|r_readStepInvalid : forall S L E v' l t v e0 S', 
                lookup H l = Some(v',S') -> S' >= S ->
                decompose t E (get (loc l)) -> logLookup L l = None ->
                replay_step H (Some(S, e0), L, t) (Some(S, e0), readItem l E v::L, fill E v)
|r_readInDomainStep : forall S l v L E t e0,
                      decompose t E (get (loc l)) -> logLookup L l = Some v ->
                      replay_step H (Some(S, e0), L, t) (Some(S, e0), L, fill E v)
|r_writeStep : forall S L E l v t,
               decompose t E (put (loc l) v) -> S <> None ->
               replay_step H (S, L, t) (S, writeItem l v::L, fill E unit)
|r_atomicIdemStep : forall E e t L S,
                     decompose t E (atomic e) -> S <> None ->
                     replay_step H (S, L, t) (S, L, fill E e)
|r_betaStep : forall L E e t v S, 
              decompose t E (app (lambda e) v) -> S <> None ->
              replay_step H (S, L, t) (S, L, fill E (open e 0 v))
.

Inductive replay H : thread -> thread -> Prop :=
|replayRefl : forall t, replay H t t
|replayStep : forall t t' t'', 
                replay_step H t t' -> replay H t' t'' -> 
                replay H t t''. 

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

Theorem trans_replay: forall H t t' t'', 
                         replay H t' t'' -> replay H t t' ->
                         replay H t t''. 
Proof.
  intros. induction H1. auto. econstructor. eauto. auto. 
Qed. 

Inductive notValid H : thread -> Prop :=
|notValid_ : forall S' S e' L L' e e0, validate S L H S' (abort e' L') ->
                                       notValid H (Some(S,e0),L,e).

Inductive threadValid H : thread -> Prop :=
|threadValid_ : forall S' S L H' e e0, validate S L H S' (commit H') ->
                                    threadValid H (Some(S,e0),L,e).

Ltac lookupSame :=
  match goal with
      |H:logLookup ?L ?l = ?v, H':logLookup ?L ?l = ?v' |- _ =>
       rewrite H in H'; inv H'
      |A:lookup ?H ?l = ?v, B:lookup ?H ?l = ?v' |- _ =>
       rewrite A in B; inv B
  end. 

Inductive stampMonotonic S : heap -> Prop :=
|nilMonotonic : stampMonotonic S nil
|consMonotonic : forall l v S' H, 
                   S' <= S -> stampMonotonic S' H -> stampMonotonic S ((l,v,S')::H). 

Inductive poolReplay C H : pool -> Prop :=
|singleRewindTX : forall S e0 e L, 
                    replay H (Some(S,e0), nil, e0) (Some(S,e0), L, e) ->
                    S < C -> poolReplay C H (Single(Some(S,e0), L, e))
|singleRewindNoTX : forall e, poolReplay C H (Single(None, nil, e))
|parRewind : forall T1 T2, 
               poolReplay C H T1 -> poolReplay C H T2 ->
               poolReplay C H (Par T1 T2). 

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

Theorem abortSameAns : forall S L H S' L' e' S'' L'' e'', 
                         validate S L H S' (abort e' L') ->
                         validate S L H S'' (abort e'' L'') ->
                         e' = e'' /\ L' = L''. 
Proof.
  induction L; intros. 
  {inv H0. }
  {inv H0; inv H1; eauto. eapply validateSameAns in H10; eauto. inv H10. 
   eapply validateSameAns in H10; eauto. inv H10. }
Qed. 

Inductive rewind H : thread -> thread -> Prop :=
|rewindRefl : forall t, rewind H t t
|rewindStep : forall t t' t'', 
                replay_step H t' t'' -> rewind H t t' -> 
                rewind H t t''. 

Theorem rewindTrans : forall H t t' t'', 
                        rewind H t t' -> rewind H t' t'' ->
                        rewind H t t''. 
Proof.
  intros. induction H1; auto. econstructor; eauto. 
Qed. 

Theorem rewindIFFReplay : forall H t t', 
                            rewind H t t' <-> replay H t t'. 
Proof.
  intros. split; intros. 
  {induction H0. constructor. eapply trans_replay; eauto.
   econstructor. eauto. constructor. }
  {induction H0. constructor. eapply rewindTrans; eauto.
   econstructor; eauto. constructor. }
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
    {apply decomposeEq in H10. subst. auto. }
   }
   {inv H2. 
    {eapply IHrewind; eauto. }
    {eapply decomposeEq in H10. subst. auto. }
   }
   {inv H2. eauto. }
  }
Qed. 

Theorem rewindDiffStamp : forall S C H e0 L e L' e' H' S', 
                            rewind H (Some(S,e0), L, e) (Some(S,e0), L', e') -> C > S ->
                            validate S L' H S' (commit H') ->
                            rewind H (Some(C,e0), L, e) (Some(C,e0), L', e').
Proof.
  intros. generalize dependent H'. dependent induction H0; intros. constructor. inv H0.
  {econstructor. eapply r_readStepValid; eauto. omega. inv H3. 
   eapply IHrewind; eauto. }
  {inv H3. lookupSame. omega. }
  {econstructor. eapply r_readInDomainStep; eauto. eauto. }
  {inv H3. econstructor. eapply r_writeStep; eauto. intros c. inv c. 
   eapply IHrewind; eauto. }
  {econstructor. eapply r_atomicIdemStep; eauto. intros c. inv c. eauto. }
  {econstructor. eapply r_betaStep; eauto. intros c. inv c. eauto. }
Qed. 

Theorem validateValidate : forall S L H S' L' e, 
                             validate S L H S' (abort e L') ->
                             exists H'', validate S L' H S' (commit H''). 
Proof.
  intros. dependent induction H0. 
  {invertHyp. exists x0. auto. }
  {exists H'. assumption. }
Qed. 

Definition getStamp (x : location * term * stamp) :=
  match x with
      |(_,_,s) => s
  end. 

Theorem validateHeapExtension : forall S H C H' L,
                                    validate S L H C (commit H')  ->
                                    exists H'', H' = H'' ++ H .
Proof.
  intros. dependent induction H0; eauto; try solve[exists nil; eauto].  
  {invertHyp. exists ((l,v,S')::x). simpl. reflexivity. }
Qed. 

Theorem validateStampGE : forall H' S L H C,
                            validate S L H C (commit (H'++H)) ->
                            Forall (fun x => getStamp x = C) H'. 
Proof.
  intros. dependent induction H0; auto. 
  {destruct H'. constructor. apply lengthsEq in x. simpl in *. 
   rewrite app_length in x. omega. }
  {copy H0. eapply validateHeapExtension in H0. invertHyp. destruct H'. 
   simpl in x. apply lengthsEq in x. simpl in x. rewrite app_length in x. omega.
   constructor. inv x. auto. eapply IHvalidate; eauto. inversion x. auto. }
Qed. 

Theorem stampHeapMonotonic : forall C H T C' H' T',
                               f_step C H T C' H' T' -> 
                               C' >= C /\ (exists H'', H' = H'' ++ H /\ Forall (fun x => getStamp x = C) H''). 
Proof.
  intros. induction H0; try invertHyp; split; eauto; try solve[exists nil; auto]. 
  {exists [(l,v,C)]. simpl. split; auto.  }
  {copy H0. apply validateHeapExtension in H0. invertHyp. exists x. split; auto. 
   eapply validateStampGE in H2. auto. }
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

Theorem lookupExtension : forall H' l v S H C, 
                            lookup H l = Some(v, S) ->
                            Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                            lookup (H'++H) l = Some(v, S) \/
                            exists S' v', lookup (H'++H) l = Some(v', S') /\
                                          S' = C. 
Proof.
  induction H'; intros. 
  {simpl. auto. }
  {simpl in *. destruct a. destruct p. destruct (eq_nat_dec l l0). 
   {right. subst. repeat econstructor. inv H1. auto. }
   {inv H1. eapply IHH' in H5; eauto. }
  }
Qed. 

Theorem replayHeapExtension : forall H H' S e0 L e L' e' C,
                                replay H (Some(S,e0),L,e) (Some(S,e0),L',e') -> S < C ->
                                Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                                replay (H'++H) (Some(S,e0),L,e) (Some(S,e0),L',e'). 
Proof.
  intros. dependent induction H0. 
  {constructor. }
  {inv H0. 
   {copy H8. eapply lookupExtension with (H':=H') in H0; eauto. inv H0. 
    {econstructor. eapply r_readStepValid; eauto. eauto. }
    {invertHyp. econstructor. eapply r_readStepInvalid; eauto. omega. eauto. }
   }
   {copy H8. eapply lookupExtension with (H':=H') in H0; eauto. inv H0. 
    {econstructor. eapply r_readStepInvalid; eauto. eauto. }
    {invertHyp. econstructor. eapply r_readStepInvalid; eauto. omega. eauto. }
   }
   {econstructor. eapply r_readInDomainStep; eauto. eauto. }
   {econstructor. eapply r_writeStep; eauto. eauto. }
   {econstructor. eapply r_atomicIdemStep; eauto. eauto. }
   {econstructor. eapply r_betaStep; eauto. eauto. }
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
                            poolReplay C H T2 ->
                            poolOK (H'++H) T1 T2.
Proof.
  intros. induction H0. 
  {constructor. inv H2. 
   {eapply OKExtension; eauto. }
   {inv H0. constructor. }
  }
  {inv H2. constructor; auto. } 
Qed. 

Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
                               f_step C H T C' H' T' -> poolOK H T PT ->
                               poolReplay C H PT -> stampMonotonic C H ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolOK H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {inv H1. inv H5. 
   {inv H0; exfalso; apply H8; auto. }
   {inv H4. 
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
     {inv H5; decompSame; invertEq; lookupSame. destruct(lt_dec S'0 S). 
      {lookupSame. econstructor. split. constructor. constructor. 
       eapply inTXOKValid. eapply validateCommitRead; eauto. auto. }
      {lookupSame. omega. }
      {lookupSame. econstructor. split. constructor.
       eapply replayInvalid in H6. Focus 2. eapply validateAbortRead; eauto. 
       invertHyp. constructor. eapply inTXInvalid; eauto.
       eapply validateAbortRead; eauto. }
     }
     {inv H5; decompSame; invertEq; lookupSame. econstructor. split.
      constructor. constructor. eapply inTXOKValid; eauto. }
     {inv H5; decompSame; invertEq. econstructor. split. constructor. 
      constructor. eapply inTXOKValid; eauto. eapply validateWrite; eauto. }
     {inv H5; decompSame; invertEq. econstructor. split.
      constructor. constructor. eapply inTXOKValid; eauto. }
     {inv H5; decompSame; invertEq. econstructor. split.
      constructor. constructor. eapply inTXOKValid; eauto. }
    }
   }
   {econstructor. split. constructor. constructor. 
    inv H0; eapply inTXInvalid; eauto; eapply validateAbortPropogate; eauto. }
  }
  {eapply stampHeapMonotonic in H0. invertHyp. inv H1. eapply IHf_step in H7. 
   invertHyp. econstructor. split. eapply p_multi_L. eauto. constructor. auto.
   inv H2. 
   eapply poolOKExtension; eauto. inv H2. auto. inv H2. auto. }
  {eapply stampHeapMonotonic in H0. invertHyp. inv H1. eapply IHf_step in H9. 
   invertHyp. econstructor. split. eapply p_multi_R. eauto. constructor. inv H2. 
   eapply poolOKExtension; eauto. auto. auto. inv H2. auto. }
  {inv H1. inv H5. econstructor. split. eapply p_multi_step.
   eapply p_forkStep; eauto. constructor. repeat constructor. }
  {inv H1. inv H5. 
   {eapply validateSameAns in H0; eauto. contradiction. }
   {econstructor. split. econstructor. eapply p_abortStep; eauto.
    constructor. constructor. inv H2. rewrite <- rewindIFFReplay in H5. 
    eapply replayValidPortion in H5; eauto. eapply inTXOKValid. constructor. 
    rewrite <- rewindIFFReplay. copy H0. eapply validateValidate in H10.  
    invertHyp. eapply rewindDiffStamp; eauto. }
  }
  {inv H2. inv H6. econstructor. split. econstructor.
   eapply p_allocStep; eauto. constructor. repeat constructor. }
  {inv H2. inv H6. 
   {inv H11. 
    {econstructor. split. econstructor. eapply p_commitStep; eauto. 
     constructor. repeat constructor. }
    {inv H2; decompSame; invertEq. }
   }
   {eapply validateSameAns in H0; eauto. contradiction. }
  }
  {inv H1. inv H5. econstructor. split. econstructor. 
   eapply p_atomicStep; eauto. constructor. constructor. 
   eapply inTXOKValid. constructor. constructor. }
  {inv H1. inv H5. econstructor. split. eapply p_multi_step. 
   eapply p_betaStep; eauto. constructor. repeat constructor. }
  Grab Existential Variables. constructor. constructor. 
Qed. 

Theorem p_stampHeapMonotonic : forall C H T C' H' T',
                               p_step C H T C' H' T' -> 
                               C' >= C /\ (exists H'', H' = H'' ++ H /\ Forall (fun x => getStamp x = C) H''). 
Proof.
  intros. induction H0; try invertHyp; split; eauto; try solve[exists nil; auto]. 
  {exists [(l,v,C)]. simpl. split; auto.  }
  {copy H0. apply validateHeapExtension in H0. invertHyp. exists x. split; auto. 
   eapply validateStampGE in H2. auto. }
Qed. 

Theorem poolReplayHeapExtension : forall H H' T C C', 
                                    C' >= C -> poolReplay C H T ->
                                    Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                                    poolReplay C' (H'++H) T.
Proof.
  intros. induction H1. 
  {constructor. eapply replayHeapExtension; eauto. omega. }
  {constructor. }
  {constructor; auto. }
Qed. 


Theorem stepPreservesReplay : forall C H T C' H' T',
                                poolReplay C H T -> p_step C H T C' H' T' ->
                                poolReplay C' H' T'. 
Proof.
  intros. induction H1.
  {inv H1; try solve[constructor]. 
   {inv H0. econstructor; auto. destruct (lt_dec S' S). 
    {eapply trans_replay. Focus 2. eauto. econstructor. 
     eapply r_readStepValid; eauto. constructor. }
    {eapply trans_replay; eauto. econstructor.
     eapply r_readStepInvalid; eauto. omega. constructor. }
   }
   {inv H0. constructor; auto. eapply trans_replay; eauto. 
    econstructor. eapply r_readInDomainStep; eauto. constructor. }
   {inv H0. econstructor. eapply trans_replay; eauto. econstructor. 
    eapply r_writeStep; eauto. constructor. auto. exfalso. auto. }
   {inv H0. econstructor. eapply trans_replay; eauto. econstructor. 
    eapply r_atomicIdemStep; eauto. constructor. auto. exfalso. auto. }
   {inv H0. econstructor. eapply trans_replay; eauto. econstructor. 
    eapply r_betaStep; eauto. constructor. auto. exfalso. auto. }
  }
  {inv H0. constructor; auto. apply p_stampHeapMonotonic in H1. invertHyp. 
   eapply poolReplayHeapExtension; eauto. }
  {inv H0. constructor; auto. apply p_stampHeapMonotonic in H1. invertHyp. 
   eapply poolReplayHeapExtension; eauto. }
  {repeat econstructor. }
  {inv H0. constructor. rewrite <- rewindIFFReplay.
   rewrite <- rewindIFFReplay in H4. eapply replayValidPortion in H4; eauto.
   apply validateValidate in H1. invertHyp. eapply rewindDiffStamp; eauto. omega. }
  {constructor. }
  {constructor. }
  {constructor. constructor. omega. }
  {constructor. }
Qed. 

Theorem multistepPreservesReplay : forall C H T C' H' T',
                                poolReplay C H T -> p_multistep C H T C' H' T' ->
                                poolReplay C' H' T'. 
Proof.
  intros. induction H1. auto. apply IHp_multistep.
  eapply stepPreservesReplay; eauto. 
Qed. 

Theorem fullImpliesPartialMulti : forall C H T C' H' T' PT, 
                               f_multistep C H T C' H' T' -> poolOK H T PT ->
                               poolReplay C H PT -> stampMonotonic C H ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolOK H' T' PT'.
Proof.
  intros. induction H0. 
  {exists PT. split. constructor. auto. }
  {



