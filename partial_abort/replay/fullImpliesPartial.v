Require Export semantics_rewind. 

Inductive rewind_step H : thread -> thread -> Prop :=
|r_readStepValid : forall S L E l t v e0 S', 
                lookup H l = Some(v, S') -> S > S' ->
                decompose t E (get (loc l)) -> logLookup L l = None ->
                rewind_step H (Some(S, e0), L, t) (Some(S, e0), readItem l E v::L, fill E v)
|r_readStepInvalid : forall S L E v' l t v e0 S', 
                lookup H l = Some(v',S') -> S' >= S ->
                decompose t E (get (loc l)) -> logLookup L l = None ->
                rewind_step H (Some(S, e0), L, t) (Some(S, e0), readItem l E v::L, fill E v)
|r_readInDomainStep : forall S l v L E t e0,
                      decompose t E (get (loc l)) -> logLookup L l = Some v ->
                      rewind_step H (Some(S, e0), L, t) (Some(S, e0), L, fill E v)
|r_writeStep : forall S L E l v t,
               decompose t E (put (loc l) v) -> S <> None ->
               rewind_step H (S, L, t) (S, writeItem l v::L, fill E unit)
|r_atomicIdemStep : forall E e t L S,
                     decompose t E (atomic e) -> S <> None ->
                     rewind_step H (S, L, t) (S, L, fill E e)
|r_betaStep : forall L E e t v S, 
              decompose t E (app (lambda e) v) -> S <> None ->
              rewind_step H (S, L, t) (S, L, fill E (open e 0 v))
.

Inductive rewind H : thread -> thread -> Prop :=
|rewindRefl : forall t, rewind H t t
|rewindStep : forall t t' t'', 
                rewind_step H t' t'' -> rewind H t t' -> 
                rewind H t t''. 

Inductive valid H L : log -> Prop :=
|validCommit : forall S S' H', validate S L H S' (commit H') -> valid H L L
|validAbort : forall S S' e' L', 
                validate S L H S' (abort e' L') -> valid H L L'. 

Inductive OK H : thread -> thread -> Prop :=
|noTXOK : forall e, OK H (None, nil, e) (None, nil, e)
|inTXOKValid : forall S e0 L L' S' e e' H', 
                 validate S L H S' (commit H') ->
                 rewind H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                 OK H (Some(S,e0),L,e) (Some(S,e0),L',e')
|inTXInvalid : forall S L L' eA S' eA' e LA LA' e0 e', 
                 validate S L H S' (abort eA LA) -> 
                 validate S L' H S' (abort eA' LA') ->
                 OK H (Some(S,e0),L,e) (Some(S,e0),L',e'). 


Inductive poolOK H : pool -> pool -> Prop := 
|SingleOK : forall t t', OK H t t' -> poolOK H (Single t) (Single t')
|ParOK : forall T1 T2 T1' T2', 
           poolOK H T1 T1' -> poolOK H T2 T2' -> poolOK H (Par T1 T2) (Par T1' T2'). 

Theorem trans_rewind : forall H t t' t'', 
                         rewind H t' t'' -> rewind H t t' ->
                         rewind H t t''. 
Proof.
  intros. induction H0. auto. econstructor. eauto. auto. 
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

Theorem backupTransStep : forall H t t' t'', 
                            rewind H t t'' -> trans_step H t t' -> threadValid H t ->
                            t = t'' \/ rewind H t' t'' \/ notValid H t'. 
Proof.
  intros. generalize dependent t'. induction H0; intros; auto. 
  copy H3. eapply IHrewind in H3; auto. inv H3.  
  {inv H0; inv H4; decompSame; invertEq; try solve[right; econstructor|lookupSame]. 
   {repeat lookupSame. right. left. constructor. } 
   {destruct (lt_dec S' S). 
    {lookupSame. omega. }
    {right. right. inv H2. econstructor. eapply validateAbortRead; eauto. 
     repeat lookupSame. auto. }
   }
   {lookupSame. right. left. constructor. }
   {right. left. constructor. }
   {right. left. constructor. }
   {right. left. constructor. }
  }
  {inv H5. 
   {right. left. eapply trans_rewind; eauto. econstructor; eauto. 
    constructor. }
   {right. right. auto. }
  }
Qed. 

Theorem rewindAbort : forall S L H S' e L' e' e0 LA eA,
                        validate S L H S' (abort eA LA) ->
                        rewind H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                        exists eA' LA', validate S L' H S' (abort eA' LA').
Proof.
  intros. dependent induction H1. 
  {eauto. }
  {inv H2. 
   {eapply IHrewind in H0. Focus 2. eauto. Focus 2. eauto. invertHyp. 
    exists x. exists x0. eapply validateAbortPropogate; eauto. }
   {eapply IHrewind in H0;[idtac|eauto|eauto]. invertHyp.
    econstructor. econstructor. eapply validateAbortPropogate; eauto. }
   {eapply IHrewind in H0;[idtac|eauto|eauto]. invertHyp.
    econstructor. econstructor. eauto. }
   {eapply IHrewind in H0;[idtac|eauto|eauto]. invertHyp.
    econstructor. econstructor. eapply validateAbortPropogate; eauto. }
   {eapply IHrewind in H0;[idtac|eauto|eauto]. invertHyp.
    econstructor. econstructor. eauto. }
   {eapply IHrewind in H0;[idtac|eauto|eauto]. invertHyp.
    econstructor. econstructor. eauto. }
  }
Qed. 

Theorem rewindStepInvalid : forall H t t' t'', 
                              rewind H t t'' -> trans_step H t t' ->
                              threadValid H t -> notValid H t' ->
                              t'' = t \/ notValid H t''. 
Proof.
  intros. generalize dependent t'. induction H0; intros; auto. copy H3. inv H3. 
  {copy H5. eapply IHrewind in H5; eauto. inv H5. 

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

Inductive poolRewind H : pool -> Prop :=
|singleRewindTX : forall S e0 e L, 
                    rewind H (Some(S,e0), nil, e0) (Some(S,e0), L, e) ->
                    poolRewind H (Single(Some(S,e0), L, e))
|singleRewindNoTX : forall e, poolRewind H (Single(None, nil, e))
|parRewind : forall T1 T2, 
               poolRewind H T1 -> poolRewind H T2 ->
               poolRewind H (Par T1 T2). 

Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
                               f_step C H T C' H' T' -> poolOK H T PT ->
                               poolRewind PT -> 
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolOK H T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {inv H1. inv H4. 
   {inv H0; exfalso; apply H7; auto. }
   {copy H0. eapply backupTransStep in H4; eauto. Focus 2. econstructor. eauto. 
    inv H4. 
    {inv H5. econstructor. split. eapply p_multi_step. eapply p_transStep. 
     eauto. constructor. repeat constructor. 
     {inv H0; try solve[eapply inTXOKValid; eauto; constructor]. 
      {destruct (lt_dec S'0 S). 
       {eapply inTXOKValid. eapply validateCommitRead; eauto. constructor. }
       {eapply inTXInvalid; eapply validateAbortRead; eauto; omega. }
      }
      {eapply inTXOKValid.  eapply validateWrite; eauto. constructor. }
     }
    }
    {inv H5.
     {econstructor. split. constructor. constructor. inv H0; try solve[eapply inTXOKValid; eauto; auto]. 
      {destruct(lt_dec S'0 S).
       {eapply inTXOKValid; eauto. eapply validateCommitRead; eauto. }
       {eapply rewindAbort in H4; eauto. Focus 2. eapply validateAbortRead; eauto. 
        omega. invertHyp. eapply inTXInvalid. eapply validateAbortRead; eauto. omega. 
        eauto. }
      }
      {eapply inTXOKValid; eauto. eapply validateWrite; eauto. }
     }
     {inv H3. 
      {econstructor. split. eapply p_multi_step. eapply p_transStep. eauto. 
       constructor. inv H4. constructor. eapply inTXInvalid; eauto. }
      {admit. }
     }
    }
   }
   {econstructor. split. constructor. constructor. 
    inv H0; eapply inTXInvalid; eauto. 
    {eapply validateAbortPropogate; eauto. }
    {eapply validateAbortPropogate; eauto. }
   }
  }
  {inv H1. inv H2. eapply IHf_step in H5; eauto. invertHyp. 
   econstructor. split. eapply p_multi_L; eauto. constructor; auto. }
  {inv H1. inv H2. eapply IHf_step in H7; eauto. invertHyp. 
   econstructor. split. eapply p_multi_R; eauto. constructor; auto. }
  {inv H1. inv H4. econstructor. split. eapply p_multi_step.
   eapply p_forkStep; eauto. constructor. repeat constructor. }
  {inv H1. inv H4. 
   {eapply validateSameAns in H0; eauto. contradiction. }
   {econstructor. split. econstructor. eapply p_abortStep; eauto. constructor. 
    constructor. eapply inTXOKValid. constructor. inv H2.

Theorem rewindAbortPortion : forall S L H S' e' L' e e0, 
                               validate S L H S' (abort e' L') ->
                               semantics_rewind.rewind (Some (S, e0), [], e0)
                                                       (Some (S, e0), L, e) ->
                               rewind H (Some (S, e0), [], e0)(Some (S, e0), L', e').
Proof.
  intros. dependent induction H1. 
  {inv H0. }
  {inv H2. 
   {






asdf