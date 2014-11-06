Require Export semantics. 

Definition getStamp (x : location * term * stamp) :=
  match x with
      |(_,_,s) => s
  end. 

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

Theorem abortRewind : forall S L H S' e' L' e0 e,
                        validate S L H S' (abort e' L') ->
                        rewind H (Some (S, e0), [], e0) (Some (S, e0), L, e) ->
                        rewind H (Some (S, e0), [], e0) (Some (S, e0), L', e'). 
Proof.
  intros. dependent induction H1. 
  {inv H0. }
  {inv H2; eauto. 
   {inv H0; eauto. apply decomposeEq in H10. subst. auto. }
   {inv H0; eauto. eapply decomposeEq in H10. subst. auto. }
   {inv H0. eauto. }
  }
Qed. 

Ltac lookupSame :=
  match goal with
      |H:logLookup ?L ?l = ?v, H':logLookup ?L ?l = ?v' |- _ =>
       rewrite H in H'; inv H'
      |A:lookup ?H ?l = ?v, B:lookup ?H ?l = ?v' |- _ =>
       rewrite A in B; inv B
  end. 

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

Theorem poolRewindWeakening : forall C C' H T,
                                poolRewind C H T -> C' >= C ->
                                poolRewind C' H T. 
Proof.
  intros. induction H0.
  {constructor. }
  {constructor; auto. omega. }
  {constructor; auto. }
Qed. 

Theorem poolRewindHeapExtension : forall H H' T C C', 
                                    C' >= C -> poolRewind C H T ->
                                    Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                                    poolRewind C' (H'++H) T.
Proof.
  intros. induction H1. 
  {constructor. }
  {constructor. rewrite rewindIFFReplay. eapply replayHeapExtension; eauto. 
   rewrite <- rewindIFFReplay. auto. omega. }
  {constructor; auto. }
Qed. 

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

(*--------------------partial rollback step---------------------*)
Theorem p_stampHeapMonotonic : forall C H T C' H' T',
                               p_step C H T C' H' T' -> 
                               C' >= C /\ (exists H'', H' = H'' ++ H /\ Forall (fun x => getStamp x = C) H''). 
Proof.
  intros. induction H0; try invertHyp; split; eauto; try solve[exists nil; auto]. 
  {exists [(l,v,C)]. simpl. split; auto.  }
  {copy H0. apply validateHeapExtension in H0. invertHyp. exists x. split; auto. 
   eapply validateStampGE in H2. auto. }
Qed. 

Theorem p_stepRewind : forall C H T C' H' T', 
                       p_step C H T C' H' T' -> poolRewind C H T ->
                       poolRewind C' H' T'. 
Proof.
  intros. induction H0; try solve[repeat econstructor]. 
  {inv H1. inv H0; exfalso; apply H6; auto. inv H0. 
   {destruct(lt_dec S' S). 
    {constructor; auto. econstructor; eauto. eapply r_readStepValid; eauto. }
    {constructor; auto. econstructor; eauto. eapply r_readStepInvalid; eauto. omega. }
   }
   {constructor. econstructor; eauto. eapply r_readInDomainStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_writeStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_atomicIdemStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_betaStep; eauto. auto. }
  }
  {inv H1. constructor; auto. eapply p_stampHeapMonotonic in H0. invertHyp. 
   eapply poolRewindHeapExtension; eauto. }
  {inv H1. constructor; auto.  eapply p_stampHeapMonotonic in H0. invertHyp. 
   eapply poolRewindHeapExtension; eauto. }
  {inv H1. constructor. copy H0. eapply abortRewind in H0; eauto. 
   apply validateValidate in H1. invertHyp.
   eapply rewindDiffStamp; eauto. omega. }
Qed. 

(*--------------------full rollback step---------------------*)
Theorem f_stampHeapMonotonic : forall C H T C' H' T',
                               f_step C H T C' H' T' -> 
                               C' >= C /\ (exists H'', H' = H'' ++ H /\ Forall (fun x => getStamp x = C) H''). 
Proof.
  intros. induction H0; try invertHyp; split; eauto; try solve[exists nil; auto]. 
  {exists [(l,v,C)]. simpl. split; auto.  }
  {copy H0. apply validateHeapExtension in H0. invertHyp. exists x. split; auto. 
   eapply validateStampGE in H2. auto. }
Qed. 

Theorem f_stepRewind : forall C H T C' H' T', 
                       f_step C H T C' H' T' -> poolRewind C H T ->
                       poolRewind C' H' T'. 
Proof.
  intros. induction H0; try solve[repeat econstructor]. 
  {inv H1. inv H0; exfalso; apply H6; auto. inv H0. 
   {destruct(lt_dec S' S). 
    {constructor; auto. econstructor; eauto. eapply r_readStepValid; eauto. }
    {constructor; auto. econstructor; eauto. eapply r_readStepInvalid; eauto. omega. }
   }
   {constructor. econstructor; eauto. eapply r_readInDomainStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_writeStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_atomicIdemStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_betaStep; eauto. auto. }
  }
  {inv H1. constructor; auto. eapply f_stampHeapMonotonic in H0. 
   invertHyp. eapply poolRewindHeapExtension; eauto. }
  {inv H1. constructor; auto. eapply f_stampHeapMonotonic in H0. 
   invertHyp. eapply poolRewindHeapExtension; eauto. }
Qed. 