Require Export semantics.   

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
                       stampMonotonic C H ->
              Forall (fun x0 : location * term * stamp => getStamp x0 = C) H' ->
              lookup H l = Some(v, S) -> S' < C ->
              lookup (H'++H) l = Some(v',S') -> v' = v /\ S' = S. 
Proof.
  induction H'; intros. 
  {simpl in *. rewrite H2 in H4. inv H4. auto. }
  {simpl in *. destruct a. destruct p. destruct (eq_nat_dec l l0). 
   {inv H1. inv H4. simpl in *.  omega. }
   {inv H1. eauto. }
  }
Qed. 

Theorem lookupValid : forall L H H' H'' l v S E S' S'0 C,
              lookup H l = Some(v, S'0) -> 
              validate S L (H'++H) S' (commit H'') -> S < C -> 
              stampMonotonic C H ->
              Forall (fun x0 : location * term * stamp => getStamp x0 = C) H' ->
              In (readItem l E) L ->
              lookup (H'++H) l = Some(v,S'0).
Proof.
  induction L; intros. 
  {inv H5. }
  {inv H5. 
   {inv H1. copy H13. eapply lookupSame in H13; eauto. Focus 2. omega. invertHyp.
    auto. }
   {inv H1; eauto. }
  }
Qed. 


Theorem trans_multiHeapExt : forall H H' S e0 e L S' L' e' C, 
                 trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                 (exists x, validate S L' (H'++H) S' (commit x)) ->
                 Forall (fun x0 : location * term * stamp => getStamp x0 = C) H' ->
                 S < C -> stampMonotonic C H ->
                 trans_multistep (H'++H) (Some(S,e0),L,e) (Some(S,e0),L',e').
Proof.
  intros. dependent induction H0.  
  {constructor. }
  {inv H0. 
   {copy H1. eapply trans_multistepLogMonotonic in H0. Focus 2. simpl. left. auto.
    invertHyp. eapply lookupValid in H13; eauto. econstructor.
    eapply t_readStep; eauto. eauto. }
   {econstructor. eapply t_readInDomainStep; eauto. eauto. }
   {econstructor. eapply t_writeStep; eauto. eapply IHtrans_multistep; eauto. }
   {econstructor. eapply t_atomicIdemStep; eauto. eauto. }
   {econstructor. eapply t_betaStep; eauto. eauto. }
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

Theorem getAbortedAct : forall S L S' H L' e,
                         validate S L H S' (abort e L') ->
                         exists l E L'', L = L'' ++ [readItem l E] ++ L' /\ 
                                            e = fill E (get (loc l)).
Proof.
  intros. dependent induction H0.
  {invertHyp. exists x0. exists x1. exists (x::x2). split; auto. }
  {exists l. exists E. exists nil. split; auto. }
Qed. 

(*left recursive trans_multistep*)
Inductive trans_multistepL : heap -> thread -> thread -> Prop :=
|l_trans_refl : forall H t, trans_multistepL H t t
|l_multi_step : forall H t t' t'', 
                  trans_multistepL H t t' -> trans_step H t' t'' ->
                  trans_multistepL H t t''. 

Theorem trans_multistepLTrans : forall H t t' t'',
                                  trans_multistepL H t t' ->
                                  trans_multistepL H t' t'' ->
                                  trans_multistepL H t t''.
Proof.
  intros. induction H1. auto. econstructor. Focus 2. eauto. apply IHtrans_multistepL. 
  auto. 
Qed. 

Theorem transMultiLIff : forall H t t', 
                           trans_multistep H t t' <-> trans_multistepL H t t'. 
Proof.
  intros. split; intros. 
  {induction H0. constructor. eapply trans_multistepLTrans. Focus 2. eauto. 
   econstructor. Focus 2. eauto. constructor. }
  {induction H0. constructor. eapply trans_multistep_trans. eassumption. 
   econstructor. eauto. constructor. }
Qed. 

Theorem decomposeEq : forall E t e, decompose t E e -> t = fill E e. 
Proof.
  induction E; intros; try solve[inv H; simpl;erewrite <- IHE; eauto]. 
  {inv H; auto. }
Qed. 

Theorem trans_multiShort : forall H S e e0 l E L' L'', 
             trans_multistepL H (Some (S, e0), [], e0)
                             (Some (S, e0), L' ++ [readItem l E] ++ L'', e) ->
             trans_multistepL H (Some(S,e0), [], e0) 
                              (Some(S,e0),L'', fill E (get (loc l))). 
Proof.
  intros. dependent induction H0. 
  {apply lengthsEq in x. repeat rewrite app_length in x. simpl in x. omega. }
  {inv H1; eauto. 
   {destruct L'. 
    {inv H4. apply decomposeEq in H6. subst. auto. }
    {inv H4. eapply IHtrans_multistepL. auto. auto. }
   }
   {destruct L'. inv H3. eapply IHtrans_multistepL. auto. inv H3. auto. }
  }
Qed.  

Theorem abortLT : forall S L S' H L' e, 
                    validate S L H S' (abort e L') ->
                    length L' < length L. 
Proof.
  intros. dependent induction H0. 
  {simpl. omega. }
  {simpl. omega. }
Qed. 

Theorem abortSameTerm : forall S L H S' S'' S''' H' L' e e', 
                          validate S L H S' (abort e L') ->
                          validate S'' L H' S''' (abort e' L') ->
                          e = e'.
Proof.
  intros. dependent induction H0.
  {inv H1. auto. apply abortLT in H0. omega. }
  {inv H3. apply abortLT in H10. omega. auto. }
Qed.

Theorem destructEnd : forall (A:Type) (x:list A),
                      x = nil \/ exists x' e, x = x' ++ [e]. 
Proof.
  induction x; intros. 
  {auto. }
  {inv IHx. right. exists nil. simpl. exists a. auto. invertHyp. right. 
   exists (a::x0). exists x1. auto. }
Qed. 

Ltac destrEnd x := assert(x=nil \/ exists x' e, x = x' ++ [e]) by apply destructEnd. 

Theorem appMidEq : forall (A:Type) a (b:A) c d e, a++[b]++c = d++[e]++c ->
                                         a = d /\ b = e. 
Proof.
  induction a; intros. 
  {destruct d. inv H. auto. apply lengthsEq in H. simpl in *. inv H. 
   rewrite app_length in H1. simpl in *. omega. }
  {destruct d. inversion H. apply lengthsEq in H2. rewrite app_length in H2. 
   simpl in *. omega. inv H. simpl in *. apply IHa in H2. invertHyp. auto. }
Qed. 

Theorem thread_wf_Extension : forall H H' t C, 
                 threadWF H t -> optLT (getThreadStamp t) C ->
                 Forall (fun x0 : location * term * stamp => getStamp x0 = C) H' ->
                 stampMonotonic C H ->
                 threadWF (H'++H) t. 
Proof. 
  intros. inv H0.  
  {constructor. } 
  {simpl in H1. eapply validateHeapExtensionC in H4; eauto. inv H4. 
   {invertHyp. econstructor. eauto. auto. eapply trans_multiHeapExt; eauto. }
   {invertHyp. eapply threadWFInvalid. eauto. auto. eapply trans_multiHeapExt; eauto.
    Focus 2. apply validateValidate in H4. eauto. apply getAbortedAct in H4.
    invertHyp. rewrite transMultiLIff in H6. rewrite transMultiLIff. 
    eapply trans_multiShort. eauto. }
  }
  {simpl in H1. copy H4. eapply validateHeapExtensionA in H4; eauto. inv H4.  
   {eapply threadWFInvalid. eauto. copy H5. auto. eapply validateValidate in H7. invertHyp. 
    eapply trans_multiHeapExt; eauto. }
   {invertHyp. eapply threadWFInvalid; eauto. eapply trans_multiHeapExt; eauto.
    Focus 2. apply validateValidate in H4. eauto. unfold postfix in H8. 
    inversion H8. destruct x1.
    {simpl in *. subst. eapply abortSameTerm in H4; eauto. subst. auto. }
    {invertHyp. apply getAbortedAct in H4. invertHyp. apply abortLogPostfix in H0. 
     invertHyp. destrEnd x1. inv H0. 
     {apply appMidEq in H4. invertHyp. rewrite transMultiLIff in H6. 
      rewrite transMultiLIff. eapply trans_multiShort with (L':=nil). eauto. }
     {invertHyp. replace( x0 ++ (l :: x6 ++ [x7]) ++ x) with 
                 ((x0 ++ l :: x6) ++ [x7] ++ x) in H4. Focus 2. simpl. 
      repeat rewrite <- app_assoc. simpl. auto. apply appMidEq in H4. invertHyp. 
      rewrite transMultiLIff in H6. rewrite transMultiLIff. 
      eapply trans_multiShort with (L' := l::x6). simpl in *. 
      rewrite <- app_assoc in H6. eauto. }
    }
   }
  }
Qed. 

Theorem trans_stepWF : forall H t t', 
                  threadWF H t -> trans_step H t t' -> threadWF H t'.
Proof.
  intros. inv H1. 
  {inv H0. 
   {destruct (lt_dec S' S). 
    {econstructor. eapply validateCommitRead; eauto. constructor; auto. 
     eapply trans_multistep_trans. 
     eassumption. econstructor. eapply t_readStep; eauto. constructor. }
    {apply not_lt in n. eapply threadWFInvalid. eapply validateAbortRead; eauto. 
     constructor; auto. eapply trans_multistep_trans. eauto. apply decomposeEq in H2. 
     subst. constructor. }
   }
   {eapply threadWFInvalid. eapply validateAbortPropogate; eauto. constructor; auto. 
    auto. }
  }
  {inv H0. econstructor; eauto. eapply trans_multistep_trans. eassumption. 
   econstructor. eapply t_readInDomainStep; eauto. constructor. 
   eapply threadWFInvalid; eauto. }
  {inv H0. exfalso. apply H3. auto. 
   {econstructor. econstructor; eauto. constructor; auto. eapply trans_multistep_trans. eauto. 
    econstructor. eapply t_writeStep; eauto. constructor. }
   {eapply threadWFInvalid. eapply validateAbortPropogate. eauto. constructor; auto. 
    auto. }
  }
  {inv H0. exfalso. apply H3. auto. 
   {econstructor; eauto. eapply trans_multistep_trans. eauto. econstructor. 
    eapply t_atomicIdemStep; eauto. constructor. }
   {eapply threadWFInvalid; eauto. }
  }
  {inv H0. exfalso. apply H3. auto. 
   {econstructor; eauto. eapply trans_multistep_trans. eauto. econstructor. 
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
   econstructor. simpl. auto. econstructor. constructor. constructor. constructor. }
  {constructor. inv H0. constructor. omega. auto. intros. inv H0. inv H3. split. 
   simpl. auto. constructor. }
  {inv H0. constructor. eapply validateMonotonic; eauto. intros. inv H0. 
   split. simpl. auto. constructor. }
  {econstructor. inv H0. eapply monotonicWeakening;[idtac|eauto]. omega. intros. 
   inv H2. split. simpl. auto. econstructor. constructor. econstructor. constructor. }
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
























