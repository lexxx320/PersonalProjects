Require Export f_stepWF. 

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
Theorem transImpliesfMulti : forall C H C' S e e0 e' L L',
                  trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L',e') -> 
                  C > S -> C' > C ->
                  f_multistep C' H (Single (Some(C,e0),L,e)) 
                              C' H (Single (Some(C,e0),L',e')). 
Proof.
  intros. dependent induction H0. 
  {constructor. }
  {inv H0.
   {econstructor. eapply f_transStep. eapply t_readStep; eauto. eauto. }
   {econstructor;[eapply f_transStep|idtac]. eapply t_readInDomainStep; eauto.
    eauto. }
   {econstructor;[eapply f_transStep|idtac]. eapply t_writeStep; eauto. intros c. 
    inv c. eapply IHtrans_multistep; eauto. }
   {econstructor. eapply f_transStep. eapply t_atomicIdemStep; eauto. intros c. 
    inv c. eauto. }
   {econstructor. eapply f_transStep. eapply t_betaStep; eauto. intros c. 
    inv c. eauto. }
  }
Qed. 

Theorem partialImpliesFull : forall C H T C' H' T', 
                               p_step C H T C' H' T' -> poolWF C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0.
  {econstructor. eapply f_transStep. eauto. constructor. }
  {apply wfPar_l in H1. apply IHp_step in H1. 
   eapply f_multi_L. eassumption. }
  {eapply wfPar_r in H1. apply IHp_step in H1. 
   eapply f_multi_R. eassumption. }
  {econstructor. eapply f_forkStep; eauto. constructor. }
  {inv H1. InTac. invertHyp. simpl in H1. inv H2. 
   {eapply validateSameAns in H0; eauto. contradiction. }
   {copy H0. eapply abortSameAns in H8; eauto. invertHyp. 
    econstructor. eapply f_abortStep; eauto. 
    apply validateValidate in H2. invertHyp. eapply transImpliesfMulti; eauto. }
  }
  {econstructor. eapply f_abortStep; eauto. constructor. }
  {econstructor. eapply f_allocStep; eauto. constructor. }
  {econstructor. eapply f_commitStep; eauto. constructor. }
  {econstructor. eapply f_atomicStep; eauto. constructor. }
  {econstructor. eapply f_betaStep; eauto. constructor. }
Qed. 

Theorem partialImpliesFullMulti : forall C H T C' H' T', 
                                    p_multistep C H T C' H' T' -> poolWF C H T ->
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
  constructor. constructor. intros. inv H2. split; auto. constructor. 
  solveByInv. solveByInv. 
Qed. 
  

















