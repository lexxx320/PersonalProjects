Require Export partialImpliesFull.  

Theorem fullImpliesPartial : forall C H T C' H' T', 
                               f_step C H T C' H' T' ->
                               p_step  C H T C' H' T'. 
Proof.
  intros. induction H0. 
  {apply p_transStep; auto. }
  {apply p_parLStep. auto. }
  {apply p_parRStep; auto. }
  {apply p_forkStep; auto. }
  {eapply p_fullAbortStep; eauto. }
  {apply p_allocStep; auto. }
  {apply p_commitStep; auto. }
  {apply p_atomicStep; auto. }
  {eapply p_betaStep; auto. }
Qed. 

Theorem fullImpliesPartialMulti : forall C H T C' H' T', 
                               f_multistep C H T C' H' T' ->
                               p_multistep  C H T C' H' T'. 
Proof.
  intros. induction H0. constructor. econstructor; eauto. 
  apply fullImpliesPartial; auto. 
Qed. 

Theorem partialImpliesFullTopLevel : forall C T C' H' T', 
                                       initPool T -> Finished T' -> 
                                       (p_multistep C nil T C' H' T' <-> 
                                       f_multistep C nil T C' H' T'). 
Proof.
  intros. split; intros. 
  {apply partialImpliesFullTopLevel in H1; auto. }
  {apply fullImpliesPartialMulti; auto. }
Qed. 






