Require Import fullImpliesPartial. 
Require Import partialImpliesFull. 

Fixpoint initialPool T :=
  match T with
      |Single(None,nil,e) => True
      |_ => False
  end. 

Fixpoint Done T :=
  match T with
      |Single(None,nil,v) => value v
      |Par T1 T2 => Done T1 /\ Done T2
      |_ => False
  end. 


Theorem DoneOK : forall H T T', 
                   Done T -> poolOK H T T' ->
                   T = T'. 
Proof.
  intros. induction H1. 
  {inv H1. auto. inv H0. inv H0. }
  {inv H0. rewrite IHpoolOK1; auto. rewrite IHpoolOK2; auto. }
Qed. 


Theorem rewindInitPool : forall T C H, 
                           initialPool T -> poolRewind C H T. 
Proof.
  intros. destruct T. destruct t. destruct p. destruct o. 
  inv H0. destruct l. constructor. inv H0. inv H0. 
Qed. 


Theorem OKInitPool : forall H T, initialPool T -> poolOK H T T. 
Proof.
  intros. destruct T. destruct t. destruct p. destruct o. 
  inv H0. destruct l. repeat constructor. inv H0. inv H0. 
Qed. 

Theorem partialEqFull : forall C H T C' H' T', 
                          initialPool T -> Done T' ->
                          (p_multistep C H T C' H' T' <-> 
                           f_multistep C H T C' H' T'). 
Proof.
  intros. split; intros. 
  {apply partialImpliesFullMulti. auto. apply rewindInitPool. auto. }
  {eapply fullImpliesPartialMulti in H2. invertHyp.
   copy H4. apply DoneOK in H4; auto. subst x. eauto. apply OKInitPool. 
   auto. apply rewindInitPool. auto. }
Qed. 











