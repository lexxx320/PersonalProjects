Require Import NonSpec. 
Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import SfLib. 

Require Import Coq.Program.Equality. 

Ltac inv H := inversion H; subst; clear H.

Theorem unspecUnionComm : forall T1 T2, unspecPoolAux (tUnion T1 T2) = 
                                        tUnion (unspecPoolAux T1) (unspecPoolAux T2).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inv H. inv H0. inv H2. inv H. 
   {econstructor. econstructor; eauto. }
   {apply Union_intror. econstructor; eauto. }
  }
  {inv H. 
   {inv H0. inv H. inv H2. econstructor; eauto. econstructor. econstructor. 
    eauto. eauto. }
   {inv H0. inv H. inv H2. econstructor; eauto. econstructor. apply Union_intror. 
    eauto. eauto. }
  }
Qed. 

Theorem stepWF : forall H T t H' t', 
                   wellFormed H (tUnion T t) -> step H T t (OK H' T t') ->
                   wellFormed H (tUnion T t'). 
Proof.
  intros. remember (OK H' T t'). induction H1; inv Heqc.  
  {inversion H0; subst. inversion H3; subst. econstructor; eauto. 
   rewrite unspecUnionComm in *. 












