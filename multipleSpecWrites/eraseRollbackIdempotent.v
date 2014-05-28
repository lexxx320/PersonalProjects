Require Import NonSpec. 
Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 


Theorem rollbackIdempotent : forall tid stack H T H' T' H'' T'', 
                               rollback tid stack H T H' T' -> 
                               eraseHeap H H'' -> erasePool T T'' ->
                               eraseHeap H' H'' /\ erasePool T' T''. 
Proof.
  intros. generalize dependent H''. generalize dependent T''. induction H0; intros; subst. 
  {split; auto. }
  {destruct s1'. 
   {(*TODO: this case is vacuous*) admit. }
   {











