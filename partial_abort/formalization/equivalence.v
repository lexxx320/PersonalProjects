Require Export well_formed.



Inductive poolEq : pool -> pool -> Prop :=
|ParEq : forall T1 T2 T1' T2', poolEq T1 T1' -> poolEq T2 T2' ->
                               poolEq (Par T1 T2) (Par T1' T2')
|ThreadEq : forall Hl L L' t, 
              getList L = getList L' -> poolEq (Single(Hl,L,t)) (Single(Hl,L',t)). 


Theorem fullImpliesPartial : forall n H T n' H' T', 
                               f_step n H T n' H' T' ->
                               multistep n H T n' H' T'. 
Proof.
  intros. induction H0. 
  {eapply multi_step. 






