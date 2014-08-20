Require Import erasure. 

Hint Constructors pbasic_step. 

Theorem simBasicStep : forall t t',
                         basic_step t t' -> pbasic_step (eraseTerm t) (eraseTerm t'). 
Proof.
  intros. inv H; try solve[
    match goal with
       |H:decompose ?t ?E ?e |- _ => rewrite <- decomposeErase in H; eauto; 
                                     rewrite eraseFill; simpl; eauto
    end].      
  {rewrite <- decomposeErase in H0; eauto. rewrite eraseFill; simpl. rewrite eraseOpenComm. eauto. }
  {rewrite <- decomposeErase in H0; eauto. rewrite eraseFill; simpl.
   econstructor. simpl in *. eauto. }
  {rewrite <- decomposeErase in H0; eauto. rewrite eraseFill; simpl.
   eapply pbasicProjR. simpl in *. eauto. }
  {rewrite <- decomposeErase in H0; eauto. rewrite eraseFill; simpl. 
   eapply pSpecJoinRaise; eauto. simpl in *.  eauto. }
Qed. 

Theorem NonSpecPureStep' : forall h tid s1 s2 M M' T,
     spec_step h T (tSingleton (tid,s1,s2,M)) 
               h T (tSingleton(tid,s1,s2,M')) ->
     pstep (eraseHeap h) (erasePool T) (pSingle (eraseTerm M)) 
           (pOK (eraseHeap h) (erasePool T) (pSingle (eraseTerm M'))).
Proof.
  intros. inversion H; try solve[                    
    match goal with
        |H:aCons ?a ?s = ?s |- _ => destruct s; simpl in *; inversion H; invertListNeq
    end]. 
  {apply simBasicStep in H8. econstructor. eauto. }
Qed. 

