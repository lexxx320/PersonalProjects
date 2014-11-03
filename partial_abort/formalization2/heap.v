Require Export ast. 
Require Export Coq.Arith.Peano_dec. 

(*General Purpose tactics*)
Ltac inv H := inversion H; subst; clear H. 
Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 
Ltac invertHyp :=
  match goal with
      |H:exists x, ?P |- _ => inv H; try invertHyp
      |H: ?P /\ ?Q |- _ => inv H; try invertHyp
  end. 


(*maps locations to terms and time stamps*)
Definition heap := list (location * term * stamp). 


Fixpoint lookup (H:heap) (l:location) :=
  match H with
      |(l', v, stamp)::H' => if eq_nat_dec l l'
                            then Some (v, stamp)
                            else lookup H' l
      |nil => None
  end. 

Theorem lookupExtension : forall Hnew H l v S, 
                            lookup H l  = Some(v, S) ->
                            exists v' S', lookup (Hnew++H) l = Some(v', S'). 
Proof.
  induction Hnew; intros. 
  {simpl. exists v. exists S. assumption. }
  {simpl. destruct a. destruct p. destruct (eq_nat_dec l l0). 
   {subst. exists t. exists s. reflexivity. }
   {eapply IHHnew in H0. invertHyp. exists x. exists x0. assumption. }
  }
Qed.

Theorem lookupDeterministic : forall H l v v' S S', 
                                 lookup H l = Some(v, S) -> lookup H l = Some(v', S') ->
                                 v = v' /\ S = S'. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct p. destruct (eq_nat_dec l l0). 
   {inv H0. inv H1. auto. }
   {eapply IHlist in H0; eauto. invertHyp. auto. }
  }
Qed. 

(*Extensional equality for heaps*)
Definition heapExtEq H1 H2 := forall l, lookup H1 l = lookup H2 l. 





