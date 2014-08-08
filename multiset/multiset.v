Require Export SfLib. 

Definition multiset (A:Type) := list A. 

Definition In {A:Type} T e := @In A e T. 

Definition Union {A:Type} (m1 m2 : multiset A) := m1 ++ m2. 

Definition Add {A:Type} (m:multiset A) (a:A) := m++[a]. 

Definition Empty_set (A:Type) := @nil A. 

Axiom classicT : forall (P : Prop), {P} + {~ P}.

Fixpoint Subtract {A:Type} (m:multiset A) (e:A) :=
  match m with
    |m::ms => if classicT (m = e)
              then Subtract ms e 
              else m::Subtract ms e
    |nil => nil
  end. 

Definition Single {A:Type} (m1 : A) : multiset A := [m1]. 

Definition Couple {A:Type} (m1 m2 : A) : multiset A := [m1;m2]. 

Axiom MultisetExtensionality : forall A (M1 M2 : multiset A),
                                 (forall x:A, In M1 x -> In M2 x) /\
                                 (forall x:A, In M2 x -> In M1 x) -> M1 = M2. 
Hint Unfold In. 
Ltac invUnion :=
  unfold In in *; 
  match goal with
      |H:List.In ?x (Union ?T1 ?T2) |- _ => apply in_app_iff in H
      | |- List.In ?x (Union ?T1 ?T2) => apply in_app_iff
  end. 
 
Hint Resolve in_app_iff.

Theorem Union_commutative : forall A (M1 M2 : multiset A), Union M1 M2 = Union M2 M1. 
Proof.
  intros. apply MultisetExtensionality. split; intros. 
  {repeat invUnion. inversion H; auto. }
  {repeat invUnion. inversion H; eauto. }
Qed. 

Theorem Union_associative : forall A (M1 M2 M3 : multiset A), 
                              Union M1 (Union M2 M3) = Union (Union M1 M2) M3. 
Proof.
  intros. apply MultisetExtensionality. split; intros. 
  {repeat invUnion. inversion H. left. invUnion; auto. invUnion. 
   inversion H0; auto. left. invUnion; auto. }
  {repeat invUnion. inversion H. invUnion. inversion H0. auto. right. 
   invUnion. auto. right. invUnion. auto. }
Qed. 

Theorem union_empty_r : forall A T, Union T (Empty_set A) = T. 
Proof. 
  intros. rewrite Union_commutative. simpl. auto. 
Qed. 

Theorem couple_swap : forall (T:Type) (t1 t2:T), Couple t1 t2 = Couple t2 t1. 
Proof.
  intros. apply MultisetExtensionality. split; intros. 
  {inversion H. subst. simpl. right. auto. inversion H0. subst. simpl. auto. 
   inversion H1. }
  {inversion H. subst. simpl. right. auto. inversion H0. subst. simpl. auto. 
   inversion H1. }
Qed. 






