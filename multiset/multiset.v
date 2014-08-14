Require Export SfLib. 

Definition multiset (A:Type) := list A. 

Definition In (A:Type) T e := @In A e T. 

Definition Union (A:Type) (m1 m2 : multiset A) := m1 ++ m2. 

Definition Add (A:Type) (m:multiset A) (a:A) := m++[a]. 

Definition Empty_set (A:Type) := @nil A. 

Axiom classicT : forall (P : Prop), {P} + {~ P}.

Fixpoint Subtract (A:Type) (m:multiset A) (e:A) :=
  match m with
    |m::ms => if classicT (m = e)
              then ms
              else m::Subtract A ms e
    |nil => nil
  end. 

Definition Single (A:Type) (m1 : A) : multiset A := [m1]. 

Definition Couple (A:Type) (m1 m2 : A) : multiset A := [m1;m2]. 

Axiom MultisetExtensionality : forall A (M1 M2 : multiset A),
                                 (forall x:A, In A M1 x -> In A M2 x) /\
                                 (forall x:A, In A M2 x -> In A M1 x) -> M1 = M2. 

Hint Unfold In. 
Ltac invUnion :=
  unfold In in *; 
  match goal with
      |H:List.In ?x (Union ?A ?T1 ?T2) |- _ => apply in_app_iff in H
      | |- List.In ?x (Union ?A ?T1 ?T2) => apply in_app_iff
  end. 
 
Hint Resolve in_app_iff.

Theorem Union_commutative : forall A (M1 M2 : multiset A), Union A M1 M2 = Union A M2 M1. 
Proof.
  intros. apply MultisetExtensionality. split; intros. 
  {repeat invUnion. inversion H; auto. }
  {repeat invUnion. inversion H; eauto. }
Qed. 

Theorem Union_associative : forall A (M1 M2 M3 : multiset A), 
                              Union A M1 (Union A M2 M3) = Union A (Union A M1 M2) M3. 
Proof.
  intros. apply MultisetExtensionality. split; intros. 
  {repeat invUnion. inversion H. left. invUnion; auto. invUnion. 
   inversion H0; auto. left. invUnion; auto. }
  {repeat invUnion. inversion H. invUnion. inversion H0. auto. right. 
   invUnion. auto. right. invUnion. auto. }
Qed. 

Theorem union_empty_r : forall A T, Union A T (Empty_set A) = T. 
Proof. 
  intros. rewrite Union_commutative. simpl. auto. 
Qed. 

Theorem couple_swap : forall (T:Type) (t1 t2:T), Couple T t1 t2 = Couple T t2 t1. 
Proof.
  intros. apply MultisetExtensionality. split; intros. 
  {inversion H. subst. simpl. right. auto. inversion H0. subst. simpl. auto. 
   inversion H1. }
  {inversion H. subst. simpl. right. auto. inversion H0. subst. simpl. auto. 
   inversion H1. }
Qed. 

Theorem pullOut : forall (A:Type) T (e:A),
                    In A T e -> T = Union A (Subtract A T e) (Single A e). 
Proof.
  induction T; intros. 
  {inversion H. }
  {inversion H; subst. 
   {simpl. destruct (classicT (e=e)). 
    {rewrite Union_commutative. simpl. auto. }
    {exfalso. apply n; auto. }
   }
   {simpl. destruct (classicT (a=e)). 
    {subst. rewrite Union_commutative. simpl. auto. }
    {simpl. erewrite <- IHT; eauto. }
   }
  }
Qed. 

Theorem UnionSubtract : forall (X:Type) T (x:X),
                          Subtract X (Union X T (Single X x)) x = T. 
Proof.
  induction T; intros. 
  {simpl. destruct (classicT(x=x)). auto. exfalso; apply n; auto. }
  {simpl. destruct (classicT(a=x)). subst. rewrite Union_commutative. 
   simpl; auto. rewrite IHT. auto. }
Qed. 

Theorem subtractSingle : forall (X:Type) T (x1:X), 
              (Subtract X (Union X (Subtract X T x1) (Single X x1)) x1) =
              Subtract X T x1. 
Proof.
  induction T; intros. 
  {simpl. destruct (classicT (x1=x1)); auto. exfalso; apply n; auto. }
  {simpl. destruct (classicT(a=x1)). 
   {rewrite UnionSubtract. auto. }
   {simpl. destruct (classicT(a=x1)); try contradiction. 
    rewrite IHT; eauto. }
  }
Qed. 

Theorem UnionSwap: forall (X : Type) (T1 T2 T3 : multiset X),
                     Union X (Union X T1 T2) T3 = Union X (Union X T1 T3) T2.
Proof.
  intros. rewrite <- Union_associative. rewrite (Union_commutative X T2). 
  rewrite Union_associative. auto. 
Qed. 

Theorem coupleUnion : forall (U:Type) (t1 t2 : U), 
                        Couple U t1 t2 = Union U (Single U t1) (Single U t2). 
Proof.
  intros. simpl. unfold Couple. unfold Single. auto. 
Qed. 

Ltac flipCouples :=
  rewrite couple_swap; rewrite coupleUnion; try flipCouples; rewrite <- coupleUnion. 

Ltac flipCouplesIn H :=
  rewrite couple_swap in H; rewrite coupleUnion in H; try flipCouplesIn H; rewrite <- coupleUnion in H. 

Theorem pullOutL : forall (A:Type) (T1 : multiset A) T2 T3,
                     Union A T1 (Couple A T2 T3) = 
                     Union A (Union A T1 (Single A T3)) (Single A T2).
Proof.
  intros. rewrite coupleUnion. rewrite Union_associative. 
  rewrite UnionSwap. auto. 
Qed. 

Theorem pullOutR : forall (A:Type) (T1 : multiset A) T2 T3,
                     Union A T1 (Couple A T2 T3) = 
                     Union A (Union A T1 (Single A T2)) (Single A T3).
Proof.
  intros. rewrite coupleUnion. rewrite Union_associative. 
  rewrite UnionSwap. auto. 
Qed. 

Theorem subtractUnion : forall (A:Type) T (e:A),
                          In A T e -> Union A (Subtract A T e) (Single A e) = T.
Proof.
  induction T; intros. 
  {inversion H. }
  {inversion H; subst. simpl. destruct (classicT(e=e)). 
   {rewrite Union_commutative. simpl. auto. }
   {exfalso. apply n; auto. }
   {simpl. destruct (classicT(a=e)). 
    {subst. rewrite Union_commutative. simpl. auto. }
    {simpl. rewrite IHT; auto. }
   }
  }
Qed. 


Theorem UnionEqSingleton : forall (A:Type) (T:multiset A) t t',
                             Union A T (Single A t) = (Single A t') ->
                             t = t' /\ T = Empty_set A. 
Proof.
  intros. destruct T. 
  {inversion H. auto. }
  {inversion H; subst. rewrite Union_commutative in H2. simpl in *. 
   inversion H2. }
Qed. 

Theorem union_empty_l : forall (A:Type) (T:multiset A),
                           Union A (Empty_set A) T = T. 
Proof.
  intros. simpl. auto. 
Qed. 

Theorem UnionSwapR : forall (A:Type) T (t1 t2 t3 : A),
                       Union A (Union A T (Single A t1)) (Couple A t2 t3) = 
                       Union A (Union A T (Single A t3)) (Couple A t2 t1).
Proof.
  intros. repeat rewrite <- Union_associative. repeat rewrite coupleUnion. 
  rewrite (Union_associative A (Single A t1)). 
  rewrite (Union_commutative A (Single A t1)). rewrite <- Union_associative. 
  rewrite (Union_commutative A (Single A t1)).
  rewrite (Union_associative A (Single A t2)). 
  rewrite (Union_commutative A (Single A t2)). rewrite <- Union_associative. 
  auto. 
Qed. 

Theorem UnionSwapL : forall (A:Type) T (t1 t2 t3 : A),
                       Union A (Union A T (Single A t1)) (Couple A t2 t3) = 
                       Union A (Union A T (Single A t2)) (Couple A t1 t3).
Proof.
  intros. repeat rewrite <- Union_associative. rewrite coupleUnion. 
  rewrite coupleUnion. rewrite (Union_associative A (Single A t1)). 
  rewrite (Union_commutative A (Single A t1)). 
  rewrite <- Union_associative. rewrite <- (coupleUnion A t1). auto. 
Qed. 
