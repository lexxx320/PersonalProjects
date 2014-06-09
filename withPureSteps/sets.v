Require Import Coq.Logic.Classical.
Require Import Coq.Sets.Ensembles.

Section Ensembles.

Variable U : Type.

Lemma union_empty : forall A,
  Union U A (Empty_set U) = A.
intros A. apply Extensionality_Ensembles.
split; intros x x_in_one.
inversion x_in_one as [ _x in_A x_eq | _x false x_eq ].
auto. inversion false.
left. auto.

Qed.

Lemma union_swap : forall A B,
  Union U A B = Union U B A.

intros A B.
apply Extensionality_Ensembles. 
split; intros x x_in_one;
destruct x_in_one as [ x x_in_left | x x_in_right ];
auto using Union_introl, Union_intror.

Qed.

Lemma disjoint_setminus :
  forall A B,
    Disjoint U A (Setminus U B A).

  intros A B.
  apply Disjoint_intro. unfold not.
  intros x in_int.
  destruct in_int as [ x x_in_A x_in_setminus ].
  destruct x_in_setminus.
  tauto.

Qed.

Lemma add_add_to_union_couple :
  forall A x y,
    (Add U (Add U A x) y) = (Union U A (Couple U y x)).

intros A x y.
apply Extensionality_Ensembles. split; intros z z_in_one.
destruct z_in_one as [ z' [ z z_in_A | z z_is_x ] | z z_is_y ].
left. auto. 
right. inversion z_is_x. subst z. right.
right. inversion z_is_y. subst z. left.
destruct z_in_one as [ z z_in_A | z [ | ] ].
left. left. auto.
right. apply In_singleton. 
left. right. apply In_singleton.

Qed.

Lemma couple_swap :
  forall A B,
    Couple U A B = Couple U B A.

intros A B.
apply Extensionality_Ensembles. split; intros x x_in_one.
destruct x_in_one. right. left.
destruct x_in_one. right. left.

Qed.

Lemma add_subtract :
  forall A x,
    In U A x ->
    A = Add U (Subtract U A x) x.

intros A x in_A.
apply Extensionality_Ensembles. split; intros y y_in_one.
assert (x = y \/ x <> y) as [ is_x | not_x ]. apply classic.
right. subst y. apply In_singleton.
left. split. auto. intros false.
inversion false. tauto.
destruct y_in_one as [ y y_in_subtract | y y_is_x ].
destruct y_in_subtract. auto. inversion y_is_x. subst y. auto.

Qed.


Theorem eqImpliesSameSet : forall (T:Type) T1 T2, T1 = T2 -> Same_set T T1 T2. 
Proof.
  intros. unfold Same_set. unfold Included. split; intros. 
  {subst. assumption. }
  {subst. assumption. }
Qed. 

Ltac unfoldSetEq H :=
  match type of H with
      |?S1 = ?S2 => apply eqImpliesSameSet in H; unfold Same_set in H; 
                    unfold Included in *; inversion H
  end. 

Hint Unfold In. 
Hint Constructors Singleton Couple. 

Theorem SingleEqCouple : forall (T:Type) s1 s2 s3,
                           Singleton T s1 = Couple T s2 s3 -> s1 = s2 /\ s1 = s3.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H.
  unfold Included in H. inversion H. split.
  {assert(In T (Couple T s2 s3) s2). auto. apply H1 in H2.
   inversion H2. reflexivity. }
  {assert(In T (Couple T s2 s3) s3). auto. apply H1 in H2.
   inversion H2. reflexivity. }
Qed.

Theorem SingletonEq : forall (T:Type) (e1 e2 : T), Singleton T e1 = Singleton T e2 -> e1 = e2. 
Proof.
  intros. unfoldSetEq H. assert(Ensembles.In T (Singleton T e1) e1). auto. apply H0 in H2. 
  inversion H2. reflexivity. Qed. 
 
Theorem UnionEqSingleton : forall (T:Type) S e1 e2, 
                             Union T S (Singleton T e1) = Singleton T e2 ->
                             e1 = e2. 
Proof.
  intros. unfoldSetEq H. clear H. assert(In T (Union T S(Singleton T e1)) e1). 
  apply Union_intror. constructor. apply H0 in H. inversion H. 
  reflexivity. Qed. 

Theorem disjointUnionEqSingleton : forall (T:Type) S e1 e2, 
                                     Disjoint T S (Singleton T e1) ->
                                     Union T S (Singleton T e1) = Singleton T e2 ->
                                     e1 = e2 /\ S = Empty_set T. 
Proof.
  intros. unfoldSetEq H0. clear H0. inversion H. split.
  {assert(In T (Union T S (Singleton T e1)) e1). apply Union_intror. 
   constructor. apply H1 in H3. inversion H3. reflexivity. }
  {assert(In T (Singleton T e2) e2). constructor. apply H2 in H3. 
   inversion H3. 
   {assert(In T (Union T S (Singleton T e1)) e1). apply Union_intror. 
    constructor. apply H1 in H6. inversion H6. subst. inversion H. 
    assert(In T (Intersection T S (Singleton T e1)) e1). constructor; assumption. 
    apply H5 in H7. inversion H7. }
   {subst. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
    split; intros. 
    {assert(In T (Union T S (Singleton T e1)) x). apply Union_introl. assumption. 
     apply H1 in H6. inversion H6. subst. inversion H4. subst. 
     assert(In T (Intersection T S(Singleton T x)) x). constructor; assumption. 
     apply H0 in H7. inversion H7. }
    {inversion H5. }
   }
  }
Qed. 

Theorem AddEqCouple : forall T S e e1 e2, Add T S e = Couple T e1 e2 ->
                                          e = e1 \/ e = e2. 
Proof.
  intros. unfold Add in H. unfoldSetEq H. assert(Ensembles.In T (Union T S (Singleton T e)) e).
  apply Union_intror. constructor. apply H0 in H2. inversion H2. auto. auto. Qed. 

Theorem AddEqSingleton : forall T S e e', Add T S e = Singleton T e' -> e = e'. 
Proof.
  intros. unfold Add in H. apply UnionEqSingleton in H. assumption. Qed. 

End Ensembles.

