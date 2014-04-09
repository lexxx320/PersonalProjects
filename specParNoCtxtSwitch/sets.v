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

Ltac unfoldSetEq :=
  match goal with
      |H : ?S1 = ?S2 |- _ => try apply eqImpliesSameSet in H; unfold Same_set in H;
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


Ltac invertSetEq := 
  match goal with
      |H : Empty_set ?T = Singleton ?T ?e |- _ => 
       apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H;
       inversion H as [sameSet1 sameSet2]; 
       assert(Hin:In T (Singleton T e) e) by auto;
       apply sameSet2 in Hin; inversion Hin
      |H : Empty_set ?T = Couple ?T ?e1 ?e2 |- _ =>
       apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H;
       inversion H as [sameSet1 sameSet2];
       assert(Hin:In T (Couple T e1 e2) e1) by auto; apply sameSet2 in Hin;
       inversion Hin
      |H:Singleton ?T ?e = Empty_set ?T |- _ => symmetry in H; invertSetEq
      |H:Couple ?T ?e1 ?e2 = Empty_set ?T |- _ => symmetry in H; invertSetEq
      |H:Singleton ?T ?e1 = Couple ?T ?e2 ?e3 |- _ => apply SingleEqCouple in H
      |H:Couple ?T ?e2 ?e3 = Singleton ?T ?e1 |- _ => symmetry in H; invertSetEq
  end. 



End Ensembles.

