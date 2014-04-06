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


End Ensembles.

