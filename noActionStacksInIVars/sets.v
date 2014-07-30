Require Import Coq.Logic.Classical.
Require Import Coq.Sets.Ensembles.

Section Ensembles.

Variable U : Type.

Lemma union_empty_r : forall A,
  Union U A (Empty_set U) = A.
Proof.
  intros A. apply Extensionality_Ensembles.
  split; intros x x_in_one.
  inversion x_in_one as [ _x in_A x_eq | _x false x_eq ].
  auto. inversion false.
  left. auto.
Qed.

Lemma union_empty_l : forall A, Union U (Empty_set U) A = A. 
Proof.
  intros. apply Extensionality_Ensembles. split; intros x x'. 
  inversion x'. inversion H. auto. apply Union_intror. auto. 
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

Theorem pullOut : forall X T t, Ensembles.In X T t -> T = Union X (Subtract X T t) (Singleton X t). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {unfold Subtract. assert(x=t \/ x<>t). apply classic. inversion H1; subst. 
   {apply Union_intror. constructor. }
   {apply Union_introl. constructor. assumption. intros c. inversion c. symmetry in H3. 
    contradiction. }
  }
  {inversion H0; subst.
   {inversion H1; subst. assumption. }
   {inversion H1; subst. assumption. }
  }
Qed. 

Theorem SingletonNeqEmpty : forall X t, Singleton X t = Empty_set X -> False.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inversion H. 
  assert(Ensembles.In X (Singleton X t) t). constructor. subst. apply H0 in H2. inversion H2. Qed. 

Theorem AddNeqEmpty : forall X T t, Add X T t = Empty_set X -> False. 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inversion H. 
  assert(Ensembles.In X (Add X T t) t). apply Union_intror. constructor. apply H0 in H2. inversion H2. 
Qed. 

Theorem CoupleNeqEmpty : forall X t1 t2, Couple X t1 t2 = Empty_set X -> False.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inversion H. 
  assert(Ensembles.In X (Couple X t1 t2) t1). constructor. apply H0 in H2. inversion H2. Qed. 


Hint Constructors Union Couple. 

Theorem coupleUnion : forall X t1 t2, Couple X t1 t2 = Union X (Singleton X t1) (Singleton X t2). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H; subst; auto. }
  {inversion H; subst. inversion H0; subst; auto. inversion H0; subst; auto. }
Qed. 

Theorem UnionSwap : forall X T1 T2 T3,
                      Union X (Union X T1 T2) T3 = Union X (Union X T1 T3) T2. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion  H; subst. inversion H0; subst. constructor. constructor. auto. apply Union_intror. 
  auto. constructor. apply Union_intror. auto. }
  {inversion H; subst. inversion H0; subst. constructor. constructor. auto. 
   apply Union_intror. auto. constructor. apply Union_intror. auto. }
Qed. 

End Ensembles.

