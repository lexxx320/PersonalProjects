Require Import MSets.
Require Import MSetList. 


Print OrderedTypeWithLeibniz.

Module OWL.
  Definition t := nat.
  Definition eq :=  @eq t.
  Instance eq_equiv : Equivalence eq.
  Definition lt := lt.
  Instance lt_strorder : StrictOrder lt. 
  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
   now unfold eq; split; subst.
  Qed.
  SearchPattern (nat -> nat -> comparison).
  Definition compare := Compare_dec.nat_compare.
  SearchAbout CompSpec.
  (*So, nothing here on nat*)
  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
   SearchPattern (forall x y, Compare_dec.nat_compare x y = _ -> _).
   intros; case_eq (compare x y); constructor.
     now apply Compare_dec.nat_compare_eq.
    now apply Compare_dec.nat_compare_Lt_lt.
   now apply Compare_dec.nat_compare_Gt_gt.
  Qed.
  SearchPattern (forall (a b:nat), {a=b}+{a<>b}).
  Definition eq_dec := Peano_dec.eq_nat_dec.
  Definition eq_leibniz a b (H:eq a b) := H.
   
End OWL.

Module NatSet := MakeWithLeibniz OWL.

Inductive exemple :=
| A : exemple
| B : NatSet.t -> exemple
| C : NatSet.t -> bool -> exemple.

Definition eq_dec : forall (a b:exemple), {a=b}+{a<>b}.
 intros; decide equality.
   destruct (NatSet.eq_dec t t0).
    now left; apply NatSet.eq_leibniz.
   right; intro; apply n; clear n; subst.
   reflexivity.
  apply bool_dec.
 destruct (NatSet.eq_dec t t0).
  now left; apply NatSet.eq_leibniz.
 right; intro; apply n; clear n; subst.
 reflexivity.
Defined.
