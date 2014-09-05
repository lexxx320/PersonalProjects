Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  

Fixpoint sum (l:list nat) :=
  match l with
      |hd::tl => hd + sum tl
      |nil => 0
  end. 

Definition extEq {X:Type} (l1 l2 : list X) := 
  (forall x, In x l1 -> In x l2) /\ (forall x, In x l2 -> In x l2). 

Definition numPartition (l : list nat) (k : nat) : Prop :=
sum l = 2 * k -> exists l1 l2, extEq (l1++l2) l /\ sum l1 = k /\ sum l2 = k. 

Theorem numPart336 : numPartition [3; 3; 6] 6. 
Proof.
  unfold numPartition. intros. exists [3;3]. exists [6]. split. simpl.
  unfold extEq. split; intros; auto. split; auto. 
Qed. 







