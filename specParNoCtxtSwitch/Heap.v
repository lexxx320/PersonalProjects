Require Export List.
Export ListNotations.
Require Export SpecLib. 
Require Export AST. 


Open Scope type_scope. 
Definition heap (T : Type) :=  list (id * T). 

Fixpoint heap_lookup {T : Type} (i : id) (h : heap T) := 
  match h with
    |(n, v)::h' => if beq_nat i n then Some v else heap_lookup i h'
    |nil => None
  end.

Definition extend {T : Type} v (heap : heap T) := 
  match heap with
    |(n, v') :: h' => (S n, (S n, v) :: (n, v') :: h')
    |nil => (1, (1, v) :: nil)
  end.

Fixpoint replace {T:Type} i v (h : heap T) :=
  match h with
      |(i', v') :: h' => if beq_nat i i' 
                         then (i, v) :: h' 
                         else (i', v') :: replace i v h'
      |nil => nil
  end.

Fixpoint remove {T:Type} (h : heap T) x :=
  match h with
      |(x', v')::h' => if beq_nat x x' then h' else (x', v')::remove h' x
      |nil => nil
  end.

Theorem heapUpdateNeq : forall (T:Type) h i (v v' : T),
                          heap_lookup i h = Some v ->
                          v <> v' -> h <> replace i v' h. 
Proof.
  intros. unfold not in *. intros. unfold replace in H1. 
  induction h. 
  {inversion H. }
  {destruct a. simpl in *. destruct (beq_nat i i0). 
   {inversion H. subst. inversion H1. contradiction. }
   {inversion H1. apply IHh in H3. assumption. assumption. }
  }
Qed. 