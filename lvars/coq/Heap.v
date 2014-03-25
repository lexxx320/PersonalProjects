Require Export List.
Export ListNotations.
Require Export SfLib. 
Require Export AST. 


Open Scope type_scope. 
Definition heap : Type :=  list (id * ivar_state). 

Fixpoint heap_lookup (i : id) (h : heap) := 
  match h with
    |(n, v)::h' => if beq_nat i n then v else heap_lookup i h'
    |nil => none
  end.

Fixpoint extend v (heap : heap) := 
  match heap with
    |(n, v') :: h' => (S n, v) :: (n, v') :: h'
    |nil => (1, v) :: nil
  end.

Fixpoint replace i v (h : heap) :=
  match h with
      |(i', v') :: h' => if beq_nat i i' then (i, v) :: h' else (i', v') :: replace i v h'
      |nil => nil
  end.

Fixpoint remove (h : heap) x :=
  match h with
      |(x', v')::h' => if beq_nat x x' then h' else (x', v')::remove h' x
      |nil => nil
  end.