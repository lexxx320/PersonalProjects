Require Export List.
Export ListNotations.
Require Export SpecLib. 
Require Export AST. 

Inductive monotone {A:Type} : list (nat * A) -> Prop :=
|mono_twoCons : forall x y v v' l, 
             monotone ((x, v)::l) -> y > x -> monotone((y,v')::(x,v)::l)
|mono_single : forall y v', monotone [(y,v')]
|mono_nill : monotone nil. 





















