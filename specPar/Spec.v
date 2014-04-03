Require Import AST. 
Require Import Heap. 

Require Import Coq.Sets.Ensembles. 

Fixpoint bump (t : tid) : tid := 
  match t with
    |(maj, min) :: t' => (maj, S min) :: t'
    |nil => nil
  end.
 
Definition sHeap := heap (ivar_state). 

Inductive ctxt : (term -> term) -> Prop :=
|bindCtxt : forall N c, ctxt c -> ctxt (fun M => bind (c M) N)
|specReturnCtxt : forall N c, ctxt c -> ctxt (fun M => specReturn M N)
|handleCtxt : forall N c, ctxt c -> ctxt (fun M => handle M N)
|hole : forall c, ctxt c -> ctxt (fun M => c M)
.
Hint Constructors ctxt. 

Definition thread := tid * specStack * specStack * term. 

Definition pool := Ensemble thread.

(*substitute e for x in t ([x := e]t)*)
Fixpoint subst (e:term) (x:id) (t:term) : term :=
  match t with
      |threadId tid => threadId tid
      |ivar y => ivar y (*not sure if this is right*)
      |unit => unit
      |pair_ e1 e2 => pair_ (subst e x e1) (subst e x e2)
      |var y => if beq_nat x y then e else t
      |lambda y eb => if beq_nat x y then t else lambda y (subst e x eb)
      |AST.app ef ea => app (subst e x ef) (subst e x ea)
      |ret M => ret (subst e x M)
      |bind M N => bind (subst e x M) (subst e x N)
      |fork M => fork (subst e x M)
      |new => new
      |put x M => put x (subst e x M)
      |get i => get i
      |raise M => raise (subst e x M)
      |handle M N => handle (subst e x M) (subst e x N)
      |done M => done (subst e x M)
      |fst M => fst (subst e x M)
      |snd M => snd (subst e x M)
      |spec M N => spec (subst e x M) (subst e x N)
      |specReturn M N => specReturn (subst e x M) (subst e x N)
  end. 

Fixpoint largeStep (t:term) : term :=
  match t with
    |pair e1 e2 => pair (largeStep e1) (largeStep e2)
    |app e1 e2 => match largeStep e1, largeStep e2 with
                      |lambda x b, arg => subst arg x b
                      |e1', e2' => app e1' e2'
                  end
    |fst M => match largeStep M with
                  |pair v1 v2 => v1
                  |e' => e'
              end
    |snd M => match largeStep M with
                  |pair v1 v2 => v2
                  |e' => e'
              end
    |t => t
  end. 

Inductive step : sHeap -> pool -> sHeap -> pool -> Prop :=
|Bind : forall tid t h E T N M s1 s2 ,
          ctxt E -> ~(In thread T t) -> t = (tid, s1, s2, E (bind (ret M) N)) ->
          step h (Add thread T t) h (Add thread T (bump tid, s1, s2, E(AST.app N M)))
|Eval : 
.






