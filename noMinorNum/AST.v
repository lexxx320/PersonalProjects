Require Import Coq.Init.Datatypes. 
Require Import Coq.Sets.Ensembles. 
Require Import SfLib. 
Definition id := nat.

Definition tid := list nat.  

Axiom classicT : forall (P : Prop), {P} + {~ P}.

Notation "'If' P 'then' v1 'else' v2" := 
  (if (classicT P) then v1 else v2)
  (at level 200, right associativity) : type_scope.

(*Syntax for speculative semantics*)
Inductive trm : Type := 
  |fvar : id -> trm
  |bvar : id -> trm
  |unit : trm
  |pair_ : trm -> trm -> trm
  |lambda : trm -> trm
  |app : trm -> trm -> trm
  |ret : trm -> trm
  |bind : trm -> trm -> trm
  |fork : trm -> trm
  |new : trm
  |put : trm -> trm -> trm
  |get : trm -> trm
  |raise : trm -> trm
  |handle : trm -> trm -> trm
  |done : trm -> trm
  |spec : trm -> trm -> trm
  |specReturn : trm -> trm -> trm (*last trm is the orignal spec term*)
  |specJoin : trm -> trm -> trm
  |fst : trm -> trm
  |snd : trm -> trm
.

Fixpoint open (k:nat) (u:trm) (t:trm) : trm :=
  match t with
      |bvar i => if beq_nat k i then u else t
      |pair_ e1 e2 => pair_ (open k u e1) (open k u e2)
      |lambda e => lambda (open (S k) u e)
      |app e1 e2 => app (open k u e1) (open k u e2)
      |ret e => ret (open k u e)
      |bind e1 e2 => bind (open k u e1) (open k u e2)
      |fork e => fork (open k u e)
      |put i e => put (open k u i) (open k u e)
      |get i => get (open k u i)
      |raise e => raise (open k u e)
      |handle e1 e2 => handle (open k u e1) (open k u e2)
      |done e => done (open k u e)
      |spec e1 e2 => spec (open k u e1) (open k u e2)
      |specReturn e1 e2 => specReturn (open k u e1) (open k u e2)
      |specJoin e1 e2 => specJoin (open k u e1) (open k u e2)
      |fst e => fst (open k u e)
      |snd e => snd (open k u e)
      |_ => t
  end. 


(*Syntax for non-speculative Par Monad semantics (uses locally nameless cofinite quantification*)
Inductive ptrm : Type :=
|pfvar : id -> ptrm
|pbvar : id -> ptrm
|punit : ptrm
|ppair : ptrm -> ptrm -> ptrm
|plambda : ptrm -> ptrm
|papp : ptrm -> ptrm -> ptrm
|pret : ptrm -> ptrm
|pbind : ptrm -> ptrm -> ptrm
|pfork : ptrm -> ptrm
|pnew : ptrm
|pput : ptrm -> ptrm -> ptrm
|pget : ptrm -> ptrm
|praise : ptrm -> ptrm
|phandle : ptrm -> ptrm -> ptrm
|pdone : ptrm -> ptrm
|pfst : ptrm -> ptrm
|psnd : ptrm -> ptrm
.

Fixpoint popen (k:nat) (u:ptrm) (t:ptrm) : ptrm :=
  match t with
      |pbvar i => if beq_nat k i then u else t
      |ppair e1 e2 => ppair (popen k u e1) (popen k u e2)
      |plambda e => plambda (popen  (S k) u e)
      |papp e1 e2 => papp (popen k u e1) (popen k u e2)
      |pret e => pret (popen k u e)
      |pbind e1 e2 => pbind (popen k u e1) (popen k u e2)
      |pfork e => pfork (popen k u e)
      |pput i e => pput (popen k u i) (popen k u e)
      |pget i => pget (popen k u i)
      |praise e => praise (popen k u e)
      |phandle e1 e2 => phandle (popen k u e1) (popen k u e2)
      |pdone e => pdone (popen k u e)
      |pfst e => pfst (popen k u e)
      |psnd e => psnd (popen k u e)
      |_ => t
  end. 

Inductive action : Type :=
  |rAct : id -> trm -> action  (*ivar written, step count, and current term*)
  |wAct : id -> trm -> action
  |cAct : id -> trm -> action
  |specRetAct : trm -> action  (* thread executing commit branch of spec*)
  |fAct : trm -> action 
  |specAct : action
.

Definition specStack := list action. 

Inductive pivar_state : Type :=
|pempty : pivar_state
|pfull : ptrm -> pivar_state.

Inductive ivar_state : Type :=
  |sempty : specStack -> ivar_state
  |sfull : specStack -> list tid -> specStack -> tid -> trm -> ivar_state. 
(*first spec is who created, second is who wrote*)

