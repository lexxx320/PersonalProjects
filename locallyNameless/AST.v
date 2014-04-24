(*id*) 
Require Import Coq.Init.Datatypes. 
Require Import Coq.Sets.Ensembles. 
Require Import SfLib. 
Definition id := nat.

Inductive tid : Type :=
|Tid : nat * nat -> list (nat * nat) -> tid. 

(*Syntax for speculative semantics*)
Inductive trm : Type := 
  |threadId : tid -> trm
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
  |specReturn : trm -> trm -> trm
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
      |fst e => fst (open k u e)
      |snd e => snd (open k u e)
      |_ => t
  end. 

Inductive term : trm -> Prop :=
|term_threadId : forall t, term (threadId t)
|term_fvar : forall x, term (fvar x)
|term_unit : term unit
|term_pair : forall e1 e2, term e1 -> term e2 -> term (pair_ e1 e2)
|term_lambda : forall L e, (forall x, ~ Ensembles.In id L x -> term (open 0 (fvar x) e)) -> 
                           term (lambda e)
|term_app : forall e1 e2, term e1 -> term e2 -> term (app e1 e2)
|term_ret : forall e, term e -> term (ret e)
|term_bind : forall e1 e2, term e1 -> term e2 -> term (bind e1 e2)
|term_fork : forall e, term e -> term (fork e)
|term_new : term new
|term_put : forall i e, term i -> term e -> term (put i e)
|term_get : forall i, term i -> term (get i)
|term_raise : forall e1, term e1 -> term (raise e1)
|term_handle : forall e1 e2, term e1 -> term e2 -> term (handle e1 e2)
|term_done : forall e, term e -> term (done e)
|term_spec : forall e1 e2, term e1 -> term e2 -> term (spec e1 e2)
|term_specReturn : forall e1 e2, term e1 -> term e2 -> term (specReturn e1 e2)
|term_fst : forall e, term e -> term (fst e)
|term_snd : forall e, term e -> term (snd e)
.

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

Inductive pterm : ptrm -> Prop :=
|pterm_fvar : forall x, pterm (pfvar x)
|pterm_unit : pterm punit
|pterm_pair : forall e1 e2, pterm e1 -> pterm e2 -> pterm (ppair e1 e2)
|pterm_lambda : forall L e, (forall x, ~ Ensembles.In id L x -> pterm (popen 0 (pfvar x) e)) ->
                            pterm (plambda e)
|pterm_app : forall e1 e2, pterm e1 -> pterm e2 -> pterm (papp e1 e2)
|pterm_ret : forall e, pterm e -> pterm (pret e)
|pterm_bind : forall e1 e2, pterm e1 -> pterm e2 -> pterm (pbind e1 e2)
|pterm_fork : forall e, pterm e -> pterm (pfork e)
|pterm_new : pterm pnew
|pterm_put : forall i e, pterm i -> pterm e -> pterm (pput i e)
|pterm_get : forall i, pterm i -> pterm (pget i)
|pterm_raise : forall e, pterm e -> pterm (praise e)
|pterm_handle : forall e1 e2, pterm e1 -> pterm e2 -> pterm (phandle e1 e2)
|pterm_done : forall e, pterm e -> pterm (pdone e)
|pterm_fst : forall e, pterm e -> pterm (pfst e)
|pterm_snd : forall e, pterm e -> pterm (psnd e)
.

Inductive action : Type :=
  |rAct : id -> tid -> trm -> action
  |wAct : id -> tid -> trm -> action
  |cAct : id -> tid -> trm -> action
  |sAct : tid -> trm -> action
  |fAct : tid -> tid -> trm -> action  (*first tid is the thread id of the forked thread*)
  |joinAct : action
  |specAct : action.

Definition specStack := list action. 

Inductive pivar_state : Type :=
|pempty : pivar_state
|pfull : ptrm -> pivar_state.

Inductive ivar_state : Type :=
  |sempty : specStack -> ivar_state
  |sfull : specStack -> list tid -> specStack -> tid -> trm -> ivar_state. 
(*first spec is who created, second is who wrote*)

