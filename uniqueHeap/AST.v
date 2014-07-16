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
  |spec : trm -> trm -> trm
  |specRun : trm -> trm -> trm (*last trm is the orignal spec term*)
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
      |spec e1 e2 => spec (open k u e1) (open k u e2)
      |specRun e1 e2 => specRun (open k u e1) (open k u e2)
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
|pfst : ptrm -> ptrm
|psnd : ptrm -> ptrm
|pspec : ptrm -> ptrm -> ptrm
|pspecRun : ptrm -> ptrm -> ptrm
|pspecJoin : ptrm -> ptrm -> ptrm
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
      |pfst e => pfst (popen k u e)
      |psnd e => psnd (popen k u e)
      |pspec M N => pspec (popen k u M) (popen k u N)
      |pspecRun e1 e2 => pspecRun (popen k u e1) (popen k u e2)
      |pspecJoin e1 e2 => pspecJoin (popen k u e1) (popen k u e2)
      |_ => t
  end. 

(*Evaluation Contexts*)
Inductive ctxt : Type :=
|appCtxt : ctxt -> trm -> ctxt
|appValCtxt : ctxt -> trm -> ctxt
|pairCtxt : ctxt -> trm -> ctxt
|pairValCtxt : ctxt -> trm -> ctxt
|bindCtxt : ctxt -> trm -> ctxt
|specRunCtxt : ctxt -> trm -> ctxt 
|specJoinCtxt : ctxt -> trm -> ctxt
|handleCtxt : ctxt -> trm -> ctxt
|fstCtxt : ctxt -> ctxt 
|sndCtxt : ctxt -> ctxt
|holeCtxt : ctxt.

Inductive val : trm -> Prop :=
|retVal : forall M, val (ret M)
|raiseVal : forall M, val (raise M)
|lamVal : forall M, val (lambda M)
|pairVal : forall M N, val M -> val N -> val (pair_ M N).

Inductive decompose : trm -> ctxt -> trm -> Prop :=
|decompBind : forall M N E M', ~ val M -> decompose M E M' ->
                               decompose (bind M N) (bindCtxt E N) M'
|decompBindVal : forall M N, val M -> decompose (bind M N) holeCtxt (bind M N)
|decompsSpec : forall M N, decompose (spec M N) holeCtxt (spec M N)
|decompSpecRun : forall M N E M', ~ val M -> decompose M E M' -> 
                               decompose (specRun M N) (specRunCtxt E N) M'
|decompSpecVal : forall M N, val M ->
                             decompose (specRun M N) holeCtxt (specRun M N)
|decompSpecJoin : forall M N E N', val M -> ~val N -> decompose N E N' ->
                                   decompose (specJoin M N) (specJoinCtxt E M) N'
|decompSpecJoinVal : forall M N, val M -> val N -> decompose (specJoin M N) holeCtxt (specJoin M N)
|decompHandle : forall M M' N E, ~val M -> decompose M E M' -> 
                                 decompose (handle M N) (handleCtxt E N) M'
|decompHandleVal : forall M N, val M -> decompose (handle M N) holeCtxt (handle M N)
|decompApp : forall M N M' E, ~val M -> decompose M E M' ->
                              decompose (app M N) (appCtxt E N) M'
|decompAppVal1 : forall M N N' E, val M -> ~val N -> decompose N E N' ->
                                 decompose (app M N) (appValCtxt E M) N'
|decompAppVal2 : forall M N, val M -> val N -> decompose (app M N) holeCtxt (app M N)
|decompPair : forall M N M' E, ~val M -> decompose M E M' ->
                               decompose (pair_ M N) (pairCtxt E N) M'
|decompPairVal : forall M N N' E, val M -> ~val N -> decompose N E N' ->
                                  decompose (pair_ M N) (pairValCtxt E M) N'
|decompFst : forall M E M', ~val M -> decompose M E M' -> 
                            decompose (fst M) (fstCtxt E) M'
|decompFstVal : forall M, val M -> decompose (fst M) holeCtxt (fst M)
|decompSnd : forall M E M', ~val M -> decompose M E M' -> 
                            decompose (snd M) (sndCtxt E) M'
|decompSndVal : forall M, val M -> decompose (snd M) holeCtxt (snd M)
|decompNew : decompose new holeCtxt new
|decompGet : forall i, decompose (get i) holeCtxt (get i)
|decompPut : forall i M, decompose (put i M) holeCtxt (put i M)
|decompFork : forall M, decompose (fork M) holeCtxt (fork M)
.  

Fixpoint fill (c:ctxt) (t:trm) : trm :=
  match c with
      |bindCtxt E N => bind (fill E t) N
      |specRunCtxt E N => specRun (fill E t) N
      |specJoinCtxt E M => specJoin M (fill E t)
      |handleCtxt E N => handle (fill E t) N
      |appCtxt E N => app (fill E t) N
      |appValCtxt E M => app M (fill E t)
      |pairCtxt E N => pair_ (fill E t) N
      |pairValCtxt E M => pair_ M (fill E t)
      |fstCtxt E =>fst (fill E t)
      |sndCtxt E => snd (fill E t)
      |holeCtxt => t
  end. 

Inductive action : Type :=
|rAct : forall x t E, decompose t E (get (fvar x)) ->  action
|wAct : forall x t E M, decompose t E (put (fvar x) M) -> action
|nAct : forall t E, decompose t E new -> id -> action  (*id is the name of the ivar created*)
|fAct : forall t E M, decompose t E (fork M) -> action
|srAct : forall t E M N, decompose t E (spec M N) -> action
|specAct : action
.

Definition actionStack := list action. 
 
Inductive pivar_state : Type :=
|pempty : pivar_state
|pfull : ptrm -> pivar_state.

Inductive ivar_state : Type :=
  |sempty : actionStack -> ivar_state
  |sfull : actionStack -> Ensemble tid -> actionStack -> tid -> trm -> ivar_state. 
(*first spec is who created, second is who wrote*)

