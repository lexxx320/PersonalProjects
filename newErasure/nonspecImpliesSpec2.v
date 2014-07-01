Require Import NonSpec.  
Require Import Spec.  
Require Import SfLib. 
Require Import AST. 
Require Import Heap. 
Require Import Coq.Sets.Ensembles.
Require Import sets. 
Require Import Powerset_facts. 
Require Import erasure. 

Inductive uneraseHeap : pHeap -> sHeap -> Prop :=
|uneraseConsFull : forall M M' i H H', 
                  eraseTerm M tEmptySet M' -> uneraseHeap H' H ->
                  uneraseHeap((i, pfull M')::H') ((i, sfull nil nil nil (Tid(0,0)nil) M)::H)
|uneraseConsEmpty : forall i H H', uneraseHeap H' H -> uneraseHeap ((i,pempty)::H') ((i,sempty nil)::H)
|uneraseNil : uneraseHeap nil nil
.

Theorem eHeap' : forall H, exists H', uneraseHeap H H'. 
Proof.
  induction H; intros. 
  {exists nil. constructor. }
  {inversion IHlist. destruct a. destruct p. 
   {exists ((i, sempty nil)::x). constructor. assumption. }
   {assert(exists M, eraseTerm M tEmptySet p). apply eTerm. inversion H1. 
    exists((i, sfull nil nil nil (Tid(0,0)nil) x0)::x). constructor; assumption. }
  }
Qed. 

Theorem eraseSpeculatedHeap : forall H H', uneraseHeap H' H -> eraseHeap H H'.
Proof.
  intros. induction H0; auto. Qed. 

Inductive uneraseTerm : ptrm -> trm -> Prop :=
|uneraseFVar : forall i, uneraseTerm (pfvar i) (fvar i)
|uneraseBVar : forall i, uneraseTerm (pbvar i) (bvar i)
|uneraseUnit : uneraseTerm punit unit
|unerasePair : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                     uneraseTerm (ppair e1' e2') (pair_ e1 e2)
|uneraseLambda : forall e e', uneraseTerm e' e -> uneraseTerm (plambda e') (lambda e)
|uneraseApp : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                    uneraseTerm (papp e1' e2') (app e1 e2)
|uneraseRet : forall e e', uneraseTerm e' e -> uneraseTerm (pret e') (ret e)
|uneraseBind : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                     uneraseTerm (pbind e1' e2') (bind e1 e2)
|uneraseFork : forall e e', uneraseTerm e' e -> uneraseTerm (pfork e') (fork e)
|uneraseNew : uneraseTerm pnew new
|unerasePut : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                    uneraseTerm (pput e1' e2') (put e1 e2)
|uneraseGet : forall e e', uneraseTerm e' e -> uneraseTerm (pget e') (get e)
|uneraseRaise : forall e e', uneraseTerm e' e -> uneraseTerm (praise e') (raise e)
|uneraseHandle : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                       uneraseTerm (phandle e1' e2') (handle e1 e2)
|uneraseDone : forall e e', uneraseTerm e' e -> uneraseTerm (pdone e') (done e)
|uneraseFst : forall e e', uneraseTerm e' e -> uneraseTerm (pfst e') (fst e)
|uneraseSnd : forall e e', uneraseTerm e' e -> uneraseTerm (psnd e') (snd e)
.

Inductive uneraseCtxt : pctxt -> ctxt -> Prop :=
|uneraseBindCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                     uneraseCtxt (pbindCtxt E' N') (bindCtxt E N)
|uneraseHandleCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (phandleCtxt E' N') (handleCtxt E N)
|uneraseAppCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (pappCtxt E' N') (appCtxt E N)
|uneraseAppValCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (pappValCtxt E' N') (appValCtxt E N)
|unerasePairCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (ppairCtxt E' N') (pairCtxt E N)
|unerasePairValCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (ppairValCtxt E' N') (pairValCtxt E N)
|uneraseFstCtxt : forall E E', uneraseCtxt E' E -> uneraseCtxt (pfstCtxt E') (fstCtxt E)
|uneraseSndCtxt : forall E E', uneraseCtxt E' E -> uneraseCtxt (psndCtxt E') (sndCtxt E)
|uneraseHoleCtxt : uneraseCtxt pholeCtxt holeCtxt
.

Hint Constructors uneraseTerm uneraseCtxt. 
 
Theorem eUneraseTerm : forall e', exists e, uneraseTerm e' e.
Proof.
  induction e'; try solve[repeat econstructor]; try solve[invertExists; econstructor; eauto].  
Qed. 

Theorem eUneraseCtxt : forall E', exists E, uneraseCtxt E' E. 
Proof.
  induction E'; try solve[assert(exists p', uneraseTerm p p') by apply eUneraseTerm; invertExists; 
  econstructor; eauto]; try solve[invertExists; econstructor; eauto]. 
  econstructor. eauto. Qed. 



Inductive uneraseThread : ptrm -> thread -> Prop :=
|unerase_thread : forall M M', uneraseTerm M' M -> (forall tid s2, uneraseThread M' (tid,nil,s2,M))
. 

Theorem eUneraseThread : forall t, exists tid s1 s2 M, uneraseThread t (tid,s1,s2,M). 
Proof.
  induction t; try solve[repeat econstructor]; try solve[
  invertHyp; inversion H0; inversion H1; subst; exists (Tid(0,0)nil); exists nil;
   exists nil; repeat econstructor; eauto].   
  Grab Existential Variables. repeat constructor. repeat constructor. repeat constructor.
  repeat constructor. repeat constructor. repeat constructor. repeat constructor.
  repeat constructor. Qed. 
   

Theorem uneraseTermDeterminism : forall M M' M'', uneraseTerm M M' -> uneraseTerm M M'' -> M' = M''. 
Proof.
  intros. generalize dependent M''. induction H; intros; try solve[inversion H0; subst; auto];   
  try solve[inversion H1; subst; repeat match goal with
     |H:forall M, uneraseTerm ?e1 M -> ?x, H':uneraseTerm ?e1 ?z |- _ => apply H in H'; clear H
  end; subst; auto];
  try solve[inversion H0; subst; repeat match goal with
     |H:forall M, uneraseTerm ?e1 M -> ?x, H':uneraseTerm ?e1 ?z |- _ => apply H in H'; clear H
  end; subst; auto]. 
Qed.   

Inductive unerasePool (T:pPool) : pool :=
|unerase_pool : forall M' t, In ptrm T M' -> uneraseThread M' t ->
                               In thread (unerasePool T) t. 

Theorem eErasePool : forall T, (exists x, Ensembles.In ptrm T x) ->  
                                  exists y, Ensembles.In thread (unerasePool T) y.
Proof.
  intros. inversion H. assert(exists tid s1 s2 M, uneraseThread x (tid,s1,s2,M)). apply eUneraseThread. 
  invertHyp. econstructor. econstructor. eapply H0. eassumption. Qed. 

Theorem uneraseFill : forall E E' e e', uneraseCtxt E' E -> uneraseTerm e' e -> 
                                        uneraseTerm (pfill E' e') (fill E e).
Proof.
  intros. generalize dependent e. generalize dependent e'. induction H; intros; auto; 
  try solve[simpl; constructor; auto]. Qed. 

Ltac unerase e := try(assert(exists e', uneraseCtxt e e') by apply eUneraseCtxt);
                 try(assert(exists e', uneraseTerm e e') by apply eUneraseTerm); invertHyp. 

Ltac rewriteUnion :=
  match goal with
      | |- unerasePool ?t = tUnion ?x ?y => replace (unerasePool t) with (tUnion tEmptySet (unerasePool t))
      | |- tUnion tEmptySet ?x = ?y => unfold tUnion; rewrite Union_commutative; rewrite union_empty
  end.  

Ltac proveDisjoint :=
  unfold tSingleton in *; unfold tEmptySet;
  match goal with
      | |- Disjoint ?T ?x (Empty_set ?T) => constructor; unfold not; intros c contra; 
                                            inversion contra as[IN1 IN2 IN3]; inversion IN3                          
      | |- Disjoint ?T (Empty_set ?T) ?x => constructor; unfold not; intros c contra; 
                                            inversion contra as[IN1 IN2]; inversion IN2
  end. 

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' H,
                               uneraseHeap PH H -> pstep PH PT pt (pOK PH' PT pt') ->
                               exists H' t, multistep H (unerasePool PT) (unerasePool pt) 
                                         (OK H' (unerasePool PT) t) /\ erasePool t pt'. 
Proof.
  intros. inversion H1; subst. 
  {exists H. assert(exists E', uneraseCtxt E E'). apply eUneraseCtxt. invertExists. 
   assert(exists e', uneraseTerm e e'). apply eUneraseTerm. assert(exists arg', uneraseTerm arg arg').
   apply eUneraseTerm. invertExists. 
   exists (tSingleton(Tid(0,0)nil,nil,nil, fill x (open 0 x0 x1))). 
   split. econstructor. rewriteUnion. auto. rewriteUnion; auto. proveDisjoint. 
   

rewrite union_empty. 

