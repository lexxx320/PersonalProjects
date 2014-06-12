Require Import NonSpec.  
Require Import Spec.  
Require Import SfLib. 
Require Import AST. 
Require Import Heap. 
Require Import Coq.Sets.Ensembles.
Require Import sets. 
Require Import Powerset_facts. 
Require Import erasure. 

Ltac applyHyp :=
  match goal with
      |H : forall a : _, ?X -> ?Y, H' : ?Z |- _ => apply H in H'
  end. 
 
Axiom uniqueThreadPool : forall T tid t t', 
                           thread_lookup T tid t -> thread_lookup T tid t' -> t = t'. 

Theorem lastElementEq : forall (T:Type) s1 s2 (e1 e2 : T), s1 ++ [e1] = s2 ++ [e2] -> e1 = e2. 
Proof.
  intros. generalize dependent s2. induction s1; intros. 
  {destruct s2. inversion H. reflexivity. inversion H. destruct s2; inversion H2. }
  {destruct s2. inversion H. destruct s1; inversion H2. inversion H. apply IHs1 in H2.
   assumption. } Qed. 


Ltac copy H := 
  match type of H with
      |?X => assert(X) by apply H
  end. 

Ltac cleanup := unfold tSingleton in *; unfold tCouple in *; unfold tAdd in *; unfold tIn in *; 
                unfold pSingleton in *; try subst;
  repeat(match goal with
           |H : ?x = ?x |- _ => clear H
           |H : In ?T (Singleton ?T ?x) ?x |- _ => clear H
           |H : In ?T (Singleton ?T ?x) ?y |- _ => inversion H; try subst
           |H : Singleton ?T ?x = Singleton ?T ?y |- _ => apply SingletonEq in H; inversion H; try subst
           |H : Singleton ?T ?x = Couple ?T ?y ?z |- _ => apply SingleEqCouple in H; inversion H; try subst
           |H : Couple ?T ?y ?z = Singleton ?t ?x |- _ => symmetry in H
         end). 

Ltac invertHyp :=
  match goal with
      |H : exists e : _, ?x |- _ => inversion H; clear H; subst; try invertHyp
      |H : ?x /\ ?y |- _ => inversion H; clear H; subst; try invertHyp
      |H : eraseTerm ?M ?T ?t, H' : eraseTerm ?M ?T ?t' |- _ => 
       eapply termErasureDeterminism in H; try eassumption; subst; try invertHyp
      |H : eraseContext ?E ?T ?E1, H' : eraseContext ?E ?T ?E2 |- _ => 
       eapply ctxtErasureDeterminism in H; try eassumption; subst; try invertHyp
  end. 

Ltac instantiateHeap :=
  match goal with
      |H:pstep ?H ?T ?t (pOK ?H ?T' ?t') |- _ => assert(EH:exists H', eraseHeap H' H) by apply eHeap; 
                                          inversion EH as[newHeap heapHyp]; exists newHeap;
                                          exists newHeap
      |H:pstep ?H ?T ?t (pOK ?H' ?T' ?t') |- _ => assert(EH:exists H', eraseHeap H' H) by apply eHeap;
                                          inversion EH as[newHeap heapHyp]; exists newHeap
  end.  

Ltac instantiatePool :=
  match goal with
      |H:pstep ?h ?T ?t (pOK ?h' ?T ?t') |- _ => assert(PHYP:exists T', erasePool T' T) by apply ePool; 
                                          inversion PHYP as [SpecPool specPoolHyp]; exists SpecPool
  end. 

Ltac eraseEq := 
  match goal with
      | |- erasePool ?T ?T' => assert(ERASEHYP:erasePoolAux T = T') by
                                (apply termErasePoolErase; eapply eraseFill; eauto); rewrite <- ERASEHYP
      | |- erasePool ?T ?T' => assert(ERASEHYP:erasePoolAux T = T')
  end.

Theorem eraseHeapDependentReader : forall H H', eraseHeap H H' -> 
                                     forall  x w M ds t, heap_lookup x H = Some(sfull nil ds nil w M) ->
                                     eraseHeap (replace x (sfull nil (t::ds) nil w M) H) H'. 
Proof.
  intros H H' U. induction U; intros;
  try solve[simpl in *; destruct (beq_nat x i); inversion H; eapply IHU in H; constructor; eassumption]. 
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H0; subst. apply beq_nat_true in eq. 
   subst. constructor. assumption. assumption. constructor. eapply IHU. assumption. assumption. }
  {simpl in *. inversion H. }
Qed. 

Ltac proveDisjoint :=
  unfold tSingleton in *;
  match goal with
      | |- Disjoint ?T ?x (Empty_set ?T) => constructor; unfold not; intros c contra; 
                                            inversion contra as[IN1 IN2 IN3]; inversion IN3                          
      | |- Disjoint ?T (Empty_set ?T) ?x => constructor; unfold not; intros c contra; 
                                            inversion contra as[IN1 IN2]; inversion IN2
  end. 


Inductive speculateHeap : pHeap -> sHeap -> Prop :=
|specConsFull : forall M M' i H H', 
                  eraseTerm M tEmptySet M' -> speculateHeap H' H ->
                  speculateHeap((i, pfull M')::H') ((i, sfull nil nil nil (Tid(0,0)nil) M)::H)
|specConsEmpty : forall i H H', speculateHeap H' H -> speculateHeap ((i,pempty)::H') ((i,sempty nil)::H)
|specNil : speculateHeap nil nil
.

Theorem eHeap' : forall H, exists H', speculateHeap H H'. 
Proof.
  induction H; intros. 
  {exists nil. constructor. }
  {inversion IHlist. destruct a. destruct p. 
   {exists ((i, sempty nil)::x). constructor. assumption. }
   {assert(exists M, eraseTerm M tEmptySet p). apply eTerm. inversion H1. 
    exists((i, sfull nil nil nil (Tid(0,0)nil) x0)::x). constructor; assumption. }
  }
Qed. 

Theorem termErasePoolCouple : forall tid tid' M1 M2 M1' M2' s2 s2',
                                eraseTerm M1 tEmptySet M1' -> eraseTerm M2 tEmptySet M2' ->
                                erasePoolAux(tCouple (tid,nil,s2,M1)(tid',nil,s2',M2)) = Couple ptrm M1' M2'.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H1. inversion H2. inversion H6; subst. 
   {inversion H7; subst; clear H7; inversion H3; subst;
                                   match goal with
                                       |H:[]=?x++[?y] |- _ => destruct x; inversion H
                                       |_ => idtac
                                   end.
    {inversion H4; subst. eapply termEraseDifferentPools with (M1:=M1')(M2:=x) in H. rewrite <- H. 
     constructor. eassumption. }
   }
   {inversion H7; subst; clear H7. inversion H3;
                                   match goal with
                                       |H:[] = ?x++[?y] |- _ => destruct x; inversion H
                                       |_ => idtac
                                   end. 
    {subst. inversion H4; subst. eapply termEraseDifferentPools with(M1:=M2')(M2:=x) in H0. 
     subst. constructor. eassumption. }
   }
  }
  {inversion H1; subst. destruct tid. destruct p.  econstructor. econstructor. 
   econstructor. reflexivity. econstructor. eapply eraseWeakening in H. eassumption. 
   constructor. destruct tid'. destruct p. econstructor. econstructor. econstructor. 
   reflexivity. econstructor. eapply eraseWeakening in H0. eassumption. constructor. }
Qed. 

Theorem eraseSpeculatedHeap : forall H H', speculateHeap H' H -> eraseHeap H H'.
Proof.
  intros. induction H0; auto. Qed. 

Theorem eraseReplaceSpecHeap : forall H H', 
                                 speculateHeap H' H -> forall x M M' tid , eraseTerm M tEmptySet M' ->
                                 eraseHeap (replace x (sfull nil nil nil tid M)H)
                                            (replace x (pfull M') H').
Proof.
  intros H H' U. induction U; intros. 
  {simpl in *. destruct (beq_nat x i) eqn:eq. 
   {apply eraseSpeculatedHeap in U. auto. }
   {constructor. eapply IHU. assumption. assumption. }
  }
  {simpl in *. destruct (beq_nat x i). 
   {constructor. apply eraseSpeculatedHeap in U. assumption. assumption. }
    {constructor. eapply IHU; auto. }
  }
  {simpl. constructor. }
Qed. 

Theorem lookupSpeculatedHeapFull : forall H H',
                                     speculateHeap H' H -> forall x M',
                                     heap_lookup x H' = Some(pfull M') ->
                                     exists M, eraseTerm M tEmptySet M' /\ 
                                     heap_lookup x H = Some(sfull nil nil nil (Tid(0,0)nil) M).
Proof.
  intros H H' U. induction U; intros. 
  {simpl in *. destruct(beq_nat x i). 
   {inversion H1; subst. exists M. split; auto. }
   {apply IHU in H1. invertHyp. exists x0. split; auto. }
  }
  {simpl in *. destruct (beq_nat x i). 
   {inversion H0. }{apply IHU in H0. invertHyp. exists x0. split; auto. }
  }
  {simpl in *. inversion H. }
Qed. 

Theorem lookupSpeculatedHeapEmpty : forall H H', 
                                      speculateHeap H' H -> forall x,
                                      heap_lookup x H' = Some pempty ->
                                      heap_lookup x H = Some (sempty nil). 
Proof.
  intros H H' U. induction U; intros. 
  {simpl in *. destruct (beq_nat x i). inversion H1. apply IHU in H1. assumption. }
  {simpl in *. destruct (beq_nat x i). reflexivity. apply IHU. assumption. }
  {simpl in *. inversion H. }
Qed. 

Theorem eraseExtended : forall H H' EH EH' i' i'', speculateHeap H' H -> (i', EH') = extend pempty H' ->
                                     (i'', EH) = extend (sempty nil) H -> eraseHeap EH EH' /\ i' = i''. 
Proof.
  intros. induction H0. 
  {simpl in *. inversion H1; inversion H2; subst. cleanup. constructor. constructor. constructor. 
   apply eraseSpeculatedHeap. assumption. assumption. reflexivity. }
  {simpl in *. inversion H1; inversion H2; subst. cleanup. repeat constructor.
   apply eraseSpeculatedHeap; auto. }
  {simpl in *. inversion H1; inversion H2; cleanup. repeat constructor. }
Qed. 

Theorem eraseFill' : forall E e E' e' T, eraseTerm e T e' -> eraseContext E T E' ->
                                       eraseTerm (fill E e) T (pfill E' e').
Proof.
  intros. generalize dependent e. generalize dependent e'. induction H0; intros; try solve[simpl; auto]. 
  {simpl. econstructor. apply IHeraseContext. assumption. reflexivity. eassumption. 
   eassumption. }
Qed. 

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

Theorem eraseOpen : forall e1 e2 e1' e2' T n, eraseTerm e1 T e1' -> eraseTerm e2 T e2' ->
                                              eraseTerm (open n e2 e1) T (popen n e2' e1'). 
Proof.
  induction e1; intros; try solve[inversion H; subst; auto];
  try solve[inversion H; subst; simpl; constructor; apply IHe1; auto]; 
  try solve[inversion H; subst; simpl; constructor; [apply IHe1_1; auto| apply IHe1_2; auto]].
  {inversion H; subst. simpl. destruct (beq_nat n i); auto. }
  {inversion H; subst. simpl. constructor. apply IHe1_2; auto. apply IHe1_1; auto. }
  {inversion H; subst. simpl. replace  (popen (S n) e2' (incBV 1 e2'0)) with (incBV 1 (popen n e2' e2'0)). 
   constructor. apply IHe1_1. assumption. assumption. admit. admit. }
  {inversion H; subst. admit. }
Qed. 

Theorem pvalImpliesVal : forall e T e', eraseTerm e T e' -> pval e' = true -> val e = true. 
Proof.
  intros. induction H; auto. 
  {simpl. apply andb_true_iff. simpl in H0. apply andb_true_iff in H0. inversion H0. 
   split. apply IHeraseTerm1. auto. apply IHeraseTerm2; auto. }
Qed. 

Theorem decomposeVal : forall E e, ctxtWF e E -> val e = true -> decompose (fill E e) E e. 
Proof.
  intros. induction H; try solve[simpl; constructor; auto]. Qed. 

Ltac instantiateContext := 
  match goal with 
      |H:pdecompose ?t (pappValCtxt ?E ?N) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt; 
       assert(NHyp:exists N', uneraseTerm N N') by apply eUneraseTerm; 
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
      |H:pdecompose ?t (pfstCtxt ?E) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt; 
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
      |H:pdecompose ?t (psndCtxt ?E) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt; 
         assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
      |H:pdecompose ?t (pbindCtxt ?E ?N) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt;
       assert(NHyp:exists N', uneraseTerm N N') by apply eUneraseTerm; 
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
    |H:pdecompose ?t (phandleCtxt ?E ?N) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt;
       assert(NHyp:exists N', uneraseTerm N N') by apply eUneraseTerm; 
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
      |H:pdecompose ?t ?E ?e |- _ =>
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt;
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
  end.

Theorem eraseUneraseTerm : forall e e', uneraseTerm e' e -> eraseTerm e tEmptySet e'. 
Proof.
  intros. induction H; auto. Qed.

Hint Resolve eraseUneraseTerm.  

Theorem eraseUneraseCtxt : forall E E', uneraseCtxt E' E -> eraseContext E tEmptySet E'. 
Proof.
  intros. induction H; auto. Qed. 

Hint Resolve eraseUneraseCtxt. 

Theorem uneraseValEq : forall M M', uneraseTerm M' M -> val M = pval M'. 
Proof.
  intros. induction H; auto. simpl. rewrite IHuneraseTerm1. rewrite IHuneraseTerm2. auto. Qed. 

Theorem uneraseFill : forall E E' e e', uneraseCtxt E' E -> uneraseTerm e' e -> 
                                        uneraseTerm (pfill E' e') (fill E e).
Proof.
  intros. generalize dependent e. generalize dependent e'. induction H; intros; auto; 
  try solve[simpl; constructor; auto]. Qed. 

Theorem uneraseDecompose : forall E E' e e' t, pdecompose t E' e' -> uneraseCtxt E' E ->
                                               uneraseTerm e' e -> decompose (fill E e) E e.
Proof.
  intros. generalize dependent E. generalize dependent e. induction H; intros; 
  try solve[inversion H0; subst; simpl; constructor; eapply IHpdecompose; auto]. 
  {inversion H2; subst. simpl. constructor. apply pdecomposeEq in H0. subst. 
   rewrite <- H. apply uneraseValEq. apply uneraseFill; auto. apply IHpdecompose; auto. }
  {inversion H2; subst. simpl. constructor. rewrite <- H. apply uneraseValEq. auto. 
   apply IHpdecompose; auto. }
  {inversion H2; subst. simpl. constructor. apply pdecomposeEq in H0. subst. 
   rewrite <- H. apply uneraseValEq. apply uneraseFill; auto. apply IHpdecompose; auto. }
  {inversion H3; subst. simpl. constructor. rewrite <- H. apply uneraseValEq; auto. 
   apply pdecomposeEq in H1. subst. rewrite <- H0. apply uneraseValEq; auto.
   apply uneraseFill; auto. apply IHpdecompose; auto. }
  {inversion H0; subst. simpl. constructor. rewrite <- H. apply uneraseValEq. assumption. }
Qed. 
   

Theorem extendSpeculatedHeap : forall H H' x1 x2 x3 PH' v v', 
                                 speculateHeap H' H -> (x1, PH') = extend v H'->
                                 (x2, x3) = extend v' H -> x1 = x2. 
Admitted. 

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt',
                               pstep PH PT pt (pOK PH' PT pt') ->
                               exists H H' t t' T,
                                 eraseHeap H PH /\ eraseHeap H' PH' /\ erasePool T PT /\
                                 erasePool t pt /\ erasePool t' pt' /\ multistep H T t (OK H' T t').
Proof.
  intros. inversion H.  
  {cleanup. instantiateHeap. instantiateContext. inversion H1; subst.  
   exists(tSingleton(Tid(0,0)nil, nil, nil, fill (appValCtxt x1 (lambda e0)) x)). 
   exists (tSingleton(Tid(0,0)nil,nil,nil, fill x1 (open 0 x e0))). instantiatePool.  
   repeat split; auto. eraseEq. apply termErasePoolErase. copy H5. apply pdecomposeEq in H5. 
   subst. apply eraseFill; auto. rewrite <- ERASEHYP. constructor. eraseEq. apply termErasePoolErase. 
   apply eraseFill; auto. apply eraseOpen; auto. rewrite <- ERASEHYP. constructor. 
   econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   constructor. eapply uneraseDecompose; eauto. eapply pvalImpliesVal; eauto.
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. auto. }
  {cleanup. instantiateHeap. instantiateContext. inversion H0; subst.  
   exists(tSingleton(Tid(0,0)nil, nil, nil, fill (fstCtxt x0) (pair_ e1 e2))). 
   exists (tSingleton(Tid(0,0)nil,nil,nil, fill x0 e1)). instantiatePool.  
   repeat split; auto. eraseEq. apply termErasePoolErase. copy H2. apply pdecomposeEq in H2. 
   subst. apply eraseFill; auto. rewrite <- ERASEHYP. constructor. eraseEq. constructor. 
   econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   eapply ProjL. eapply uneraseDecompose; eauto. eapply pvalImpliesVal; eauto.
   eapply pvalImpliesVal; eauto. 
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. auto. }
  {cleanup. instantiateHeap. instantiateContext. inversion H0; subst.  
   exists(tSingleton(Tid(0,0)nil, nil, nil, fill (sndCtxt x0) (pair_ e1 e2))). 
   exists (tSingleton(Tid(0,0)nil,nil,nil, fill x0 e2)). instantiatePool.  
   repeat split; auto. eraseEq. apply termErasePoolErase. copy H2. apply pdecomposeEq in H2. 
   subst. apply eraseFill; auto. rewrite <- ERASEHYP. constructor. eraseEq. constructor. 
   econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   eapply ProjR. eapply uneraseDecompose; eauto. eapply pvalImpliesVal; eauto.
   eapply pvalImpliesVal; eauto. 
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. auto. }
  {cleanup. instantiateHeap. instantiateContext. inversion H0; subst. 
   exists (tSingleton (Tid(0,0)nil, nil, nil, fill (bindCtxt x1 x0) (ret e))). 
   exists (tSingleton (Tid(0,0)nil, nil, nil, fill x1 (AST.app x0 e))). instantiatePool. 
   repeat(split; try assumption). eraseEq. apply termErasePoolErase. apply pdecomposeEq in H4. subst. 
   apply eraseFill; eauto. rewrite <- ERASEHYP. constructor. eraseEq. constructor. econstructor.
   rewrite <- union_empty at 1. rewrite Union_commutative. 
   reflexivity. proveDisjoint. apply Bind. eapply uneraseDecompose; eauto. unfold tUnion. 
   rewrite Union_commutative. rewrite union_empty. constructor. }
  {cleanup. instantiateHeap. instantiateContext. inversion H0; subst. 
   exists(tSingleton(Tid(0,0)nil,nil,nil,fill (bindCtxt x1 x0) (raise e))). 
   exists(tSingleton(Tid(0,0)nil,nil,nil,fill x1 (raise e))). instantiatePool. repeat(split; try assumption). 
   eraseEq. apply termErasePoolErase. apply pdecomposeEq in H4; subst. apply eraseFill; eauto. 
   rewrite <- ERASEHYP. constructor. eraseEq. constructor. 
   econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   eapply BindRaise. eapply uneraseDecompose; eauto. unfold tUnion. rewrite Union_commutative. 
   rewrite union_empty. constructor. }
  {cleanup. instantiateHeap. instantiateContext. inversion H0; subst. 
   exists(tSingleton(Tid(0,0)nil,nil,nil,fill (handleCtxt x1 x0) (raise e))). 
   exists(tSingleton(Tid(0,0)nil,nil,nil,fill x1 (app x0 e))). instantiatePool. repeat(split; try assumption). 
   eraseEq. apply termErasePoolErase. apply pdecomposeEq in H4; subst. apply eraseFill; eauto. 
   rewrite <- ERASEHYP. constructor. eraseEq. constructor. econstructor. 
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. eapply Handle. 
   eapply uneraseDecompose; eauto. unfold tUnion. rewrite Union_commutative. rewrite union_empty. 
   constructor. }
  {cleanup. instantiateHeap. instantiateContext. inversion H0; subst. 
   exists(tSingleton(Tid(0,0)nil,nil,nil,fill (handleCtxt x1 x0) (ret e))). 
   exists(tSingleton(Tid(0,0)nil,nil,nil,fill x1 (ret e))). instantiatePool. repeat(split; try assumption). 
   eraseEq. apply termErasePoolErase. apply pdecomposeEq in H4; subst. apply eraseFill; eauto. 
   rewrite <- ERASEHYP. constructor. eraseEq. constructor. econstructor. 
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. eapply HandleRet. 
   eapply uneraseDecompose; eauto. unfold tUnion. rewrite Union_commutative. rewrite union_empty. 
   constructor. }
  {cleanup. instantiateHeap. instantiateContext. inversion H0; subst.
   exists (tSingleton(Tid(0,0)nil,nil,nil, fill x0 (fork e))). 
   exists (tCouple (Tid(0, 1)nil,nil,[fAct (Tid(1,1) [(0,0)]) 0 (fill x0 (fork e))], 
                    fill x0 (ret unit)) (Tid(1,1)[(0,0)], nil,[specAct], e)). 
   instantiatePool. repeat(split; try assumption). eraseEq. 
   apply termErasePoolErase. apply pdecomposeEq in H4; subst. apply eraseFill; eauto. 
   rewrite <- ERASEHYP. constructor. eraseEq. apply termErasePoolCouple; eauto. 
   eapply eraseFill; eauto. rewrite <- ERASEHYP. constructor. econstructor. 
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   apply Fork. eapply uneraseDecompose; eauto. auto. econstructor. unfold tUnion. 
   rewrite Union_commutative. rewrite union_empty.
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   eapply PopFork. rewrite app_nil_l. reflexivity. rewrite app_nil_l. reflexivity. 
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. constructor. }
  {cleanup. assert(exists H, speculateHeap PH' H). apply eHeap'.  invertExists. 
   exists x0. eapply lookupSpeculatedHeapFull with(x:=x) in H5; eauto. invertHyp. 
   exists(replace x (sfull nil [Tid(0,0)nil] nil (Tid(0,0)nil) x1) x0). instantiateContext. 
   inversion H0; subst. inversion H7; subst. 
   exists (tSingleton(Tid(0,0)nil,nil,nil,fill x3 (get (fvar x)))). 
   exists (tSingleton(bump (Tid(0,0)nil),nil, [rAct x 0 (fill x3 (get(fvar x)))], fill x3 (ret x1))). 
   instantiatePool. repeat(split; try assumption). apply eraseSpeculatedHeap. assumption. 
   apply eraseHeapDependentReader; auto. apply eraseSpeculatedHeap. assumption. 
   eraseEq. apply termErasePoolErase. apply pdecomposeEq in H6; subst. apply eraseFill; eauto. 
   rewrite <- ERASEHYP. constructor. eraseEq. constructor. econstructor. 
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. eapply Get. 
   eapply uneraseDecompose; eauto. eauto. eauto. eauto. econstructor. reflexivity. 
   proveDisjoint. eapply PopRead. rewrite app_nil_l. auto. eapply HeapLookupReplace. eassumption. 
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. constructor. }
  {cleanup. assert(exists H, speculateHeap PH H). apply eHeap'. invertExists.  
   exists x0. instantiateContext. inversion H0; subst. inversion H7; subst. 
   exists (replace x (sfull nil nil nil (Tid(0,0)nil) e2) x0).
   exists (tSingleton(Tid(0,0)nil,nil,nil,fill x2 (put (fvar x) e2))). 
   exists (tSingleton(Tid(0,1)nil,nil,[wAct x 0 (fill x2 (put (fvar x) e2))], fill x2 (ret unit))). 
   instantiatePool. repeat (split; try assumption). apply eraseSpeculatedHeap. assumption. 
   apply eraseReplaceSpecHeap; auto. eraseEq. apply termErasePoolErase. apply pdecomposeEq in H2; subst. 
   apply eraseFill; eauto. rewrite <- ERASEHYP. constructor. eraseEq. constructor. 
   econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   eapply Put. eapply uneraseDecompose; eauto. eapply lookupSpeculatedHeapEmpty; eauto. reflexivity. 
   reflexivity. econstructor. reflexivity. proveDisjoint. eapply PopWrite. rewrite app_nil_l. auto. 
   eapply HeapLookupReplace. eapply lookupSpeculatedHeapEmpty; eauto. reflexivity. unfold tUnion. 
   rewrite Union_commutative. rewrite union_empty. constructor. }
  {cleanup. assert(exists H, speculateHeap PH H). apply eHeap'. invertExists. exists x0.
   assert(exists i newHeap', (i,newHeap') = extend (sempty nil) x0). 
   destruct x0; simpl; eauto. destruct p. eauto. invertHyp. exists x2. 
   instantiateContext. exists(tSingleton(Tid(0,0)nil,nil,nil,fill x4 new)). 
   exists (tSingleton(Tid(0,1)nil,nil,[cAct x1 0 (fill x4 new)],fill x4 (ret (fvar x)))). 
   instantiatePool. repeat(split; try assumption). eapply eraseSpeculatedHeap. assumption.
   eapply eraseExtended; eauto. eraseEq. apply termErasePoolErase. apply pdecomposeEq in H5; subst. 
   apply eraseFill; eauto. rewrite <- ERASEHYP. constructor. eraseEq. constructor. 
   econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. eapply New.
   eapply uneraseDecompose; eauto. eauto. eauto. econstructor. reflexivity. proveDisjoint. 
   eapply PopNewEmpty. rewrite app_nil_l. auto. eapply lookupExtend. eassumption. reflexivity. 
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. 
   eapply extendSpeculatedHeap in H1; eauto. subst. constructor. }
  {cleanup. instantiateHeap. assert(exists M', uneraseTerm M M'). apply eUneraseTerm. 
   invertHyp. exists(tSingleton(Tid(0,0)nil,nil,nil,ret x)). 
   exists tEmptySet. instantiatePool. repeat(split; try assumption). eraseEq. apply termErasePoolErase. 
   auto. rewrite <- ERASEHYP. constructor. eraseEq. apply Extensionality_Ensembles. 
   unfold Same_set. unfold Included. split; intros. inversion H2. inversion H3. inversion H7. 
   inversion H2. rewrite <- ERASEHYP. constructor. econstructor. rewrite <- union_empty at 1. 
   rewrite Union_commutative. reflexivity. proveDisjoint. eapply Terminate. unfold tUnion. 
   rewrite union_empty. constructor. }
Qed. 
   










