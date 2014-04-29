Require Import NonSpec.  
Require Import Spec.  
Require Import SfLib. 
Require Import AST. 
Require Import Heap. 
Require Import Coq.Sets.Ensembles.
Require Import sets. 

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

Theorem termErasureDeterminism : forall M T M1 M2,
                                   eraseTerm M T M1 -> eraseTerm M T M2 -> M1 = M2. 
Proof.
  intros. generalize dependent M2. induction H; intros; 
                                   try(inversion H0; reflexivity);
  try(clear H; clear H0; match goal with
                           |H:eraseTerm ?T ?T' ?M |- _ => 
                    inversion H; clear H; applyHyp; applyHyp; subst; reflexivity
                         end); 
  try(clear H; match goal with
                |H : eraseTerm ?T ?T' ?M |- _ =>
                 inversion H; clear H; applyHyp; subst; reflexivity
               end). 
  {inversion H3; subst. apply IHeraseTerm1 in H8. rewrite H8. 
   apply uniqueThreadPool with (t' := (Tid(maj,min') tid, s1' ++ [sAct (Tid(maj,min'')tid) M'], s2, M)) in H13. 
   inversion H13. apply lastElementEq in H5. inversion H5. subst. apply IHeraseTerm2 in H12. 
   subst. reflexivity. assumption. }
Qed. 

Theorem erasureDeterminism : forall t t1' t2' T, 
                               eraseThread t T t1' -> 
                               eraseThread t T t2' -> t1' = t2'.
Proof.
  intros. induction H; inversion H0;
  try(subst; match goal with
               |H:eraseTerm ?M ?T ?x, H':eraseTerm ?M ?T ?y |- _ =>
                eapply termErasureDeterminism in H;[rewrite<-H;reflexivity|auto]
               |H:[] = [] ++ [?x] |- _ => inversion H       
               |H:[] = ?x ++ [?y] |- _ => destruct x; inversion H
               |H:?s1++[?x]=?s2++[?y]|-_ => apply lastElementEq in H; inversion H
             end);
  try(subst; eapply termErasureDeterminism in H12;[rewrite <-H12; reflexivity| auto]);
  reflexivity. Qed. 
  
Theorem eraseHeapDeterminism : forall h h1 h2, 
                                 eraseHeap h h1 -> eraseHeap h h2 ->
                                 h1 = h2. 
Proof.
  intros. generalize dependent h2. induction H; intros. 
  {inversion H0. subst. apply IHeraseHeap in H6. assumption. }
  {inversion H0. subst. apply IHeraseHeap in H4. subst. reflexivity. }
  {inversion H0; subst. apply IHeraseHeap in H10. assumption. }
  {inversion H0. subst. apply IHeraseHeap in H9. subst. reflexivity. }
  {inversion H1. subst. apply IHeraseHeap in H8. subst. 
   eapply termErasureDeterminism in H0. rewrite <-H0. reflexivity. assumption. }
  {inversion H0; subst. reflexivity. }
Qed. 

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


Inductive eraseContext : ctxt -> pool -> pctxt -> Prop :=
|eraseCtxtHole : forall T, eraseContext holeCtxt T pholeCtxt
|eraseCtxtBind : forall T N N' E E', eraseTerm N T N' -> eraseContext E T E' ->
                                     eraseContext (bindCtxt E N) T (pbindCtxt E' N')
|eraseCtxtSpec : forall T M M' M'' E E' t maj min min' min'' s1 s2,
                   eraseContext E T E' -> 
                   thread_lookup T (Tid(maj,min) t) (Tid(maj,min')t, s1 ++ [sAct (Tid(maj,min'')t) M'], s2, M) ->
                   eraseTerm M' T M'' ->
                   eraseContext (specReturnCtxt E (threadId (Tid(maj,min)t))) T 
                                (pbindCtxt E' (plambda (pbind (incBV 1 M'') (plambda (pret (ppair (pbvar 0)(pbvar 1)))))))
|eraseCtxtHandle : forall T N N' E E',
                     eraseTerm N T N' -> eraseContext E T E' ->
                     eraseContext (handleCtxt E N) T (phandleCtxt E' N')
.

Theorem ctxtErasureDeterminism : forall E T E1 E2, eraseContext E T E1 -> eraseContext E T E2 ->
                                                   E1 = E2. 
Proof.
  intros. generalize dependent E2. induction H; intros. 
  {inversion H0; subst. reflexivity. }
  {inversion H1; subst. apply IHeraseContext in H7. subst. eapply termErasureDeterminism in H. 
   rewrite <- H. reflexivity. assumption. }
  {inversion H2; subst. apply IHeraseContext in H9. subst. 
   apply uniqueThreadPool with (t' := (Tid (maj, min'0) t, s0 ++ [sAct (Tid (maj, min''0) t) M'0], s3, M0)) in H0. 
   inversion H0; subst. apply lastElementEq in H5. inversion H5; subst. 
   eapply termErasureDeterminism in H11. rewrite <- H11. reflexivity. assumption. assumption. }
  {inversion H1; subst. apply IHeraseContext in H7. subst. eapply termErasureDeterminism in H. 
   rewrite <- H. reflexivity. assumption. }
Qed. 

Ltac invertHyp :=
  match goal with
      |H : exists e : _, ?x |- _ => inversion H; clear H; subst; try invertHyp
      |H : ?x /\ ?y |- _ => inversion H; clear H; subst; try invertHyp
      |H : eraseTerm ?M ?T ?t, H' : eraseTerm ?M ?T ?t' |- _ => 
       eapply termErasureDeterminism in H; try eassumption; subst; try invertHyp
      |H : eraseContext ?E ?T ?E1, H' : eraseContext ?E ?T ?E2 |- _ => 
       eapply ctxtErasureDeterminism in H; try eassumption; subst; try invertHyp
  end. 
Hint Constructors eraseContext eraseTerm. 
Theorem decomposeErase : forall E e T t', 
                           eraseTerm (fill E e) T t' -> 
                           exists E' e', eraseContext E T E' /\ eraseTerm e T e' /\ t' = pfill E' e'.
Proof. 
  intros. remember (fill E e). generalize dependent E. generalize dependent e. induction H; intros;
       try solve[destruct E; inversion Heqt; simpl in *; subst; econstructor; econstructor; eauto]; 
       try solve[destruct E; inversion Heqt; simpl in *; repeat (match goal with
       |H:forall e0 E, ?e = fill E e0 -> ?X |- _ => 
        assert(Z:e = fill holeCtxt e) by reflexivity; apply H in Z;
       invertHyp; clear H
       |H:eraseContext holeCtxt ?T ?x |- _ => inversion H; subst
   end); econstructor; econstructor; eauto].
  {destruct E; inversion Heqt; simpl in *. 
   {apply IHeraseTerm1 in H2. invertHyp. econstructor. econstructor. eauto. } 
   {subst. econstructor. econstructor. eauto. }
  }
  {destruct E; inversion Heqt; simpl in *. 
   {apply IHeraseTerm1 in H2. invertHyp. econstructor. econstructor. eauto. }
   {subst. econstructor. econstructor. eauto. }
  }
  {destruct E; inversion Heqt; simpl in *. 
   {apply IHeraseTerm1 in H4. invertHyp. econstructor. econstructor. eauto. }
   {subst. econstructor. econstructor. eauto. }
  }
Qed. 


Theorem inErasure : forall t t', erasePoolAux t = Singleton ptrm t' -> Ensembles.In ptrm (erasePoolAux t) t'.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inversion H. 
  assert(In ptrm (Singleton ptrm t') t') by constructor. apply H1 in H2. assumption. Qed. 

Theorem eTerm : forall pt T, exists t, eraseTerm t T pt. 
Proof.
  induction pt; eauto;
  try intros; repeat( match goal with
               |T:?pool, H:forall T':?pool, ?X |- _ => specialize (H T); try invertHyp
           end); econstructor; eauto. Qed. 

Theorem eHeap : forall PH, exists H, eraseHeap H PH. 
Proof.
  induction PH; eauto. 
  {destruct a. destruct p. 
   {assert(hd:action). repeat constructor.  assert(tl:specStack). repeat constructor. 
    assert(w:tid). repeat constructor. assert(M:trm). repeat constructor. 
    inversion IHPH. exists((i, sfull nil nil (hd::tl) w M)::x). constructor. 
    assumption. }
   {inversion IHPH. assert(exists t, eraseTerm t tEmptySet p) by apply eTerm.  
    inversion H0. assert(t:tid). repeat constructor. 
    exists ((i, sfull nil nil nil t x0)::x). constructor. assumption. 
    assumption. }
  }
Qed. 
    
Theorem eCtxt : forall E T, exists E', eraseContext E' T E. 
Proof.
  induction E; eauto. 
  {intros. specialize (IHE T). inversion IHE. assert(exists N, eraseTerm N T p). 
   apply eTerm. inversion H0. exists (bindCtxt x x0). constructor; assumption. }
  {intros. specialize (IHE T). inversion IHE. assert(exists N, eraseTerm N T p). 
   apply eTerm. inversion H0. exists (handleCtxt x x0). econstructor; assumption. }
Qed.  

Theorem ePool : forall T, exists T', erasePool T' T. 
Proof.
  intros. Admitted. 

Theorem pdecomposeDecomposed : forall E e, pdecompose e = (pholeCtxt, e) -> 
                                           pdecompose (pfill E e) = (E, e).
Proof.
  induction E; intros; auto;
  simpl; apply IHE in H; destruct (pdecompose(pfill E e)); inversion H; auto. 
Qed. 

Theorem termEraseDifferentPools : forall T M M1 M2, eraseTerm M tEmptySet M1 -> 
                                            eraseTerm M T M2 -> M1 = M2. 
Proof.
  intros. remember tEmptySet. generalize dependent M2. generalize dependent T. induction H; intros;
  try solve[inversion H0; subst; reflexivity]; 
  try solve[inversion H0; subst; apply IHeraseTerm in H2; subst; reflexivity]; 
  try solve[inversion H1; subst; assert(tEmptySet = tEmptySet) by reflexivity; eapply IHeraseTerm1 in H2;[
   rewrite  H2; assert(tEmptySet = tEmptySet) by reflexivity; eapply IHeraseTerm2 in H3;[ 
   rewrite H3; reflexivity|eassumption]|eassumption]]. 
  {subst. inversion H2. inversion H8. }
Qed. 

Hint Constructors thread_lookup erasePoolAux Singleton eraseThread eraseTerm. 

Theorem eraseEmpty : forall M T e, eraseTerm M tEmptySet e -> eraseTerm M T e. 
Proof.
  intros. remember tEmptySet. generalize dependent T. induction H; eauto. 
  {subst. inversion H2. inversion H7. }
Qed. 

Theorem termErasePoolErase : forall tid M M' s2,
                               eraseTerm M tEmptySet M' ->
                               erasePoolAux (tSingleton(tid,nil,s2,M)) = (pSingleton M'). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst.
   inversion H2; subst; try solve[match goal with
                                     |H:nil=?x++[?y] |- _ => destruct x; inversion H
                                 end]. 
   {eapply termEraseDifferentPools with(M:=M0)(M1:=M')(M2:=M'0)in H. subst. assumption. 
    eassumption. }
  }
  {inversion H0; subst. inversion H; subst;
   try solve[destruct tid; destruct p; econstructor;[econstructor;[econstructor|eauto]|eauto|eauto]];
   try solve[destruct tid; destruct p; econstructor;[econstructor;[econstructor|auto]| econstructor; 
    econstructor; eapply eraseEmpty; eassumption| assumption]]. 
   {inversion H4. inversion H9. }
  }
Qed. 

Theorem eraseFillHelper : forall E e E' e' T, eraseTerm e T e' -> eraseContext E T E' -> 
                                              eraseTerm (fill E e) T (pfill E' e').
Proof.
  induction E; intros; inversion H0; subst; simpl; eauto. Qed. 

Theorem eraseFill : forall E e pt E' e' T, 
                      pdecompose pt = (E', e') -> eraseContext E T E' -> eraseTerm e T e' ->
                      eraseTerm (fill E e) T pt. 
Proof.
  intros. generalize dependent e'. generalize dependent pt. generalize dependent e. induction H0; intros. 
  {apply pdecomposeEq in H. simpl in *. subst. assumption. }
  {simpl in *. apply pdecomposeEq in H1. subst. simpl. constructor. apply eraseFillHelper; eauto. 
   assumption. }
  {simpl. apply pdecomposeEq in H2. subst. simpl. econstructor. apply eraseFillHelper; eauto. 
   reflexivity. eassumption. eassumption. }
  {simpl. apply pdecomposeEq in H1. subst; simpl. econstructor. apply eraseFillHelper; eauto. 
   eauto. }
Qed. 

Unset Ltac Debug. 

Ltac instantiateHeap :=
  match goal with
      |H:pstep ?H ?T ?t ?H ?T' ?t' |- _ => assert(EH:exists H', eraseHeap H' H) by apply eHeap; 
                                          inversion EH as[newHeap heapHyp]; exists newHeap;
                                          exists newHeap
      |H:pstep ?H ?T ?t ?H' ?T' ?t' |- _ => assert(EH:exists H', eraseHeap H' H) by apply eHeap;
                                          inversion EH as[newHeap heapHyp]; exists newHeap
  end. 

Ltac instantiateContext := 
  match goal with 
      |H:pdecompose ?t = (pbindCtxt ?E ?N, ?e) |- _ => 
       assert(CTXT:exists E', eraseContext E' tEmptySet E) by apply eCtxt; inversion CTXT; clear CTXT;
       assert(NHyp:exists N', eraseTerm N' tEmptySet N) by apply eTerm; inversion NHyp; clear NHyp;
       assert(eHyp:exists e', eraseTerm e' tEmptySet e) by apply eTerm; inversion eHyp; clear eHyp
      |H:pdecompose ?t = (phandleCtxt ?E ?N, ?e) |- _ => 
       assert(CTXT:exists E', eraseContext E' tEmptySet E) by apply eCtxt; inversion CTXT; clear CTXT;
       assert(NHyp:exists N', eraseTerm N' tEmptySet N) by apply eTerm; inversion NHyp; clear NHyp;
       assert(eHyp:exists e', eraseTerm e' tEmptySet e) by apply eTerm; inversion eHyp; clear eHyp
      |H:pdecompose ?t = (?E, ?e) |- _ =>
       assert(CTXT:exists E', eraseContext E' tEmptySet E) by apply eCtxt; inversion CTXT; clear CTXT;
       assert(eHyp:exists e', eraseTerm e' tEmptySet e) by apply eTerm; inversion eHyp; clear eHyp
  end.

Unset Ltac Debug. 
Ltac instantiatePool :=
  match goal with
      |H:pstep ?h ?T ?t ?h' ?T ?t' |- _ => assert(PHYP:exists T', erasePool T' T) by apply ePool; 
                                          inversion PHYP as [SpecPool specPoolHyp]; exists SpecPool
  end. 

Ltac eraseEq := 
  match goal with
      | |- erasePool ?T ?T' => assert(ERASEHYP:erasePoolAux T = T') by
                                (apply termErasePoolErase; eapply eraseFill; eauto); rewrite <- ERASEHYP
      | |- erasePool ?T ?T' => assert(ERASEHYP:erasePoolAux T = T')
  end.

Theorem eraseHeapLookupSome : forall H' H, eraseHeap H H' ->
                                forall M' x, heap_lookup x H' = Some (pfull M') -> 
                                exists M t ds, heap_lookup x H = Some (sfull nil ds nil t M) /\ eraseTerm M tEmptySet M'. 
Proof.
  intros H H' U. induction U; intros;
                 try solve[simpl in *; destruct (beq_nat x i);[inversion H|eapply IHU; eassumption]].
  {admit. }
  {admit. }
  {simpl in *. destruct (beq_nat x i). inversion H0; subst. exists M. exists t. exists d. split; auto. 
   apply IHU in H0. eassumption. }
  {simpl in *. inversion H. }
Qed.  

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


Fixpoint speculateHeap(h:pHeap) : sHeap :=
  match h with
      |pempty::h' => (sempty nil)::speculateHeap h'
      |pfull M => 

Theorem eraseHeapLookupEmpty : forall H H' x, 
                                 heap_lookup x H' = Some pempty -> eraseHeap H H' ->
                                 heap_lookup x H = Some (sempty nil). 
Proof. 
  Admitted. 

Require Import Powerset_facts. 

Ltac proveDisjoint :=
  unfold tSingleton in *;
  match goal with
      | |- Disjoint ?T ?x (Empty_set ?T) => constructor; unfold not; intros c contra; 
                                            inversion contra as[IN1 IN2 IN3]; inversion IN3                          
      | |- Disjoint ?T (Empty_set ?T) ?x => constructor; unfold not; intros c contra; 
                                            inversion contra as[IN1 IN2]; inversion IN2
  end. 



Theorem eraseHeapCommitWrite : forall H H', 
                                 eraseHeap H H' -> forall x tid M M', heap_lookup x H' = Some pempty -> 
                                 eraseTerm M tEmptySet M' ->
                                 eraseHeap (replace x (sfull nil nil nil tid M) H) (replace x (pfull M') H').  
Proof.
  intros H H' U. induction U; intros. 
Admitted. 



Axiom extendSameVar : forall H H' x1 x2 H1 H1' v1 v2, eraseHeap H H' -> (x1,H1) = extend v1 H ->
                                                      (x2, H1') = extend v2 H' -> x1 = x2. 

Theorem eraseHeapExtend : forall H1 H2, 
                            eraseHeap H1 H2 -> forall  i1 i2 H1' H2', (i1, H1') = extend (sempty nil) H1 ->
                            (i2, H2') = extend pempty H2 -> eraseHeap H1' H2'. 
Proof.
  Admitted. 

Theorem termErasePoolCouple : forall tid tid' M1 M2 M1' M2' s2 s2',
                                eraseTerm M1 tEmptySet M1' -> eraseTerm M2 tEmptySet M2' ->
                                erasePoolAux(tCouple (tid,nil,s2,M1)(tid',nil,s2',M2)) = Couple ptrm M1' M2'.
Admitted. 

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt',
                               pstep PH PT pt PH' PT pt' ->
                               exists H H' t t' T,
                                 eraseHeap H PH /\ eraseHeap H' PH' /\ erasePool T PT /\
                                 erasePool t pt /\ erasePool t' pt' /\ multistep H T t H' T t'.
Proof.
  intros. inversion H. 
  {cleanup. instantiateHeap. instantiateContext. inversion H3; subst. invertHyp. 
   assert(tid:tid); repeat constructor. 
   exists (tSingleton (tid, nil, nil, fill (bindCtxt x x0) (ret e))). 
   exists (tSingleton (tid, nil, nil, fill x (AST.app x0 e))). instantiatePool. 
   repeat(split; try assumption). eraseEq. constructor. eraseEq. apply termErasePoolErase. 
   eapply eraseFill. eapply pdecomposeDecomposed; eauto. assumption. constructor; eauto. 
   rewrite <- ERASEHYP. constructor. econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. 
   reflexivity. proveDisjoint. constructor. apply decomposeDecomposed. auto. unfold tUnion. 
   rewrite Union_commutative. rewrite union_empty. constructor. }
  {cleanup. instantiateHeap. instantiateContext. assert(tid:tid); repeat constructor. 
   exists(tSingleton(tid,nil,nil,fill (bindCtxt x x0) x1)). 
   exists(tSingleton(tid,nil,nil,fill x x1)). instantiatePool. repeat(split; try assumption). 
   eraseEq. constructor. eraseEq. apply termErasePoolErase. eapply eraseFill; eauto. 
   apply pdecomposeDecomposed; auto. rewrite <- ERASEHYP. constructor. inversion H3; subst.
   econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   eapply BindRaise. eapply decomposeDecomposed. auto. unfold tUnion. rewrite Union_commutative. 
   rewrite union_empty. constructor. }
  {cleanup. instantiateHeap. instantiateContext. assert(tid:tid); repeat constructor. inversion H3; subst.
   exists(tSingleton(tid,nil,nil,fill (handleCtxt x x0) (raise e))). 
   exists(tSingleton(tid,nil,nil,fill x (app x0 e))). instantiatePool. repeat(split; try assumption). 
   eraseEq. constructor. eraseEq. apply termErasePoolErase. eapply eraseFill; eauto. 
   eapply pdecomposeDecomposed; eauto. rewrite <- ERASEHYP. constructor. econstructor. 
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. eapply Handle. 
   eapply decomposeDecomposed; eauto. unfold tUnion. rewrite Union_commutative. rewrite union_empty. 
   constructor. }
  {cleanup. instantiateHeap. instantiateContext. assert(tid:tid); repeat constructor. inversion H3; subst.
   exists(tSingleton(tid,nil,nil,fill (handleCtxt x x0) (ret e))). 
   exists(tSingleton(tid,nil,nil,fill x (ret e))). instantiatePool. repeat(split; try assumption). 
   eraseEq. constructor. eraseEq. apply termErasePoolErase. eapply eraseFill; eauto. 
   apply pdecomposeDecomposed. auto. rewrite <- ERASEHYP. constructor. econstructor. 
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. eapply HandleRet. 
   eapply decomposeDecomposed; eauto. unfold tUnion. rewrite Union_commutative. rewrite union_empty. 
   constructor. }
  {cleanup. instantiateHeap. instantiateContext. assert(tid:tid). repeat constructor.  
   inversion H2; subst. exists (tSingleton(tid,nil,nil, fill x (fork e))). 
   exists (tCouple (bump tid,nil,[fAct (extendTid tid) tid (fill x (fork e))], 
                    fill x (ret unit))(extendTid tid, nil,[specAct], e)). 
   instantiatePool. repeat(split; try assumption). eraseEq. constructor. eraseEq.
   apply termErasePoolCouple. eapply eraseFill. apply pdecomposeDecomposed. auto. auto. auto. auto. 
   rewrite <- ERASEHYP. constructor. econstructor. rewrite <- union_empty at 1. rewrite Union_commutative. 
   reflexivity. proveDisjoint. apply Fork. apply decomposeDecomposed; auto. reflexivity. 
   econstructor. unfold tUnion. rewrite Union_commutative. rewrite union_empty.
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. 
   eapply PopFork. instantiate(4:=nil). reflexivity. instantiate(1:=nil). reflexivity. 
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. constructor. }
  {cleanup. assert(exists H, eraseHeap H PH'). apply eHeap. inversion H2.
   assert(exists E', eraseContext E' tEmptySet E). apply eCtxt. inversion H4. clear H4.
   apply eraseHeapLookupSome with (H:=x0)in H0. invertHyp. 
   assert(tid:tid). repeat constructor. exists x0. exists (replace x (sfull nil (tid::x5) nil x4 x3) x0). 
   exists (tSingleton(tid,nil,nil,fill x1 (get (fvar x)))). 
   exists (tSingleton(bump tid,nil, [rAct x tid (fill x1 (get(fvar x)))], fill x1 (ret x3))). 
   instantiatePool. repeat(split; try assumption). apply eraseHeapDependentReader; auto.
   eraseEq. constructor. eraseEq. apply termErasePoolErase. eapply eraseFill; eauto.
   apply pdecomposeDecomposed. auto. rewrite <- ERASEHYP. constructor. econstructor. 
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. eapply Get. 
   eapply decomposeDecomposed. auto. eassumption. reflexivity. econstructor. reflexivity. proveDisjoint. 
   eapply PopRead. instantiate (4:=nil). reflexivity. eapply HeapLookupReplace. eassumption. 
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. constructor. assumption. }
  {cleanup. instantiateHeap. instantiateContext. inversion H3; subst. assert(tid:tid). repeat constructor. 
   exists (replace x (sfull nil nil nil tid e) newHeap). inversion H9; subst. 
   exists (tSingleton(tid,nil,nil,fill x0 (put (fvar x) e))). 
   exists (tSingleton(bump tid,nil,[wAct x tid (fill x0 (put (fvar x) e))], fill x0 (ret unit))). 
   instantiatePool. repeat (split; try assumption). eapply eraseHeapCommitWrite; auto. 
   eraseEq. constructor. eraseEq. apply termErasePoolErase. eapply eraseFill. apply pdecomposeDecomposed; auto. 
   assumption. auto. rewrite <- ERASEHYP. constructor. econstructor. rewrite <- union_empty at 1. 
   rewrite Union_commutative. reflexivity. proveDisjoint. eapply Put. eapply decomposeDecomposed. 
   auto. eapply eraseHeapLookupEmpty; eauto. reflexivity. econstructor. reflexivity. proveDisjoint. 
   eapply PopWrite. instantiate(4:=nil). reflexivity. eapply HeapLookupReplace. 
   eapply eraseHeapLookupEmpty; eauto. reflexivity. unfold tUnion. rewrite Union_commutative. 
   rewrite union_empty. constructor. }
  {cleanup. instantiateHeap. assert(exists i newHeap', (i,newHeap') = extend (sempty nil) newHeap). 
   destruct newHeap; simpl; eauto. destruct p. eauto. invertHyp. exists x1. 
   assert(tid:tid). repeat constructor. instantiateContext. exists(tSingleton(tid,nil,nil,fill x3 new)). 
   exists (tSingleton(bump tid,nil,[cAct x0 tid (fill x3 new)],fill x3 (ret (fvar x0)))). instantiatePool. 
   repeat(split; try assumption). eapply eraseHeapExtend. eapply heapHyp. eassumption. eassumption. 
   eraseEq. constructor. eraseEq. apply termErasePoolErase. eapply eraseFill. apply pdecomposeDecomposed. 
   auto. assumption. constructor. assert(x0 =x). eapply extendSameVar. eapply heapHyp. eassumption. 
   eassumption. subst. constructor. rewrite <- ERASEHYP. constructor. econstructor. 
   rewrite <- union_empty at 1. rewrite Union_commutative. reflexivity. proveDisjoint. eapply New. 
   apply decomposeDecomposed. auto. eassumption. econstructor. reflexivity. proveDisjoint. 
   eapply PopNewEmpty. instantiate(4:=nil). reflexivity. eapply lookupExtend. eassumption. reflexivity. 
   unfold tUnion. rewrite Union_commutative. rewrite union_empty. constructor. }
  {cleanup. instantiateHeap. assert(exists M', eraseTerm M' tEmptySet M). apply eTerm. 
   invertHyp. assert(tid:tid). repeat constructor. exists(tSingleton(tid,nil,nil,ret x)). 
   exists tEmptySet. instantiatePool. repeat(split; try assumption). eraseEq. apply termErasePoolErase. 
   constructor. assumption. rewrite <- ERASEHYP. constructor. eraseEq. apply Extensionality_Ensembles. 
   unfold Same_set. unfold Included. split; intros. inversion H2. inversion H3. inversion H7. 
   inversion H2. rewrite <- ERASEHYP. constructor. econstructor. rewrite <- union_empty at 1. 
   rewrite Union_commutative. reflexivity. proveDisjoint. eapply Terminate. unfold tUnion. 
   rewrite union_empty. constructor. }
Qed. 
   












