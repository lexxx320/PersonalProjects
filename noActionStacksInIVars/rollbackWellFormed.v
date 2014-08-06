Require Import NonSpec.   
Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import SfLib.  
Require Import unspec. 
Require Import sets. 
Require Import SpecLib. 
Require Import classifiedStep. 
Require Import hetList. 
Require Import Coq.Program.Equality. 
Require Import Heap. 
Require Import Coq.Sets.Powerset_facts. 
Require Import IndependenceCommon. 

Hint Constructors actionTerm. 

Definition commitPool' T := forall tid s1 s2 M, tIn T (tid,s1,s2,M) -> 
                                                s1 = unlocked nil \/ exists N, s1 = specStack nil N.

Theorem eqUnspec : forall T, T = unspecPoolAux T -> commitPool' T. 
Proof. 
  intros. unfold commitPool'. intros. unfoldSetEq H. apply H1 in H0. inv H0.
  inv H3; try solve[inv H4; eauto]. 
Qed. 
 
Theorem eraseTrmConsSame : forall a l M' M'' N,
                             actionTerm a M' -> 
                             eraseTrm l M' M'' -> eraseTrm (a::l) N M''. 
Proof.
  intros. destructLast l. 
  {rewrite <- (app_nil_l [a]). inv H; inv H0; try invertListNeq; constructor. }
  {invertHyp. destruct x; inv H0; try solve[invertListNeq]; apply lastElementEq in H2; 
   try solveByInv; inv H2; rewrite app_comm_cons; constructor. }
Qed. 

Inductive spec_multistep_rev : sHeap -> pool -> sHeap -> pool -> Prop :=
    smulti_refl_r : forall (h : sHeap) (p2 : pool), spec_multistep_rev h p2 h p2
  | smulti_step_r : forall (T T' t' t'' : pool) (h h' h'' : sHeap),
                  spec_multistep_rev h T h' (tUnion T' t') ->
                  spec_step h' T' t' h'' T' t'' ->
                  spec_multistep_rev h T h'' (tUnion T' t''). 

Theorem spec_multi_rev_trans : forall H T H' T' H'' T'',
                              spec_multistep_rev H T H' T' ->
                              spec_multistep_rev H' T' H'' T'' ->
                              spec_multistep_rev H T H'' T''.
Proof. 
  intros. induction H1. 
  {auto. } 
  {econstructor. Focus 2. eassumption. eapply IHspec_multistep_rev. eauto. }
Qed. 

Theorem smultiSmultiRevEq : forall H T H' T',
                            spec_multistep H T H' T' <-> spec_multistep_rev H T H' T'. 
Proof.
  intros. split; intros. 
  {induction H0. 
   {constructor. }
   {eapply spec_multi_rev_trans. eapply smulti_step_r. Focus 2. eauto. constructor. 
    eauto. }
  }
  {induction H0. 
   {constructor. }
   {eapply spec_multi_trans. eassumption. econstructor; eauto. 
    constructor. }
  }
Qed. 

Inductive rbTerm : list action -> trm -> trm -> Prop :=
|rbCons : forall a b M M', actionTerm a M' -> rbTerm (a::b) M M'
|rbNil : forall M M', rbTerm nil M M'.

Inductive rbTerm' : actionStack -> trm -> trm -> Prop :=
|rbU : forall s M M', rbTerm s M M' -> rbTerm' (unlocked s) M M' 
|rbL : forall s M M', rbTerm s M M' -> rbTerm' (locked s) M M'
|rbS : forall s M M' N, rbTerm s M M' -> rbTerm' (specStack s N) M M'. 

Require Import Coq.Logic.Classical_Prop. 

Theorem specStepCouple : forall H tid s1 s2 M H' T t',
     spec_step H T (tSingleton(tid,s1,s2,M)) H' T t' ->
     (exists s1' M', t' = tSingleton(tid,s1',s2,M')) \/
     (exists n N s1' M',t' = tCouple(tid,s1',s2,M') (n::tid,locked nil,nil,N)). 
Proof.
  intros. inv H0; unfoldTac; invertHyp; invThreadEq; eauto. 
  {right. repeat econstructor. }
  {right. repeat econstructor. }
Qed. 

Ltac cleanup := 
  match goal with
      |H:?x = ?x |- _ => clear H; try cleanup
  end.  

Ltac takeTStepRev :=
  match goal with
  | H:Ensembles.In thread ?T ?t
    |- _ =>
        apply pullOut in H; rewrite H; unfoldTac; rewrite UnionSwap;
         econstructor
  end.

Theorem aConsEq : forall a b c d, aCons a b = aCons c d -> a = c /\ b = d. 
Proof.
  intros. destruct b; destruct d; simpl in *; inv H; auto.
Qed. 

Theorem eraseTrmConsSame' : forall a M' N s1 s2 tid,
                             actionTerm a M' -> 
                             unspecPoolAux(tSingleton(tid,s1,s2,M')) = 
                             unspecPoolAux(tSingleton(tid,aCons a s1,s2,N)). 
Proof.
  intros. destruct s1. 
  {simpl. repeat erewrite unspecSingleton; eauto. }
  {destructLast l. 
   {simpl. erewrite unspecSingleton; eauto. erewrite unspecSingleton; eauto. 
    inv H; unspecThreadTac; rewrite app_nil_l; auto.  }
   {invertHyp. assert(exists t', unspecThread (tid,unlocked(x0++[x]),s2,M') t'). 
    apply unspecThreadTotal. invertHyp. erewrite unspecSingleton; eauto. 
    erewrite unspecSingleton; eauto. inv H1; try solve[invertListNeq]; inv H6; 
    apply lastElementEq in H1; subst; simpl; rewrite app_comm_cons; unspecThreadTac; auto. }
  }
  {simpl. repeat erewrite unspecSingleton; eauto. }
Qed. 

Theorem unspecSpecSame : forall M' N s1 s2 tid,
                           Spec s1 -> 
                           unspecPoolAux(tSingleton(tid,s1,s2,M')) = 
                           unspecPoolAux(tSingleton(tid,s1,s2,N)). 
Proof.
  intros. destruct s1. 
  {simpl. repeat erewrite unspecSingleton; eauto. }
  {inv H. destructLast b. 
   {destruct a; repeat erewrite unspecSingleton; eauto; unspecThreadTac; rewrite app_nil_l; auto. }
   {invertHyp. rewrite app_comm_cons. destruct x; repeat erewrite unspecSingleton; eauto; 
    unspecThreadTac; eauto. }
  }
  {repeat erewrite unspecSingleton; eauto. }
Qed. 

Theorem specStepExistsIn : forall H T t H' t',
                             spec_step H T t H' T t' ->
                             exists x, tIn t' x. 
Proof.
  intros. inv H0; repeat econstructor. 
Qed. 
  
Require Import Coq.Logic.Classical_Prop.
 
Ltac exMid a b := let n := fresh
                  in (assert(n:a=b\/a<>b) by apply classic); inv n. 


Theorem UnionSubtract : forall U A x,
                          Ensembles.In U A x ->
                          A = Union U (Subtract U A x) (Singleton U x). 
Proof.
  intros. eqSets. 
  {assert(x=x0\/x<>x0). apply classic. inv H1. solveSet. constructor. 
   constructor. auto. intros c. inv c. apply H2; auto. }
  {inv H0. inv H1. auto. inv H1. auto. }
Qed. 

Ltac stacksNeq := 
  match goal with
      |H:aCons ?a ?b = aCons ?c ?d |- _ => 
       let n1 := fresh
       in let n2 := fresh
          in apply aConsEq in H; inversion H as [n1 n2]; inv n1
  end.

Theorem UnionEqR : forall U T T1 T2, T1 = T2 -> Union U T T1 = Union U T T2. 
Proof.
  intros. subst; auto. 
Qed. 
Theorem UnionEqL : forall U T T1 T2, T1 = T2 -> Union U T1 T = Union U T2 T. 
Proof.
  intros. subst; auto. 
Qed. 

Theorem specStepUnspecEq : forall H T t H' t',
                             spec_step H T t H' T t' ->
                             unspecPoolAux(tUnion T t') = unspecPoolAux (tUnion T t). 
Admitted. 

Ltac unspecsEq :=
  solve[erewrite specStepUnspecEq; eauto|rewrite UnionSwap; erewrite specStepUnspecEq; eauto].

Ltac rewriteUnspec :=
  match goal with
      | |- spec_multistep_rev ?h (unspecPoolAux ?T) ?h' ?T' =>
        let n := fresh 
        in (assert(n:unspecPoolAux T = unspecPoolAux T') by unspecsEq); rewrite n
      | |- spec_multistep_rev ?h (unspecPoolAux ?T) ?h' ?T' =>
        let n := fresh 
        in assert(n:unspecPoolAux T = unspecPoolAux T')  
  end. 

Theorem unspecEmpty : forall tid s2 M, 
                        unspecPoolAux(tSingleton(tid,locked nil,s2,M)) = tEmptySet. 
Proof. 
  intros. erewrite unspecSingleton; eauto. 
Qed. 
 

Theorem tUnionSwap :forall T1 T2 T3, Union thread (Union thread T1 T2) T3 = tUnion (tUnion T1 T3) T2.
Admitted. 

Theorem passThroughWrite : forall M M' T s1 sc s2 H H' tid x E N' d,
        heap_lookup x H' = Some (sfull sc [] SPEC tid N') -> 
        spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,aCons (wAct x M' E N' d) s1,s2,M))))
                       H' (tUnion T(tSingleton(tid,aCons (wAct x M' E N' d) s1,s2,M))) ->
          spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,s1,s2,M'))))
                             (replace x (sempty sc) H') (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H1. 
  {symmetry in x. apply eqUnspec in x. unfold commitPool' in x. 
   assert(tIn(tUnion T(tSingleton(tid,aCons(wAct x0 M' E N' d)s1,s2,M)))(tid,aCons(wAct x0 M' E N' d)s1,s2,M)). 
   apply InL. constructor. apply x in H. inv H. destruct s1; inv H1. invertHyp. 
   destruct s1; inv H. }
  {inv H. 
   {copy x. unfoldSetEq x. eqIn H4. inv H6. 
    {takeTStep. Focus 2. eapply SBasicStep; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap.  
     eapply IHspec_multistep_rev; eauto. rewrite H7. rewrite subtractSingle.
     repeat rewrite unspecUnionComm. apply UnionEqL. erewrite unspecSpecSame; eauto.
     proveUnionEq H. rewrite H7. solveSet. }
    {inv H7. apply UnionEqTID in H. invertHyp. cleanup. eapply IHspec_multistep_rev. 
     Focus 2. unspecsEq. eauto. auto. auto. }
   } 
   {copy x. unfoldSetEq x. eqIn H3. inv H4. 
    {symmetry in H. apply UnionSingletonCoupleEq in H; eauto.  
     rewrite H. unfoldTac. rewrite UnionSwap. econstructor. Focus 2. eapply SFork; eauto. 
     unfoldTac. rewrite UnionSwap. rewriteUnspec. rewrite UnionSwap.
     eapply IHspec_multistep_rev; eauto. rewrite H. rewrite tUnionSwap.
     rewrite UnionSwap. erewrite specStepUnspecEq; eauto. rewrite UnionSwap. 
     rewrite <- UnionSubtract. auto. auto. }
    {inv H5. stacksNeq. destruct s1; simpl in *; inv H8. }
   }
   {copy x. unfoldSetEq x. eqIn H3. inv H5. 
    {varsEq x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0. takeTStep. 
     Focus 2. eapply SGet with(h:=replace x0 (sempty sc) h'); eauto.
     rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. 
     rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. 
     rewrite lookupReplaceNeq in H0; eauto. rewrite H6. rewrite subtractSingle.
     repeat rewrite unspecUnionComm. apply UnionEqL. erewrite <- eraseTrmConsSame'; eauto.
     proveUnionEq H. rewrite H6. solveSet. }
    {inv H6. stacksNeq. }
   } 
   {copy x. unfoldSetEq x. eqIn H3. inv H5. 
    {varsEq x1 x0. 
     {erewrite HeapLookupReplace in H0; eauto. inv H0. apply UnionEqTID in H. invertHyp.
      stacksNeq. rewrite replaceOverwrite. rewrite unspecUnionComm in *. 
      erewrite <- eraseTrmConsSame' in H1; eauto. rewrite replaceSame; eauto. }
     {rewrite lookupReplaceNeq in H0; eauto. takeTStep. Focus 2. 
      eapply SPut with(h:=replace x0 (sempty sc) h'); eauto.
      rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. 
      rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. 
      rewrite H6. rewrite subtractSingle. repeat rewrite unspecUnionComm. apply UnionEqL. 
      erewrite <- eraseTrmConsSame'; eauto. proveUnionEq H. rewrite H6. solveSet. }
    }
    {inv H6. apply UnionEqTID in H. invertHyp. stacksNeq. rewrite replaceOverwrite. 
     rewrite unspecUnionComm in *. erewrite <- eraseTrmConsSame' in H1; eauto.
     rewrite replaceSame; eauto. erewrite HeapLookupReplace in H0; eauto. inv H0. 
     eauto. }
   }
   {copy x. unfoldSetEq x. eqIn H2. inv H4. 
    {varsEq x1 x0. erewrite lookupExtend in H0; eauto. inv H0. takeTStep. 
     Focus 2. eapply SNew with(h:=replace x0 (sempty sc) h'); eauto.
     erewrite extendReplaceSwitch; eauto. erewrite lookupExtendNeq in H0; eauto.
     rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. 
     erewrite lookupExtendNeq in H0; eauto. rewrite H5. rewrite subtractSingle.
     repeat rewrite unspecUnionComm. apply UnionEqL. erewrite <- eraseTrmConsSame'; eauto.
     proveUnionEq H. rewrite H5. solveSet. }
    {inv H5. stacksNeq. }
   }
   {copy x. unfoldSetEq x. eqIn H3. inv H4. 
    {symmetry in H. apply UnionSingletonCoupleEq in H; eauto.  
     rewrite H. unfoldTac. rewrite UnionSwap. econstructor. Focus 2. eapply SSpec; eauto. 
     unfoldTac. rewrite UnionSwap. rewriteUnspec. rewrite UnionSwap.
     eapply IHspec_multistep_rev; eauto. rewrite H. rewrite tUnionSwap.
     rewrite UnionSwap. erewrite specStepUnspecEq; eauto. rewrite UnionSwap. 
     rewrite <- UnionSubtract. auto. auto. }
    {inv H5. stacksNeq. destruct s1; simpl in *; inv H8. }
   }
  }
  Grab Existential Variables. assumption. assumption. eauto.
  rewrite lookupReplaceNeq; eauto. assumption. assumption. assumption. assumption. 
Qed. 

Theorem lookupRemoveNeq : forall (T:Type) x x' H (v:option T),
                            x <> x' -> heap_lookup x H = v ->
                            heap_lookup x (remove H x') = v.
Proof.
  destruct H. induction h; intros. 
  {simpl in *. auto. }
  {simpl in *. destruct a. destruct (beq_nat x' i) eqn:eq. 
   {destruct (beq_nat x i) eqn:eq2.
    {apply beq_nat_true in eq. apply beq_nat_true in eq2. subst. 
     exfalso. apply H; auto. }
    {auto. }
   }
   {destruct (beq_nat x i) eqn:eq2. 
    {simpl. rewrite eq2. auto. }
    {simpl. rewrite eq2. eapply IHh; eauto. inv u. eapply uniqueSubset; eauto. 
     constructor. inv H0. }
   }
  }
Qed. 

Theorem raw_removeReplaceSwitch : forall (T:Type) x x' H (v:T),
                                x<>x' -> raw_remove (raw_replace x v H) x' = raw_replace x v (raw_remove H x'). 
Proof.
  induction H; intros. 
  {auto. }
  {simpl. destruct a. destruct (beq_nat x i) eqn:eq1. 
   {destruct (beq_nat x' i) eqn:eq2. 
    {simpl. apply beq_nat_true in eq1. apply beq_nat_true in eq2. subst. exfalso. 
     apply H0; auto. }
    {simpl. apply beq_nat_true in eq1. subst. rewrite eq2. rewrite <- beq_nat_refl. 
     auto. }
   }
   {simpl. destruct (beq_nat x' i) eqn:eq2; auto. simpl. rewrite eq1. erewrite IHlist; eauto. }
  }
Qed. 

Theorem removeReplaceSwitch : forall (T:Type) x x' H (v:T),
                                x<>x' -> remove (replace x v H) x' = replace x v (remove H x'). 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. eapply raw_removeReplaceSwitch; eauto. 
Qed. 

Theorem removeExtendSwitch : forall (T:Type) x x' H (v:T) p p',
                               x<>x' -> remove (extend x v H p) x' = extend x v (remove H x') p'. 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. apply neqSym in H0. 
  apply beq_nat_false_iff in H0. rewrite H0. unfold raw_extend. auto.
Qed. 

Theorem removeExtend : forall (T:Type) H x (v:T) p,
                         remove(extend x v H p) x = H.
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. rewrite <- beq_nat_refl. auto. 
Qed. 
  
Theorem smultiRevNewFull : forall H T H' T' tid M' E d x s1 s2 M,
                             spec_multistep_rev H T H' T' -> 
                             tIn T' (tid,aCons (nAct M' E d x) s1,s2,M) ->
                             exists v, heap_lookup x H' = Some v.
Proof.
  intros. induction H0. 
Admitted. 

Theorem passThroughNew : forall M M' T s1 s2 H H' tid x E d,
        heap_lookup x H' = Some (sempty SPEC) -> 
        spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,aCons (nAct M' E d x) s1,s2,M))))
                       H' (tUnion T(tSingleton(tid,aCons (nAct M' E d x) s1,s2,M))) ->
          spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,s1,s2,M'))))
                             (remove H' x) (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H1. 
  {symmetry in x. apply eqUnspec in x. unfold commitPool' in x. 
   assert(tIn(tUnion T(tSingleton(tid,aCons(nAct M' E d x0)s1,s2,M)))(tid,aCons(nAct M' E d x0)s1,s2,M)). 
   apply InL. constructor. apply x in H. inv H. destruct s1; inv H1. invertHyp. 
   destruct s1; inv H. }
  {inv H. 
   {copy x. unfoldSetEq x. eqIn H4. inv H6. 
    {takeTStep. Focus 2. eapply SBasicStep; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap.  
     eapply IHspec_multistep_rev; eauto. rewrite H7. rewrite subtractSingle.
     repeat rewrite unspecUnionComm. apply UnionEqL. erewrite unspecSpecSame; eauto.
     proveUnionEq H. rewrite H7. solveSet. }
    {inv H7. apply UnionEqTID in H. invertHyp. cleanup. eapply IHspec_multistep_rev. 
     Focus 2. unspecsEq. eauto. auto. auto. }
   } 
   {copy x. unfoldSetEq x. eqIn H3. inv H4. 
    {symmetry in H. apply UnionSingletonCoupleEq in H; eauto.  
     rewrite H. unfoldTac. rewrite UnionSwap. econstructor. Focus 2. eapply SFork; eauto. 
     unfoldTac. rewrite UnionSwap. rewriteUnspec. rewrite UnionSwap.
     eapply IHspec_multistep_rev; eauto. rewrite H. rewrite tUnionSwap.
     rewrite UnionSwap. erewrite specStepUnspecEq; eauto. rewrite UnionSwap. 
     rewrite <- UnionSubtract. auto. auto. }
    {inv H5. stacksNeq. destruct s1; simpl in *; inv H8. }
   }
   {copy x. unfoldSetEq x. eqIn H3. inv H5. 
    {varsEq x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0.  takeTStep. 
     Focus 2. eapply SGet with(h:=remove h' x0); eauto. erewrite lookupRemoveNeq; eauto. 
     rewrite removeReplaceSwitch; auto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. rewrite lookupReplaceNeq in H0; eauto. rewrite H6. 
     rewrite subtractSingle. repeat rewrite unspecUnionComm. apply UnionEqL. 
     erewrite <- eraseTrmConsSame'; eauto. proveUnionEq H. rewrite H6. solveSet. }
    {inv H6. stacksNeq. }
   } 
   {copy x. unfoldSetEq x. eqIn H3. inv H5. 
    {varsEq x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0. 
     rewrite lookupReplaceNeq in H0; eauto. takeTStep. Focus 2. 
     eapply SPut with(h:=remove h' x0); eauto. eapply lookupRemoveNeq; eauto. 
     rewrite removeReplaceSwitch; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. rewrite H6. rewrite subtractSingle. 
     repeat rewrite unspecUnionComm. apply UnionEqL. erewrite <- eraseTrmConsSame'; eauto. 
     proveUnionEq H. rewrite H6. solveSet. } 
    {inv H6. stacksNeq. }
   }
   {copy x. unfoldSetEq x. eqIn H2. inv H4. 
    {varsEq x1 x0. apply UnionSingletonEq in H. rewrite H in H1. 
     eapply smultiRevNewFull in H1. Focus 2. constructor. apply InL. constructor. 
     Focus 2. auto. invertHyp. heapsDisagree. takeTStep. Focus 2. eapply SNew. 
     erewrite removeExtendSwitch; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. erewrite lookupExtendNeq in H0; eauto. 
     rewrite H5. rewrite subtractSingle. repeat rewrite unspecUnionComm. apply UnionEqL. 
     erewrite <- eraseTrmConsSame'; eauto. proveUnionEq H. rewrite H5. solveSet. }
    {inv H5. stacksNeq. rewrite removeExtend. rewrite unspecUnionComm in *.
     apply UnionEqTID in H. invertHyp. erewrite <- eraseTrmConsSame' in H1; eauto. }
   }
   {copy x. unfoldSetEq x. eqIn H3. inv H4. 
    {symmetry in H. apply UnionSingletonCoupleEq in H; eauto.  
     rewrite H. unfoldTac. rewrite UnionSwap. econstructor. Focus 2. eapply SSpec; eauto. 
     unfoldTac. rewrite UnionSwap. rewriteUnspec. rewrite UnionSwap.
     eapply IHspec_multistep_rev; eauto. rewrite H. rewrite tUnionSwap.
     rewrite UnionSwap. erewrite specStepUnspecEq; eauto. rewrite UnionSwap. 
     rewrite <- UnionSubtract. auto. auto. }
    {inv H5. stacksNeq. destruct s1; simpl in *; inv H8. }
   }
  }
  Grab Existential Variables. auto. auto. erewrite lookupExtendNeq in H0; eauto. 
  erewrite lookupRemoveNeq; eauto. auto. auto. auto. auto. 

Qed. 

Theorem alignLists : forall (T:Type) (a:list T) b c d, 
                       b::c = a++b::d -> ~In b a -> a = nil /\ d = c. 
Proof.
  induction a; intros. 
  {simpl in *. inv H. auto. }
  {inversion H. rewrite H2 in H0. exfalso. apply H0. constructor. auto. }
Qed. 
Theorem alignLists' : forall (T:Type) a b c (d:T) e, 
                       a::b = c++d::e -> a <> d -> ~In d c ->
                       exists f, c = a::f. 
Proof.
  induction c; intros. 
  {simpl in *. inv H. exfalso. apply H0; auto. }
  {inversion H. eauto. }
Qed. 

Theorem passThroughRead : forall M M' T s1 ds1 ds2 sc s2 H H' tid TID x E N' d,
        heap_lookup x H' = Some (sfull sc (ds1++[tid]++ds2) SPEC TID N') -> ~List.In tid ds1 ->
        spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,aCons (rAct x M' E d) s1,s2,M))))
                       H' (tUnion T(tSingleton(tid,aCons (rAct x M' E d) s1,s2,M))) ->
          spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,s1,s2,M'))))
                             (replace x (sfull sc (ds1++ds2) SPEC TID N') H') (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H2; intros.
  {symmetry in x. apply eqUnspec in x. unfold commitPool' in x. 
   assert(tIn(tUnion T(tSingleton(tid,aCons(rAct x0 M' E d)s1,s2,M)))(tid,aCons(rAct x0 M' E d)s1,s2,M)). 
   apply InL. constructor. apply x in H. inv H. destruct s1; inv H2. invertHyp. 
   destruct s1; inv H. }
  {inv H. 
   {copy x. unfoldSetEq x. eqIn H5. inv H7. 
    {takeTStep. Focus 2. eapply SBasicStep; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap.  
     eapply IHspec_multistep_rev; eauto. rewrite H8. rewrite subtractSingle.
     repeat rewrite unspecUnionComm. apply UnionEqL. erewrite unspecSpecSame; eauto.
     proveUnionEq H. rewrite H8. solveSet. }
    {inv H8. apply UnionEqTID in H. invertHyp. cleanup. eapply IHspec_multistep_rev. 
     Focus 3. unspecsEq. eauto. auto. auto. eauto. }
   } 
   {copy x. unfoldSetEq x. eqIn H4. inv H5. 
    {symmetry in H. apply UnionSingletonCoupleEq in H; eauto.  
     rewrite H. unfoldTac. rewrite UnionSwap. econstructor. Focus 2. eapply SFork; eauto. 
     unfoldTac. rewrite UnionSwap. rewriteUnspec. rewrite UnionSwap.
     eapply IHspec_multistep_rev; eauto. rewrite H. rewrite tUnionSwap.
     rewrite UnionSwap. erewrite specStepUnspecEq; eauto. rewrite UnionSwap. 
     rewrite <- UnionSubtract. auto. auto. }
    {inv H6. stacksNeq. destruct s1; simpl in *; inv H9. }
   } 
   {admit. }
   {copy x. unfoldSetEq x. eqIn H4. inv H6. 
    {varsEq x1 x0. erewrite HeapLookupReplace in H0. inv H0. destruct ds1; inv H10. 
     eauto. erewrite lookupReplaceNeq in H0. takeTStep. Focus 2. 
     eapply SPut with(h:=replace x0 (sfull sc (ds1 ++ ds2) SPEC TID N') h'); eauto.
     rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. 
     rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. 
     rewrite H7. rewrite subtractSingle. repeat rewrite unspecUnionComm. apply UnionEqL. 
     erewrite <- eraseTrmConsSame'; eauto. proveUnionEq H. rewrite H7. solveSet. auto. }
    {inv H7. stacksNeq. }
   }
   {copy x. unfoldSetEq x. eqIn H3. inv H5. 
    {varsEq x1 x0. erewrite lookupExtend in H0; eauto. inv H0. takeTStep. 
     Focus 2. eapply SNew with(h:=replace x0 (sfull sc (ds1 ++ ds2) SPEC TID N') h'); eauto.
     erewrite extendReplaceSwitch; eauto. erewrite lookupExtendNeq in H0; eauto.
     rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. 
     erewrite lookupExtendNeq in H0; eauto. rewrite H6. rewrite subtractSingle.
     repeat rewrite unspecUnionComm. apply UnionEqL. erewrite <- eraseTrmConsSame'; eauto.
     proveUnionEq H. rewrite H6. solveSet. }
    {inv H6. stacksNeq. }
   }
   {copy x. unfoldSetEq x. eqIn H4. inv H5. 
    {symmetry in H. apply UnionSingletonCoupleEq in H; eauto.  
     rewrite H. unfoldTac. rewrite UnionSwap. econstructor. Focus 2. eapply SSpec; eauto. 
     unfoldTac. rewrite UnionSwap. rewriteUnspec. rewrite UnionSwap.
     eapply IHspec_multistep_rev; eauto. rewrite H. rewrite tUnionSwap.
     rewrite UnionSwap. erewrite specStepUnspecEq; eauto. rewrite UnionSwap. 
     rewrite <- UnionSubtract. auto. auto. }
    {inv H6. stacksNeq. destruct s1; simpl in *; inv H9. }
   }
  }
  Grab Existential Variables. auto. auto. eauto.  rewrite lookupReplaceNeq. eauto. 
  auto. auto. auto. auto. auto. 
Qed. 


Axiom UnionCoupleNeq : forall T T' tid tid' n n' s1 s1' s2 s2' S1 S1' S2 S2' M M' N N',
                           tid <> tid' -> 
                           tUnion T (tCouple(tid,s1,s2,M)(n::tid,S1,S2,N)) = 
                           tUnion T'(tCouple(tid',s1',s2',M')(n'::tid',S1',S2',N')) -> 
                           T' = tUnion (Setminus thread T (tCouple(tid',s1',s2',M')(n'::tid',S1',S2',N')))
                                       (tCouple(tid,s1,s2,M)(n::tid,S1,S2,N)) /\
                           T = tUnion (Setminus thread T' (tCouple(tid,s1,s2,M)(n::tid,S1,S2,N)))
                                       (tCouple(tid',s1',s2',M')(n'::tid',S1',S2',N')).


Theorem UnionSetminus : forall (X : Type) (T : Ensemble X) x1,
       Setminus X (Union X (Setminus X T x1) x1) x1 =
       Setminus X T x1. 
Admitted. 

Theorem passThroughFork : forall M M' T s1 s2 H n H' tid E N' d s2' N,
        spec_multistep_rev H (unspecPoolAux(tUnion T(tCouple(tid,aCons (fAct M' E N' d n) s1,s2,M)
                                                            (n::tid,locked nil, s2', N))))
                           H' (tUnion T(tCouple(tid,aCons (fAct M' E N' d n) s1,s2,M)
                                               (n::tid,locked nil, s2', N))) ->
        spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,s1,s2,M'))))
                           H' (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. generalize_eqs_vars H0. induction H0; simplify_dep_elim; intros.
  {symmetry in x. apply eqUnspec in x. unfold commitPool' in x. 
   assert(tIn(tUnion T (tCouple (tid, aCons (fAct M' E N' d n) s1, s2, M)
              (n :: tid, locked [], s2', N)))(n :: tid, locked [], s2', N)). 
   apply InL. apply Couple_r. apply x in H. inv H. inv H0. invertHyp. inv H. }
  {inv H. 
   {copy x. unfoldSetEq x. eqIn H3. inv H5. 
    {takeTStep. Focus 2. eapply SBasicStep; eauto. rewriteUnspec. unfoldTac. 
     rewrite UnionSwap. eapply IHspec_multistep_rev; eauto.  rewrite H6.
     rewrite subtractSingle. repeat rewrite unspecUnionComm. apply UnionEqL. 
     erewrite unspecSpecSame; eauto. apply UnionSingletonCoupleEq in H. rewrite H. 
     unfoldTac. rewrite UnionSwap. auto. rewrite H6. solveSet. }
    {inv H6.
     {unfoldTac. rewrite pullOutL in H. apply UnionEqTID in H. invertHyp. 
      cleanup. eapply IHspec_multistep_rev. Focus 2. rewrite Union_associative. 
      rewrite <- coupleUnion. rewrite couple_swap. auto. repeat rewrite coupleUnion. 
      repeat rewrite unspecUnionComm. erewrite unspecSpecSame; eauto. }
     {unfoldTac. rewrite pullOutR in H. apply UnionEqTID in H. invertHyp. cleanup. 
      eapply IHspec_multistep_rev. Focus 2. rewrite Union_associative. 
      rewrite <- coupleUnion. auto. repeat rewrite coupleUnion.
      repeat rewrite unspecUnionComm. repeat apply UnionEqR. apply unspecSpecSame. auto. }
    }
   }
   {unfoldTac. exMid tid tid0. 
    {repeat rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. 
     apply UnionEqTID in H. invertHyp. inv H1. cleanup. rewrite coupleUnion in H0. 
     repeat rewrite unspecUnionComm in *. rewrite unspecEmpty in H0. unfoldTac. 
     rewrite union_empty_r in H0. erewrite <- eraseTrmConsSame' in H0;eauto. }
    {apply UnionCoupleNeq in x; auto. invertHyp. rewrite H. unfoldTac. rewrite UnionSwap. 
     econstructor. Focus 2. eapply SFork; eauto. rewriteUnspec. unfoldTac. 
     rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite H. 
     repeat rewrite coupleUnion. repeat rewrite unspecUnionComm. apply UnionEqL. 
     apply UnionEqR. rewrite unspecEmpty. unfoldTac. rewrite union_empty_r. 
     symmetry. eapply eraseTrmConsSame'; eauto. admit. }
   }
   {copy x. unfoldSetEq x. eqIn H2. inv H4. 
    {takeTStep. Focus 2. eapply SGet; eauto. rewriteUnspec. unfoldTac.
     rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite H5. 
     rewrite subtractSingle. repeat rewrite unspecUnionComm. apply UnionEqL. 
     apply UnionEqR. symmetry. apply eraseTrmConsSame'. auto. 
     apply UnionSingletonCoupleEq in H. rewrite H.  unfoldTac. 
     rewrite UnionSwap. auto. rewrite H5. solveSet. }
    {inv H5. stacksNeq. destruct b; simpl in *; inv H8. }
   }
   {copy x. unfoldSetEq x. eqIn H2. inv H4. 
    {takeTStep. Focus 2. eapply SPut; eauto. rewriteUnspec. unfoldTac.
     rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite H5. 
     rewrite subtractSingle. repeat rewrite unspecUnionComm. apply UnionEqL. 
     apply UnionEqR. symmetry. apply eraseTrmConsSame'. auto. 
     apply UnionSingletonCoupleEq in H. rewrite H.  unfoldTac. 
     rewrite UnionSwap. auto. rewrite H5. solveSet. }
    {inv H5. stacksNeq. destruct b; simpl in *; inv H8. }
   }
   {copy x. unfoldSetEq x. eqIn H1. inv H3. 
    {takeTStep. Focus 2. eapply SNew; eauto. rewriteUnspec. unfoldTac.
     rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite H4. 
     rewrite subtractSingle. repeat rewrite unspecUnionComm. apply UnionEqL. 
     apply UnionEqR. symmetry. apply eraseTrmConsSame'. auto. 
     apply UnionSingletonCoupleEq in H. rewrite H.  unfoldTac. 
     rewrite UnionSwap. auto. rewrite H4. solveSet. }
    {inv H4. stacksNeq. destruct b; simpl in *; inv H7. }
   }
   {

Theorem rollbackWF : forall H H' T TR TR' tidR acts,
                       wellFormed H (tUnion T TR) ->
                       rollback tidR acts H TR H' TR' ->
                       wellFormed H' (tUnion T TR'). 
Proof.
  intros. induction H1. 
  {auto. }
  {subst. inv H0. inv H1. apply IHrollback. unfoldTac. 
   econstructor; eauto. 
   erewrite unspecHeapRBRead; eauto. rewrite <- Union_associative in H4. 
   copy H4. rewrite smultiSmultiRevEq in H4. eapply passThroughRead in H4; eauto. 
   repeat rewrite <- Union_associative. rewrite smultiSmultiRevEq. eauto. }
  {subst. inv H0. inv H3. apply IHrollback. unfoldTac. econstructor; eauto. 
   repeat rewrite <- Union_associative in *. rewrite smultiSmultiRevEq in *. 
   eapply passThroughFork; eauto. }
  {subst. inv H0. inv H2. apply IHrollback. unfoldTac. econstructor; eauto. 
   erewrite unspecHeapRBWrite; eauto. repeat rewrite <- Union_associative in *. 
   rewrite smultiSmultiRevEq in *.  eapply passThroughWrite; eauto. }
  {subst. inv H0. inv H3. apply IHrollback. unfoldTac. econstructor; eauto. 
   erewrite <- unspecHeapRBNew; eauto. repeat rewrite <- Union_associative in *. 
   rewrite smultiSmultiRevEq in *. eapply passThroughNew; eauto. }
  {