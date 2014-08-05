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

Theorem passThroughAct : forall a M M' T s1 s2 H H' tid,
        actionTerm a M' ->
        spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,aCons a s1,s2,M))))
                       H' (tUnion T(tSingleton(tid,aCons a s1,s2,M))) ->
        exists H'' T'', 
          spec_multistep_rev H (unspecPoolAux(tUnion T(tSingleton(tid,s1,s2,M'))))
                       H'' (tUnion T'' (tSingleton(tid,s1,s2,M'))) /\
          spec_multistep_rev H'' (tUnion T'' (tSingleton(tid,s1,s2,M')))
                         H (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.  
  Admitted. 

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

Theorem unspecSpecSame : forall a M' N s1 s2 tid,
                             unspecPoolAux(tSingleton(tid,aCons a s1,s2,M')) = 
                             unspecPoolAux(tSingleton(tid,aCons a s1,s2,N)). 
Proof.
  intros. destruct s1. 
  {simpl. repeat erewrite unspecSingleton; eauto. }
  {destructLast l. 
   {Admitted. 

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

Theorem passThroughWrite : forall M M' T T' s1 sc s2 H H' tid x E N' d,
        heap_lookup x H' = Some (sfull sc [] SPEC tid N') -> 
        spec_multistep_rev H (tUnion T(unspecPoolAux(tSingleton(tid,aCons (wAct x M' E N' d) s1,s2,M))))
                       H' (tUnion T'(tSingleton(tid,aCons (wAct x M' E N' d) s1,s2,M))) ->
          spec_multistep_rev H (tUnion T(unspecPoolAux(tSingleton(tid,s1,s2,M'))))
                             (replace x (sempty sc) H') (tUnion T'(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H1. 
  {admit. }
  {inv H. 
   {exMid tid tid0. 
    {apply UnionEqTID in x. invertHyp. eapply IHspec_multistep_rev. Focus 3. 
     auto. Focus 3. auto. eauto. erewrite unspecSpecSame. eauto. }
    {copy x. unfoldSetEq x. eqIn H5. inv H7. takeTStep. Focus 2. eapply SBasicStep; eauto.
     unfoldTac. rewrite <- UnionSwap. eapply IHspec_multistep_rev; eauto. proveUnionEq H. 
     rewrite H9. solveSet. inv H9. exfalso. apply H4; auto. }
   }
   {copy x. unfoldSetEq x. eqIn H3. inv H4. symmetry in H. apply UnionSingletonCoupleEq in H; eauto. 
    rewrite H. unfoldTac. rewrite UnionSwap. econstructor. Focus 2. eapply SFork; eauto. 
    unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite UnionSwap. 
    rewrite <- UnionSubtract; auto. inv H5. apply aConsEq in H8. invertHyp. solveByInv. 
    destruct s1; simpl in *; inv H8. }
   {exMid tid TID. apply UnionEqTID in x. invertHyp. stacksNeq. copy x. unfoldSetEq H. 
    eqIn H4. inv H. 
    {varsEq x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0. takeTStep. Focus 2. 
     eapply SGet with(h:=replace x0 (sempty sc) h'). rewrite lookupReplaceNeq; eauto.
     rewrite lookupReplaceSwitch; auto. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. rewrite lookupReplaceNeq in H0; eauto. 
     proveUnionEq x. rewrite H6. solveSet. }
    {inv H6. stacksNeq. }
   }
   {copy x. unfoldSetEq H. eqIn H3. inv H. 
    {varsEq x1 x0. 
     {erewrite HeapLookupReplace in H0; eauto. inv H0. apply UnionEqTID in x. 
      invertHyp. stacksNeq. rewrite replaceOverwrite. erewrite <- eraseTrmConsSame' in H1; eauto. 
      rewrite replaceSame; eauto. }
     {takeTStepRev. Focus 2. eapply SPut with(h:=replace x0 (sempty sc) h'); eauto. 
      rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. unfoldTac. 
      rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite lookupReplaceNeq in H0; eauto. 
      proveUnionEq x. rewrite H5. solveSet. }
    }
    {inv H5. stacksNeq. erewrite <- eraseTrmConsSame' in H1; eauto. rewrite replaceOverwrite. 
     rewrite replaceSame; eauto. apply UnionEqTID in x. invertHyp. assumption.
     erewrite HeapLookupReplace in H0; eauto. inv H0. eauto. }
   }
   {exMid tid tid0. apply UnionEqTID in x. invertHyp. stacksNeq. copy x. unfoldSetEq H. 
    eqIn H3. inv H. 
    {varsEq x1 x0. erewrite lookupExtend in H0. inv H0. takeTStep. Focus 2. 
     eapply SNew with(h:=replace x0 (sempty sc) h'). erewrite extendReplaceSwitch; eauto. 
     erewrite lookupExtendNeq in H0; eauto. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. erewrite lookupExtendNeq in H0; eauto. 
     proveUnionEq x. rewrite H5. solveSet. }
    {inv H5. stacksNeq. }
   }
   {copy x. unfoldSetEq x. eqIn H3. inv H4. symmetry in H. apply UnionSingletonCoupleEq in H. 
    rewrite H. unfoldTac. rewrite UnionSwap. econstructor. Focus 2. eapply SSpec; eauto. 
    unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite UnionSwap. 
    rewrite <- UnionSubtract. auto. auto. auto. inv H5. stacksNeq. destruct s1; simpl in*; inv H8. }
  }
  Grab Existential Variables. rewrite lookupReplaceNeq. eauto. auto. 
Qed. 


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
   copy H4. rewrite smultiSmultiRevEq in H4. eapply passThroughAct in H4. 
   Focus 2. constructor. invertHyp. admit. }
  {subst. inv H0. inv H3. admit. }
  {subst. inv H0. inv H2. apply IHrollback. unfoldTac. econstructor; eauto. 
   erewrite unspecHeapRBWrite; eauto. rewrite <- Union_associative in H4. 
   copy H4. rewrite smultiSmultiRevEq in H4. erewrite unspecUnionComm in H4. 
   eapply passThroughWrite in H4; eauto. repeat rewrite <- Union_associative. 
   rewrite smultiSmultiRevEq. rewrite unspecUnionComm. eauto. }
  {subst. inv H0. inv H3. apply IHrollback. unfoldTac. econstructor; eauto. 
   erewrite <- unspecHeapRBNew; eauto. rewrite <- Union_associative in H5. 
   copy H5. rewrite smultiSmultiRevEq in H5. erewrite unspecUnionComm in H5. 
   


