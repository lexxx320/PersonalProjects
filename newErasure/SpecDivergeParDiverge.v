Require Import AST.       
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 
Require Import erasure.  
Require Import classifiedStep.  
Require Import Powerset_facts. 

CoInductive ParDiverge : pHeap -> pPool -> Prop :=
|divergeStep : forall T1 T2 T2' H H',
                 pstep H T1 T2 (pOK H' T1 T2') -> 
                 ParDiverge H' (Union ptrm T1 T2') -> ParDiverge H (Union ptrm T1 T2)
.

Theorem ParDivergeMultistep : forall H T H' T', 
                   ParDiverge H' T' ->
                   pmultistep H (Empty_set ptrm) T (pOK H' (Empty_set ptrm) T') ->
                   ParDiverge H T.
Proof.
  intros. remember (Empty_set ptrm). remember (pOK H' e T'). induction H1; subst.  
  {inversion Heqp; subst. assumption. }
  {econstructor. unfold pUnion in H1. rewrite Union_commutative in H1. 
   rewrite union_empty in H1. eassumption. auto. } 
  {inversion Heqp. }
Qed. 

CoInductive SpecDiverge : sHeap -> pool-> Prop :=
|specDiverge : forall T1 T2 T2' H H' H'' T,
                 spec_multistep H tEmptySet T H' tEmptySet (tUnion T1 T2) -> 
                 Disjoint thread T1 T2 ->
                 progress_step H' T1 T2 (OK H'' T1 T2') -> 
                 SpecDiverge H' (tUnion T1 T2') -> SpecDiverge H T.

Theorem termErasePoolErase : forall tid M M' s2,
                               eraseTerm M M' -> 
                               erasePoolAux (tSingleton(tid,nil,s2,M)) = 
                               (pSingleton M'). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H0; subst. inversion H1; subst. cleanup. inversion H4; subst. clear H4. 
   inversion H2; subst; try invertListNeq. inversion H3; subst. 
   eapply termErasureDeterminism in H. rewrite <- H. econstructor. assumption. }
  {inversion H0; subst. clear H0.
   inversion H; subst; destruct tid; destruct p; try solve[repeat econstructor];
   try solve[inversion H; subst; repeat econstructor; eauto]. 
  }
Qed. 

Ltac eraseEq :=
  match goal with
      |H:eraseTerm ?M ?M1, H':eraseTerm ?M ?M2 |- _ => 
       eapply termErasureDeterminism in H; eauto; subst
  end. 

Theorem eraseValEq : forall e e', eraseTerm e e' -> (val e <-> pval e'). 
Proof.
  intros. split; intros; try solve[ 
  inversion H0; subst; inversion H; subst; constructor]. Qed. 

Ltac valEq :=
  match goal with
      |H:eraseTerm ?e ?e', H':val ?e |- pval ?e' =>
       apply eraseValEq in H; apply H in H'; auto
      |H:eraseTerm ?e ?e', H':~val ?e |- ~pval ?e' =>
       intros c; apply eraseValEq in H; apply H in c; contradiction
  end. 

Theorem eraseDecomp : forall t t' E e E' e', 
                        (forall M N, e <> spec M N) -> decompose t E e ->
                        eraseContext E E' -> eraseTerm e e' ->
                        eraseTerm t t' -> pdecompose t' E' e'. 
Proof.
  intros. generalize dependent e. generalize dependent e'. generalize dependent t. 
  generalize dependent t'. induction H1; intros; try solve[
  match goal with
      |H:decompose ?t ?E ?e |- _ => 
       inversion H; subst
  end; inversion H3; subst; eraseEq; constructor;[valEq|
   eapply IHeraseContext; eauto]]. 
  {inversion H0; subst. inversion H3; subst. constructor. valEq. 
   eapply IHeraseContext; eauto. }
  {inversion H0; subst. inversion H3; subst. constructor. valEq. 
   eapply IHeraseContext; eauto. }
  {inversion H0; subst; inversion H3; subst; inversion H2; subst; 
   eraseEq; cleanup; constructor; valEq. }
Qed. 

Theorem eraseCtxtTotal : forall E, exists E', eraseContext E E'. 
Proof.
  induction E; try solve[ 
  assert(exists t', eraseTerm t t') by apply erasureTotal; invertHyp;   
  repeat econstructor; eauto]; 
  try solve[invertHyp; repeat econstructor; eauto]. 
  assert(exists t0', eraseTerm t0 t0') by apply erasureTotal. invertHyp. 
  repeat econstructor; eauto. repeat econstructor. Qed. 
  

Ltac existsTac :=
  match goal with
      |H:decompose ?t ?E ?e, H':eraseTerm ?t ?T ?x |- _ => 
       assert(exists E', eraseContext E T E') by apply eraseCtxtTotal; 
         assert(exists e', eraseTerm e T e') by apply erasureTotal
  end. 

Axiom ParDisjoint : forall T1 T2, Disjoint ptrm T1 T2. 

Ltac eraseExists t :=
  try (assert(exists t', eraseTerm t t') by apply erasureTotal);
  try (assert(exists E', eraseContext t E') by apply eraseCtxtTotal); invertHyp. 

Theorem eraseUnion : forall T t t', eraseThread t t' ->
                                    erasePoolAux (Union thread T (tSingleton t)) = 
                                    Union ptrm (erasePoolAux T) t'. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H0; subst. inversion H1; subst. cleanup. inversion H4; subst. 
   {econstructor. econstructor. econstructor. eassumption. auto. 
    eassumption. auto. }
   {inversion H5; subst. apply Union_intror. eapply erasureDeterminism in H2; eauto. 
    subst. assumption. }
  }
  {inversion H0; subst. 
   {inversion H1; subst. inversion H2; subst. cleanup. econstructor. 
    econstructor. econstructor. eassumption. auto. eassumption. auto. }
   {inversion H; subst; destruct tid; destruct p; try solve[ 
    econstructor;[econstructor;[apply Union_intror;econstructor|auto]|
    eauto|auto]]. 
   }
  }
Qed. 

Theorem eraseUnionCouple : forall T t1 t2 t1' t2', 
                             eraseThread t1 t1' -> eraseThread t2 t2' ->
                             erasePoolAux(Union thread T (tCouple t1 t2)) = 
                             Union ptrm (erasePoolAux T) (Union ptrm t1' t2'). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H1; subst. inversion H2; subst. cleanup. inversion H5; subst. 
   {econstructor. econstructor. econstructor. eauto. auto. eauto. auto. }
   {inversion H6; subst. 
    {apply Union_intror. econstructor. eapply erasureDeterminism in H3; eauto.
     subst; auto. }
    {apply Union_intror. apply Union_intror. eapply erasureDeterminism in H3; eauto. 
     subst; auto. }
   }
  }
  {inversion H1; subst. 
   {inversion H2; subst. inversion H3; subst. cleanup. econstructor. econstructor. 
    econstructor. eassumption. auto. eauto. auto. }
   {inversion H2; subst. 
    {inversion H; subst; destruct tid; destruct p; try solve[
     inversion H2; subst; econstructor;[econstructor;[apply Union_intror; 
     apply Couple_l|auto]|eauto|eauto|econstructor;[ apply Union_intror; 
     apply Couple_l|auto]|eauto|auto]]. 
    }
    {inversion H0; subst; destruct tid; destruct p; try solve[ 
     inversion H3; subst; econstructor;[econstructor;[apply Union_intror; 
     apply Couple_r; auto|eauto]|eauto|auto]]. 
     inversion H3. inversion H3. 
    }
   }
  }
Qed. 
     
Hint Constructors eraseTerm. 

Theorem eraseOpen : forall e1 e2 n e1' e2', 
                      eraseTerm e1 e1' -> eraseTerm e2 e2' -> 
                      eraseTerm (open n e1 e2) (popen n e1' e2').  
Proof.
  intros. generalize dependent e1. generalize dependent e1'. generalize dependent n.
  induction H0; intros; simpl; auto.  
  {destruct (beq_nat n i) eqn:eq; auto. }
  {admit. }
  {admit. }
  {admit. }
Qed. 

Theorem coupleEqUnion : forall X T1 T2,
                          Couple X T1 T2 = Union X (Singleton X T1) (Singleton X T2).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H. subst. repeat constructor. subst. apply Union_intror. constructor. }
  {inversion H; subst. inversion H0; subst; constructor. inversion H0; subst. 
   apply Couple_r. }
Qed. 

Theorem lookupCommit : forall x H ds w N N' H', 
                         eraseHeap H H' -> eraseTerm N N' ->
                         heap_lookup x H = Some(sfull nil ds nil w N) ->
                         heap_lookup x H' = Some(pfull N'). 
Proof.
  intros. induction H0; try solve[ 
  simpl in *; destruct (beq_nat x i); auto; inversion H2; subst]. 
  {simpl in *. destruct (beq_nat x i) eqn:eq; auto. inversion H2; subst.  
   eapply termErasureDeterminism in H1; eauto. subst. auto. }
  {simpl in *. inversion H2. }
Qed. 

Theorem lookupEmptyCommit : forall x H H', 
                              eraseHeap H H' -> 
                              heap_lookup x H = Some(sempty nil) ->
                              heap_lookup x H' = Some pempty. 
Proof.
  intros. induction H0; try solve[ 
  simpl in *; destruct (beq_nat x i); auto; inversion H1].
  inversion H1. Qed. 

Theorem eraseCommitFull : forall H H' x t N N', 
                            eraseHeap H H' -> eraseTerm N N' ->
                            heap_lookup x H = Some (sempty nil) ->
                            eraseHeap (replace x (sfull nil nil nil t N) H)
                                      (replace x (pfull N') H').
Proof.
  intros. induction H0; simpl in *;
  try solve[destruct (beq_nat x i); eauto; inversion H2]. 
  inversion H2. Qed. 


Theorem SpecDivergeParDiverge : forall H H' T T',
                                  eraseHeap H H' -> erasePool T T' ->
                                  SpecDiverge H T -> ParDiverge H' T'. 
Proof.
  cofix CH. intros. inversion H2; subst. 
  apply spec_multistepErase with (H'':=H')(T'':=T')in H4; auto. 
  inversion H4; subst. clear H4. inversion H6; subst.
  {inversion H8; subst. rewrite eraseUnionComm.  
   assert(exists t', eraseTerm t t'). apply erasureTotal. 
   invertExists. erewrite termErasePoolErase. Focus 2. eassumption. 
   eraseExists E. eraseExists e. eraseExists N. econstructor.  
   apply PBetaRed. eapply eraseDecomp. Focus 2. eassumption. intros. intros c. 
   inversion c. eassumption. constructor. constructor. eauto. eauto. auto. 
   eapply CH. eassumption. Focus 2. eapply H7. 
   erewrite <- eraseUnion. constructor. constructor. apply eraseFill; auto. 
   apply eraseOpen; auto. } 
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists V1. eraseExists V2. econstructor.  
   eapply pProjectL. eapply eraseDecomp; eauto. intros. intros c; inversion c. 
   eapply CH. eauto. Focus 2. eapply H7. erewrite <- eraseUnion. 
   constructor. constructor. apply eraseFill; auto. }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists V1. eraseExists V2. econstructor.
   eapply pProjectR. eapply eraseDecomp; eauto. intros. intros c; inversion c. 
   eapply CH. eauto. Focus 2. eapply H7. erewrite <- eraseUnion. 
   constructor. constructor. apply eraseFill; auto. }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists M. eraseExists N. econstructor. 
   eapply PBind. eapply eraseDecomp; eauto. intros. intros c; inversion c. 
   eapply CH. eauto. Focus 2. eapply H7. erewrite <- eraseUnion. 
   constructor. constructor. apply eraseFill; auto. }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists M. eraseExists N. econstructor. 
   eapply PBindRaise. eapply eraseDecomp; eauto. intros. intros c; inversion c. 
   eapply CH. eauto. Focus 2. eapply H7. erewrite <- eraseUnion. 
   constructor. constructor. apply eraseFill; auto. }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists M. eraseExists N. econstructor. 
   eapply pHandle. eapply eraseDecomp; eauto. intros. intros c; inversion c. 
   eapply CH. eauto. Focus 2. eapply H7. erewrite <- eraseUnion. 
   constructor. constructor. apply eraseFill; auto. }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists M. eraseExists N. econstructor.  
   eapply pHandleRet. eapply eraseDecomp; eauto. intros. intros c; inversion c. 
   eapply CH. eauto. Focus 2. eapply H7. erewrite <- eraseUnion. 
   constructor. constructor. apply eraseFill; auto. }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm M t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   econstructor. apply PTerminate. 
   eapply CH. eauto. Focus 2. eapply H7. unfold tUnion. 
   unfold tEmptySet. repeat rewrite union_empty. constructor. }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists M. econstructor. apply pFork. 
   eapply eraseDecomp; eauto. intros. intros c. inversion c. eapply CH. 
   eauto. Focus 2. eapply H7. rewrite coupleEqUnion. erewrite <- eraseUnionCouple. 
   constructor. constructor. apply eraseFill; eauto. constructor. auto. }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists N. econstructor. 
   eapply PGet. eapply lookupCommit. eapply H3. eapply H13. eassumption. 
   eapply eraseDecomp; eauto. intros. intros c. inversion c. 
   eapply CH. eauto. Focus 2. eapply H7. erewrite <- eraseUnion. 
   constructor. constructor. apply eraseFill; auto. apply decomposeEq in H10. 
   subst. assumption.  }
  {inversion H8; subst. rewrite eraseUnionComm. assert(exists t', eraseTerm t t'). 
   apply erasureTotal. invertHyp. erewrite termErasePoolErase; eauto. 
   eraseExists E. eraseExists N. econstructor. eapply PPut.  
   eapply eraseDecomp; eauto. intros. intros c. inversion c. Focus 3. 
   eapply CH. Focus 3. eap



