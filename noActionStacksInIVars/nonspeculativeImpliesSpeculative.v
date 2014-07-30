Require Import SfLib. 
Require Import NonSpec.  
Require Import AST. 
Require Import classifiedStep. 
Require Import Spec.  
Require Import Heap. 
Require Import Coq.Sets.Ensembles.
Require Import sets. 
Require Import Powerset_facts. 
Require Import erasure. 
Require Import SpecLib. 
Require Import unspec. 
Require Import Coq.Logic.ProofIrrelevance. 

Ltac existTac e := let n := fresh in
                   try(assert(n:exists e', eraseTerm e' = e) by apply eTerm; invertHyp);
                   try(assert(n:exists e', eraseCtxt e' = e) by apply eCtxt; invertHyp). 


Ltac eTermTac := 
  match goal with
      |H:pbasic_step ?M ?M' |- _ => assert(exists M'', eraseTerm M'' = M') by apply eTerm;
                                   invertHyp
  end. 

Theorem eraseBasicStep : forall x t t', 
                           pbasic_step t t' -> eraseThread x (pSingleton t) ->
                           exists tid s2 M M', x = (tid, unlocked nil, s2, M) /\ eraseTerm M = t /\
                                               eraseTerm M' = t'. 
Proof.
  intros. inv H0. 
  {apply SingletonEq in H3. inversion H; subst; eTermTac; repeat econstructor; eauto. }
  {apply SingletonEq in H1. subst. copy d. rewrite <- decomposeErase in H0; eauto. 
   inv H; match goal with
            |H:pdecompose ?M ?E ?e, H':pdecompose ?M ?E' ?e' |- _ => 
             eapply pctxtUnique in H; eauto; invertHyp 
          end; solveByInv. }
  {apply SingletonEq in H1. subst. copy d. rewrite <- decomposeErase in H0; eauto. 
   inv H; match goal with
            |H:pdecompose ?M ?E ?e, H':pdecompose ?M ?E' ?e' |- _ => 
             eapply pctxtUnique in H; eauto; invertHyp 
          end; solveByInv. }
  {apply SingletonEq in H1. subst. copy d. rewrite <- decomposeErase in H0; eauto. 
   inv H; match goal with
            |H:pdecompose ?M ?E ?e, H':pdecompose ?M ?E' ?e' |- _ => 
             eapply pctxtUnique in H; eauto; invertHyp 
          end; solveByInv. }
  {apply SingletonEq in H1. subst. copy d. rewrite <- decomposeErase in H0; eauto. 
   inv H; match goal with
            |H:pdecompose ?M ?E ?e, H':pdecompose ?M ?E' ?e' |- _ => 
             eapply pctxtUnique in H; eauto; invertHyp 
          end; solveByInv. }
  {apply SingletonEq in H1. subst. copy d. rewrite <- decomposeErase in H0; eauto. 
   inv H; match goal with
            |H:pdecompose ?M ?E ?e, H':pdecompose ?M ?E' ?e' |- _ => 
             eapply pctxtUnique in H; eauto; invertHyp 
          end; solveByInv. }
  {symmetry in H3. apply SingletonNeqEmpty in H3. solveByInv. }
  {symmetry in H3. apply SingletonNeqEmpty in H3. solveByInv. }
Qed. 


Theorem eraseThreadCardinality : forall t t', eraseThread t t' -> 
                                              t' = Empty_set ptrm \/ exists t'', t' = pSingleton t''.
Proof.
  intros. inv H; eauto. 
Qed. 


Theorem ePool : forall PT, exists T, erasePoolAux T = PT. 
Proof.
  Admitted. 

Theorem UnionAdd : forall X T t, Add X T t = Union X T (Singleton X t). 
Proof.
  intros. unfold Add. auto. 
Qed. 

Theorem splitPool : forall T PT pt,
                      erasePoolAux T = pUnion PT (pSingleton pt) ->
                      exists T' t', T = tAdd T' t' /\ 
                                    erasePoolAux T' = PT /\ eraseThread t' (pSingleton pt). 
Proof.
  intros. copy H.  unfoldSetEq H. assert(In ptrm (pUnion PT (pSingleton pt)) pt). 
  apply Union_intror. constructor. apply H2 in H. inv H. inv H3. inv H6. copy H.
  apply pullOut in H. exists (Subtract thread T (t,s0,s3,M0)). exists (t,s0,s3,M0). 
  split. rewrite H. unfold tAdd. rewrite <- UnionAdd. rewrite <- add_subtract; auto. 
  split. Focus 2. clear H. inv H4; inv H5; eauto. eqSets. 
  Admitted. 



Theorem simBasicStep : forall t t', pbasic_step (eraseTerm t) (eraseTerm t') ->
                                    basic_step t t'. 
Proof.
  intros. inv H. 
  {existTac E. existTac e. existTac N. rewrite <-eraseOpenComm in H0.
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. econstructor. 
   rewrite decomposeErase in H2; eauto. }
  {existTac E. existTac V1. existTac V2. rewrite <- eraseFill in H0.
   apply eraseTermUnique in H0. subst. econstructor. rewrite decomposeErase in H2; eauto. 
   simpl. auto. }
  {existTac E. existTac V1. existTac V2. rewrite <- eraseFill in H0.
   apply eraseTermUnique in H0. subst. eapply basicProjR. rewrite decomposeErase in H2; eauto. 
   simpl. auto. }
  {existTac E. existTac N. existTac M.
   replace (papp (eraseTerm x0) (eraseTerm x1)) with (eraseTerm (app x0 x1)) in H0; auto. 
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. eapply basicBind.  
   rewrite decomposeErase in H2; eauto. }
  {existTac E. existTac N. existTac M.
   replace (praise (eraseTerm x1)) with (eraseTerm (raise x1)) in H0; auto. 
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. eapply basicBindRaise.
   rewrite decomposeErase in H2; eauto. simpl. auto. }
  {existTac E. existTac N. existTac M. 
   replace (papp (eraseTerm x0) (eraseTerm x1)) with (eraseTerm (app x0 x1)) in H0; auto. 
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. eapply basicHandle. 
   rewrite decomposeErase in H2; eauto. }
  {existTac E. existTac M. existTac N. replace(pret (eraseTerm x0)) with (eraseTerm (ret x0)) in H0. 
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. eapply basicHandleRet. 
   rewrite decomposeErase in H2; eauto. simpl. auto. simpl. auto. }
Qed. 

Theorem decompNeq : forall t E e E' e',
                      decompose t E e -> pdecompose (eraseTerm t) E' e' -> 
                      eraseTerm e <> e' -> False. 
Proof.
  intros. rewrite <- decomposeErase in H; eauto. eapply pctxtUnique in H0; eauto. 
  invertHyp. apply H1. auto.
Qed. 

Ltac inv' := unfoldTac; unfold pSingleton in *; 
  match goal with
      |H:Singleton ?X ?T = Empty_set ?X |- _ => apply SingletonNeqEmpty in H; inv H
      |H:Empty_set ?X = Singleton ?X ?T |- _ => symmetry in H; inv'
      |H:Singleton ?X ?t = Singleton ?X ?t' |- _ => apply SingletonEq in H; subst
      |H:eraseTerm ?x = eraseTerm ?y |- _ => apply eraseTermUnique in H; subst
      |H:decompose ?M ?E ?e,H':pdecompose ?M' ?E' ?e' |- _ =>
       eapply decompNeq in H'; eauto; try solveByInv; introsInv
      |_ => invertListNeq
  end. 

Ltac solveByInv :=
  match goal with
      |H:_ |- _ => solve[inv H|inv']
  end. 

Theorem eraseAuxEq : forall T T', erasePoolAux T = T' -> erasePool T T'. 
Proof.
  intros. rewrite <- H. constructor. 
Qed. 

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' H T,
                               pstep PH PT pt (pOK PH' PT pt') -> eraseHeap H = PH ->
                               erasePool T (Union ptrm PT pt) ->
                               exists H' T' t' t'',
                                 T = tUnion T' t' /\ 
                                 eraseHeap H' = PH' /\ erasePool (tUnion T' t'') (Union ptrm PT pt') /\
                                 multistep H T' t' (OK H' T' t''). 
Proof.
  intros. inversion H0; subst.  
  {inv H2.  apply splitPool in H5. invertHyp. exists H. exists x. exists (tSingleton x0). 
   eapply eraseBasicStep in H2; eauto. invertHyp. apply simBasicStep in H7. 
   econstructor. split. unfold tAdd. unfold Add. auto. split; auto. split. 
   Focus 2. eapply multi_step. rewrite <- union_empty_l at 1. auto. eapply BasicStep. 
   eauto. unfoldTac. rewrite union_empty_l. constructor.
   replace (pSingleton (eraseTerm x4)) with (erasePoolAux(tSingleton(x1,unlocked nil,x2,x4))). 
   rewrite <- eraseUnionComm. constructor. erewrite erasePoolSingleton; eauto. }
  {existTac E. existTac M. existTac N. inv H2. apply splitPool in H4. invertHyp. 
   inv H2; try solve[inv'; try inv']. 
   {unfold pSingleton in *. invertHyp. exists H. econstructor. 
    econstructor. econstructor. split. unfoldTac. auto. split; auto. split. Focus 2. eapply multi_step. 
    rewrite <- union_empty_l at 1. auto. eapply Spec. unfoldTac. rewrite union_empty_l. 
    eapply multi_step. rewrite <- union_empty_l at 1. auto. eapply PopSpec. simpl. 
    rewrite app_nil_l. auto. unfoldTac. rewrite union_empty_l. constructor. unfoldTac. 
    rewrite coupleUnion. apply eraseAuxEq. repeat rewrite eraseUnionComm. simpl.
    erewrite erasePoolSingleton. Focus 2. auto. erewrite erasePoolSingleton; eauto. 
    rewrite union_empty_r. existTac E. existTac M. existTac N.  rewrite eraseFill. simpl. auto. }
   {unfold pSingleton in *. invertHyp. exists H. exists x2. econstructor. econstructor. split. 
    unfoldTac. auto. split; auto. split. Focus 2. constructor. unfoldTac. apply eraseAuxEq. 
    rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto. 
    replace (specpe

eapply tEraseSpecRet.







alsdkjfalskdjfh