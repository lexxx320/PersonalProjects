Require Import SfLib. 
Require Import NonSpec.  
Require Import AST. 
Require Import Spec.  
Require Import Heap. 
Require Import Coq.Sets.Ensembles.
Require Import sets. 
Require Import Powerset_facts. 
Require Import erasure. 
Require Import SpecLib. 
Require Import unspec. 

(*terms that when erased to require the erased thread to be commit*)
Inductive commitTrm : ptrm -> Prop :=
|commitApp : forall E ef ea t, pdecompose t E (papp (plambda ef) ea)-> commitTrm t
|commitProjL : forall t E V1 V2, pdecompose t E (pfst (ppair V1 V2)) -> commitTrm t
|commitProjR : forall t E V1 V2, pdecompose t E (psnd (ppair V1 V2)) -> commitTrm t
|commitHandleRet : forall t E N M, pdecompose t E (phandle (pret M) N) -> commitTrm t
|commitHandleRaise : forall t E N M, pdecompose t E (phandle (praise M) N) -> commitTrm t
|commitRet : forall M, commitTrm (pret M).   
  
Ltac commitFill :=
  match goal with
    |H:commitTrm (pfill ?E ?e) |- _ => assert(pdecompose (pfill E e) E e)
    |H:pdecompose ?t ?E ?e, H':pdecompose ?t ?E' ?e' |- _ => 
     eapply pctxtUnique in H; eauto; inversion H as [Eq1 Eq2]; inversion Eq2
  end. 

Ltac existTac e := let n := fresh in
                   try(assert(n:exists e', eraseTerm e' = e) by apply eTerm; invertHyp);
                   try(assert(n:exists e', eraseCtxt e' = e) by apply eCtxt; invertHyp). 


Theorem eraseThreadCommitTrm : forall x t, commitTrm t -> eraseThread x (pSingleton t) ->
                                       exists tid s2 M, x = (tid,nil,s2,M) /\ eraseTerm M = t.
Proof.
  intros. inversion H0; subst. 
  {exists tid. exists s2. exists M. split; auto. apply SingletonEq in H3. subst. auto. }
  {unfold pSingleton in *; invertHyp. inv H; try(copy d;
   match goal with
       |H:pdecompose ?M ?E ?e, H':decompose ?M' ?E' ?e' |- _ => 
        rewrite <- decomposeErase in H'; eauto; eapply pctxtUnique in H; eauto; invertHyp 
   end; inv H3). destruct M'; inv H2. inv d. }
  {unfold pSingleton in *; invertHyp. inv H; try(copy d;
   match goal with
       |H:pdecompose ?M ?E ?e, H':decompose ?M' ?E' ?e' |- _ => 
        rewrite <- decomposeErase in H'; eauto; eapply pctxtUnique in H; eauto; invertHyp 
   end; inv H3). destruct M'; inv H2. inv d. }
  {unfold pSingleton in *; invertHyp. inv H; try(copy d;
   match goal with
       |H:pdecompose ?M ?E ?e, H':decompose ?M' ?E' ?e' |- _ => 
        rewrite <- decomposeErase in H'; eauto; eapply pctxtUnique in H; eauto; invertHyp 
   end; inv H3). destruct M'; inv H2. inv d. }
  {unfold pSingleton in *; invertHyp. inv H; try(copy d;
   match goal with
       |H:pdecompose ?M ?E ?e, H':decompose ?M' ?E' ?e' |- _ => 
        rewrite <- decomposeErase in H'; eauto; eapply pctxtUnique in H; eauto; invertHyp 
   end; inv H3). destruct M'; inv H2. inv d. }
  {unfold pSingleton in *; invertHyp. inv H; try(copy d;
   match goal with
       |H:pdecompose ?M ?E ?e, H':decompose ?M' ?E' ?e' |- _ => 
        rewrite <- decomposeErase in H'; eauto; eapply pctxtUnique in H; eauto; invertHyp 
   end; inv H3). destruct M'; inv H2. inv d. }
  {symmetry in H1. apply SingletonNeqEmpty in H1. inv H1. }
Qed.

Theorem erasePoolSingleton : forall T t', erasePoolAux T = pSingleton t' ->
                                          exists t, tIn T t /\ eraseThread t (pSingleton t'). 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
  assert(In ptrm (pSingleton t') t'). constructor. apply H1 in H. inv H. inv H2. inv H5.
  inv H3; try solve[econstructor; split; eauto; inv H4; eauto]. Qed. 

Theorem eraseThreadCardinality : forall t t', eraseThread t t' -> 
                                              t' = Empty_set ptrm \/ exists t'', t' = pSingleton t''.
Proof.
  intros. inv H; eauto. 
Qed. 

Theorem nonspecImpliesSpec' : forall PH PH' PT pt pt' H T,
                               pstep PH PT pt (pOK PH' PT pt') -> eraseHeap H = PH ->
                               erasePool T (Union ptrm PT pt) ->
                               exists H' T' t' t'',
                                 T = tUnion T' t' /\ 
                                 eraseHeap H' = PH' /\ erasePool (tUnion T' t'') (Union ptrm PT pt') /\
                                 multistep H T' t' (OK H' T' t''). 
Proof.
  intros. inversion H0; subst. 
  {exists H. inversion H2; subst. unfoldSetEq H5. assert(In ptrm (pUnion PT (pSingleton t)) t). 
   apply Union_intror. constructor. apply H3 in H4. inversion H4; subst. inv H5. 
   inv H10. apply pullOut in H9. rewrite H9 in H2. exists (Subtract thread T(t0,s0,s3,M0)). 
   exists (tSingleton(t0,s0,s3,M0)). existTac E. existTac e. existTac arg. econstructor.
   split. auto. split; auto. clear H9. inv H2. rewrite eraseUnionComm in H13. 
   copy H6. apply eraseThreadCardinality in H6. inv H6. inv H8. invertHyp. inv H8. 
   eapply eraseThreadCommitTrm in H2; eauto. invertHyp. Focus 2. eapply commitApp; eauto.
   inv H2. split. Focus 2. eapply multi_step. rewrite <- union_empty_l at 1. auto. 
   eapply BetaRed. eapply decomposeErase in H7; eauto. simpl; auto. constructor. 
   



econstructor. split; auto. split; auto. clear H9. inv H2. 
   rewrite eraseUnionComm in H10. copy H6. apply eraseThreadCardinality in H6. inv H6. 
   inv H8. invertHyp. inv H8. eapply eraseThreadCommitTrm in H2; eauto. Focus 2. 
   eapply commitApp; eauto. invertHyp. inv H2. existTac E. existTac e. existTac arg. 
   split. Focus 2. eapply multi_step. rewrite <- union_empty_l at 1. auto. eapply BetaRed. 
   eapply decomposeErase in H7; eauto. simpl. auto. unfoldTac. rewrite union_empty_l. 
   apply multi_refl. constructor. 



Theorem ePool : forall T', exists T, erasePool T T'.
Admitted.  

Theorem erasePoolEqUnion : forall T PT pt, erasePoolAux T = Union ptrm PT (pSingleton pt) ->
                     exists PT' pt', erasePoolAux PT' = PT /\
                                     erasePoolAux pt' = (pSingleton pt) /\ T = tUnion PT' pt'.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H.
  assert(exists T', erasePool T' PT). apply ePool. inv H0. inv H1. 
  eErase pt. exists x. exists (tSingleton (nil,nil,nil, x0)). split; auto. split. 
  erewrite termErasePoolErase; auto. apply Extensionality_Ensembles. unfold Same_set. 
  unfold Included. split; intros. 
  {


   assert(Ensembles.In ptrm (Union ptrm PT (pSingleton (eraseTerm x0))) (eraseTerm x0)). 
   apply Union_intror. constructor. eapply inErasure in H5; eauto. apply pullOut in H5.
   rewrite <- termErasePoolErase with(tid0:=nil)(s2:=nil)in H5. 
   exists (Subtract thread T (nil,nil,nil,x0)). exists (tSingleton(nil,nil,nil,x0)). 
   econstructor. split. 





Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' H T t,
                               pstep PH PT pt (pOK PH' PT pt') -> eraseHeap H = PH ->
                               erasePool T PT -> erasePool t pt ->
                               exists H' t', eraseHeap H' = PH' /\ erasePool t' pt' /\
                                             multistep H T t (OK H' T t'). 
Proof.
  intros. inversion H0; subst. 
  {exists H. inversion H3. copy H6. apply erasePoolSingleton in H6. invertHyp. apply pullOut in H1. 
   rewrite H1. eErase e. eErase arg. eErase E. apply eraseThreadCommitTrm in H4. Focus 2. 
   econstructor. eauto. invertHyp. rewrite H4. eErase e. econstructor. split; auto. 
   split. Focus 2. eapply multi_step. auto. eapply BetaRed. clear H1; subst. 
   eapply decomposeErase in H8; eauto. simpl. eauto. clear H1; subst. eauto. rewrite H1 in H5. 
   clear H1; subst. rewrite eraseUnionComm in H5. rewrite termErasePoolErase in H5. 
   apply AddEqSingleton in H5. 



adsf