Require Import SfLib. 
Require Import NonSpec.  
Require Import AST. 
Require Import Spec.  
Require Import Heap. 
Require Import Coq.Sets.Ensembles.
Require Import sets. 
Require Import Powerset_facts. 
Require Import erasure. 


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

Theorem eraseThreadCommitTrm : forall x t, commitTrm t -> eraseThread x (pSingleton t) ->
                                       exists tid s2 M, x = (tid,nil,s2,M) /\ eraseTerm M = t.
Proof.
  intros. inversion H0; subst. 
  {exists tid. exists s2. exists M. split; auto. apply SingletonEq in H3. subst. auto. }
  {apply SingletonEq in H1; subst. copy H4. apply decomposeEq in H4. subst. rewrite eraseFill in H. 
   inversion H; subst; try solve[
   commitFill; clear H;[
    match goal with
        |H:decompose ?t ?E ?e |- _ => apply pdecomposeDecomposed; try constructor;
                                      apply decomposeWF in H; apply eraseCtxtWF; auto
    end| commitFill]]. destruct (eraseCtxt E); simpl in H3; inversion H3. }
  {apply SingletonEq in H1; subst. copy H4. apply decomposeEq in H4. subst. rewrite eraseFill in H. 
   inversion H; subst; try solve[
   commitFill; clear H;[
    match goal with
        |H:decompose ?t ?E ?e |- _ => apply pdecomposeDecomposed; try constructor;
                                      apply decomposeWF in H; apply eraseCtxtWF; auto
    end| commitFill]]. destruct (eraseCtxt E); simpl in H3; inversion H3. }
  {apply SingletonEq in H1; subst. copy H4. apply decomposeEq in H4. subst. rewrite eraseFill in H. 
   inversion H; subst; try solve[
   commitFill; clear H;[
    match goal with
        |H:decompose ?t ?E ?e |- _ => apply pdecomposeDecomposed; try constructor;
                                      apply decomposeWF in H; apply eraseCtxtWF; auto
    end| commitFill]]. destruct (eraseCtxt E); simpl in H3; inversion H3. }
  {apply SingletonEq in H1; subst. copy H4. apply decomposeEq in H4. subst. rewrite eraseFill in H. 
   inversion H; subst; try solve[
   commitFill; clear H;[
    match goal with
        |H:decompose ?t ?E ?e |- _ => apply pdecomposeDecomposed; try constructor;
                                      apply decomposeWF in H; apply eraseCtxtWF; auto
    end| commitFill]]. destruct (eraseCtxt E); simpl in H3; inversion H3. }
  {apply SingletonEq in H1; subst. copy H4. apply decomposeEq in H4. subst. rewrite eraseFill in H. 
   inversion H; subst; try solve[
   commitFill; clear H;[
    match goal with
        |H:decompose ?t ?E ?e |- _ => apply pdecomposeDecomposed; try constructor;
                                      apply decomposeWF in H; apply eraseCtxtWF; auto
    end| commitFill]]. destruct (eraseCtxt E); simpl in H3; inversion H3. }
  {symmetry in H1. apply SingletonNeqEmpty in H1. inversion H1. }
Qed. 

Ltac eErase e := try (assert(exists e', eraseTerm e' = e) by apply eTerm; invertHyp);
                try (assert(exists e', eraseCtxt e' = e) by apply eCtxt; invertHyp);
                try(assert(exists e', eraseThread e' e) by apply eThread; invertHyp).

Theorem erasePoolSingleton : forall T t', erasePoolAux T = pSingleton t' ->
                                          exists t, tIn T t /\ eraseThread t (pSingleton t'). 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
  assert(In ptrm (pSingleton t') t'). constructor. apply H1 in H. inv H. inv H2. inv H5.
  inv H3; try solve[econstructor; split; eauto; inv H4; eauto]. Qed. 
 
Theorem nonspecImpliesSpec' : forall PH PH' PT pt pt' H T,
                               pstep PH PT pt (pOK PH' PT pt') -> eraseHeap H = PH ->
                               erasePool T (Union ptrm PT pt) ->
                               exists H' T' t' t'',
                                 T = tUnion T' t' /\ 
                                 eraseHeap H' = PH' /\ erasePool (tUnion T' t'') (Union ptrm PT pt') /\
                                 multistep H T' t' (OK H' T' t'). 
Proof.
  intros. inversion H0; subst. 
  {exists H. inversion H2; subst. 

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