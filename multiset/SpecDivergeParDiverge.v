Require Import AST.          
Require Import NonSpec.    
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 
Require Import erasure.  
Require Import classifiedStep.  
Require Import Powerset_facts. 
Require Import unspec.
Require Import hetList. 
Require Import Coq.Program.Equality. 
 
(*Definitions*)
CoInductive ParDiverge : pHeap -> pPool -> Prop :=
|divergeStep : forall T1 T2 T2' H H',
                 pstep H T1 T2 (pOK H' T1 T2') -> 
                 ParDiverge H' (Union ptrm T1 T2') -> ParDiverge H (Union ptrm T1 T2)
.
 
(*H; T ->+ H'; T'*)
Inductive pstepPlus : pHeap -> pPool -> pPool -> pconfig -> Prop :=
|stepPlus : forall T1 T2 h h' t t' c,
              pstep h (pUnion T1 T2) (pSingleton t) (pOK h' (pUnion T1 T2) t') ->
              pmultistep h' T1 (pUnion T2 t') c ->
              pstepPlus h T1 (Add ptrm T2 t) c
|stepError : forall h T1 T2 t, 
               pstep h (pUnion T1 T2) (pSingleton t) pError ->
               pstepPlus h T1 (Add ptrm T2 t) pError. 

CoInductive ParDiverge' : pHeap -> pPool -> Prop :=
|divergeMulti : forall T1 T2 T2' H H',
                  pstepPlus H T1 T2 (pOK H' T1 T2') ->
                  ParDiverge' H' (pUnion T1 T2') -> ParDiverge' H (pUnion T1 T2). 

(*Theorems that should be proven elsewhere, but relied upon here*)
Theorem specImpliesNonSpec : forall H H' T t t' PT pt, 
                               erasePool T PT -> erasePool t pt -> 
                               prog_step H T t (OK H' T t') -> wellFormed H (tUnion T t) ->
                               exists PH' pt', pstepPlus (eraseHeap H) PT pt (pOK PH' PT pt') /\
                                               eraseHeap H' = PH' /\ erasePool t' pt'. 
Admitted. 

Theorem specMultiWF : forall H T H' T', wellFormed H T -> spec_multistep H T H' T' ->
                                        wellFormed H' T'. 
Admitted. 


Theorem prog_stepWF : forall H T t H' t', prog_step H T t (OK H' T t') ->
                                          wellFormed H (tUnion T t) -> 
                                          wellFormed H' (tUnion T t'). 
Admitted. 

(*Divergence Theorem and Supporting Lemmas*)
Theorem pstepDiffUnused : forall H H' T T' t t',
                            pstep H T t (pOK H' T t') ->
                            pstep H T' t (pOK H' T' t'). 
Proof.
  intros. Hint Constructors pstep. inv H0; eauto. 
Qed. 

Theorem pstepSingleton : forall H T1 T2 H' T2', 
                           pstep H T1 T2 (pOK H' T1 T2') -> exists t, T2 = Singleton ptrm t. 
Proof.
  intros. inv H0; eauto. 
Qed.

Theorem pmultiMoveFromUnused : forall H T1 T2 H' T2',
                                 pmultistep H T1 T2 (pOK H' T1 T2') ->
                                 pmultistep H (Empty_set ptrm) (pUnion T1 T2)
                                            (pOK H' (Empty_set ptrm) (pUnion T1 T2')). 
Proof.
  intros. dependent induction H0. 
  {constructor. }
  {unfold pUnion. unfold Add. rewrite <- Union_associative. econstructor. 
   unfold pUnion. rewrite union_empty_l. eassumption. unfold pUnion. 
   rewrite Union_associative. eauto. }
Qed. 

Theorem ParDiverge'Multistep : forall H T H' T', 
                   ParDiverge' H T ->
                   pmultistep H (Empty_set ptrm) T (pOK H' (Empty_set ptrm) T') ->
                   ParDiverge' H' T'.
Proof. 
  intros. Admitted. 

Theorem DivergeIFFDiverge' : forall H T, ParDiverge H T <-> ParDiverge' H T. 
Proof.
  intros. split; intros. 
  {genDeps{H; T}. cofix. intros. inversion H0; subst. econstructor. 
   rewrite <- (union_empty_l ptrm T2). copy H2. apply pstepSingleton in H2. invertHyp. 
   econstructor. unfold pUnion. rewrite union_empty_r. eauto. unfold pUnion. 
   rewrite union_empty_l. constructor. eapply DivergeIFFDiverge'. assumption. }
  {genDeps{H; T}. cofix CH. intros. inversion H0; subst. inversion H2; subst. 
   unfold Add. unfold pUnion. rewrite <- Union_associative. econstructor. 
   eapply pstepDiffUnused. eauto. eapply CH. eapply ParDiverge'Multistep. Focus 2.
   eapply pmulti_step. unfold pUnion. rewrite union_empty_l. eassumption. 
   constructor. unfold Add. unfold pUnion. rewrite Union_associative. eassumption. }
Qed.


CoInductive SpecDiverge : sHeap -> pool-> Prop :=
|specDiverge : forall T1 T2 T2' H H' H'' T,
                 spec_multistep H T H' (tUnion T1 T2) -> 
                 prog_step H' T1 T2 (OK H'' T1 T2') -> 
                 SpecDiverge H'' (tUnion T1 T2') -> SpecDiverge H T.

Theorem SpecDivergeParDiverge : forall H T T',
                                  wellFormed H T -> erasePool T T' ->
                                  SpecDiverge H T -> ParDiverge' (eraseHeap H) T'. 
Proof.
  cofix CH. intros. inversion H2; subst. copy H4. apply specMultiWF in H4; auto. 
  eapply spec_multistepErase with (H'':=eraseHeap H)(T'':=T') in H3; [idtac|eauto|eauto]. 
  invertHyp. rewrite <- H7. inversion H8; subst. 
  copy H5. eapply specImpliesNonSpec with(PT:=erasePoolAux T1)(pt:=erasePoolAux T2)in H5. 
  apply prog_stepWF in H3. 
  invertHyp. inv H11. rewrite eraseUnionComm. Focus 2. eauto. Focus 2. auto.
  econstructor. eassumption. rewrite <- eraseUnionComm. eapply CH. eapply H3. constructor. 
  eauto. constructor. eassumption.
Qed. 










