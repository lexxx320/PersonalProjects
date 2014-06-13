Require Import AST.  
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 
Require Import erasure. 
Require Import nonspeculativeImpliesSpeculative. 
Require Import classifiedStep. 

CoInductive ParDiverge : pHeap -> pPool -> Prop :=
|divergeStep : forall T1 T2 T2' H H',
                 Disjoint ptrm T1 T2 -> pstep H T1 T2 (pOK H' T1 T2') -> 
                 ParDiverge H' (Union ptrm T1 T2') -> ParDiverge H (Union ptrm T1 T2)
.

CoInductive SpecDiverge : sHeap -> pool-> Prop :=
|specDiverge : forall T1 T2 T2' H H' T,
                 spec_multistep H tEmptySet T H' tEmptySet (tUnion T1 T2) -> Disjoint thread T1 T2 ->
                 progress_step H T1 T2 (OK H' T1 T2') -> SpecDiverge H' (tUnion T1 T2') ->
                 SpecDiverge H T.



Theorem splitErase : forall T T1 t,
                       erasePoolAux T = Union ptrm T1 (pSingleton t) ->
                       exists T' t', erasePoolAux T' = T1 /\ eraseThread t' T (pSingleton t) /\
                                     T = tAdd T' t'. 
Proof.
  intros. Admitted. 

Theorem eraseDisjoint : forall T1 T1' T2 T2' T, erasePool T1 T1' -> eraseThread T2 T T2' ->
                                                Disjoint ptrm T1' T2' -> 
                                                Disjoint thread T1 (tSingleton T2). 
Proof.
  Admitted. 

Theorem ParDivergeSpecDiverge : forall H H' T T', eraseHeap H H' -> erasePool T T' ->
                                                  ParDiverge H' T' -> SpecDiverge H T. 
Proof.
  cofix. intros. inversion H2; subst. inversion H5; subst. 
  {inversion H1; subst. apply splitErase in H8. invertHyp. econstructor. apply smulti_refl. 
   eapply eraseDisjoint; eauto. inversion H3; subst. apply SingletonEq in H7. subst. 
   apply pdecomposeEq in H11. subst. 
   




