Require Import AST.      
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 
Require Import erasure. 
Require Import classifiedStep. 
Require Import Powerset_facts. 

Theorem eraseUnionComm : forall T1 T2, erasePoolAux (tUnion T1 T2) (tUnion T1 T2) = 
                                       Union ptrm (erasePoolAux T1 (tUnion T1 T2))(erasePoolAux T2 (tUnion T1 T2)).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H; subst. inversion H0; subst. cleanup. inversion H4; subst. 
   {constructor. econstructor. econstructor. eassumption. reflexivity. constructor. auto. 
    eassumption. assumption. }
   {apply Union_intror. econstructor. econstructor. eassumption. auto. unfold tUnion. 
    rewrite Union_commutative. constructor. auto. eassumption. assumption. }
  }
  {inversion H; subst. 
   {inversion H0; subst. inversion H1; subst. cleanup. econstructor. econstructor. 
    econstructor. eassumption. reflexivity. unfold Included. intros; auto.  eassumption. auto. }
   {inversion H0; subst. inversion H1; subst. cleanup. econstructor. econstructor. 
    apply Union_intror. eassumption. auto. unfold Included. auto. eassumption. auto. }
  }
Qed. 

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

Theorem termErasePoolErase : forall tid M M' s2 T,
                               eraseTerm M T M' -> Included thread (tSingleton (tid, [], s2, M)) T ->
                               erasePoolAux (tSingleton(tid,nil,s2,M)) T = (pSingleton M'). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H1; subst. inversion H2; subst. cleanup. inversion H6; subst. clear H6. 
   inversion H4; subst; try invertListNeq. inversion H5; subst. 
   eapply termErasureDeterminism in H. rewrite <- H. econstructor. assumption. }
  {inversion H1; subst. clear H1. inversion H; subst; destruct tid; destruct p; try solve[
   econstructor; [econstructor; auto; econstructor; eauto|auto|auto|econstructor; eauto]]; try solve[ 
   econstructor;[econstructor; eauto; econstructor; eauto|auto|econstructor; eauto|constructor]]. 
  }
Qed. 

Theorem inErase : forall T T1 t, 
                    erasePoolAux T T = Union ptrm T1 (pSingleton t) ->
                    exists t', tIn T t' /\ eraseThread t' T (pSingleton t). 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. 
  inversion H; clear H. assert(Ensembles.In ptrm (Union ptrm T1 (pSingleton t)) t). 
  apply Union_intror. constructor. apply H1 in H. inversion H; subst. inversion H2; subst. 
  cleanup. inversion H4; subst; inversion H5; subst; econstructor; eauto.  
Qed. 

Theorem pullOutDisjoint : forall X T t, Disjoint X (Subtract X T t) (Singleton X t). 
Proof.
  intros. constructor. intros. intros c. inversion c. inversion H0; subst. inversion H; subst. 
  apply H2. constructor. Qed. 


(*terms that when erased to require the erased thread to be commit*)
Inductive commitTrm : ptrm -> Prop :=
|commitApp : forall E ef ea t, pdecompose t E (papp (plambda ef) ea)-> commitTrm t
|commitProjL : forall t E V1 V2, pdecompose t E (pfst (ppair V1 V2)) -> commitTrm t
|commitProjR : forall t E V1 V2, pdecompose t E (psnd (ppair V1 V2)) -> commitTrm t
|commitHandleRet : forall t E N M, pdecompose t E (phandle (pret M) N) -> commitTrm t
|commitHandleRaise : forall t E N M, pdecompose t E (phandle (praise M) N) -> commitTrm t
|commitRet : forall M, commitTrm (pret M). 

Theorem eraseDecompose' : forall E e E' e' T, eraseTerm e T e' -> eraseContext E T E' ->
                                              eraseTerm (fill E e) T (pfill E' e'). 
Proof.
  intros. generalize dependent e. generalize dependent e'. induction H0; intros;
                                                           try solve[simpl; econstructor; eauto]. 
  {simpl. auto. }
Qed. 

Theorem eraseValEq : forall e T e', eraseTerm e T e' -> (val e <-> pval e'). 
Proof.
  intros. split; intros; try solve[ 
  inversion H0; subst; inversion H; subst; constructor]. Qed. 

Ltac eq x := assert(x=x) by auto. 

Theorem eraseDecompose'' : forall E e E' e' T, decompose (fill E e) E e -> pdecompose (pfill E' e') E' e' ->
                                               eraseTerm (fill E e) T (pfill E' e') ->
                                               eraseTerm e T e' /\ eraseContext E T E'. 
Proof.
  intros. generalize dependent E'. generalize dependent e'. remember (fill E e). induction H; intros.
  {simpl in Heqt. inversion Heqt; subst. destruct E'; inversion H2; subst. 
   {eq (fill E M'). eapply IHdecompose in H3. inversion H3. split. eassumption. constructor; eauto. 
    simpl in *. inversion H1; subst. assumption. assumption. }
   {simpl in *. subst. inversion H1; subst. apply eraseValEq in H5. apply H5 in H4. contradiction. }
  }
  {simpl in Heqt. inversion H1; subst. rewrite <- H4 in H0. inversion H0; subst. 
   {apply eraseValEq in H6. apply H6 in H. contradiction. }
   {simpl in *. auto. }
  }
  {simpl in Heqt. inversion Heqt; subst. destruct E'; inversion H2; subst. 
   {eq (fill E M'). eapply IHdecompose in H3. inversion H3. split. eassumption. econstructor; eauto. 
    simpl in *. inversion H1; subst. assumption. assumption. }
   {simpl in *. subst. inversion H1; subst. apply eraseValEq in H5. apply H5 in H4. contradiction. }
  }
  {simpl in Heqt. inversion H1; subst. rewrite <- H4 in H0. inversion H0; subst. 
   {apply eraseValEq in H5. apply H5 in H. contradiction. }
   {simpl in *. auto. }
  }
  {simpl in Heqt. inversion Heqt; subst. destruct E'; inversion H2; subst. 
   {eq (fill E M'). eapply IHdecompose in H3. inversion H3. split. eassumption. constructor; eauto. 
    simpl in *. inversion H1; subst. assumption. assumption. }
   {simpl in *. subst. inversion H1; subst. apply eraseValEq in H5. apply H5 in H4. contradiction. }
  }
  {simpl in Heqt. inversion H1; subst. rewrite <- H4 in H0. inversion H0; subst. 
   {apply eraseValEq in H6. apply H6 in H. contradiction. }
   {simpl in *. auto. }
  }
  {simpl in Heqt. inversion Heqt; subst. destruct E'; inversion H2; subst. 
   {eq (fill E M'). eapply IHdecompose in H3. inversion H3. split. eassumption. constructor; eauto. 
    simpl in *. inversion H1; subst. assumption. assumption. }
   {simpl in *. subst. inversion H1; subst. apply eraseValEq in H5. apply H5 in H4. contradiction. }
  }
  {simpl in Heqt. inversion H1; subst. rewrite <- H4 in H0. inversion H0; subst. 
   {apply eraseValEq in H6. apply H6 in H. contradiction. }
   {simpl in *. auto. }
  }
  {simpl in Heqt. inversion Heqt; subst. destruct E'; inversion H2; subst. 
   {eq (fill E M'). eapply IHdecompose in H3. inversion H3. split. eassumption. constructor; eauto. 
    simpl in *. inversion H1; subst. assumption. assumption. }
   {simpl in *. subst. inversion H1; subst. apply eraseValEq in H4. apply H4 in H5. contradiction. }
  }
  {simpl in Heqt. inversion H1; subst. rewrite <- H3 in H0. inversion H0; subst. 
   {apply eraseValEq in H5. apply H5 in H. contradiction. }
   {simpl in *. auto. }
  }
  {simpl in Heqt. inversion Heqt; subst. destruct E'; inversion H2; subst. 
   {eq (fill E M'). eapply IHdecompose in H3. inversion H3. split. eassumption. constructor; eauto. 
    simpl in *. inversion H1; subst. assumption. assumption. }
   {simpl in *. subst. inversion H1; subst. apply eraseValEq in H4. apply H4 in H5. contradiction. }
  }
  {simpl in Heqt. inversion H1; subst. rewrite <- H3 in H0. inversion H0; subst. 
   {apply eraseValEq in H5. apply H5 in H. contradiction. }
   {simpl in *. auto. }
  }
  {simpl in *. inversion H1; subst. rewrite <- H in H0. inversion H0; subst. auto. }
  {simpl in *. inversion H1; subst. rewrite <- H2 in H0. inversion H0; subst. auto. }
  {simpl in *. inversion H1; subst. rewrite <- H3 in H0. inversion H0; subst. auto. }
  {simpl in *. inversion H1; subst. rewrite <- H2 in H0. inversion H0; subst. auto. }
Qed. 

Theorem eraseThreadCommitTrm : forall x T t, commitTrm t -> eraseThread x T (pSingleton t) ->
                                       exists tid s2 M, x = (tid,nil,s2,M) /\ eraseTerm M T t.
Proof.
  intros. inversion H0; subst. 
  {exists tid. exists s2. exists M. split; auto. apply SingletonEq in H1. subst. auto. }
  {apply SingletonEq in H1; subst. inversion H; subst; try solve[ 
   match goal with
       |H:decompose ?M ?E ?e, H':pdecompose ?M' ?E' ?e' |- _ => 
        copy H; apply decomposeEq in H; copy H'; apply pdecomposeEq in H'; subst
   end; apply eraseDecompose'' in H3; auto; inversion H3; inversion H1]. 
   inversion H3; subst. inversion H6. }
  {apply SingletonEq in H1; subst. inversion H; subst; try solve[ 
   match goal with
       |H:decompose ?M ?E ?e, H':pdecompose ?M' ?E' ?e' |- _ => 
        copy H; apply decomposeEq in H; copy H'; apply pdecomposeEq in H'; subst
   end; apply eraseDecompose'' in H3; auto; inversion H3; inversion H1]. 
   inversion H3; subst. inversion H6. }
  {apply SingletonEq in H1; subst. inversion H; subst; try solve[ 
   match goal with
       |H:decompose ?M ?E ?e, H':pdecompose ?M' ?E' ?e' |- _ => 
        copy H; apply decomposeEq in H; copy H'; apply pdecomposeEq in H'; subst
   end; apply eraseDecompose'' in H3; auto; inversion H3; inversion H1]. 
   inversion H3; subst. inversion H6. }
  {apply eqImpliesSameSet in H1. unfold Same_set in H1. unfold Included in H1. 
   inversion H1; clear H1. assert(Ensembles.In ptrm (pSingleton t) t). constructor. 
   apply H3 in H1. inversion H1. }
  {apply SingletonEq in H1; subst. inversion H; subst; try solve[ 
   match goal with
       |H:decompose ?M ?E ?e, H':pdecompose ?M' ?E' ?e' |- _ => 
        copy H; apply decomposeEq in H; copy H'; apply pdecomposeEq in H'; subst
   end; apply eraseDecompose'' in H3; auto; inversion H3; inversion H1]. 
   inversion H3; subst. inversion H6. }
  {apply SingletonEq in H1; subst. inversion H; subst; try solve[ 
   match goal with
       |H:decompose ?M ?E ?e, H':pdecompose ?M' ?E' ?e' |- _ => 
        copy H; apply decomposeEq in H; copy H'; apply pdecomposeEq in H'; subst
   end; apply eraseDecompose'' in H3; auto; inversion H3; inversion H1]. 
   inversion H3; subst. inversion H6. }
  {apply eqImpliesSameSet in H1. unfold Same_set in H1. unfold Included in H1. 
   inversion H1; clear H1. assert(Ensembles.In ptrm (pSingleton t) t). constructor. 
   apply H3 in H1. inversion H1. }
Qed. 

Ltac existsErase e T := try (assert(exists e', eraseTerm e' T e) by apply eTerm);
                        try (assert(exists E', eraseContext E' T e) by apply eCtxt);
                        invertHyp.
Ltac valEq :=
  match goal with
      |H:eraseTerm ?e ?T ?e', H':pval ?e' |- val ?e => apply eraseValEq in H; apply H in H'
      |H:eraseTerm ?e ?T ?e', H':~pval ?e' |- ~val ?e =>
       intros c; apply eraseValEq in H; apply H in c; contradiction
  end. 

Ltac invertDecomp :=
  match goal with
      |H:pdecompose ?M ?E ?e |- _ => inversion H; subst
      |H:decompose ?M ?E ?e |- _ => inversion H; subst
  end. 

(*TODO: move this to NonSpec.v*)
Theorem uniquePCtxtDecomp : forall t E e E' e',
                             pdecompose t E e -> pdecompose t E' e' ->
                             E = E' /\ e = e'. 
Proof.
  induction t; intros; try solve[inversion H; inversion H0; subst; auto]; try solve[
  inversion H; inversion H0; subst; simpl in *; try contradiction; auto; 
   eapply IHt1 in H6; eauto; inversion H6; subst; auto]. 
  {inversion H; inversion H0; subst; auto; try contradiction. eapply IHt in H3; eauto. 
   inversion H3; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction. eapply IHt in H3; eauto. 
   inversion H3; subst; auto. }
Qed. 

Theorem eraseWF : forall E e E' e' T, pctxtWF e' E' -> eraseContext E T E' -> 
                                      eraseTerm e T e' -> ctxtWF e E. 
Admitted. 


Theorem eraseCommitTrm : forall t t' E' e' T, eraseTerm t T t' -> pdecompose t' E' e' ->
                                                  exists E e, eraseTerm e T e' /\
                                                              decompose t E e. 
Proof.
  intros. generalize dependent E'. generalize dependent e'. induction H; intros;
      try solve[invertDecomp]; try solve[invertDecomp; repeat econstructor; eauto]. 
  {inversion H1; subst. apply IHeraseTerm1 in H7. invertHyp. 
   exists (appCtxt x e2). repeat econstructor; eauto. valEq. 
   exists (holeCtxt). repeat econstructor; eauto. valEq; auto. }
  {inversion H1; subst. apply IHeraseTerm1 in H7. invertHyp. 
   exists (bindCtxt x e2). repeat econstructor; eauto. valEq.  
   exists (holeCtxt). repeat econstructor; eauto. valEq; auto. }
  {inversion H1; subst. apply IHeraseTerm1 in H7. invertHyp. 
   exists (handleCtxt x e2). repeat econstructor; eauto. valEq.  
   exists (holeCtxt). repeat econstructor; eauto. valEq; auto. }
  {inversion H0; subst. apply IHeraseTerm in H3. invertHyp. 
   exists (fstCtxt x). repeat econstructor; eauto. valEq.  
   exists (holeCtxt). repeat econstructor; eauto. valEq; auto. }
  {inversion H0; subst. apply IHeraseTerm in H3. invertHyp. 
   exists (sndCtxt x). repeat econstructor; eauto. valEq.  
   exists (holeCtxt). repeat econstructor; eauto. valEq; auto. }
  {inversion H1; subst. apply IHeraseTerm1 in H7. invertHyp. 
   Admitted. 



Theorem erasePoolUnion : forall T T' t t', 
          eraseThread t (Union thread T (tSingleton t)) t' ->
          erasePoolAux(Union thread T (Singleton thread t)) (Union thread T (Singleton thread t)) = 
          Union ptrm T' t' -> erasePoolAux T (Union thread T (tSingleton t)) = T'. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {Admitted. 

Theorem ParDivergeSpecDiverge : forall H H' T T', eraseHeap H H' -> erasePool T T' ->
                                                  ParDiverge H' T' -> SpecDiverge H T. 
Proof.
  cofix. intros. inversion H2; subst. inversion H5; subst.  
  {inversion H1; subst. copy H8. apply inErase in H8. invertHyp. apply pullOut in H8. 
   rewrite H8 in H3. rewrite H8. apply erasePoolUnion in H3; auto. Focus 2. rewrite H8 in H9. 
   assumption. apply eraseThreadCommitTrm in H9. invertHyp.  
   apply eraseCommitTrm with(E':=E)(e':=(papp (plambda e) arg))in H11. invertHyp.   
   inversion H7. inversion H16. subst x. subst x4. subst e1. econstructor. 
   apply smulti_refl. apply pullOutDisjoint. apply CBetaRed. eassumption. 
   eapply ParDivergeSpecDiverge. eassumption. econstructor. 
   assert((erasePoolAux
        (tUnion (Subtract thread T (x0, [], x1, x2))
           (tSingleton (x0, [], x1, fill x3 (open 0 e2 e0))))
        (tUnion (Subtract thread T (x0, [], x1, x2))
           (tSingleton (x0, [], x1, fill x3 (open 0 e2 e0))))) = (Union ptrm T1 (pSingleton (pfill E (popen 0 arg e))))). admit. rewrite H9. assumption. assumption. copy H10. apply pdecomposeEq in H10. rewrite H10. 
   econstructor. rewrite H10 in H7. eassumption. }



