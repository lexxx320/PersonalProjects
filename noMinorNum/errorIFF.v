Require Import NonSpec.     
Require Import Spec.
Require Import Coq.Sets.Ensembles.
Require Import SfLib.  
Require Import erasure.  
Require Import sets. 
Require Import hetList. 
Require Import Heap. 
Require Import AST. 

Theorem eraseFull : forall H H' x N tid ds N',
                      eraseHeap H H' -> eraseTerm N N' ->
                      heap_lookup x H = Some(sfull nil ds nil tid N) ->
                      heap_lookup x H' = Some(pfull N'). 
Proof.
  induction H; intros. 
  {simpl in *. inversion H1. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq.  
   {inversion H2; subst. clear H2. inversion H0; subst. simpl. rewrite eq. 
    eapply termErasureDeterminism in H1. rewrite <- H1. reflexivity. assumption. }
   {inversion H0; subst; eauto; solve[simpl; rewrite eq; eauto]. }
  }
Qed. 



Ltac inv H := inversion H; subst; clear H. 
  
Ltac eqSets := apply Extensionality_Ensembles; unfold Same_set; unfold Included; split; intros.

Hint Constructors eraseContext. 




Ltac unfoldSetEq H := apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H; inv H.

Theorem eErasePoolAuxSingleton : forall t t', erasePoolAux t = pSingleton t' ->
                                              exists t'', t = tSingleton t'' /\ 
                                                          eraseThread t'' (pSingleton t'). 
Proof.
  intros. unfoldSetEq H. assert(Ensembles.In AST.ptrm (pSingleton t') t'). constructor. 
  apply H1 in H. inv H. inv H2. inv H5. 


Ltac existTac e := let n := fresh in
                   try(assert(n:exists e', eraseTerm e' e) by apply eTerm; inv n);
                   try(assert(n:exists e', eraseContext e' e) by apply eCtxt; inv n). 

Ltac clean :=
  repeat match goal with
           |H:exists c, ?a |- _ => inv H
           |H:?a /\ ?b |- _ => inv H
         end. 

Require Import Coq.Program.Equality.

Theorem eraseDecomp : forall M M' E' e', eraseTerm M M' -> pdecompose M' E' e' -> pdecompose e' pholeCtxt e' ->
                                      exists E e, eraseContext E E' /\ eraseTerm e e' /\ M = fill E e. 
Proof.
  intros. genDeps{E'; e'}. induction H; intros; try solve[inversion H0]. 
  {inversion H2; subst. }
  {inversion H2; subst. apply IHeraseTerm1 in H8; eauto. clean. 
   exists (appCtxt x e2). eauto. exists holeCtxt. eauto. }
  {inversion H2; subst. apply IHeraseTerm1 in H8; eauto. clean. exists (bindCtxt x e2). eauto. 
   exists holeCtxt. eauto. }
  {inversion H0; subst. exists holeCtxt. eauto. }
  {inversion H0; subst. eauto. }
  {inversion H2; subst. exists holeCtxt. eauto. }
  {inversion H0; subst. exists holeCtxt. eauto. }
  {inversion H2; subst. apply IHeraseTerm1 in H8. clean. exists (handleCtxt x e2). eauto. 
   eauto. exists holeCtxt. eauto. }
  {inversion H0; subst. apply IHeraseTerm in H4. clean. exists (fstCtxt x). eauto.
   eauto. exists holeCtxt. eauto. }
  {inversion H0; subst. apply IHeraseTerm in H4. clean. exists (sndCtxt x). eauto. 
   eauto. exists holeCtxt. eauto. }
  { inversion H2; subst. admit. admit. }
  {inversion H2; subst. Admitted. 


Fixpoint unfoldCtxt (E:pctxt) (e:ptrm) n :=
  match n with
      |0 => (E, e) 
      |S n' => match E with
                 |pbindCtxt E' e' => let (E'', e'') := unfoldCtxt E' e n'
                                     in(E'', pbind e'' e')
                 |phandleCtxt E' e' => let (E'', e'') := unfoldCtxt E' e n'
                                       in(E'', phandle e'' e')
                 |pappCtxt E' e' => let (E'', e'') := unfoldCtxt E' e n'
                                    in(E'', papp e'' e')
                 |pfstCtxt E' => let (E'', e'') := unfoldCtxt E' e n'
                                 in(E'', pfst e'')
                 |psndCtxt E' => let (E'', e'') := unfoldCtxt E' e n'
                                 in(E'', psnd e'')
                 |pholeCtxt => (pholeCtxt, e)
               end
  end. 

Theorem decomposeUnfold : forall E e E' e' n, unfoldCtxt E e n = (E', e') ->
                                              pdecompose (pfill E' e') E e.  
Admitted. 
 
Theorem eraseDecomp' : forall M M' E' e', 
                        eraseTerm M M' -> pdecompose M' E' e' -> pdecompose e' pholeCtxt e' ->
                        exists E e, M = fill E e /\ eraseTerm (fill E e) (pfill E' e'). 
Proof.
  intros. genDeps{E'; e'}. induction H; intros; try solve[inversion H0]. 
  {inversion H2; subst. }
  {inversion H2; subst. 
   Admitted. 

(*
Theorem eraseDecomp'' : forall M M' E' e', 
                        eraseTerm M M' -> pdecompose M' E' e' -> pdecompose e' pholeCtxt e' ->
                        (exists E e, eraseContext E E' /\ eraseTerm e e' /\ M = fill E e) \/
                        (exists E N e, eraseContext E E' /\ eraseTerm (spec e N) e' /\ M = fill E (spec e N)). 
Proof.
  intros. genDeps{E'; e'}. induction H; intros; try solve[inversion H0]. 
  {inversion H2; subst. }
  {inversion H2; subst. 
   {apply IHeraseTerm1 in H8; eauto. inv H8; clean. 
    {left. exists (appCtxt x e2). eauto. }
    {inversion H4; subst. right. exists (appCtxt x e2). exists x0. exists x1. eauto. }
   }
   {left. exists holeCtxt. eauto. }
  }
  {inversion H2; subst. 
   {apply IHeraseTerm1 in H8; eauto. inv H8; clean. 
    {left. exists (bindCtxt x e2). eauto. }
    {inversion H4; subst. right. exists (bindCtxt x e2). exists x0. exists x1. eauto. }
   }
   {left. exists holeCtxt. eauto. }
  }
  {inversion H0; subst. left.  exists holeCtxt. eauto. }
  {inversion H0; subst. left. eauto. }
  {inversion H2; subst. left. exists holeCtxt. eauto. }
  {inversion H0; subst. left. exists holeCtxt. eauto. }
  {inversion H2; subst. apply IHeraseTerm1 in H8. inv H8. clean. left. exists (handleCtxt x e2). eauto. 
   clean. inversion H4; subst. right. exists (handleCtxt x e2). exists x0. exists x1. eauto. 
   auto. left. exists holeCtxt. eauto. }
  {inv H0. apply IHeraseTerm in H4; eauto. inv H4. clean. left. exists (fstCtxt x). eauto. 
   clean. right. inversion H2; subst. exists (fstCtxt x). exists x0. exists x1. eauto. 
   left. exists holeCtxt. eauto. }
  {inv H0. apply IHeraseTerm in H4; eauto. inv H4. clean. left. exists (sndCtxt x). eauto. 
   clean. right. inversion H2; subst. exists (sndCtxt x). exists x0. exists x1. eauto. 
   left. exists holeCtxt. eauto. }
  {inversion H2; subst.
   {

*)

Theorem specErrorParError : forall H T t PH PT pt, 
                              eraseHeap H PH -> erasePool T PT -> eraseThread t pt ->
                              step H T (tSingleton t) Error -> pstep PH PT pt pError. 
Proof.
  intros. inversion H3; subst. assert(exists N'', eraseTerm N' N''). apply termEraseTotal. 
   inv H6. eapply eraseFull in H8; eauto. assert(exists E', eraseContext E E').
   apply eraseCtxtTotal. inv H6. assert(exists N', eraseTerm N N'). apply termEraseTotal. inv H6. 
   apply SingletonEq in H4; subst. inversion H2; subst; try invertListNeq. 
   eapply PPutError. assert(eraseTerm (fill E (AST.put(AST.fvar x) N))
                                      (pfill x1 (AST.pput (AST.pfvar x)x2))). 
   apply eraseFill; eauto. eapply termErasureDeterminism in H13; eauto. subst. copy H5. 
   apply decomposeWF in H5. eapply pdecomposeDecomposed. eapply eraseCtxtWF; eauto. 
   constructor. constructor. eauto. Qed. 

Theorem eraseFull' : forall H H' x N N', 
                       eraseHeap H H' -> eraseTerm N N' ->
                       heap_lookup x H' = Some(pfull N') ->
                       exists tid ds, Heap.heap_lookup x H = Some(sfull nil ds nil tid N). 
Proof.
  intros. induction H0. 
  {generalize dependent H

 
Theorem ParErrorSpecError : forall H T t PH PT pt,
                               eraseHeap H PH -> erasePool T PT -> eraseThread t pt ->
                               pstep PH PT pt pError -> multistep H T (tSingleton t) Error. 
Proof.
  intros. inversion H3; subst. inversion H2; subst. 
  {apply SingletonEq in H6; subst. existTac N. eapply eraseFull' in H5; eauto. invertHyp. 
   




