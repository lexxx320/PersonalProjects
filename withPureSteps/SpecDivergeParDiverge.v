Require Import AST.      
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 
Require Import erasure. 
Require Import classifiedStep. 
Require Import Powerset_facts. 

Theorem eraseUnionComm : forall T1 T2, erasePoolAux (Union thread T1 T2) (Union thread T1 T2) = 
                                       Union ptrm (erasePoolAux T1 (Union thread T1 T2))
                                             (erasePoolAux T2 (Union thread T1 T2)).
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

Theorem listAlign : forall (T:Type) l (x y :T) l' (e:T),
                      x::y::l = l' ++ [e] ->
                      exists l'', (y::l) = l'' ++ [e]. 
Proof.
  induction l; intros. 
  {destruct l'. inversion H. exists nil. inversion H.
   destruct l'. inversion H2. auto. inversion H2. destruct l'; inversion H4. }
  {destruct l'. 
   {inversion H. }
   {inversion H. exists l'. assumption. }
  }
Qed. 

Hint Resolve app_comm_cons. 

Theorem eraseTwoActs : forall tid tid' A1 A2 As s2 M M' T t,
                         eraseThread (tid', (A1::A2::As), s2, M') T t <->
                         eraseThread (tid, (A2 :: As), s2, M) T t. 
Proof.
  intros. split; intros. 
  {inversion H; subst; match goal with
       |H:?A1::?A2::?As=?s++[?a] |- _ => apply listAlign in H; invertExists
        end; match goal with
               |H:?A::?As=?x++[?a] |- eraseThread(?t,?A::?As,?s2,?m) ?T ?M =>
                rewrite H; destruct t; destruct p
             end; eauto. 
  }
  {inversion H; subst; rewrite H6; eauto. }
Qed. 

Ltac poolAuxEq :=
  match goal with
    | |- erasePool ?t ?t' => assert(erasePoolAux t  t = t');[apply Extensionality_Ensembles;
                                                            unfold Same_set; unfold Included; split;
                                                            intros|idtac]
  end. 

Theorem eraseSpecThreadSame : forall tid tid' a b s2 M M' t, 
                                eraseThread (tid,a::b,s2,M) (tSingleton (tid,a::b,s2,M)) t <->
                                eraseThread (tid',a::b,s2,M') (tSingleton(tid',a::b,s2,M')) t.
Proof.
  intros. split; intros. 
  {inversion H; subst. 
   {rewrite H6. eapply tEraseRead; eauto. 



Theorem specSingleStepErase : forall H T H' T' H'' T'' P,
                                spec_step H P T (OK H' P T') ->
                                eraseHeap H H'' -> erasePool T T'' -> 
                                eraseHeap H' H'' /\ erasePool T' T''.
Proof.
  intros. inversion H0; subst. 
  {split. assumption. inversion H2; subst. poolAuxEq. 
   {inversion H; subst. inversion H3; subst. cleanup. inversion H8; subst; clear H8. 
    clear H3. econstructor. econstructor. econstructor. auto. unfold Included; intros. 
    inversion H3; subst; constructor. erewrite eraseSpecThreadSame. eassumption. 
    assumption. }
   {inversion H; subst. inversion H3; subst. cleanup. inversion H8; subst; clear H8. 
    econstructor. econstructor. econstructor. auto. unfold Included; intros. inversion H8; subst. 
    constructor. erewrite eraseSpecThreadSame. eassumption. assumption. }
   rewrite <- H. constructor. }
  {
   


Theorem spec_multistepErase : forall H T H' T' H'' T'',
                                spec_multistep H tEmptySet T H' tEmptySet T' ->
                                eraseHeap H H'' -> erasePool T T'' -> 
                                eraseHeap H' H'' /\ erasePool T' T''.
Proof.
  intros. remember tEmptySet. generalize dependent H''. generalize dependent T''. 
  induction H0; subst; auto; intros. inversion H3; subst. 
  apply specSingleStepErase with(H'':=H''0)(T'':= erasePoolAux P2 (tUnion P1 P2))in H1; auto. 
  inversion H1. apply IHspec_multistep; auto. rewrite eraseUnionComm in H3.  
  inversion H5; subst. Admitted. 


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

Theorem eraseDecomp : forall t t' E e E' e' T, (forall M N, e <> spec M N) -> 
                                               eraseContext E T E' -> eraseTerm e T e' ->
                                               eraseTerm t T t' -> pdecompose t' E' e'. 
Proof.
  intros. generalize dependent e. generalize dependent e'. generalize dependent t. 
  generalize dependent t'. induction H0; intros. 
  Admitted. 

Axiom termEraseExists : forall t T, exists t', eraseTerm t T t'. 
Axiom ctxtEraseExists : forall E T, exists E', eraseContext E T E'.

Ltac existsTac :=
  match goal with
      |H:decompose ?t ?E ?e, H':eraseTerm ?t ?T ?x |- _ => 
       assert(exists E', eraseContext E T E') by apply ctxtEraseExists; 
         assert(exists e', eraseTerm e T e') by apply termEraseExists
  end. 


Theorem SpecDivergeParDiverge : forall H H' T T', eraseHeap H H' -> erasePool T T' ->
                                                  SpecDiverge H T -> ParDiverge H' T'. 
Proof.
  cofix. intros. inversion H2; subst. apply spec_multistepErase with (H'':=H')(T'':=T')in H4; auto. 
  inversion H4; subst. clear H4. inversion H6; subst. 
  {inversion H8; subst. rewrite eraseUnionComm. 
   assert(exists t', eraseTerm t (tUnion T1 (tSingleton (tid, [], s2, t))) t'). apply termEraseExists. 
   invertExists. erewrite termErasePoolErase. Focus 3. unfold Included. intros. inversion H; subst. 
   apply Union_intror. constructor. Focus 2. eassumption. existsTac. invertHyp. inversion H10; subst. 
   inversion H13; subst. econstructor. admit. apply PBetaRed. eapply eraseDecomp. 
   Focus 3. eassumption. intros. intros c. inversion c. eassumption. eassumption. 
   eapply SpecDivergeParDiverge. eassumption. rewrite <- eraseUnionComm. 



