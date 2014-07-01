Require Import Spec.   
Require Import NonSpec. 
Require Import AST.
Require Import Coq.Sets.Ensembles.   
Require Import sets. 
Require Import SfLib. 
Require Import Coq.Program.Equality. 
Require Import erasure. 

Ltac applyHyp :=
  match goal with
      |H : forall a : _, ?X -> ?Y, H' : ?Z |- _ => apply H in H'
  end. 

Axiom uniqueThreadPool : forall T tid t t', 
                           thread_lookup T tid t -> thread_lookup T tid t' -> t = t'. 

Theorem lastElementEq : forall (T:Type) s1 s2 (e1 e2 : T), s1 ++ [e1] = s2 ++ [e2] -> e1 = e2. 
Proof.
  intros. generalize dependent s2. induction s1; intros. 
  {destruct s2. inversion H. reflexivity. inversion H. destruct s2; inversion H2. }
  {destruct s2. inversion H. destruct s1; inversion H2. inversion H. apply IHs1 in H2.
   assumption. } Qed. 

Ltac copy H := 
  match type of H with
      |?X => assert(X) by apply H
  end. 

Ltac cleanup := unfold tSingleton in *; unfold tCouple in *; unfold tAdd in *;
  repeat(match goal with
           |H : ?x = ?x |- _ => clear H; try subst
           |H : Singleton ?T ?x = Singleton ?T ?y |- _ => apply SingletonEq in H; inversion H; try subst
           |H : Singleton ?T ?x = Couple ?T ?y ?z |- _ => apply SingleEqCouple in H; inversion H; try subst
           |H : Couple ?T ?y ?z = Singleton ?t ?x |- _ => symmetry in H
         end). 

Ltac invertHyp :=
  match goal with
      |H : exists e : _, ?x |- _ => inversion H; clear H; subst; try invertHyp
      |H : ?x /\ ?y |- _ => inversion H; clear H; subst; try invertHyp
      |H : eraseTerm ?M ?T ?t, H' : eraseTerm ?M ?T ?t' |- _ => 
       eapply termErasureDeterminism in H; try eassumption; subst; try invertHyp
      |H : eraseContext ?E ?T ?E1, H' : eraseContext ?E ?T ?E2 |- _ => 
       eapply ctxtErasureDeterminism in H; try eassumption; subst; try invertHyp
  end. 

Theorem listNeq : forall (T:Type) l (e:T), l = e::l -> False. 
Proof.
  intros. induction l. 
  {inversion H. }{inversion H. apply IHl in H2. assumption. }Qed. 

Theorem openErase : forall e1 e1' e2 e2' n T, eraseTerm e1 T e1' -> eraseTerm e2 T e2' ->
                                              eraseTerm (open n e1 e2) T (popen n e1' e2').
Admitted. 

Theorem eraseVal : forall e T e', eraseTerm e T e' -> pval e' = true -> val e = true.
Proof.
  intros. induction H; auto. 
  {simpl. simpl in H0. apply andb_true_iff in H0. inversion H0. apply IHeraseTerm1 in H2. 
   rewrite H2. auto. }
Qed. 

Theorem pdecomposeVal : forall e, pval e = true -> pdecompose e = (pholeCtxt, e).
Proof.
  induction e; intros; auto; try solve[simpl in H; inversion H].
  {simpl in *. apply andb_true_iff in H. inversion H; subst. rewrite H0. rewrite H1. auto. }
Qed. 
 
Theorem pdecomposedWF : forall E e, pctxtWF e E -> pdecompose (pfill E e) = (E, e).
Proof.
  induction E; intros; try solve[ 
  inversion H; subst; simpl; apply IHE in H2; rewrite H2; auto]; try solve[ 
  inversion H; subst; apply IHE in H3; simpl; rewrite H4; rewrite H3; auto]. 
  {inversion H; subst. apply IHE in H2. simpl. rewrite H4. rewrite H5. rewrite H2. auto. }
  {inversion H; subst. simpl. apply pdecomposeVal in H0. auto. }
Qed. 

Theorem eraseWF : forall E e E' e' T, eraseContext E T E' -> eraseTerm e T e' ->
                                      pctxtWF e' E' -> ctxtWF e E. 
Proof.
  intros. generalize dependent e. generalize dependent e'. induction H; intros;try solve[
  match goal with
      |H:pctxtWF ?e ?E |- _ => inversion H; constructor; subst; eapply IHeraseContext; eauto
  end]. 
  {inversion H1; subst. constructor. eapply IHeraseContext; eauto. rewrite <- H7.  
   eapply eraseVal. eapply eraseFill; eauto. apply pdecomposedWF. assumption. }
  {inversion H1; subst. constructor. eapply IHeraseContext. eassumption. assumption. 
   rewrite <- H7. eapply eraseVal.  eassumption. }
 



Theorem NonSpecPureStep : forall h sh pt pt' tid tid' s1 s2 M M' T T',
                            step h T (tSingleton (tid,s1,s2,M)) (OK h T (tSingleton(tid',s1,s2,M'))) ->
                            eraseTerm M tEmptySet pt ->
                            eraseTerm M' tEmptySet pt' ->
                            erasePool T T' ->
                            eraseHeap h sh ->
                            pstep sh T' (pSingleton pt) (pOK sh T' (pSingleton pt')).
Proof.
  intros. inversion H; cleanup; try solve[
     match goal with
         |H:?y = ?x::?y |- _ => apply listNeq in H; inversion H
         |H:?x::?y = ?y |- _ => symmetry in H; apply listNeq in H; inversion H
     end].
  {(*copy H1. apply decomposeErase in H1. invertHyp.  apply decomposeEq in H8. subst. 
   eapply decomposeErase in H0. invertHyp. inversion H6; subst.
   apply openErase with(e1:=N)(e1':=x2)(e2:= e)(e2':=N')(n:=0) in H0. 
   apply termErasureDeterminism with(M2:=popen 0 x2 N')in H1. subst. constructor. simpl. 
   apply eraseVal in H10. simpl in H10. rewrite <- H10. destruct (pdecompose (pfill E' x2)) eqn:eq. *) admit. }
  {copy H1. apply decomposeErase in H1. invertHyp. copy H6. apply decomposeEq in H6. subst. 
   apply decomposeErase in H0. invertHyp. inversion H6; subst. inversion H0; subst.
   eapply termErasureDeterminism in H1. rewrite <- H1. eapply pProjectL. 
   eapply ctxtErasureDeterminism in H11. rewrite <- H11. apply pdecomposeDecomposed. 
   apply decomposeWF in H7. 

  {subst. cleanup. copy H1. apply decomposeErase in H1. invertHyp. inversion H1; subst. 
   apply decomposeEq in H8. subst. eapply decomposeErase in H0. invertHyp. inversion H0. 
   subst. apply PBind. inversion H6. subst. invertHyp. apply pdecomposeDecomposed. auto. }
  {subst. cleanup. copy H1. apply decomposeErase in H1. invertHyp. inversion H1; subst. copy H8. 
   apply decomposeEq in H8. subst. copy H0. eapply decomposeErase in H0. invertHyp.  
   inversion H0; subst. inversion H9. invertHyp. econstructor. apply pdecomposeDecomposed; auto. }
  {subst. cleanup. copy H1. apply decomposeErase in H1. invertHyp. inversion H1; subst. copy H8. 
   apply decomposeEq in H8. subst. copy H0. eapply decomposeErase in H0. invertHyp.  
   inversion H0; subst. inversion H8. invertHyp. eapply pHandle.  apply pdecomposeDecomposed; auto. }
  {subst. cleanup. copy H1. apply decomposeErase in H1. invertHyp. inversion H1; subst. copy H8. 
   apply decomposeEq in H8. subst. copy H0. eapply decomposeErase in H0. invertHyp.  
   inversion H0; subst. inversion H9. invertHyp. econstructor. apply pdecomposeDecomposed; auto. }
  {match goal with
       |H:tEmptySet = Singleton ?T ?x |- _ => apply eqImpliesSameSet in H; unfold Same_set in H;
                                              unfold Included in H; inversion H as [Imp1 Imp2];
                                              assert(INHYP:Ensembles.In T (Singleton T x) x) by constructor;
                                              apply Imp2 in INHYP; inversion INHYP
   end. }
  {inversion H4. inversion H6. subst. inversion H10. }
  {eapply Heap.heapUpdateNeq in H10. exfalso. apply H10. eassumption. intros c. inversion c. 
   invertListNeq. }
  { eapply Heap.heapUpdateNeq in H10. exfalso. apply H10. eassumption. intros c. inversion c. }
  {apply AddEqSingleton in H4. apply AddEqSingleton in H6. inversion H4. inversion H6.
   rewrite <- H18 in H22. symmetry in H22. invertListNeq. }
  {inversion H7. invertListNeq. }
  {inversion H7. subst. inversion H8. invertListNeq. }
  {apply decomposeEq in H6. inversion H8. subst. inversion H7. subst. destruct E; simpl in *; 
   match goal with
       |H:ret ?N = ?x |- _ => inversion H
   end.
  } 
  {eapply disjointUnionEqSingleton in H4. inversion H4; subst. inversion H13. inversion H17. 
   constructor. unfold not. intros. inversion H16. inversion H18. apply AddEqSingleton in H4.
   subst x. subst x0. subst t1. destruct tid0. destruct p. 
   assert(exists x, thread_lookup TRB (Tid (n, n0) l) x). econstructor. econstructor. 
   eassumption. reflexivity. contradiction. }
  {inversion H8. apply decomposeEq in H6. subst. inversion H7; subst. }
  {inversion H10; inversion H11; subst. inversion H17. }
Qed. 

 