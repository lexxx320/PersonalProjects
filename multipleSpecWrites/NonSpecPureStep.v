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

Theorem pdecomposeDecomposed : forall E e, pdecompose e = (pholeCtxt, e) -> pdecompose (pfill E e) = (E, e).
Proof.
  induction E; eauto. 
  {intros. apply IHE in H. simpl. destruct (pdecompose(pfill E e)). inversion H; auto. }
  {intros. apply IHE in H. simpl. destruct (pdecompose(pfill E e)). inversion H; auto. }
Qed. 

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
   apply listNeq in H21. assumption. }
  { eapply Heap.heapUpdateNeq in H10. exfalso. apply H10. eassumption. intros c. inversion c. }
  {apply AddEqSingleton in H4. apply AddEqSingleton in H6. inversion H4. inversion H6.
   rewrite <- H17 in H21. symmetry in H21. apply listNeq in H21. inversion H21. }
  {inversion H4. apply listNeq in H10. inversion H10. }

  {inversion H8. subst. inversion H7. destruct s1'; inversion H11. }
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

 