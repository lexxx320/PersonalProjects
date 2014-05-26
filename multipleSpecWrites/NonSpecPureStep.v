Require Import Spec.   
Require Import NonSpec. 
Require Import AST.
Require Import Coq.Sets.Ensembles.   
Require Import sets. 
Require Import SfLib. 
Require Import Coq.Program.Equality. 

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

Theorem termErasureDeterminism : forall M T M1 M2,
                                   eraseTerm M T M1 -> eraseTerm M T M2 -> M1 = M2. 
Proof.
  intros. generalize dependent M2. induction H; intros; 
                                   try(inversion H0; reflexivity);
  try(clear H; clear H0; match goal with
                           |H:eraseTerm ?T ?T' ?M |- _ => 
                    inversion H; clear H; applyHyp; applyHyp; subst; reflexivity
                         end); 
  try(clear H; match goal with
                |H : eraseTerm ?T ?T' ?M |- _ =>
                 inversion H; clear H; applyHyp; subst; reflexivity
               end). 
  {inversion H3; subst. apply IHeraseTerm1 in H8. rewrite H8. 
   apply uniqueThreadPool with (t' := (Tid(maj,min') tid, s1' ++ [sAct (Tid(maj,min'')tid) M'], s2, M)) in H13. 
   inversion H13. apply lastElementEq in H5. inversion H5. subst. apply IHeraseTerm2 in H12. 
   subst. reflexivity. assumption. }
Qed. 

Theorem erasureDeterminism : forall t t1' t2' T, 
                               eraseThread t T t1' -> 
                               eraseThread t T t2' -> t1' = t2'.
Proof.
  intros. induction H; inversion H0;
  try(subst; match goal with
               |H:eraseTerm ?M ?T ?x, H':eraseTerm ?M ?T ?y |- _ =>
                eapply termErasureDeterminism in H;[rewrite<-H;reflexivity|auto]
               |H:[] = [] ++ [?x] |- _ => inversion H       
               |H:[] = ?x ++ [?y] |- _ => destruct x; inversion H
               |H:?s1++[?x]=?s2++[?y]|-_ => apply lastElementEq in H; inversion H
             end);
  try(subst; eapply termErasureDeterminism in H12;[rewrite <-H12; reflexivity| auto]);
  reflexivity. Qed. 
  
Theorem eraseHeapDeterminism : forall h h1 h2, 
                                 eraseHeap h h1 -> eraseHeap h h2 ->
                                 h1 = h2. 
Proof.
  intros. generalize dependent h2. induction H; intros. 
  {inversion H0. subst. apply IHeraseHeap in H6. assumption. }
  {inversion H0. subst. apply IHeraseHeap in H4. subst. reflexivity. }
  {inversion H0; subst. apply IHeraseHeap in H10. assumption. }
  {inversion H0. subst. apply IHeraseHeap in H9. subst. reflexivity. }
  {inversion H1. subst. apply IHeraseHeap in H8. subst. 
   eapply termErasureDeterminism in H0. rewrite <-H0. reflexivity. assumption. }
  {inversion H0. reflexivity. }
Qed. 

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


Inductive eraseContext : ctxt -> pool -> pctxt -> Prop :=
|eraseCtxtHole : forall T, eraseContext holeCtxt T pholeCtxt
|eraseCtxtBind : forall T N N' E E', eraseTerm N T N' -> eraseContext E T E' ->
                                     eraseContext (bindCtxt E N) T (pbindCtxt E' N')
|eraseCtxtSpec : forall T M M' M'' E E' t maj min min' min'' s1 s2,
                   eraseContext E T E' -> 
                   thread_lookup T (Tid(maj,min) t) (Tid(maj,min')t, s1 ++ [sAct (Tid(maj,min'')t) M'], s2, M) ->
                   eraseTerm M' T M'' ->
                   eraseContext (specReturnCtxt E (threadId (Tid(maj,min)t))) T 
                                (pbindCtxt E' (plambda (pbind (incBV 1 M'') (plambda (pret (ppair (pbvar 0)(pbvar 1)))))))
|eraseCtxtHandle : forall T N N' E E',
                     eraseTerm N T N' -> eraseContext E T E' ->
                     eraseContext (handleCtxt E N) T (phandleCtxt E' N')
.

Theorem ctxtErasureDeterminism : forall E T E1 E2, eraseContext E T E1 -> eraseContext E T E2 ->
                                                   E1 = E2. 
Proof.
  intros. generalize dependent E2. induction H; intros. 
  {inversion H0; subst. reflexivity. }
  {inversion H1; subst. apply IHeraseContext in H7. subst. eapply termErasureDeterminism in H. 
   rewrite <- H. reflexivity. assumption. }
  {inversion H2; subst. apply IHeraseContext in H9. subst. 
   apply uniqueThreadPool with (t' := (Tid (maj, min'0) t, s0 ++ [sAct (Tid (maj, min''0) t) M'0], s3, M0)) in H0. 
   inversion H0; subst. apply lastElementEq in H5. inversion H5; subst. 
   eapply termErasureDeterminism in H11. rewrite <- H11. reflexivity. assumption. assumption. }
  {inversion H1; subst. apply IHeraseContext in H7. subst. eapply termErasureDeterminism in H. 
   rewrite <- H. reflexivity. assumption. }
Qed. 

Hint Constructors eraseContext eraseTerm. 

Ltac invertHyp :=
  match goal with
      |H : exists e : _, ?x |- _ => inversion H; clear H; subst; try invertHyp
      |H : ?x /\ ?y |- _ => inversion H; clear H; subst; try invertHyp
      |H : eraseTerm ?M ?T ?t, H' : eraseTerm ?M ?T ?t' |- _ => 
       eapply termErasureDeterminism in H; try eassumption; subst; try invertHyp
      |H : eraseContext ?E ?T ?E1, H' : eraseContext ?E ?T ?E2 |- _ => 
       eapply ctxtErasureDeterminism in H; try eassumption; subst; try invertHyp
  end. 

Theorem decomposeErase : forall E e T t', 
                           eraseTerm (fill E e) T t' -> 
                           exists E' e', eraseContext E T E' /\ eraseTerm e T e' /\ t' = pfill E' e'.
Proof. 
  intros. remember (fill E e). generalize dependent E. generalize dependent e. induction H; intros;
       try solve[destruct E; inversion Heqt; simpl in *; subst; econstructor; econstructor; eauto]; 
       try solve[destruct E; inversion Heqt; simpl in *; repeat (match goal with
       |H:forall e0 E, ?e = fill E e0 -> ?X |- _ => 
        assert(Z:e = fill holeCtxt e) by reflexivity; apply H in Z;
       invertHyp; clear H
       |H:eraseContext holeCtxt ?T ?x |- _ => inversion H; subst
   end); econstructor; econstructor; eauto].
  {destruct E; inversion Heqt; simpl in *. 
   {apply IHeraseTerm1 in H2. invertHyp. econstructor. econstructor. eauto. } 
   {subst. econstructor. econstructor. eauto. }
  }
  {destruct E; inversion Heqt; simpl in *. 
   {apply IHeraseTerm1 in H2. invertHyp. econstructor. econstructor. eauto. }
   {subst. econstructor. econstructor. eauto. }
  }
  {destruct E; inversion Heqt; simpl in *. 
   {apply IHeraseTerm1 in H4. invertHyp. econstructor. econstructor. eauto. }
   {subst. econstructor. econstructor. eauto. }
  }
Qed. 

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
                            step h T (tSingleton (tid,s1,s2,M)) h T (tSingleton(tid',s1,s2,M')) ->
                            eraseTerm M tEmptySet pt ->
                            eraseTerm M' tEmptySet pt' ->
                            erasePool T T' ->
                            eraseHeap h sh ->
                            pstep sh T' (pSingleton pt) sh T' (pSingleton pt').
Proof.
  intros. inversion H; cleanup.
  {subst. cleanup. copy H1. apply decomposeErase in H1. invertHyp. inversion H1; subst. copy H10. 
   apply decomposeEq in H10. subst. copy H0. eapply decomposeErase in H0. invertHyp.  
   inversion H0; subst. apply PBind. inversion H9. invertHyp. apply pdecomposeDecomposed; auto. }
  {subst. cleanup. copy H1. apply decomposeErase in H1. invertHyp. inversion H1; subst. copy H10. 
   apply decomposeEq in H10. subst. copy H0. eapply decomposeErase in H0. invertHyp.  
   inversion H0; subst. inversion H9. invertHyp. econstructor. apply pdecomposeDecomposed; auto. }
  {subst. cleanup. copy H1. apply decomposeErase in H1. invertHyp. inversion H1; subst. copy H10. 
   apply decomposeEq in H10. subst. copy H0. eapply decomposeErase in H0. invertHyp.  
   inversion H0; subst. inversion H9. invertHyp. eapply pHandle.  apply pdecomposeDecomposed; auto. }
  {subst. cleanup. copy H1. apply decomposeErase in H1. invertHyp. inversion H1; subst. copy H10. 
   apply decomposeEq in H10. subst. copy H0. eapply decomposeErase in H0. invertHyp.  
   inversion H0; subst. inversion H9. invertHyp. econstructor. apply pdecomposeDecomposed; auto. }
  { apply eqImpliesSameSet in H10. unfold Same_set in H10. inversion H10. unfold Included in H5. 
   assert(Ensembles.In thread (Singleton thread (tid', [], s2, M'))(tid', [], s2, M')). 
   constructor. apply H5 in H6. inversion H6. }
  {inversion H4. inversion H6. subst. inversion H10. }
  {eapply Heap.heapUpdateNeq in H9. exfalso. apply H9. eassumption. intros c. inversion c. 
   apply listNeq in H21. assumption. }
  { eapply Heap.heapUpdateNeq in H9. exfalso. apply H9. eassumption. intros c. inversion c. }
  {destruct h; simpl in H11; inversion H11. destruct p. inversion H11. apply listNeq in H16. 
   inversion H16. }
  {inversion H4. inversion H7. subst. inversion H10. }
  {inversion H7. inversion H8. subst. destruct s1'; inversion H17. }
  {inversion H8. }
  {eapply disjointUnionEqSingleton in H4. inversion H4; subst. inversion H10. inversion H17. 
   constructor. unfold not. intros. inversion H7.  inversion H11; subst. 
   destruct tid0. destruct p. assert(exists p, thread_lookup TRB (Tid (n,n0)l) p). 
   econstructor. econstructor. eassumption. reflexivity. contradiction. }
  {inversion H8. }
  {symmetry in H9. apply listNeq in H9. inversion H9. }
  {symmetry in H10. apply listNeq in H10. inversion H10. }
  {symmetry in H10. apply listNeq in H10. inversion H10. }
  {symmetry in H10. apply listNeq in H10. inversion H10. }
  {inversion H8; inversion H9; subst. inversion H17. }
Qed. 

 