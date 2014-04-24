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
Qed. 

Theorem erasureDecompose : forall t T pt E e,
                            eraseTerm t T pt -> decompose t = (E, e) ->
                            exists E' e', eraseTerm e T e' /\ pdecompose pt = (E',e').
Proof.
  induction t; intros; simpl in *;try(inversion H; inversion H0; subst; econstructor; econstructor; split;[eassumption | reflexivity]).
  {inversion H; inversion H0; subst. }
  {destruct (decompose t1). inversion H0; inversion H; subst. eapply IHt1 in H5. 
   inversion H5. inversion H1. inversion H2. econstructor. econstructor. split. 
   eassumption. simpl. rewrite H4. reflexivity. reflexivity. }
  {destruct (decompose t1). inversion H0; inversion H; subst. eapply IHt1 in H5. 
   inversion H5. inversion H1. inversion H2. econstructor. econstructor. split. 
   eassumption. simpl. rewrite H4. reflexivity. reflexivity. }
  {

Ltac copy H := 
  match type of H with
      |?X => assert(X) by apply H
  end. 

Theorem eraseHole : forall E E' t e1 e2 e1' e2' T,
                      decompose t E e1 ->
                      eraseTerm t T (E' e1') ->
                      eraseTerm e2 T e2' ->
                      eraseTerm (E e2) T (E' e2').
Proof.
  intros. remember (E' e1'). generalize dependent E. generalize dependent E'. 
  generalize dependent e2. generalize dependent e2'. generalize dependent e1. 
  generalize dependent e1'. induction H0; intros; try(solve[inversion H]). 
Admitted. 




Theorem EmptyEqUnion : forall (T:Type) S1 S2, Empty_set T = Union T S1 S2 -> 
                                              S1 = Empty_set T /\ S2 = Empty_set T. 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. 
  inversion H; clear H. split. 
  {apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
   {intros. assert(Ensembles.In T (Union T S1 S2) x). apply Union_introl; assumption. 
    apply H1 in H2. inversion H2. }
   {intros. inversion H. }
  }
  {apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
   {assert(Ensembles.In T (Union T S1 S2) x). apply Union_intror; assumption. 
    apply H1 in H2. inversion H2. }
   {inversion H. }
  }
Qed. 

Theorem SingletonNeqEmpty : forall (T:Type) s, Singleton T s = Empty_set T -> False. 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. 
  inversion H. assert(Ensembles.In T (Singleton T s) s). constructor. apply H0 in H2. 
  inversion H2. Qed. 

Theorem CoupleNeqEmpty : forall (T:Type) s1 s2, Couple T s1 s2 = Empty_set T -> False. 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inversion H. 
  assert(Ensembles.In T (Couple T s1 s2) s1). constructor. apply H0 in H2. inversion H2. Qed. 

Theorem listNeq : forall (T:Type) l (e:T), l = e::l -> False. 
Proof.
  intros. induction l. 
  {inversion H. }{inversion H. apply IHl in H2. assumption. }Qed. 

Require Import Coq.Sets.Powerset_facts. 

Ltac cleanup' := unfold tSingleton in *; unfold tCouple in *; unfold tAdd in *;
  repeat(match goal with
           |H : ?x = ?x |- _ => clear H; subst
           |H : Singleton ?T ?x = Singleton ?T ?y |- _ => apply SingletonEq in H; inversion H; subst
         end). 
            
Theorem NonSpecPureStep : forall h sh pt pt' tid tid' s1 s2 M M',
                            step h tEmptySet (tSingleton (tid,s1,s2,M)) h tEmptySet (tSingleton(tid',s1,s2,M')) ->
                            eraseTerm M tEmptySet pt ->
                            eraseTerm M' tEmptySet pt' ->
                            eraseHeap h sh ->
                            pstep sh (Empty_set ptrm)(pSingleton pt) sh
                                       (Empty_set ptrm) (pSingleton pt').
Proof.
  intros. inversion H. 
  {subst. cleanup'. copy H9. eapply erasureDecompose in H9; try eassumption. inversion H9. 
   inversion H4. inversion H5. inversion H6; subst. apply pdecomposeEq in H8. subst. 
   

Inductive eraseContext : ctxt -> pool -> pctxt -> Prop :=
|eraseCtxtHole : forall T, eraseContext (fun x => x) T (fun x' => x')
|eraseCtxtBind : forall T N N' E E', eraseTerm N T N' -> eraseContext E T E' ->
                                     eraseContext (fun x => bind (E x) N) T (fun y : ptrm => pbind (E' y) N')
|eraseCtxtSpec : forall T M M' M'' E E' t maj min min' min'' s1 s2,
                   eraseContext E T E' -> 
                   thread_lookup T (Tid(maj,min) t) (Tid(maj,min')t, s1 ++ [sAct (Tid(maj,min'')t) M'], s2, M) ->
                   eraseTerm M' T M'' ->
                   eraseContext (fun x => specReturn (E x) (threadId (Tid(maj,min) t))) T 
           (fun x => pbind (E' x) (plambda (pbind (incBV 1 M'') (plambda (pret (ppair (pbvar 0)(pbvar 1)))))))
|eraseCtxtHandle : forall T N N' E E',
                     eraseTerm N T N' -> eraseContext E T E' ->
                     eraseContext (fun x => handle (E x) N) T (fun y => phandle (E' y) N')
.



Theorem eraseHole' : forall t T E' e1',
                       eraseTerm t T (E' e1') -> forall E e1 e2 e2' T,
                                                   decompose t E e1 ->
                      
                      eraseTerm e2 T e2' -> 
                      eraseTerm (E e2) T (E' e2').
Proof.
  intros t T E' e1' H. induction H; intros; 
                       try(match goal with
                               |H : decompose ?M ?T ?e |- _ => try solve[inversion H]
                          end). 
  {inversion H1; subst. 
   {eapply IHeraseTerm1 in H6. 



Theorem NonSpecPureMultistep : forall h sh t t' pt pt' tid tid' s1 s2 M M',
                                 t = tSingleton (tid,s1,s2,M) -> 
                                 t' = tSingleton(tid',s1,s2,M') ->
                                 multistep h tEmptySet t h tEmptySet t' ->
                                 eraseTerm M tEmptySet pt ->
                                 eraseTerm M' tEmptySet pt' ->
                                 eraseHeap h sh ->
                                 pmultistep sh (Empty_set pterm)(pSingleton pt) sh
                                            (Empty_set pterm) (pSingleton pt').
Proof.
  intros. generalize dependent tid'. generalize dependent M'. 
  generalize dependent pt. generalize dependent M. induction H1. 
  {intros. subst. apply SingletonEq in H0. inversion H0. subst.  
   eapply termErasureDeterminism in H2. rewrite <- H2.  econstructor. assumption. }
   {intros. inversion H1; subst. 
   {symmetry in H. apply disjointUnionEqSingleton with (e2:=(tid,s1,s2,M)) in H0; try assumption. 
    inversion H0. inversion H3; subst. copy H8; apply decomposeEq in H8. copy H5. 
    eapply erasureDecompose with (e:=bind(ret M0) N)in H5; try eassumption. inversion H5. 
    inversion H10. inversion H11. inversion H12. inversion H16. subst. 
    eapply pSingletonMultistep. econstructor. intros c. inversion c. apply PBind. eassumption. 
    unfold pUnion. unfold pSingleton. rewrite Union_commutative. rewrite union_empty. 
    eapply IHmultistep; try eassumption. rewrite <- union_empty. 
    rewrite Union_commutative. unfold tUnion. reflexivity. 
    apply eraseHole with (t:=E(bind(ret M0) N))(e1:=bind(ret M0)N)(e1':=pbind(pret e') e2'). 
    assumption. apply pdecomposeEq in H13. rewrite H13 in H9. assumption. constructor. assumption. 
    assumption. reflexivity. }
   {symmetry in H. apply disjointUnionEqSingleton with (e2:=(tid,s1,s2,M)) in H0; try assumption. 
    inversion H0. inversion H3. subst. copy H8. apply decomposeEq in H8. copy H5. 
    eapply erasureDecompose with (e:=bind(raise M0) N)in H5; try eassumption. inversion H5. 
    inversion H10. inversion H11. inversion H12. inversion H16. subst. 
    eapply pSingletonMultistep. econstructor. intros c. inversion c. eapply PBindRaise. eassumption. 
    unfold pUnion. unfold pSingleton. rewrite Union_commutative. rewrite union_empty. 
    eapply IHmultistep; try eassumption. rewrite <- union_empty. 
    rewrite Union_commutative. unfold tUnion. reflexivity. eapply eraseHole. eassumption. 
    apply pdecomposeEq in H13. rewrite H13 in H9. eassumption. eassumption. reflexivity. }
   {symmetry in H. apply disjointUnionEqSingleton with (e2:=(tid,s1,s2,M)) in H0; try assumption. 
    inversion H0. inversion H3. subst. copy H8. apply decomposeEq in H8. copy H5. 
    eapply erasureDecompose with (e:=handle(raise M0) N)in H5; try eassumption. inversion H5. 
    inversion H10. inversion H11. inversion H12. inversion H16. subst. 
    eapply pSingletonMultistep. econstructor. intros c. inversion c. eapply pHandle. eassumption. 
    unfold pUnion. unfold pSingleton. rewrite Union_commutative. rewrite union_empty. 
    eapply IHmultistep; try eassumption. rewrite <- union_empty. 
    rewrite Union_commutative. unfold tUnion. reflexivity. eapply eraseHole. eassumption. 
    apply pdecomposeEq in H13. rewrite H13 in H9. eassumption. econstructor; assumption. reflexivity. }
   {symmetry in H. apply disjointUnionEqSingleton with (e2:=(tid,s1,s2,M)) in H0; try assumption. 
    inversion H0. inversion H3. subst. copy H8. apply decomposeEq in H8. copy H5. 
    eapply erasureDecompose with (e:=handle(ret M0) N)in H5; try eassumption. inversion H5. 
    inversion H10. inversion H11. inversion H12. inversion H16. subst. 
    eapply pSingletonMultistep. econstructor. intros c. inversion c. eapply pHandleRet. eassumption. 
    unfold pUnion. unfold pSingleton. rewrite Union_commutative. rewrite union_empty. 
    eapply IHmultistep; try eassumption. rewrite <- union_empty. 
    rewrite Union_commutative. unfold tUnion. reflexivity. eapply eraseHole. eassumption. 
    apply pdecomposeEq in H13. rewrite H13 in H9. eassumption. econstructor; assumption. reflexivity. }
   {symmetry in H. apply disjointUnionEqSingleton with (e2:=(tid,s1,s2,M)) in H0; try assumption. 
    inversion H0. inversion H3. subst. unfold tUnion in H2. rewrite union_empty in H2. 
    inversion H2. 
    {apply eqImpliesSameSet in H13. unfold Same_set in H13. unfold Included in H13. inversion H13. 
     assert(tIn (tSingleton(tid',nil,s2,M'))(tid',nil,s2,M')). constructor. apply H14 in H15. 
     inversion H15. }
    {subst. apply EmptyEqUnion in H7. inversion H7. subst. inversion H9; try(
     match goal with
         |H : tSingleton ?s = Empty_set ?T |- _ => apply SingletonNeqEmpty in H; inversion H
         |H : tCouple ?s1 ?s2 = Empty_set ?T |- _ => apply CoupleNeqEmpty in H; inversion H
     end). 
     {subst. unfold tAdd in H11. unfold Add in H11. symmetry in H11. apply EmptyEqUnion in H11. 
      inversion H11. apply SingletonNeqEmpty in H14. inversion H14. }
    }
   }
   {admit. }
   {inversion H1; try
    match goal with
        |H:Heap.heap_lookup ?x ?h = Some ?v, H':?h = Heap.replace ?x ?V' ?h |- _ =>
         apply Heap.heapUpdateNeq with (v' := V') in H;[exfalso; unfold not in H; apply H; assumption|
         intros c; inversion c; match goal with
                                    |H:?l = ?x::?l |- _ => apply listNeq in H; inversion H
                                end]
    end.
    {subst. apply SingletonEq in H3. apply SingletonEq in H7. inversion H3; inversion H7; subst. 
     cleanup. 









