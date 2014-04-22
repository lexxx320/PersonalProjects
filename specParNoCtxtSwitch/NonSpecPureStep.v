Require Import Spec.   
Require Import NonSpec. 
Require Import AST.
Require Import Coq.Sets.Ensembles.   
Require Import sets. 
Require Import SfLib. 

Ltac applyHyp :=
  match goal with
      |H : forall a : _, ?X -> ?Y, H' : ?Z |- _ => apply H in H'
  end. 

Fixpoint alphaConvert t x y :=
  match t with
      |pivar z => if beq_nat x z then pivar y else t
      |punit => punit
      |ppair e1 e2 => ppair (alphaConvert e1 x y) (alphaConvert e2 x y)
      |pvar z => if beq_nat x z then pvar y else t
      |plambda z e => if beq_nat x z then plambda y (alphaConvert e x y) 
                      else plambda z (alphaConvert e x y)
      |papp e1 e2 => papp (alphaConvert e1 x y) (alphaConvert e2 x y)
      |pret e => pret (alphaConvert e x y)
      |pbind e1 e2 => pbind (alphaConvert e1 x y) (alphaConvert e2 x y)
      |pfork e => pfork (alphaConvert e x y)
      |pnew => pnew
      |pput z e => if beq_nat x y then pput y (alphaConvert e x y) 
                   else pput z (alphaConvert e x y)
      |pget z => if beq_nat x y then pget y else t
      |praise e => praise (alphaConvert e x y)
      |phandle e1 e2 => phandle (alphaConvert e1 x y) (alphaConvert e2 x y)
      |pdone e => pdone (alphaConvert e x y)
      |pfst e => pfst (alphaConvert e x y)
      |psnd e => psnd (alphaConvert e x y)
  end. 

Axiom alphaEqual : forall t x y t2, alphaConvert t x y = t2 -> t = t2. 

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
  {admit. }{admit. }
Qed. 

Theorem lastElementEq : forall (T:Type) l1 l2 (e1 e2 : T),
                          l1 ++ [e1] = l2 ++ [e2] -> e1 = e2. 
Proof.
  intros. generalize dependent l2. induction l1; intros. 
  {destruct l2. 
   {inversion H. reflexivity. }
   {inversion H. destruct l2; inversion H2. }
  }
  {destruct l2. 
   {simpl in *. inversion H. destruct l1; inversion H2. }
   {simpl in *. inversion H. apply IHl1 in H2. assumption. }
  }
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
  try(subst; eapply termErasureDeterminism in H9;[rewrite <-H9; reflexivity| auto]);
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

Require Import Coq.Program.Equality. 
 
Theorem pdecomposeNotVal : forall M E e,
                             pdecompose M E e -> ~pvalue M. 
Proof.
  intros. inversion H; subst; intros c; inversion c. Qed. 

Theorem eraseValue : forall M T e, value M -> eraseTerm M T e -> pvalue e. 
Proof.
  intros. inversion H0; subst; try inversion H; try constructor. Qed. 

Theorem erasureDecompose : forall t T pt E e,
                             eraseTerm t T pt -> decompose t E e ->
                             exists E' e', eraseTerm e T e' /\ pdecompose pt E' e'. 
Proof.
  intros. generalize dependent pt. induction H0. 
  {intros. inversion H2; subst. apply IHdecompose in H5. inversion H5. 
   inversion H3. inversion H4. econstructor. exists x0. split. 
   assumption. econstructor. apply pdecomposeNotVal in H7. assumption. 
   eassumption. }
  {intros. inversion H0; subst. econstructor. econstructor. split. 
   eassumption. eapply bindCtxtValue. eapply eraseValue in H. eassumption. 
   eassumption. }
  {intros. inversion H2; subst. apply IHdecompose in H5. inversion H5. 
   inversion H3. inversion H4. econstructor. exists x0. split. assumption. 
   econstructor. apply pdecomposeNotVal in H10. assumption. eassumption. }
  {intros. inversion H0; subst. econstructor. econstructor. split. 
   eassumption. eapply bindCtxtValue. eapply eraseValue in H. eassumption. 
   eassumption. }
  {intros. inversion H2; subst. apply IHdecompose in H5. inversion H5. 
   inversion H3. inversion H4. econstructor. econstructor. split. eassumption. 
   econstructor. apply pdecomposeNotVal in H7. assumption. eassumption. }
  {intros. inversion H0; subst. econstructor. econstructor. split. eassumption. 
   eapply handleCtxtValue. eapply eraseValue in H. eassumption. eassumption. }
Qed. 

Ltac copy H := 
  match type of H with
      |?X => assert(X) by apply H
  end. 

Theorem eraseHole : forall E E' t (e1 e2:term) (e1' e2':pterm) T,
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
Theorem NonSpecPureStep : forall h sh t t' pt pt' tid tid' s1 s2 M M',
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









