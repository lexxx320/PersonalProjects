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
   econstructor. apply pdecomposeNotVal in H9. assumption. eassumption. }
  {intros. inversion H0; subst. econstructor. econstructor. split. 
   eassumption. eapply bindCtxtValue. eapply eraseValue in H. eassumption. 
   eassumption. }
  {intros. inversion H2; subst. apply IHdecompose in H5. inversion H5. 
   inversion H3. inversion H4. econstructor. econstructor. split. eassumption. 
   econstructor. apply pdecomposeNotVal in H7. assumption. eassumption. }
  {intros. inversion H0; subst. econstructor. econstructor. split. eassumption. 
   eapply handleCtxtValue. eapply eraseValue in H. eassumption. eassumption. }
Qed. 

Theorem erasureDecompose' : forall t T pt E e e',
                             eraseTerm t T pt -> decompose t E e ->
                             eraseTerm e T e' -> 
                             exists E', pdecompose pt E' e'. 
Proof.
  intros. generalize dependent pt. generalize dependent e'. induction H0. 
  {intros. inversion H1; 
   try(subst; inversion H2; subst; inversion H3; subst; eapply IHdecompose in H2; 
    inversion H2; [econstructor; econstructor;[apply pdecomposeNotVal in H4| 
    eassumption]; eassumption |assumption]). }
  {intros; apply termErasureDeterminism with (M1:=pt)in H1; [subst; econstructor; 
   inversion H0; subst; econstructor; eapply eraseValue in H; [eassumption|
   eassumption]|assumption]. }
  {intros. inversion H1; 
    try(subst; inversion H2; subst; inversion H3; subst; eapply IHdecompose in H2; 
    inversion H2; [econstructor; econstructor;[apply pdecomposeNotVal in H4| 
    eassumption]; eassumption |assumption]). }
 {intros; apply termErasureDeterminism with (M1:=pt)in H1; [subst; econstructor; 
   inversion H0; subst; econstructor; eapply eraseValue in H; [eassumption|
   eassumption]|assumption]. }   
 {intros. inversion H1; 
    try(subst; inversion H2; subst; inversion H3; subst; eapply IHdecompose in H2; 
    inversion H2; [econstructor; econstructor;[apply pdecomposeNotVal in H4| 
    eassumption]; eassumption |assumption]). }
 {intros; apply termErasureDeterminism with (M1:=pt)in H1; [subst; econstructor; 
   inversion H0; subst; econstructor; eapply eraseValue in H; [eassumption|
   eassumption]|assumption]. }  
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
  intros. remember (E' e1'). induction H0; try(solve[inversion H]). 
  {

Require Import Coq.Sets.Powerset_facts. 
Theorem NonSpecPureStep : forall h h' sh sh' t t' pt pt' tid tid' s1 s2 M M',
                            t = tSingleton (tid,s1,s2,M) -> 
                            t' = tSingleton(tid',s1,s2,M') ->
                            multistep h tEmptySet t h' tEmptySet t' ->
                            eraseTerm M tEmptySet pt ->
                            eraseTerm M' tEmptySet pt' ->
                            eraseHeap h sh -> eraseHeap h' sh' ->
                            pmultistep sh (Empty_set pterm)(pSingleton pt) sh'
                                       (Empty_set pterm) (pSingleton pt').
Proof.
  intros. generalize dependent tid'. generalize dependent M'. 
  generalize dependent pt. generalize dependent M. induction H1. 
  {intros. subst. apply SingletonEq in H0. inversion H0. subst. 
   eapply termErasureDeterminism in H2. eapply eraseHeapDeterminism in H4. 
   rewrite <- H2. rewrite <- H4. econstructor. assumption. assumption. }
  {intros. inversion H1; subst. 
   {symmetry in H. apply disjointUnionEqSingleton with(e2:=(tid,s1,s2,M))in H0. 
    inversion H0. copy H9. apply decomposeEq in H9. subst t.  copy H6. 
    eapply erasureDecompose with (e:=bind(ret M0) N)in H6. inversion H6. 
    inversion H11. inversion H12. inversion H13. inversion H17. 
    eapply pSingletonMultistep. econstructor. 
    intros c. inversion c. apply PBind. subst x0. subst e1'. eassumption. 
    unfold pUnion. unfold pSingleton. rewrite Union_commutative. rewrite union_empty. 
    eapply IHmultistep. assumption. assumption. subst. rewrite <- union_empty. 
    rewrite Union_commutative. unfold tUnion. inversion H3. subst. reflexivity. 
    subst. 

