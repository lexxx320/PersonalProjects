Require Import Spec. 
Require Import NonSpec. 
Require Import AST.
Require Import Coq.Sets.Ensembles.   
Require Import sets. 
Require Import CpdtTactics. 
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
      |plambda z e => if beq_nat x z then plambda y (alphaConvert e x y) else plambda z (alphaConvert e x y)
      |papp e1 e2 => papp (alphaConvert e1 x y) (alphaConvert e2 x y)
      |pret e => pret (alphaConvert e x y)
      |pbind e1 e2 => pbind (alphaConvert e1 x y) (alphaConvert e2 x y)
      |pfork e => pfork (alphaConvert e x y)
      |pnew => pnew
      |pput z e => if beq_nat x y then pput y (alphaConvert e x y) else pput z (alphaConvert e x y)
      |pget z => if beq_nat x y then pget y else t
      |praise e => praise (alphaConvert e x y)
      |phandle e1 e2 => phandle (alphaConvert e1 x y) (alphaConvert e2 x y)
      |pdone e => pdone (alphaConvert e x y)
      |pfst e => pfst (alphaConvert e x y)
      |psnd e => psnd (alphaConvert e x y)
  end. 

Axiom alphaEqual : forall t x y t2, alphaConvert t x y = t2 -> t = t2. 

Theorem termErasureDeterminsim : forall M T M1 M2,
                                   eraseTerm M T M1 -> eraseTerm M T M2 -> M1 = M2. 
Proof.
  intros. generalize dependent M2. induction H; intros; try(inversion H0; reflexivity);
  try(clear H; clear H0; match goal with
                           |H:eraseTerm ?T ?T' ?M |- _ => 
                            inversion H; clear H; applyHyp; applyHyp; subst; reflexivity
                         end); 
  try(clear H; match goal with
                |H : eraseTerm ?T ?T' ?M |- _ =>
                 inversion H; clear H; applyHyp; subst; reflexivity
               end). 
  {inversion H2. subst. apply IHeraseTerm1 in H5. apply IHeraseTerm2 in H6. 
   subst. assert(pbind e1'0
     (plambda i (pbind e2'0 (plambda j (pret (ppair (pvar i) (pvar j)))))) =
   pbind e1'0
     (plambda i (pbind e2'0 (plambda j0 (pret (ppair (pvar i0) (pvar j0))))))). 
   apply alphaEqual with (x := j)(y := j0). simpl. 


Theorem erasureDeterminism : forall t t1' t2' T, 
                               eraseThread t T t1' -> eraseThread t T t2' -> t1' = t2'.
Proof.
  intros. inversion H. 
  {subst. inversion H0. subst. 


Theorem NonSpecPureStep : forall h h' sh sh' tid s1 s2 M tid' M' t t', 
                            multistep h tEmptySet (tSingleton (tid, s1, s2, M)) h' 
                                      tEmptySet (tSingleton(tid', s1, s2, M')) ->
                            eraseThread (tid, s1, s2, M) tEmptySet (pSingleton t) ->
                            eraseThread (tid', s1, s2, M') tEmptySet (pSingleton t') ->
                            eraseHeap h sh -> eraseHeap h' sh' ->
                            pmultistep sh (Empty_set pterm) (pSingleton t) sh' (Empty_set pterm) (pSingleton t'). 
Proof.
  intros. remember (tSingleton(tid, s1, s2, M)). remember (tSingleton (tid', s1, s2, M')).  induction H. 
  {subst. inversion Heqe0. apply SingletonEq in H4. inversion H4. subst. 
   

