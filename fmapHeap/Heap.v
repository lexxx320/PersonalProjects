Require Export List.
Require Export SpecLib.
Require Import AST. 
Require Export FMapList.
Require Export Coq.Structures.OrderedTypeEx.
Require Export FMapFacts.

Module M := FMapList.Make(Nat_as_OT).

Module MFacts := WFacts(M). 

Definition heap (T:Type) := M.t T. 

Definition heap_lookup {T:Type} (k:id) (m:heap T) := M.find k m.

Definition replace {T:Type} (i:id) (v:T) (h:heap T) := 
  M.add i v h. 

Definition extend {T:Type} (i:id) (v:T) (h:heap T) :=
  M.add i v h. 

Hint Unfold heap_lookup replace extend. 

Theorem heapUpdateNeq : forall (T:Type) h i (v v' : T),
                          heap_lookup i h = Some v -> 
                          v <> v' -> h <> replace i v' h. 
Proof.
  intros. intros c. rewrite c in H. unfold heap_lookup in H. 
  unfold replace in H. rewrite <- MFacts.find_mapsto_iff in H. 
  rewrite MFacts.add_mapsto_iff in H. inversion H. inversion H1. 
  symmetry in H3. contradiction. inversion H1. apply H2; auto. 
Qed.

Theorem HeapLookupReplace : forall (T:Type) x (h:heap T) v v', 
                              heap_lookup x h = Some v' ->
                              heap_lookup x (replace x v h) = Some v. 
Proof.
  intros. apply MFacts.add_eq_o. auto. 
Qed. 

Theorem lookupExtend : forall (T:Type) H (v:T) x, 
                         heap_lookup x (extend x v H) = Some v.
Proof.
  intros. apply MFacts.add_eq_o. auto.
Qed. 

Theorem lookupDeterministic : forall (T:Type) x H (v v':option T), 
                                heap_lookup x H = v -> heap_lookup x H = v' -> v = v'. 
Proof.
  intros. destruct v; destruct v'. 
  {



  induction H; intros. 
  {simpl in *. subst. auto. }
  {simpl in *. destruct a. destruct (beq_nat x i). subst. auto. subst. auto. }
Qed. 

Theorem lookupDeterministic : forall (T:Type) x H (v v':option T), 
                                heap_lookup x H = v -> heap_lookup x H = v' -> v = v'. 
Proof.
  destruct H. intros. simpl in *. eapply raw_lookupDeterministic in H; eauto.
Qed. 

Theorem raw_lookupReplaceNeq : forall (T:Type) H x x' v (v':T), 
                                 x<>x' -> 
                                 (raw_heap_lookup x H = v <->
                                  raw_heap_lookup x (raw_replace x' v' H) = v).
Proof.
  intros. split; intros. 
  {induction H. 
   {inv H1. auto. }
   {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq1; destruct (beq_nat x' i) eqn:eq2. 
    {apply beq_nat_true in eq1. apply beq_nat_true in eq2. subst. exfalso. apply H0; auto. }
    {simpl. rewrite eq1. auto. }
    {simpl. apply beq_nat_false_iff in H0. rewrite H0; auto. }
    {simpl. rewrite eq1. auto. }
   }
  }
  {induction H.
   {inv H1. auto. }
   {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq1; destruct (beq_nat x' i)eqn:eq2. 
    {apply beq_nat_true in eq1. apply beq_nat_true in eq2. subst. exfalso. apply H0; auto. }
    {simpl in *. rewrite eq1 in H1. auto. }
    {simpl in *. apply beq_nat_false_iff in H0. rewrite H0 in H1. auto. }
    {simpl in *. rewrite eq1 in H1. auto. }
   }
  }
Qed. 

Theorem lookupReplaceNeq : forall (T:Type) H x x' v (v':T), 
                             x<>x' -> 
                             (heap_lookup x H = v <->
                              heap_lookup x (replace x' v' H) = v).
Proof.
  intros. destruct H. simpl. apply raw_lookupReplaceNeq. auto. 
Qed. 

Theorem rawHeapsEq : forall T H H' prf prf',  H = H' -> heap_ T H prf = heap_ T H' prf'. 
Proof.
  intros. subst. assert(prf=prf'). apply proof_irrelevance. subst. auto.
Qed. 

Theorem raw_replaceOverwrite : forall (T:Type) x (v v':T) H, 
                             raw_replace x v (raw_replace x v' H) = raw_replace x v H. 
Proof. 
  induction H; intros. 
  {auto. }
  {simpl. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl. rewrite <- beq_nat_refl. auto. }
   {simpl. rewrite eq. rewrite IHlist. auto. }
  }
Qed. 

Theorem replaceOverwrite : forall (T:Type) x (v v':T) H,
                             replace x v (replace x v' H) = replace x v H. 
Proof.
  intros. destruct H. simpl in *. eapply rawHeapsEq. apply raw_replaceOverwrite. 
Qed. 

Theorem ltLookup : forall T u x H v, raw_heap_lookup x H = Some v ->
                                       monotonic u T H -> optLT x u = true. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. inversion H1; subst. apply beq_nat_true in eq. subst; auto. }
   {eapply IHlist; eauto. inversion H1; subst. eapply monotonicLowerUB; eauto. }
  }
Qed. 

Theorem raw_lookupReplaceSwitch : forall T x x' (v v':T) H,
                                x<>x' -> raw_replace x v (raw_replace x' v' H) =
                                         raw_replace x' v' (raw_replace x v H).
Proof.
  induction H. 
  {auto. }
  {intros. simpl. destruct a. destruct(beq_nat x' i) eqn:eq1. 
   {destruct(beq_nat x i) eqn:eq2. 
    {apply beq_nat_true in eq1. apply beq_nat_true in eq2. subst. exfalso; apply H0; auto. }
    {simpl. apply beq_nat_false_iff in H0. rewrite H0. rewrite eq1. auto. }
   }
   {destruct (beq_nat x i) eqn:eq2. 
    {simpl. rewrite eq2. apply beq_nat_false_iff in H0. destruct (beq_nat x' x) eqn:eq3; auto. 
     apply beq_nat_true in eq3. subst. apply beq_nat_false in H0. exfalso. apply H0; auto. }
    {simpl. rewrite eq1. rewrite eq2. rewrite IHlist. auto. assumption. }
   }
  }
Qed.  

Theorem lookupReplaceSwitch : forall T x x' (v v':T) H,
                                x<>x' -> replace x v (replace x' v' H) = replace x' v' (replace x v H).
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq. apply raw_lookupReplaceSwitch; auto. 
Qed. 

