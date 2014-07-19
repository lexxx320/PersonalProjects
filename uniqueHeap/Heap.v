Require Export List.
Export ListNotations.
Require Export SpecLib. 
Require Export AST. 
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles. 
Require Import Coq.Sets.Powerset_facts. 

Definition rawHeap (T:Type) := list (id * T). 

Inductive unique (T:Type) (seen:Ensemble id) : rawHeap T -> Prop :=
|consUnique : forall m H v, ~ In id seen m -> unique T (Add id seen m) H ->
                            unique T seen ((m, v)::H)
|nilUnique : unique T seen nil. 

Inductive heap (T:Type) : Type := 
|heap_ : forall h, unique T (Empty_set id) h -> heap T. 

Fixpoint raw_heap_lookup {T : Type} (i : id) (h : rawHeap T) := 
  match h with
    |(n, v)::h' => if beq_nat i n then Some v else raw_heap_lookup i h'
    |nil => None
  end.

Definition heap_lookup {T:Type} (i:id) (h:heap T) :=
  match h with
      |heap_ h prf => raw_heap_lookup i h
  end. 

Definition raw_extend {T : Type} (x:id) v (heap : rawHeap T) := ((x, v)::heap). 
 
Theorem AddUnique : forall T x H S, 
                 raw_heap_lookup x H = None ->
                 unique T S H -> unique T (Add id S x) H. 
Proof.
  induction H; intros. 
  {constructor. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. inv H0. inv H1. 
   constructor. intros c. inv c. contradiction. inv H1. apply beq_nat_false in eq. 
   apply eq. auto. rewrite Add_commutative. apply IHlist; auto. }
Qed. 
  
Theorem extendPreservesUniqueness : forall T h v x prf, 
                             heap_lookup x (heap_ T h prf) = None -> 
                             unique T (Empty_set id) h ->
                             unique T (Empty_set id) (raw_extend x v h). 
Proof.
  induction h; intros. 
  {inv H0. inv H. constructor. intros c. inv c. constructor. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. inv H. inv H0. 
   constructor. intros c. inv c. constructor. intros c. inv c. 
   inv H0. inv H0. apply beq_nat_false in eq. apply eq. auto. 
   rewrite Add_commutative. apply AddUnique; auto. }
Qed. 


Definition getRawHeap {T:Type} (h:heap T) := 
  match h with
      heap_ h p => h
  end. 

Inductive listn : nat -> Type :=
|nNil : listn 0
|nCons : forall n, nat -> listn n -> listn (S n).

Definition lengthn (n:nat) (l:listn n) := n. 

Fixpoint concatN (n:nat) (m:nat) (l1 : listn n) (l2 : listn m) : listn (n + m) :=
  match l1 in listn n return listn (n+m) with
      |nCons n' hd tl => nCons (n'+m) hd (concatN n' m tl l2)
      |nNil => l2
  end. 

Definition trans {T:Type} (h:heap T) :=
  match h as y return (h = y) with
      |heap_ h' prf => (fun H:(h = heap_ T h' prf) => H)
  end.  

(match x as y return (x = y -> _) with
Coq <   | 0 => fun H : x = 0 -> t
Coq <   | S n => fun H : x = S n -> u
Coq <   end) (eq_refl n).

Theorem asdf : forall (T:Type) (x:T), x = x. 
Proof. auto. 
Qed. 

Theorem lookupImpliesRawLookup : forall T x (H:heap T) v, 
                                   heap_lookup x H = v -> 
                                   raw_heap_lookup x (getRawHeap H) = v. 
Proof.
  intros. destruct H. simpl in *. auto. 
Qed. 

Definition extend {T:Type} x v (h : heap T) (p:heap_lookup x h = None) :=
  match h with
      |heap_ h' prf => heap_ T (raw_extend x v h')
             (extendPreservesUniqueness T (getRawHeap h) v x prf (lookupImpliesRawLookup T x h None p) prf)
  end.


Fixpoint raw_replace {T:Type} i v (h : rawHeap T) :=
  match h with
      |(i', v') :: h' => if beq_nat i i' 
                         then (i, v) :: h' 
                         else (i', v') :: raw_replace i v h'
      |nil => nil
  end.

Theorem replacePreservesMonotonicity : forall T h v x u, 
                                         monotonic u T h ->
                                         monotonic u T (raw_replace x v h). 
Proof.
  induction h; intros.
  {simpl. constructor. }
  {inv H. simpl. destruct (beq_nat x m) eqn:eq. 
   {apply beq_nat_true in eq; subst. constructor. auto. assumption. }
   {constructor. auto. apply Hh. auto. }
  }
Qed. 

Definition replace {T:Type} i v (h:heap T) :=
  match h with
      |heap_ h' prf => heap_ T (raw_replace i v h') 
                             (replacePreservesMonotonicity T h' v i None prf)
  end. 

Fixpoint raw_remove {T:Type} (h : rawHeap T) x :=
  match h with
      |(x', v')::h' => if beq_nat x x' then h' else (x', v')::raw_remove h' x
      |nil => nil
  end.

Theorem monotonicLowerUB : forall u u' T h,
                             monotonic (Some u) T h -> optLT u u' = true ->
                             monotonic u' T h. 
Proof.
  induction h; intros. 
  {constructor. }
  {inv H. constructor. simpl in H4. destruct (lt_dec m u). 
   {destruct u'. simpl in H0. destruct (lt_dec u n). simpl. 
    assert(m < n). omega. destruct (lt_dec m n). auto. contradiction. 
    inv H0. auto. }
   {inv H4. }
   auto.
  }
Qed. 

Theorem removePreservesMonotonicity : forall T h x u, 
                                        monotonic u T h ->
                                        monotonic u T (raw_remove h x). 
Proof.
  induction h; intros. 
  {simpl. constructor. }
  {simpl. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H. eapply monotonicLowerUB in H5; eauto. }
   {inv H. constructor. auto. apply IHh; auto. }
  }
Qed. 

Definition remove {T:Type} (h:heap T) x :=
  match h with
    |heap_ h' prf => heap_ T (raw_remove h' x) (removePreservesMonotonicity T h' x None prf)
  end. 

Theorem raw_heapUpdateNeq : forall (T:Type) h i (v v' : T),
                          raw_heap_lookup i h = Some v -> 
                          v <> v' -> h <> raw_replace i v' h. 
Proof.
  intros. intros c. induction h. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat i i0) eqn:eq. 
   {inv H. inv c. apply H0. auto. }
   {inversion c. apply IHh. auto. auto. }
  }
Qed. 

Theorem heapUpdateNeq : forall (T:Type) h i (v v' : T),
                          heap_lookup i h = Some v ->
                          v <> v' -> h <> replace i v' h. 
Proof.
  intros. intros c. destruct h. simpl in *.
  eapply raw_heapUpdateNeq in H; eauto. inversion c. contradiction. 
Qed. 



Theorem raw_HeapLookupReplace : forall (T:Type) x (h:rawHeap T) v v', 
                              raw_heap_lookup x h = Some v' ->
                              raw_heap_lookup x (raw_replace x v h) = Some v. 
Proof.
  intros. induction h. 
  {inversion H. }
  {simpl. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl. rewrite <- beq_nat_refl. reflexivity. }
   {simpl in *.  rewrite eq. rewrite eq in H. apply IHh in H. assumption. }
  }
Qed. 

Theorem HeapLookupReplace : forall (T:Type) x (h:heap T) v v', 
                              heap_lookup x h = Some v' ->
                              heap_lookup x (replace x v h) = Some v. 
Proof.
  intros. destruct h. simpl in *. eapply raw_HeapLookupReplace. eauto. 
Qed. 

Theorem raw_lookupExtend : forall (T:Type) H (v:T) res, 
                             res = raw_extend v H ->
                             raw_heap_lookup (FST res) (SND res) = Some v. 
Proof.
  intros. induction H. 
  {simpl in *. inversion H0; subst. simpl. reflexivity. }
  {destruct a. simpl in *. inversion H0; subst. simpl. rewrite <- beq_nat_refl. 
   reflexivity. }
Qed. 

Theorem lookupExtend : forall (T:Type) x H H' (v:T), (x, H') = extend v H ->
                                                     heap_lookup x H' = Some v. 
Proof.
  destruct H. intros. simpl in *. inv H. eapply raw_lookupExtend. auto. 
Qed. 

Theorem raw_lookupDeterministic : forall (T:Type) x H (v v':option T), 
                                raw_heap_lookup x H = v -> raw_heap_lookup x H = v' -> v = v'. 
Proof.
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

