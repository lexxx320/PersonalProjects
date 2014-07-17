Require Export List.
Export ListNotations.
Require Export SpecLib. 
Require Export AST. 
Require Import Coq.Logic.ProofIrrelevance.

Definition rawHeap (T:Type) := list (id * T). 

Definition optLT (n:nat) (m:option nat) :=
  match m with
      |Some m' => if lt_dec n m' then true else false
      |None => true
  end. 

Inductive monotonic (n:option nat) (T:Type) : rawHeap T -> Prop :=
|consMono : forall m H v, optLT m n = true -> monotonic (Some m) T H ->
                          monotonic n T ((m, v)::H)
|nilMono : monotonic n T nil. 

Inductive heap (T:Type) : Type := 
|heap_ : forall h, monotonic None T h -> heap T. 

Fixpoint raw_heap_lookup {T : Type} (i : id) (h : rawHeap T) := 
  match h with
    |(n, v)::h' => if beq_nat i n then Some v else raw_heap_lookup i h'
    |nil => None
  end.

Definition heap_lookup {T:Type} (i:id) (h:heap T) :=
  match h with
      |heap_ h prf => raw_heap_lookup i h
  end. 

Definition raw_extend {T : Type} v (heap : rawHeap T) := 
  match heap with
    |(n, v') :: h' => (S n, (S n, v) :: (n, v') :: h')
    |nil => (1, (1, v) :: nil)
  end.

Definition FST {T1 T2:Type} (p:T1 * T2) := match p with (x, _) => x end. 
Definition SND {T1 T2:Type} (p:T1 * T2) := match p with (_, x) => x end. 

Theorem extendPreservesMonotonicity : forall T h v, 
                                        monotonic None T h ->
                                        monotonic None T (SND (raw_extend v h)). 
Proof.
  induction h; intros. 
  {simpl in *. inv H. constructor. auto. constructor. }
  {simpl in *. destruct a. inv H. constructor. auto. 
   constructor. simpl. assert(i < S i) by apply lt_n_Sn. destruct (lt_dec i (S i)). 
   auto. contradiction. auto. }
Qed. 

Definition extend {T:Type} v (h : heap T) :=
  match h with
      |heap_ h prf => let res := raw_extend v h
                      in (FST res, heap_ T (SND res) (extendPreservesMonotonicity T h v prf))
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
   {constructor. auto. apply IHh. auto. }
  }
Qed. 

Definition replace {T:Type} i v (h:heap T) :=
  match h with
      |heap_ h' prf => heap_ T (raw_replace i v h') (replacePreservesMonotonicity T h' v i None prf)
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

