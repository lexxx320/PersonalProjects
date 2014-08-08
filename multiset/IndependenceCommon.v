Require Import erasure. 

Axiom uniqueTP : forall T1 T2 t, tIn (tUnion T1 T2) t -> tIn T1 t -> tIn T2 t -> False. 

Theorem UnionEqTID : forall T T' tid s1 s2 M s1' s2' M',
                       tUnion T (tSingleton(tid,s1,s2,M)) = tUnion T' (tSingleton(tid,s1',s2',M')) ->
                       T = T' /\ s1 = s1' /\ s2 = s2' /\ M = M'. 
Proof. 
  intros.
  assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1,s2,M)). 
  econstructor. rewrite <- H. unfoldTac; invUnion. right. simpl; auto. 
  auto. assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1',s2',M')). 
  econstructor; auto. unfoldTac; invUnion. right; simpl; auto. 
  eapply uniqueThreadPool in H0; eauto. inv H0. apply UnionEqL in H. subst; auto. 
Qed. 




Theorem UnionSingletonEq : forall T T' a b, 
                 tUnion T (tSingleton a) = tUnion T' (tSingleton b) -> 
                 tIn T' a -> T = tUnion (Subtract T' a) (tSingleton b).
Proof.
  intros. unfoldTac. apply pullOut in H0. rewrite H0 in H. 
  rewrite <- Union_associative in H.
  rewrite (Union_commutative thread (Single a)) in H. rewrite Union_associative in H. 
  apply UnionEqL in H. auto. 
Qed. 

Ltac proveUnionEq H := apply UnionSingletonEq in H;[rewrite H; unfoldTac; rewrite UnionSwap; auto|idtac]; auto.
Theorem neqSym : forall (T:Type) (x y : T), x <> y <-> y <> x. 
  intros. split; intros. intros c; subst. apply H; auto. 
  intros c; subst; apply H; auto. 
Qed. 

Inductive eraseTrm : list action -> trm -> trm -> Prop :=
|eraseTrmNil : forall M, eraseTrm nil M M
|eraseTrmRead : forall x t E d s M, eraseTrm (s++[rAct x t E d]) M t
|eraseTrmWrite : forall x t E M d N s, eraseTrm (s++[wAct x t E M d]) N t
|eraseTrmNew : forall x t E d s M, eraseTrm (s++[nAct t E d x]) M t
|eraseTrmFork : forall t E M d N s n, eraseTrm (s++[fAct t E M d n]) N t
|eraseTrmSR : forall t E M N d M' s, eraseTrm (s++[srAct t E M N d]) M' t. 

Theorem getLastApp : forall (T:Type) a c (b:T),
                       last(a++[b]) c = b.
Proof.
  induction a; intros. 
  {simpl. auto. }
  {simpl. destruct (a0++[b]) eqn:eq. 
   {invertListNeq. }
   {rewrite <- eq. eauto. }
  }
Qed. 

Theorem unspecLastAct : forall tid s a s2 M' M, 
                         actionTerm a M' ->
                         unspecThread(tid,unlocked(s++[a]),s2,M) = tSingleton (tid,unlocked nil,s2,M'). 
Proof.
  induction s; intros. 
  {simpl. inv H; auto. }
  {simpl. destruct (s++[a0])eqn:eq. 
   {invertListNeq. }
   {rewrite <- eq. rewrite getLastApp. inv H; auto. }
  }
Qed. 

Theorem unspecEraseTrm : forall tid s1 s2 M M', 
                          eraseTrm s1 M M' ->
                          unspecThread(tid,unlocked s1,s2,M) = (tSingleton(tid,unlocked nil,s2,M')). 
Proof.
  intros. destructLast s1. 
   {inv H; try invertListNeq. auto. }
   {invertHyp. inv H; try solve[invertListNeq]; apply lastElementEq in H1;
               subst; erewrite unspecLastAct; eauto; constructor. }
Qed. 
 
Theorem eEraseTrm : forall s1 M, exists M', eraseTrm s1 M M'. 
  intros. destructLast s1. 
  {econstructor. econstructor. }
  {invertHyp. destruct x; econstructor; econstructor. }
Qed. 
Theorem eraseTrmApp : forall x a M M', 
                        eraseTrm (x ++ [a]) M M' -> actionTerm a M'. 
Proof.
  intros. inv H; try solve[apply lastElementEq in H1; subst; constructor].
  invertListNeq. 
Qed. 
Ltac eraseTrmTac s1 M := assert(exists M', eraseTrm s1 M M') by apply eEraseTrm; invertHyp.  
Theorem EqJMeq : forall (T:Type) (x y:T), x = y -> JMeq x y.
Proof.
  intros. subst. auto. Qed. 

Ltac copyAs H n := 
  match type of H with
      |?x => assert(n:x) by auto
  end.
Ltac falseDecomp :=
  match goal with
      |H:decompose ?M ?E ?e,H':decompose ?M ?E' ?e' |- _ => 
       let n := fresh
       in let n' := fresh
          in copyAs H n; copyAs H' n'; eapply uniqueCtxtDecomp in n; eauto; inversion n as [F1 F2];
             inv F2
  end. 

Theorem specStepFullIVar' : forall x H H' ds TID s1 s2 N S tid M T t' sc,
       spec_step H T (tSingleton(TID,s1,s2,N)) H' T t' ->
       heap_lookup x H = Some (sfull sc ds S tid M) ->
       (heap_lookup x H' = Some (sfull sc ds S tid M) \/
        heap_lookup x H' = Some(sfull sc (TID::ds) S tid M)). 
Proof.
  intros. inv H0; eauto. 
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H11 in H1. inv H1. 
    right. erewrite HeapLookupReplace; eauto. }
   {rewrite lookupReplaceNeq. eauto. intros c. subst. apply beq_nat_false in eq. apply eq. 
    auto. }
  }
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. heapsDisagree. }
   {apply beq_nat_false in eq. rewrite lookupReplaceNeq; auto. }
  }
  {destruct H; simpl in *. destruct h. 
   {inv H1. } 
   {assert(x<>x0). intros c. subst. rewrite p in H1. inv H1. 
    rewrite <- beq_nat_false_iff in H. rewrite H. left; eauto. }
  }
Qed.

Ltac startIndCase :=
  match goal with
    |H:spec_step ?a ?b ?c ?d ?e ?f,H':tUnion ?T ?t = tUnion ?T' ?t' |- _ =>
     let n := fresh
     in let n' := fresh
        in copyAs H n; copyAs H' n'; apply specStepSingleton in n; invertHyp
  end. 

Ltac takeTStep :=
  match goal with
      |H:Ensembles.In thread ?T ?t |- _ => apply pullOut in H; rewrite H; unfoldTac; rewrite UnionSwap;
                                 econstructor;[eapply specStepChangeUnused; eassumption|idtac];
                                 unfoldTac; rewrite <- UnionSwap
      |H:Ensembles.In thread ?T ?t |- _ => apply pullOut in H; rewrite H; unfoldTac; rewrite UnionSwap;
                                 econstructor
      |H:Ensembles.In thread ?T ?t |- _ => apply pullOut in H; rewrite H; 
                                 econstructor;[eapply specStepChangeUnused; eassumption|idtac]
  end.

Ltac lookupTac :=
  match goal with
    |H:spec_step ?H ?T ?t (replace ?x ?v ?H) ?T' ?t',H':heap_lookup ?x' ?H = Some ?v',H'':?x'<>?x |- _ =>
     assert(heap_lookup x' (replace x v H) = Some v') by (rewrite lookupReplaceNeq; auto)
    |H:spec_step ?H ?T ?t (replace ?x ?v ?H) ?T' ?t',H':heap_lookup ?x ?H = Some ?v' |- _ =>
     assert(heap_lookup x (replace x v H) = Some v) by (erewrite HeapLookupReplace; eauto)                             
    |H:spec_step ?H ?T ?t (Heap.extend ?x ?v ?H ?p) ?T' ?t',H':heap_lookup ?x' ?H = Some ?v',H'':?x'<>?x |- _ => 
     assert(heap_lookup x' (Heap.extend x v H p) = Some v') by (apply lookupExtendNeq; eauto)
  end. 


Ltac destructThread x :=
     let n1 := fresh in
     let n2 := fresh in 
     destruct x as [n1 n2];
       let n3 := fresh in
       let n4 := fresh in
       destruct n1 as [n3 n4];
         let n5 := fresh in
         let n6 := fresh in 
         destruct n3 as [n5 n6]. 

Ltac nonEmptyStackTac H :=
  eapply nonEmptyStack in H;unfoldTac; [idtac|solveSet|solveSet|rewrite app_nil_l; simpl;auto|
                                        simpl;auto].

Theorem UnionNeqTID : forall T T' tid tid' s1 s2 s1' s2' M M',
       tUnion T (tSingleton (tid, s1, s2, M)) =
       tUnion T' (tSingleton (tid', s1', s2', M')) -> tid <> tid' ->
       T = tUnion (Subtract T' (tid,s1,s2,M)) (tSingleton(tid',s1',s2',M')) /\
       T' = tUnion (Subtract T (tid',s1',s2',M')) (tSingleton(tid,s1,s2,M)).
Proof.
  intros. assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) (tid',s1',s2',M')). 
  rewrite H. unfoldTac; invUnion. right; simpl; auto. 
  assert(tIn (tUnion T' (tSingleton(tid',s1',s2',M'))) (tid,s1,s2,M)). 
  rewrite <- H. unfoldTac. repeat invUnion. right. simpl; auto. unfoldTac. 
  repeat invUnion. inv H1; inv H2. 
  {split. apply UnionSingletonEq in H; auto. symmetry in H. 
   apply UnionSingletonEq in H; auto. }
  {inv H1. invThreadEq. exfalso. apply H0. auto. inv H2. }
  {inv H3; try contradiction. invThreadEq. exfalso. apply H0; auto. }
  {inv H1; try contradiction. invThreadEq. exfalso. apply H0; auto. }
Qed. 

Theorem stackNonNil : forall s1 a s1' s2 x M M' tid H H' T T' z,
        eraseTrm (s1'++[x]) z M' ->
        spec_multistep H (tUnion T (tSingleton(tid,unlocked [a],s2, M')))
                       H' (tUnion T' (tSingleton(tid,unlocked (s1 ++ [a]),s2,M))) ->
        M <> M' -> s1 <> nil. 
Proof. 
  intros. dependent induction H1.  
  {inv H0; invertListNeq; apply app_inj_tail in H1; invertHyp; apply UnionEqTID in x; 
   invertHyp; inv H; exfalso; apply H2; auto. }
  {copy x. copy H. apply specStepSingleton in H4. invertHyp. destructThread x1. 
   exMid tid H8. 
   {apply UnionEqTID in H3. invertHyp. apply eraseTrmApp in H0. inv H. 
    {inv H0; inv H13; falseDecomp. }
    {inv H0; clear d1; try solve[falseDecomp]. copy d. copy d0. 
     eapply uniqueCtxtDecomp in H; eauto. invertHyp. nonEmptyStackTac H1.
     invertHyp. introsInv. invertListNeq. }
    {inv H0; clear d1; try solve[falseDecomp]. copy d. copy d0. 
     eapply uniqueCtxtDecomp in H; eauto. invertHyp. nonEmptyStackTac H1.
     invertHyp. introsInv. invertListNeq. }
    {inv H0; clear d1; try solve[falseDecomp]. copy d. copy d0. 
     eapply uniqueCtxtDecomp in H; eauto. invertHyp. nonEmptyStackTac H1.
     invertHyp. introsInv. invertListNeq. }
    {inv H0; clear d1; try solve[falseDecomp]. copy d. copy d0. 
     eapply uniqueCtxtDecomp in H; eauto. invertHyp. nonEmptyStackTac H1.
     invertHyp. introsInv. invertListNeq. }
    {inv H0; clear d1; try solve[falseDecomp]. copy d. copy d0. 
     eapply uniqueCtxtDecomp in H; eauto. invertHyp. nonEmptyStackTac H1.
     invertHyp. introsInv. invertListNeq. }
   }
   {apply UnionNeqTID in H3; auto. invertHyp. eapply IHspec_multistep. 
    eauto. Focus 2. auto. rewrite H4. unfoldTac. rewrite UnionSwap. eauto. auto. }
  }
Qed. 

Theorem numForksDistribute : forall a b, numForks'(a++b) = plus(numForks' a) (numForks' b). 
Proof.
  induction a; intros. 
  {auto. }
  {simpl. destruct a; auto. rewrite IHa. auto. }
Qed. 

Ltac proofsEq p p' := assert(p = p') by apply proof_irrelevance; subst. 
Ltac consedActTac H :=
  eapply consedActEq in H;[idtac|solveSet|solveSet].


Ltac varsEq a b := let n := fresh 
                    in destruct (beq_nat a b) eqn:n;[apply beq_nat_true in n; subst|apply beq_nat_false in n]. 

Theorem UnionSingletonCoupleEq : forall T T' a b c, 
                 tUnion T (tSingleton a) = tUnion T' (tCouple b c) -> 
                  tIn T' a -> T = tUnion (Subtract T' a) (tCouple b c).
Proof. 
  intros. unfoldTac. apply pullOut in H0. rewrite H0 in H. 
  rewrite <- Union_associative in H. rewrite (Union_commutative thread (Single a)) in H. 
  rewrite Union_associative in H. apply UnionEqL in H. auto. 
Qed. 


