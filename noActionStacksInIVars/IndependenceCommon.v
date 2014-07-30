Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import SpecLib. 
Require Import sets. 
Require Import unspec. 
Require Import erasure. 
Require Import classifiedStep. 
Require Import AST. 
Require Import Coq.Program.Equality. 
Require Import Heap.
Require Import hetList.


Axiom uniqueTP : forall T1 T2 t, tIn (tUnion T1 T2) t -> tIn T1 t -> tIn T2 t -> False. 

Theorem unionEq : forall T1 T2 T2', tUnion T1 T2 = tUnion T1 T2' -> T2 = T2'.  
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
   assert(tIn (tUnion T1 T2) x). apply Union_intror. auto. copy H. apply H1 in H.
   inversion H; subst. eapply uniqueTP in H0; eauto. inversion H0. auto. }
  {apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
   assert(tIn (tUnion T1 T2') x). apply Union_intror. auto. copy H. apply H2 in H3. 
   inversion H3; subst. eapply uniqueTP in H0; eauto. inversion H0. auto. }
Qed. 

Theorem UnionEqTID : forall T T' tid s1 s2 M s1' s2' M',
                       tUnion T (tSingleton(tid,s1,s2,M)) = tUnion T' (tSingleton(tid,s1',s2',M')) ->
                       T = T' /\ s1 = s1' /\ s2 = s2' /\ M = M'. 
Proof. 
  intros. unfoldSetEq H. assert(tIn (tUnion T (tSingleton(tid,s1,s2,M)))(tid,s1,s2,M)). 
  apply Union_intror. constructor. copy H.  apply H0 in H. inversion H.  
  {assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1,s2,M)). 
   econstructor. econstructor. eauto. auto. 
   assert(thread_lookup (tUnion T' (tSingleton(tid,s1',s2',M'))) tid (tid,s1',s2',M')). 
   econstructor. apply Union_intror. constructor. auto. eapply uniqueThreadPool in H5; eauto. 
   inv H5. repeat constructor; auto. eqSets. 
   {assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H5. apply H0 in H5. 
    inversion H5; subst. auto. inv H8. exfalso. eapply uniqueTP; eauto. constructor. }
   {assert(tIn (tUnion T' (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H5. 
    apply H1 in H5. inversion H5; subst. auto. inv H8. exfalso. eapply uniqueTP; eauto. 
    constructor. }
  }
  {subst. inv H3. repeat constructor; auto. eqSets. 
   {assert(tIn (tUnion T (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H4. apply H0 in H4. 
    inversion H4; subst. auto. inv H6. exfalso. eapply uniqueTP; eauto. constructor. }
   {assert(tIn (tUnion T' (tSingleton(tid,s1,s2,M))) x). constructor. auto. copy H4. 
    apply H1 in H4. inversion H4; subst. auto. inv H6. exfalso. eapply uniqueTP; eauto. 
    constructor. }
  }
Qed. 

Axiom UnionSingletonEq : forall T T' a b, 
                 tUnion T (tSingleton a) = tUnion T' (tSingleton b) -> 
                 tIn T' a -> T = tUnion (Subtract thread T' a) (tSingleton b).

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

Theorem unspecEraseTrm : forall tid s1 s2 M M', 
                          eraseTrm s1 M M' ->
                          unspecThread(tid,unlocked s1,s2,M) (tSingleton(tid,unlocked nil,s2,M')). 
Proof.
  intros. destructLast s1. 
   {inv H; try invertListNeq. auto. }
   {invertHyp. inv H; try solve[invertListNeq]; apply lastElementEq in H1;
   subst; unspecThreadTac; auto. }
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

Theorem subtractSingle : forall X T x1, 
              (Subtract X (Union X (Subtract X T x1) (Singleton X x1)) x1) =
              Subtract X T x1. 
Proof.
  intros. eqSets. 
  {inv H. inv H0. auto. inv H. exfalso. apply H1. constructor. }
  {inv H. constructor. constructor. constructor. auto. auto. auto. }
Qed. 


Theorem specStepFullIVar' : forall x H H' ds TID s1 s2 N S tid M T t' sc,
       spec_step H T (tSingleton(TID,s1,s2,N)) H' T t' ->
       heap_lookup x H = Some (sfull sc ds S tid M) ->
       (heap_lookup x H' = Some (sfull sc ds S tid M) \/
        heap_lookup x H' = Some(sfull sc (TID::ds) S tid M)). 
Proof.
  intros. inv H0; unfoldTac; invertHyp; invThreadEq; eauto. 
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H3 in H1. inv H1. 
    right. erewrite HeapLookupReplace; eauto. }
   {rewrite lookupReplaceNeq. eauto. intros c. subst. apply beq_nat_false in eq. apply eq. 
    auto. }
  }
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H3 in H1. inv H1. }
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
        in copyAs H n; copyAs H' n'; apply specStepSingleton in n; invertHyp;
           unfoldSetEq n'
  end. 
Ltac eqIn H := 
  match type of H with
      |forall x, Ensembles.In ?X (tUnion ?T (tSingleton ?x1)) x -> ?a => 
       let n := fresh 
       in assert(n:Ensembles.In X (tUnion T (tSingleton x1)) x1) by (apply Union_intror; constructor);apply H in n
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
    |H:spec_step ?H ?T ?t (extend ?x ?v ?H ?p) ?T' ?t',H':heap_lookup ?x' ?H = Some ?v',H'':?x'<>?x |- _ => 
     assert(heap_lookup x' (extend x v H p) = Some v') by (apply lookupExtendNeq; eauto)
  end. 

Theorem consedActEq : forall H H' tid s1 s1' a b s2 M M' T T',
                 spec_multistep H T H' T' -> tIn T (tid,unlocked (s1++[a;b]),s2,M) -> 
                 tIn T' (tid,unlocked(s1'++[b]),s2,M') -> exists s, s1' = s ++ [a]. 
Proof.
  intros. genDeps{s1';s1;s2;a;b;M;M';tid}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,unlocked(s1++[a;b]),s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,unlocked(s1'++[b]),s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. destruct s1'. simpl in *. destruct s1; inv H4. 
   destruct s1; inv H5. alignTac a0 s1'. rewrite H in H4. replace [a;b] with ([a]++[b]) in H4; auto. 
   rewrite app_assoc in H4. apply app_inj_tail in H4. invertHyp. apply app_inj_tail in H3. invertHyp. 
   econstructor. rewrite H. eauto. }
  {inv H1. 
   {eapply IHspec_multistep. constructor. eauto. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H3. inv H1. 
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. constructor. eauto. }
    {unfoldTac; invertHyp; invThreadEq. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
    {unfoldTac; invertHyp. inv H5. eapply IHspec_multistep. apply Union_intror. simpl. 
     rewrite app_comm_cons. constructor. eauto. }
   }
  }
Qed. 

Theorem nonEmptyStack : forall s1 a s1' s2 x M M' tid H H' T T' z,
        eraseTrm (s1'++[x]) z M' ->
        spec_multistep H (tUnion T (tSingleton(tid,unlocked [a],s2, M')))
                       H' (tUnion T' (tSingleton(tid,unlocked (s1 ++ [a]),s2,M))) ->
        M <> M' -> s1 <> nil. 
Proof. 
  intros. dependent induction H1.  
  {inv H0; invertListNeq; apply app_inj_tail in H1; invertHyp; apply UnionEqTID in x; 
   invertHyp; inv H; exfalso; apply H2; auto. }
  {copy x. copy H. apply specStepSingleton in H4. invertHyp. unfoldSetEq H3. 
   assert(tIn (tUnion T0 (tSingleton x1)) x1). apply Union_intror. constructor. 
   apply H4 in H3. inv H3. 
   {eapply IHspec_multistep; eauto. apply UnionSingletonEq in x. rewrite x. 
    unfoldTac. rewrite UnionSwap. auto. auto. }
   {inv H6. apply eraseTrmApp in H0. inv H0. 
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H3; falseDecomp. }
     {simpl in *. eapply consedActEq in H1.  Focus 2. apply Union_intror. rewrite app_nil_l. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. introsInv. invertListNeq. }
    }
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H3; falseDecomp. }
     {simpl in *. eapply consedActEq in H1. Focus 2. apply Union_intror. rewrite app_nil_l. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. introsInv. invertListNeq. }
    }
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H3; falseDecomp. }
     {simpl in *. eapply consedActEq in H1. Focus 2. apply Union_intror. rewrite app_nil_l. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. introsInv. invertListNeq. }
    }
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H3; falseDecomp. }
     {simpl in *. eapply consedActEq in H1. Focus 2. apply Union_intror. rewrite app_nil_l. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. introsInv. invertListNeq. }
    }
    {inv H; unfoldTac; invertHyp; invThreadEq; try solve[falseDecomp]. 
     {inv H3; falseDecomp. }
     {simpl in *. eapply consedActEq in H1. Focus 2. apply Union_intror. rewrite app_nil_l. 
      constructor. Focus 2. apply Union_intror. constructor. invertHyp. introsInv. invertListNeq. }
    }
   }
  }
Qed. 


Theorem numForksDistribute : forall a b, numForks'(a++b) = plus(numForks' a) (numForks' b). 
Proof.
  induction a; intros. 
  {auto. }
  {simpl. destruct a; auto. rewrite IHa. auto. }
Qed. 
