Require Import erasure. 
Require Import IndependenceCommon. 
Require Import eraseRollbackIdempotent. 
Require Import NonSpecPureStep. 

Hint Constructors actionTerm. 

Fixpoint commitPool' (T:pool) :=
  match T with
      |(tid,unlocked nil,s2,M)::ts => commitPool' ts
      |(tid, specStack nil N, s2, M)::ts => commitPool' ts
      |nil => True
      |_ => False
  end. 
Ltac solveSet := 
  unfoldTac; simpl;
  match goal with
      | |- In ?X (Union ?X ?T1 ?T2) ?x => invUnion;try solve[left; solveSet|right;solveSet]
      | |- List.In ?x (Union ?X ?T1 ?T2) => invUnion;try solve[left; solveSet|right;solveSet]
      | |- ?a \/ ?b => try solve[left; solveSet|right; solveSet]
      |_ => eauto
  end. 

Theorem unspecUnspecPool : forall T, unspecPool(unspecPool T) = unspecPool T. 
Proof.
  induction T; auto. simpl. rewrite unspecUnionComm. rewrite IHT. 
  destructThread a. destruct H4; auto. destructLast l; auto. invertHyp. 
  assert(exists M, actionTerm x M). destruct x; repeat econstructor. 
  invertHyp. erewrite unspecLastAct; eauto. 
Qed. 
 
Theorem unspecCons : forall t T, unspecPool (t::T) = tUnion (unspecThread t) (unspecPool T). 
Proof. 
  reflexivity. 
Qed. 

Theorem unspecLength : forall T t, 
                 t++T = unspecPool T -> length t = 0. 
Proof.
  induction T; intros. 
  {rewrite app_nil_r in H. inv H. simpl. auto. }
  {destructThread a. destruct H5. 
   {simpl in *. 
    replace (t++(H4, locked l, H3, H1) :: T) with ((t++[(H4, locked l, H3, H1)])++T) in H.
    Focus 2. rewrite <- app_assoc. simpl. auto. apply IHT in H. rewrite app_length in H. 
    simpl in *. omega. }
   {destructLast l. 
    {simpl in *.
     replace (t ++ (H4, unlocked [], H3, H1) :: T) with ((t ++ [(H4, unlocked [], H3, H1)])++ T ) in H. 
     rewrite (Union_commutative thread t) in H. unfold Union in H. simpl in H. inversion H. 
     eapply IHT in H2. auto. rewrite <- app_assoc. auto. }
    {invertHyp. assert(exists M, actionTerm x M). destruct x; repeat econstructor. 
     invertHyp. rewrite unspecCons in H. erewrite unspecLastAct in H. simpl in *.
     replace (t ++ (H4, unlocked (x0 ++ [x]), H3, H1) :: T) with
     ((t ++ [(H4, unlocked (x0 ++ [x]), H3, H1)])++T) in H. 
     rewrite (Union_commutative thread t) in H. unfold Union in H. simpl in H. inversion H. 
     invertListNeq. rewrite <- app_assoc; auto. eauto. }
   }
   {simpl in *. 
    replace (t ++ (H4, specStack l t0, H3, H1) :: T) with ((t ++ [(H4, specStack l t0, H3, H1)])++T) in H. 
    rewrite (Union_commutative thread t) in H. simpl in *. inversion H. subst. inversion H. 
    eapply IHT in H1; eauto. rewrite <- app_assoc. auto. }
  }
Qed. 

Theorem eqUnspec : forall T, T = unspecPool T -> commitPool' T. 
Proof. 
  induction T; intros.  
  {unfold commitPool'. auto. }
  {destructThread a. destruct H5.
   {copy H. simpl in *. 
    replace ((H4, locked l, H3, H1) :: T) with ([(H4, locked l, H3, H1)]++T) in H0. 
    apply unspecLength in H0. simpl in *. inv H0. simpl. auto. }
   {destructLast l.
    {simpl in *. apply IHT. inversion H. rewrite unspecUnspecPool. auto. }
    {invertHyp. assert(exists M, actionTerm x M). destruct x; repeat econstructor. 
     invertHyp. rewrite unspecCons in H. erewrite unspecLastAct in H; eauto. 
     unfold tUnion in H. simpl in H. inversion H. invertListNeq. }
   }
   {simpl in H. inversion H. simpl. rewrite <- H6. apply IHT. auto. }
  }
Qed. 

Theorem eraseTrmConsSame : forall a l M' M'' N,
                             actionTerm a M' -> 
                             eraseTrm l M' M'' -> eraseTrm (a::l) N M''. 
Proof.
  intros. destructLast l. 
  {rewrite <- (app_nil_l [a]). inv H; inv H0; try invertListNeq; constructor. }
  {invertHyp. destruct x; inv H0; try solve[invertListNeq]; apply lastElementEq in H2; 
   try solveByInv; inv H2; rewrite app_comm_cons; constructor. }
Qed. 

Inductive spec_multistep_rev : sHeap -> pool -> sHeap -> pool -> Prop :=
    smulti_refl_r : forall (h : sHeap) (p2 : pool), spec_multistep_rev h p2 h p2
  | smulti_step_r : forall (T T' t' t'' : pool) (h h' h'' : sHeap),
                  spec_multistep_rev h T h' (tUnion T' t') ->
                  spec_step h' T' t' h'' T' t'' ->
                  spec_multistep_rev h T h'' (tUnion T' t''). 

Theorem spec_multi_rev_trans : forall H T H' T' H'' T'',
                              spec_multistep_rev H T H' T' ->
                              spec_multistep_rev H' T' H'' T'' ->
                              spec_multistep_rev H T H'' T''.
Proof. 
  intros. induction H1. 
  {auto. } 
  {econstructor. Focus 2. eassumption. eapply IHspec_multistep_rev. eauto. }
Qed. 

Theorem smultiSmultiRevEq : forall H T H' T',
                            spec_multistep H T H' T' <-> spec_multistep_rev H T H' T'. 
Proof.
  intros. split; intros. 
  {induction H0. 
   {constructor. }
   {eapply spec_multi_rev_trans. eapply smulti_step_r. Focus 2. eauto. constructor. 
    eauto. }
  }
  {induction H0. 
   {constructor. }
   {eapply spec_multi_trans. eassumption. econstructor; eauto. 
    constructor. }
  }
Qed. 

Theorem specStepCouple : forall H tid s1 s2 M H' T t',
     spec_step H T (tSingleton(tid,s1,s2,M)) H' T t' ->
     (exists s1' M', t' = tSingleton(tid,s1',s2,M')) \/
     (exists n N s1' M',t' = tCouple(tid,s1',s2,M') (n::tid,locked nil,nil,N)). 
Proof.
  intros. inv H0; eauto. 
  {right. repeat econstructor. }
  {right. repeat econstructor. }
Qed. 

Ltac cleanup := 
  match goal with
      |H:?x = ?x |- _ => clear H; try cleanup
  end.  

Ltac takeTStepRev :=
  match goal with
  | H:Ensembles.In thread ?T ?t
    |- _ =>
        apply pullOut in H; rewrite H; unfoldTac; rewrite UnionSwap;
         econstructor
  end.

Theorem aConsEq : forall a b c d, aCons a b = aCons c d -> a = c /\ b = d. 
Proof.
  intros. destruct b; destruct d; simpl in *; inv H; auto.
Qed. 

Theorem eraseTrmConsSame'' : forall a M' N s1 s2 tid,
                             actionTerm a M' -> 
                             unspecPool(tSingleton(tid,unlocked s1,s2,M')) = 
                             unspecPool(tSingleton(tid,aCons a (unlocked s1),s2,N)). 
Proof.
  induction s1; intros. 
  {simpl. inv H; auto.  }
  {simpl. destruct s1. auto. erewrite getLastNonEmpty; eauto. }
Qed. 

Theorem eraseTrmConsSame' : forall a M' N s1 s2 tid,
                             actionTerm a M' -> 
                             unspecPool(tSingleton(tid,s1,s2,M')) = 
                             unspecPool(tSingleton(tid,aCons a s1,s2,N)). 
Proof.
  intros. destruct s1; auto. apply eraseTrmConsSame''. auto. 
Qed. 

Theorem unspecSpecSame : forall M' N s1 s2 tid,
                           Spec s1 -> 
                           unspecPool(tSingleton(tid,s1,s2,M')) = 
                           unspecPool(tSingleton(tid,s1,s2,N)). 
Proof.
  induction s1; auto; intros. 
  {simpl. inv H; auto. }
Qed. 

Theorem specStepExistsIn : forall H T t H' t',
                             spec_step H T t H' T t' ->
                             exists x, tIn t' x. 
Proof.
  intros. inv H0; repeat econstructor. 
Qed. 

Ltac stacksNeq := 
  match goal with
      |H:aCons ?a ?b = aCons ?c ?d |- _ => 
       let n1 := fresh
       in let n2 := fresh
          in apply aConsEq in H; inversion H as [n1 n2]; inv n1
  end.

Theorem UnionEqR' : forall (U:Type) (T T1 T2:multiset U), T1 = T2 -> Union U T T1 = Union U T T2. 
Proof.
  intros. subst; auto. 
Qed. 

Theorem UnionEqL' : forall U (T T1 T2:multiset U), T1 = T2 -> Union U T1 T = Union U T2 T. 
Proof.
  intros. subst; auto. 
Qed. 

Theorem specStepUnspecEq : forall H T t H' t',
                             spec_step H T t H' T t' ->
                             unspecPool(tUnion T t') = unspecPool (tUnion T t). 
Proof.
  intros. rewrite unspecUnionComm. apply unspecSpecStep in H0. invertHyp. rewrite H2.
  rewrite unspecUnionComm. reflexivity. 
Qed. 

Ltac unspecsEq :=
  solve[erewrite specStepUnspecEq; eauto|rewrite UnionSwap; erewrite specStepUnspecEq; eauto].

Ltac rewriteUnspec :=
  match goal with
      | |- spec_multistep_rev ?h (unspecPool ?T) ?h' ?T' =>
        let n := fresh 
        in (assert(n:unspecPool T = unspecPool T') by unspecsEq); rewrite n
      | |- spec_multistep_rev ?h (unspecPool ?T) ?h' ?T' =>
        let n := fresh 
        in assert(n:unspecPool T = unspecPool T')  
  end.

Theorem tUnionSwap :forall T1 T2 T3, Union thread (Union thread T1 T2) T3 = tUnion (tUnion T1 T3) T2.
Proof. 
  intros. unfoldTac. apply UnionSwap. 
Qed. 

Ltac rewriteSolveSet :=
  match goal with
      |H:?T = ?x |- In ?X ?T ?z => rewrite H; solveSet
  end.

Theorem unspecEmpty : forall tid s1 s2 M, 
                unspecPool(tSingleton(tid,locked s1,s2,M)) = (Empty_set thread).
Proof.
  intros. simpl. auto. 
Qed. 

Ltac unspecsEq' :=
  match goal with
      |H:?T = ?x |- unspecPool(Union ?X ?T ?t') ~= ?z =>
       rewrite H; rewrite UnionSwap; rewrite subtractUnion;[rewrite UnionSwap;rewrite subtractUnion;
                                                            [idtac|rewriteSolveSet]|rewriteSolveSet];
       repeat rewrite unspecUnionComm;erewrite <- eraseTrmConsSame';[eauto|constructor]
      |H:?T = ?x |- unspecPool(Union ?X ?T ?t') ~= ?z => 
       rewrite UnionSwap; rewrite subtractUnion;[idtac|rewriteSolveSet]; rewrite H;
       rewrite UnionSwap; rewrite subtractUnion;[idtac|rewriteSolveSet]; rewrite coupleUnion;
       repeat rewrite unspecUnionComm; rewrite unspecEmpty; unfoldTac; rewrite union_empty_r;
       erewrite <- eraseTrmConsSame'; eauto
      |H:?T = ?x |- unspecPool(Union ?X ?T ?t') ~= ?z =>
       rewrite H; rewrite UnionSwap; rewrite subtractUnion;[rewrite UnionSwap;rewrite subtractUnion;
                                                            [idtac|rewriteSolveSet]|rewriteSolveSet];
       repeat rewrite unspecUnionComm
  end. 

Theorem passThroughWrite : forall M M' T s1 sc s2 H H' tid x E N' d,
        heap_lookup x H' = Some (sfull sc [] SPEC tid N') -> 
        spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,aCons (wAct x M' E N' d) s1,s2,M))))
                       H' (tUnion T(tSingleton(tid,aCons (wAct x M' E N' d) s1,s2,M))) ->
          spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,s1,s2,M'))))
                             (replace x (sempty sc) H') (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H1. 
  {symmetry in x. apply eqUnspec in x. unfoldTac. rewrite Union_commutative in x.
   destruct s1; simpl in *; contradiction. }
  {inv H. 
   {exMid tid tid0. 
    {apply UnionEqTID in x. invertHyp. eapply IHspec_multistep_rev. eauto. 
     Focus 3. auto. Focus 2. auto. repeat rewrite unspecUnionComm. 
     erewrite unspecSpecSame; eauto. }
    {apply UnionNeqTID in x;auto. invertHyp. takeTStep. econstructor. Focus 2. 
     eapply SBasicStep; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap.  
     eapply IHspec_multistep_rev; eauto. unspecsEq'. erewrite unspecSpecSame; eauto.
     rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet. }
   }
   {exMid tid tid0. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. 
     stacksNeq. }
    {exMid (plus(numForks b) (numForks' s0)::tid0) tid. 
     {unfoldTac; rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct s1; simpl in *; inv H. }
     {symmetry in x. apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. 
      econstructor. Focus 2. eapply SFork; auto. rewriteUnspec. unfoldTac. 
      rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq'. rewrite UnionSwap. 
      rewrite subtractUnion. auto. rewriteSolveSet. intros c. invertListNeq. }
    }
   }
   {exMid TID tid. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. }
    {varsEq x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0. 
     apply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2.
     eapply SGet with(h:=replace x0 (sempty sc) h'); eauto.
     rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. 
     rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto.
     rewrite lookupReplaceNeq in H0; auto. eauto. unspecsEq'. rewrite UnionSwap. 
     rewrite subtractUnion. eauto. rewriteSolveSet. }
   }
   {exMid TID tid. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. erewrite HeapLookupReplace in H0; eauto. 
     inv H0. rewrite replaceOverwrite. rewrite unspecUnionComm in *. rewrite replaceSame; eauto. 
     erewrite <- eraseTrmConsSame' in H1; eauto. }
    {exMid x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0. exfalso. apply H3; auto. 
     apply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
     eapply SPut with (h:=replace x0 (sempty sc) h'); eauto. rewrite lookupReplaceNeq; eauto. 
     rewrite lookupReplaceSwitch ;eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. rewrite lookupReplaceNeq in H0; eauto. unspecsEq'.
     rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet. }
   }
   {exMid tid tid0. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid x1 x0. erewrite lookupExtend in H0. inv H0. eapply UnionNeqTID in x; auto. 
     invertHyp. takeTStep. econstructor. Focus 2.
     eapply SNew with (h:=replace x0 (sempty sc) h'); eauto. erewrite extendReplaceSwitch; eauto. 
     erewrite lookupExtendNeq in H0; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. erewrite lookupExtendNeq in H0; eauto. unspecsEq'. 
     rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet. }
   }
   {unfoldTac. exMid tid tid0. 
    {rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid tid (2::tid0). 
     {rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. destruct s1; inv H. }
     {symmetry in x. apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. 
      econstructor. Focus 2. eapply SSpec; eauto. rewriteUnspec. unfoldTac. 
      rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq'. rewrite UnionSwap. 
      rewrite subtractUnion. auto. rewriteSolveSet. intros c. invertListNeq. }
    }
   }
  }
  Grab Existential Variables. auto. eauto. rewrite lookupReplaceNeq; eauto. auto. 
  auto. 
Qed. 

Theorem lookupRemoveNeq : forall (T:Type) x x' H (v:option T),
                            x <> x' -> heap_lookup x H = v ->
                            heap_lookup x (Heap.remove H x') = v.
Proof.
  destruct H. induction h; intros. 
  {simpl in *. auto. }
  {simpl in *. destruct a. destruct (beq_nat x' i) eqn:eq. 
   {destruct (beq_nat x i) eqn:eq2.
    {apply beq_nat_true in eq. apply beq_nat_true in eq2. subst. 
     exfalso. apply H; auto. }
    {auto. }
   }
   {destruct (beq_nat x i) eqn:eq2. 
    {simpl. rewrite eq2. auto. }
    {simpl. rewrite eq2. eapply IHh; eauto. inv u. eapply uniqueSubset; eauto. 
     constructor. inv H0. }
   }
  }
Qed. 

Theorem raw_removeReplaceSwitch : forall (T:Type) x x' H (v:T),
                                x<>x' -> raw_remove (raw_replace x v H) x' = raw_replace x v (raw_remove H x'). 
Proof.
  induction H; intros. 
  {auto. }
  {simpl. destruct a. destruct (beq_nat x i) eqn:eq1. 
   {destruct (beq_nat x' i) eqn:eq2. 
    {simpl. apply beq_nat_true in eq1. apply beq_nat_true in eq2. subst. exfalso. 
     apply H0; auto. }
    {simpl. apply beq_nat_true in eq1. subst. rewrite eq2. rewrite <- beq_nat_refl. 
     auto. }
   }
   {simpl. destruct (beq_nat x' i) eqn:eq2; auto. simpl. rewrite eq1. erewrite IHlist; eauto. }
  }
Qed. 

Theorem removeReplaceSwitch : forall (T:Type) x x' H (v:T),
                                x<>x' -> Heap.remove (Heap.replace x v H) x' =
                                         Heap.replace x v (Heap.remove H x'). 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. eapply raw_removeReplaceSwitch; eauto. 
Qed. 

Theorem removeExtendSwitch : forall (T:Type) x x' H (v:T) p p',
                               x<>x' -> Heap.remove (Heap.extend x v H p) x' = 
                                        Heap.extend x v (Heap.remove H x') p'. 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. apply neqSym in H0. 
  apply beq_nat_false_iff in H0. rewrite H0. unfold raw_extend. auto.
Qed. 

Theorem removeExtend : forall (T:Type) H x (v:T) p,
                         Heap.remove(Heap.extend x v H p) x = H.
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. rewrite <- beq_nat_refl. auto. 
Qed. 

Definition Included (A:Type) T1 T2 := forall (x:A), In A T1 x -> In A T2 x. 
 
Theorem subtractUnspec : forall T t t',
                           tIn T t ->
                           unspecThread t = unspecThread t' ->
                           tUnion (unspecPool (Subtract thread T t)) (unspecPool(tSingleton t')) = unspecPool T.
Proof.
  induction T; intros. 
  {inv H. }
  {simpl in *. destruct (classicT(a=t)). 
   {unfoldTac. rewrite union_empty_r. subst. rewrite H0.
    rewrite Union_commutative. auto. }
   {inv H. exfalso. apply n; auto. simpl. unfoldTac. rewrite union_empty_r.  
    erewrite <- IHT. Focus 2. eauto. Focus 2. eauto. rewrite union_empty_r. 
    rewrite Union_associative. auto. }
  }
Qed. 

Theorem SubExpand : forall (A:Type) T (x:A) T',
                      In A T x -> Union A (Subtract A T x) T' = Subtract A (Union A T T') x. 
Proof.
  induction T; intros. 
  {inv H. }
  {inv H. 
   {simpl. destruct (classicT (x=x)). 
    {auto. }
    {exfalso. apply n; auto. }
   }
   {simpl. destruct (classicT (a=x)). 
    {auto. } 
    {simpl. rewrite IHT; auto. }
   }
  }
Qed. 

Theorem SubSwitch : forall (A:Type) T (x x':A), 
                      Subtract A (Subtract A T x) x' = Subtract A (Subtract A T x') x. 
Proof.
  induction T; intros. 
  {simpl. auto. }
  {simpl. destruct (classicT (a=x)); destruct (classicT (a=x')). 
   {subst. rewrite e0. auto. }
   {simpl. destruct (classicT(a=x)); try contradiction. auto. }
   {simpl. destruct(classicT(a=x') ); try contradiction. auto. }
   {simpl. destruct (classicT(a=x')); try contradiction. 
    destruct (classicT(a=x)); try contradiction. erewrite IHT; eauto. }
  }
Qed. 


Theorem unspecSubtractEmpty : forall T t, 
                                unspecThread t = Empty_set thread ->
                                unspecPool (Subtract thread T t) = unspecPool T. 
Proof.
  induction T; intros. 
  {simpl. auto. }
  {simpl. destruct (classicT(a=t)) eqn:eq.
   {subst. rewrite H. unfoldTac. simpl. auto. }
   {simpl. rewrite IHT; eauto. }
  }
Qed. 


Theorem InSubNeq : forall (A:Type) T (t1 t2 : A),
                     In A T t2 -> t1 <> t2 ->
                     In A (Subtract A T t1) t2.
Proof.
  induction T; intros. 
  {inv H. }
  {simpl. destruct (classicT(a=t1)). 
   {subst. inv H. exfalso. apply H0; auto. auto. } 
   {simpl. inv H. auto. right. eauto. }
  }
Qed. 


Theorem unspecSingleton : forall t, 
                            unspecPool (tSingleton t) = unspecThread t.
Proof.
  intros. simpl. unfoldTac. rewrite Union_commutative. auto. 
Qed. 

Theorem lookupExtendNeq : forall (T:Type) H x x' (v':T) p,
                            x<>x' ->
                            heap_lookup x (Heap.extend x' v' H p) = heap_lookup x H. 
Proof.
  intros. destruct H. simpl. apply beq_nat_false_iff in H0. rewrite H0. auto.
Qed. 

Theorem smultiRevNewFull : forall H T H' tid M' E d x s1 s2 M,
        spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,aCons (nAct M' E d x) s1,s2,M))))
                           H' (tUnion T(tSingleton(tid,aCons (nAct M' E d x) s1,s2,M))) -> 
                             exists v, heap_lookup x H' = Some v.
Proof.
  intros. dependent induction H0.
  {symmetry in x. apply eqUnspec in x. unfoldTac. rewrite Union_commutative in x. 
   destruct s1; simpl in *; contradiction. }
  {startIndCase. destructThread x1. exMid tid H6. 
   {inv H. 
    {apply UnionEqTID in x. invertHyp. eapply IHspec_multistep_rev. Focus 2. eauto. 
     repeat rewrite unspecUnionComm. erewrite unspecSpecSame; eauto. }
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {unfoldTac. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {unfoldTac. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {unfoldTac. apply UnionEqTID in x. invertHyp. stacksNeq. econstructor. 
     rewrite lookupExtend; eauto. }
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
   }
   {inv H. 
    {apply UnionNeqTID in x; auto. invertHyp. eapply IHspec_multistep_rev. Focus 2. 
     rewrite H. unfoldTac. rewrite UnionSwap. auto. unfoldTac.
     repeat erewrite unspecUnionComm. apply EqJMeq. apply UnionEqL'. rewrite H1. 
     rewrite UnionSubtract. rewrite unspecUnionComm. erewrite unspecSpecSame; eauto. }
    {exMid tid ((numForks H7 + numForks' H5)%nat :: H6). 
     {unfoldTac. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct s1; simpl in *; inv H. }
     {symmetry in x. apply UnionCoupleNeqTID in x; auto. invertHyp. eapply IHspec_multistep_rev. 
      Focus 2. rewrite H8. unfoldTac. rewrite UnionSwap. eauto. unfoldTac. 
      repeat erewrite unspecUnionComm. apply EqJMeq. apply UnionEqL'. rewrite SubSwitch. 
      rewrite subtractUnspec. rewrite unspecSubtractEmpty; auto. apply InSubNeq. 
      rewriteSolveSet. intros c. inversion c. destruct H7; inv H11.
      destruct H7; auto. destruct l. auto. uCons a l. erewrite unspecTwoActs'; eauto. auto. 
      intros c. invertListNeq. }
    }
    {varsEq x1 x0.
     {econstructor. erewrite HeapLookupReplace; eauto. }
     {rewrite lookupReplaceNeq; auto. apply UnionNeqTID in x; auto. invertHyp. 
      eapply IHspec_multistep_rev. Focus 2. rewrite H1. unfoldTac. rewrite UnionSwap. 
      eauto. rewrite H8. rewrite UnionSubtract. repeat rewrite unspecUnionComm. 
      erewrite <- eraseTrmConsSame'; eauto. }
    }
    {varsEq x1 x0. 
     {econstructor. erewrite HeapLookupReplace; eauto. }
     {rewrite lookupReplaceNeq; eauto. apply UnionNeqTID in x; auto. invertHyp. 
      eapply IHspec_multistep_rev. Focus 2. rewrite H1. unfoldTac. rewrite UnionSwap. 
      eauto. rewrite H8. rewrite UnionSubtract. repeat rewrite unspecUnionComm. 
      erewrite <- eraseTrmConsSame'; eauto. }
    }
    {varsEq x1 x0. 
     {econstructor. erewrite lookupExtend; eauto. }
     {erewrite lookupExtendNeq; eauto. apply UnionNeqTID in x; auto. invertHyp. 
      eapply IHspec_multistep_rev. Focus 2. rewrite H1. unfoldTac. rewrite UnionSwap. 
      eauto. rewrite H8. rewrite UnionSubtract. repeat rewrite unspecUnionComm. 
      erewrite <- eraseTrmConsSame'; eauto. }
    }
    {exMid tid (2%nat :: H6). 
     {unfoldTac. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct s1; simpl in *; inv H. }
     {symmetry in x. apply UnionCoupleNeqTID in x; auto. invertHyp. eapply IHspec_multistep_rev. 
      Focus 2. rewrite H8. unfoldTac. rewrite UnionSwap. eauto. unfoldTac. 
      repeat erewrite unspecUnionComm. apply EqJMeq. apply UnionEqL'. rewrite SubSwitch. 
      rewrite subtractUnspec. rewrite unspecSubtractEmpty; auto. apply InSubNeq. 
      rewriteSolveSet. intros c. inversion c. destruct H7; inv H11.
      destruct H7; auto. destruct l. auto. uCons a l. erewrite unspecTwoActs'; eauto. auto. 
      intros c. invertListNeq. }
    }
   }
  }
Qed. 

Theorem passThroughNew : forall M M' T s1 s2 H H' tid x E d,
        heap_lookup x H' = Some (sempty SPEC) -> 
        spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,aCons (nAct M' E d x) s1,s2,M))))
                       H' (tUnion T(tSingleton(tid,aCons (nAct M' E d x) s1,s2,M))) ->
          spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,s1,s2,M'))))
                             (Heap.remove H' x) (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H1. 
  {symmetry in x. apply eqUnspec in x. unfoldTac. rewrite Union_commutative in x.
   destruct s1; simpl in *; contradiction. }
  {inv H. 
   {exMid tid tid0. 
    {apply UnionEqTID in x. invertHyp. eapply IHspec_multistep_rev. eauto. 
     Focus 3. auto. Focus 2. auto. repeat rewrite unspecUnionComm. 
     erewrite unspecSpecSame; eauto. }
    {apply UnionNeqTID in x;auto. invertHyp. takeTStep. econstructor. Focus 2. 
     eapply SBasicStep; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap.  
     eapply IHspec_multistep_rev; eauto. unspecsEq'. erewrite unspecSpecSame; eauto.
     rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet. }
   }
   {exMid tid tid0. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. 
     stacksNeq. }
    {exMid (plus(numForks b) (numForks' s0)::tid0) tid. 
     {unfoldTac; rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct s1; simpl in *; inv H. }
     {symmetry in x. apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. 
      econstructor. Focus 2. eapply SFork; auto. rewriteUnspec. unfoldTac. 
      rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq'. rewrite UnionSwap. 
      rewrite subtractUnion. auto. rewriteSolveSet. intros c. invertListNeq. }
    }
   }
   {exMid TID tid. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. }
    {varsEq x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0. 
     apply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2.
     eapply SGet with(h:=Heap.remove h' x0); eauto.
     erewrite lookupRemoveNeq; eauto. rewrite removeReplaceSwitch; eauto. 
     rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto.
     rewrite lookupReplaceNeq in H0; auto. eauto. unspecsEq'. rewrite UnionSwap. 
     rewrite subtractUnion. eauto. rewriteSolveSet. }
   }
   {exMid TID tid. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0. 
     apply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
     eapply SPut with (h:=Heap.remove h' x0); eauto. erewrite lookupRemoveNeq. eapply H2.
     auto. auto. rewrite removeReplaceSwitch ;eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. rewrite lookupReplaceNeq in H0; eauto. unspecsEq'.
     rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet. }
   }
   {exMid tid tid0. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. rewrite removeExtend; eauto. 
     rewrite unspecUnionComm in *. erewrite <- eraseTrmConsSame' in H1; eauto. }
    {exMid x1 x0.
     {apply UnionNeqTID in x; auto. invertHyp. rewrite H in H1. unfoldTac. 
      rewrite UnionSwap in H1.  
      assert(T = (tUnion
               (Subtract thread T
                  (tid0, aCons (nAct t E0 d0 x0) b, s0,
                  fill E0 (ret (fvar x0)))) 
               (tSingleton (tid0, aCons (nAct t E0 d0 x0) b, s0, fill E0 (ret (fvar x0)))))). 
      rewrite H3. rewrite UnionSubtract. auto. 
      assert(unspecPool
            (Union thread T
               (Single thread (tid, aCons (nAct M' E d x0) s1, s2, M))) =
         unspecPool(Union thread
            (Union thread
               (Subtract thread T
                  (tid0, aCons (nAct t E0 d0 x0) b, s0,
                  fill E0 (ret (fvar x0)))) (Single thread (tid0, b, s0, t)))
            (Single thread (tid, aCons (nAct M' E d x0) s1, s2, M)))).
      rewrite H4. rewrite UnionSubtract. repeat rewrite unspecUnionComm. 
      erewrite <- eraseTrmConsSame'. eauto. constructor. 
      unfoldTac. rewrite H5 in H1. eapply smultiRevNewFull in H1. invertHyp. heapsDisagree. }
     {eapply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2.
      eapply SNew with (h:=Heap.remove h' x0); eauto. erewrite removeExtendSwitch; eauto. 
      rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. 
      erewrite lookupExtendNeq in H0; eauto. unspecsEq'. rewrite UnionSwap.
      rewrite subtractUnion. auto. rewriteSolveSet. }
    }
   }
   {unfoldTac. exMid tid tid0. 
    {rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid tid (2::tid0). 
     {rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. destruct s1; inv H. }
     {symmetry in x. apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. 
      econstructor. Focus 2. eapply SSpec; eauto. rewriteUnspec. unfoldTac. 
      rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq'. rewrite UnionSwap. 
      rewrite subtractUnion. auto. rewriteSolveSet. intros c. invertListNeq. }
    }
   }
  }
  Grab Existential Variables. auto. eauto. erewrite lookupRemoveNeq; eauto. 
  auto. auto. 
Qed. 

Theorem alignLists : forall (T:Type) (a:list T) b c d, 
                       b::c = a++b::d -> ~List.In b a -> a = nil /\ d = c. 
Proof.
  induction a; intros. 
  {simpl in *. inv H. auto. }
  {inversion H. rewrite H2 in H0. exfalso. apply H0. constructor. auto. }
Qed. 

Theorem alignLists' : forall (T:Type) a b c (d:T) e, 
                       a::b = c++d::e -> a <> d -> ~List.In d c ->
                       exists f, c = a::f. 
Proof.
  induction c; intros. 
  {simpl in *. inv H. exfalso. apply H0; auto. }
  {inversion H. eauto. }
Qed. 

Theorem passThroughRead : forall M M' T s1 ds1 ds2 sc s2 H H' tid TID x E N' d,
        heap_lookup x H' = Some (sfull sc (ds1++[tid]++ds2) SPEC TID N') -> ~List.In tid ds1 ->
        spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,aCons (rAct x M' E d) s1,s2,M))))
                       H' (tUnion T(tSingleton(tid,aCons (rAct x M' E d) s1,s2,M))) ->
          spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,s1,s2,M'))))
                             (replace x (sfull sc (ds1++ds2) SPEC TID N') H') (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. genDeps{ds1;ds2}. depInd H2. 
  {symmetry in x. apply eqUnspec in x. unfoldTac. rewrite Union_commutative in x.
   destruct s1; simpl in *; contradiction. }
  {inv H. 
   {exMid tid tid0. 
    {apply UnionEqTID in x. invertHyp. eapply IHspec_multistep_rev. Focus 2. auto.
     Focus 2. auto. Focus 2. eauto. Focus 2. auto. repeat rewrite unspecUnionComm. 
     erewrite unspecSpecSame; eauto. }
    {apply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
     eapply SBasicStep; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
     eapply IHspec_multistep_rev; eauto. unspecsEq'. erewrite unspecSpecSame; eauto.
     rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet. }
   }
   {exMid tid tid0. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid tid ((numForks b + numForks' s0)%nat :: tid0). 
     {unfoldTac; rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct s1; simpl in *; inv H. }
     {symmetry in x. unfoldTac. apply UnionCoupleNeqTID in x. invertHyp. takeTStep. 
      econstructor. Focus 2. eapply SFork; eauto. rewriteUnspec. unfoldTac. 
      rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq'. rewrite UnionSwap. 
      rewrite subtractUnion. auto. rewriteSolveSet. auto. auto. intros c. invertListNeq. }
    }
   }
   {exMid TID0 tid. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. rewrite replaceOverwrite. 
     erewrite HeapLookupReplace in H0; eauto. inv H0. copy H6. eapply alignLists in H0; auto. 
      invertHyp. simpl in *. rewrite replaceSame; eauto. rewrite unspecUnionComm in *. 
      erewrite <- eraseTrmConsSame' in H2; eauto. }
    {varsEq x1 x0. 
     {erewrite HeapLookupReplace in H0; eauto. inv H0. copy H6. 
      eapply alignLists' in H; eauto. invertHyp. inversion H6. apply UnionNeqTID in x; auto. 
      invertHyp. takeTStep. econstructor. Focus 2.
      eapply SGet with (h:=(replace x0 (sfull sc (x1++ds2) SPEC TID N') h')).
      erewrite HeapLookupReplace; eauto. repeat rewrite replaceOverwrite.  simpl. auto.
      rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. 
      unspecsEq'. rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet.
      rewrite H0 in H3. eauto. intros c. apply H1. simpl. right; auto. }
     {apply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
      eapply SGet with (h:=(replace x0 (sfull sc (ds1++ds2) SPEC TID N') h')).
      rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch. auto. auto.
      rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto.
      unspecsEq'. rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet. 
      rewrite lookupReplaceNeq in H0; auto. }
    }
   }
   {exMid TID0 tid. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid x1 x0. erewrite HeapLookupReplace in H0; eauto. inv H0. destruct ds1; inv H6. 
     eapply UnionNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2.
     eapply SPut with (h:=replace x0 (sfull sc (ds1++ds2) SPEC TID N') h'); eauto. 
     rewrite lookupReplaceNeq; eauto. rewrite lookupReplaceSwitch; eauto. rewriteUnspec. 
     unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq'. 
     rewrite UnionSwap. rewrite subtractUnion. auto. rewriteSolveSet. 
     rewrite lookupReplaceNeq in H0; eauto. }
   }
   {exMid tid tid0. 
    {apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid x1 x0. erewrite lookupExtend in H0. inv H0. eapply UnionNeqTID in x; auto. 
     invertHyp. takeTStep. econstructor. Focus 2.
     eapply SNew with (h:=replace x0 (sfull sc (ds1++ds2) SPEC TID N') h'); eauto. 
     erewrite extendReplaceSwitch; eauto. erewrite lookupExtendNeq in H0; eauto.
     rewriteUnspec. unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. 
     erewrite lookupExtendNeq in H0; eauto. unspecsEq'. rewrite UnionSwap. 
     rewrite subtractUnion. auto. rewriteSolveSet. erewrite lookupExtendNeq in H0; eauto. }
   }
   {unfoldTac. exMid tid tid0. 
    {rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid tid (2::tid0). 
     {rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. destruct s1; inv H. }
     {symmetry in x. apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. 
      econstructor. Focus 2. eapply SSpec; eauto. rewriteUnspec. unfoldTac. 
      rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq'. rewrite UnionSwap. 
      rewrite subtractUnion. auto. rewriteSolveSet. intros c. invertListNeq. }
    }
   }
  }
  Grab Existential Variables. auto. eauto. rewrite lookupReplaceNeq; eauto. auto. 
  auto. 
Qed. 

Ltac unspecsEq'' :=
  match goal with
      |H:?T = ?x |- unspecPool(Union ?X ?T ?t') ~= ?z =>
       rewrite H;repeat rewrite unspecUnionComm; erewrite unspecSpecSame; eauto
      |H:?T = ?x |- unspecPool(Union ?X ?T ?t') ~= ?z => 
       rewrite UnionSwap; rewrite subtractUnion;[idtac|rewriteSolveSet]; rewrite H;
       rewrite UnionSwap; rewrite subtractUnion;[idtac|rewriteSolveSet]; rewrite coupleUnion;
       repeat rewrite unspecUnionComm; rewrite unspecEmpty; unfoldTac; rewrite union_empty_r;
       erewrite <- eraseTrmConsSame'; eauto
      |H:?T = ?x |- unspecPool(Union ?X ?T ?t') ~= ?z =>
       rewrite H; rewrite UnionSwap; rewrite subtractUnion;[rewrite UnionSwap;rewrite subtractUnion;
                                                            [idtac|rewriteSolveSet]|rewriteSolveSet];
       repeat rewrite unspecUnionComm
  end.

Ltac solveSet' :=
  match goal with
      | |- In ?A (Union ?A ?T1 ?T2) ?x =>
        unfold Union; unfold In; apply in_app_iff; try solve[left;solveSet|right;solveSet]
  end.

Theorem pullOutSub : forall A T x x',
                       x <> x' ->
                       Subtract A (Union A T (Single A x)) x' = 
                       Union A (Subtract A T x') (Single A x).
Proof.
  induction T; intros. 
  {simpl. destruct (classicT(x=x')). contradiction. auto. }
  {simpl. destruct (classicT(a=x')); auto. simpl. erewrite IHT; eauto. }
Qed. 


Ltac falseNeq :=
  match goal with
      |H:?x<>?x |- _ => exfalso; apply H; auto
  end. 

Ltac helper :=
  match goal with
      |H:List.In ?t (Couple ?X ?t1 ?t2) |- _ => inv H;[falseNeq|try helper]
      |H:List.In ?t [?t'] |- _ => inv H;[falseNeq|try helper]
      |H:List.In ?t [] |- _ => inv H
  end.

Theorem UnionCoupleNeq : forall (A:Type) T T' t1 t2 t3 t4,
                           Union A T (Couple A t1 t2) = Union A T' (Couple A t3 t4) ->
                           t1 <> t2 -> t2 <> t4 -> t1 <> t4 -> t2 <> t3 -> t3 <> t4 -> t1 <> t3 -> 
                           T = Union A (Subtract A (Subtract A T' t1) t2) (Couple A t3 t4) /\
                           T' = Union A (Subtract A (Subtract A T t3) t4) (Couple A t1 t2). 
Proof.
  intros. 
  assert(In A (Union A T (Couple A t1 t2)) t3). rewrite H. solveSet'. 
  assert(In A (Union A T (Couple A t1 t2)) t4). rewrite H. solveSet'. 
  assert(In A (Union A T' (Couple A t3 t4)) t1). rewrite <- H. solveSet'. 
  assert(In A (Union A T' (Couple A t3 t4)) t2). rewrite <- H. solveSet'. 
  repeat invUnion. inv H6; inv H7; inv H8; inv H9; try helper.
  {apply pullOut in H6. apply pullOut in H10. rewrite H6 in H. 
   rewrite H10 in H. apply pullOut in H7. apply pullOut in H8. rewrite H8 in H.     
   rewrite H7 in H. rewrite pullOutSub in H; auto. rewrite pullOutSub in H; auto.
   rewrite <- (Union_associative A (Subtract A (Subtract A T t3) t4)) in H.
   rewrite <- coupleUnion in H. 
   rewrite <- (Union_associative A (Subtract A (Subtract A T' t1) t2)) in H. 
   rewrite <- coupleUnion in H. rewrite UnionSwap in H. apply UnionEqL in H; auto. 
   apply UnionEqL in H. split.
   {rewrite <- H. rewrite couple_swap. rewrite coupleUnion. rewrite Union_associative. 
    rewrite subtractUnion. auto. rewrite H6. rewrite pullOutSub; auto. solveSet. }
   {rewrite H. rewrite couple_swap. rewrite coupleUnion. rewrite Union_associative. 
    rewrite subtractUnion. auto. rewrite H8. rewrite pullOutSub; auto. solveSet. }
  }
Qed. 


Theorem doubleSubtract : forall A T t1 t2,
                           In A T t1 -> In A T t2 -> t1 <> t2 -> 
                           Union A (Subtract A (Subtract A T t1) t2) (Couple A t1 t2) = T.
Proof.
  intros. rewrite couple_swap. rewrite coupleUnion. rewrite Union_associative. 
  rewrite subtractUnion. rewrite subtractUnion; auto. apply InSubNeq; eauto. 
Qed. 



Theorem passThroughFork : forall M M' T s1 s2 H n H' tid E N' d s2' N,
        spec_multistep_rev H (unspecPool(tUnion T(tCouple(tid,aCons (fAct M' E N' d n) s1,s2,M)
                                                            (n::tid,locked nil, s2', N))))
                           H' (tUnion T(tCouple(tid,aCons (fAct M' E N' d n) s1,s2,M)
                                               (n::tid,locked nil, s2', N))) ->
        spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,s1,s2,M'))))
                           H' (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H0.   
  {symmetry in x. apply eqUnspec in x. unfoldTac. rewrite Union_commutative in x. 
   simpl in x. destruct s1; simpl in *; contradiction. }
  {inv H. 
   {unfoldTac; exMid tid tid0. 
    {rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. 
     eapply IHspec_multistep_rev. Focus 2. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. auto. repeat rewrite coupleUnion. 
     repeat rewrite unspecUnionComm. repeat rewrite unspecEmpty. 
     erewrite unspecSpecSame; eauto. }
    {exMid tid0 (n::tid). 
     {rewrite pullOutR in x . apply UnionEqTID in x. invertHyp. 
      eapply IHspec_multistep_rev. Focus 2. rewrite <- Union_associative. 
      rewrite <- coupleUnion. auto. repeat rewrite coupleUnion. 
      repeat rewrite unspecUnionComm. simpl. auto. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. 
      econstructor. Focus 2. eapply SBasicStep; eauto. rewriteUnspec. 
      unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq''.
      rewrite UnionSwap. rewrite doubleSubtract. auto. rewriteSolveSet. rewriteSolveSet. 
      intros c. inversion c. invertListNeq. intros c. invertListNeq. }
    }
   }
   {exMid tid tid0; unfoldTac.  
    {repeat rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. 
     apply UnionEqTID in H. invertHyp. rewrite coupleUnion in H0. 
     repeat rewrite unspecUnionComm in *. rewrite unspecEmpty in H0. unfoldTac. 
     rewrite union_empty_r in H0. erewrite <- eraseTrmConsSame' in H0; eauto. }
    {apply UnionCoupleNeq in x; auto. Focus 2. intros c. inversion c. 
     destruct b; inv H3. Focus 2. introsInv. falseNeq. Focus 2. introsInv. 
     rewrite pullOutL in x. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
     destruct b; inv H3. Focus 2. introsInv. destruct s1; inv H4. Focus 2. intros c. 
     inversion c. destruct s1; inv H3. Focus 2. introsInv. falseNeq. 
     invertHyp. takeTStep. econstructor. Focus 2. eapply SFork; eauto. rewriteUnspec.
     unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite UnionSwap. 
     rewrite doubleSubtract. rewrite H. rewrite UnionSwap. repeat rewrite unspecUnionComm. 
     apply EqJMeq. apply UnionEqL'. erewrite SubSwitch. rewrite subtractUnspec.
     rewrite unspecSubtractEmpty; auto. rewrite H2. apply InSubNeq. solveSet. intros c. 
     inversion c. destruct b; inv H7. repeat erewrite <- unspecSingleton. 
     erewrite <- eraseTrmConsSame'; eauto. rewriteSolveSet. rewriteSolveSet. intros c. 
     inversion c. destruct s1; inv H7. rewrite UnionSwap. rewrite doubleSubtract. auto. 
     rewriteSolveSet. rewriteSolveSet. intros c. inversion c. invertListNeq. }
   }
   {exMid TID tid. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid TID (n::tid). 
     {unfoldTac. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct b; inv H. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
      eapply SGet; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
      eapply IHspec_multistep_rev; eauto. unspecsEq''. 
      erewrite <- eraseTrmConsSame'; eauto. destruct b; constructor. 
      rewrite UnionSwap. rewrite doubleSubtract; auto. rewriteSolveSet. 
      rewriteSolveSet. intros c. inversion c. invertListNeq. intros c. invertListNeq. }
    }
   }
   {exMid TID tid. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid TID (n::tid). 
     {unfoldTac. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct b; inv H. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
      eapply SPut; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
      eapply IHspec_multistep_rev; eauto. unspecsEq''. 
      erewrite <- eraseTrmConsSame'; eauto. destruct b; constructor. 
      rewrite UnionSwap. rewrite doubleSubtract; auto. rewriteSolveSet. 
      rewriteSolveSet. intros c. inversion c. invertListNeq. intros c. invertListNeq. }
    }
   }
   {exMid tid0 tid. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid tid0 (n::tid). 
     {unfoldTac. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct b; inv H. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
      eapply SNew; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
      eapply IHspec_multistep_rev; eauto. unspecsEq''. 
      erewrite <- eraseTrmConsSame'; eauto. destruct b; constructor. 
      rewrite UnionSwap. rewrite doubleSubtract; auto. rewriteSolveSet. 
      rewriteSolveSet. intros c. inversion c. invertListNeq. intros c. invertListNeq. }
    }
   }
   {exMid tid tid0; unfoldTac.  
    {repeat rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {apply UnionCoupleNeq in x; auto. Focus 2. intros c. inversion c. 
     destruct b; inv H3. Focus 2. introsInv. falseNeq. Focus 2. introsInv. 
     rewrite pullOutL in x. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
     destruct b; inv H3. Focus 2. introsInv. destruct s1; inv H4. Focus 2. intros c. 
     inversion c. destruct s1; inv H3. Focus 2. introsInv. falseNeq. 
     invertHyp. takeTStep. econstructor. Focus 2. eapply SSpec; eauto. rewriteUnspec.
     unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite UnionSwap. 
     rewrite doubleSubtract. rewrite H. rewrite UnionSwap. repeat rewrite unspecUnionComm. 
     apply EqJMeq. apply UnionEqL'. erewrite SubSwitch. rewrite subtractUnspec.
     rewrite unspecSubtractEmpty; auto. rewrite H2. apply InSubNeq. solveSet. intros c. 
     inversion c. destruct b; inv H7. repeat erewrite <- unspecSingleton. 
     erewrite <- eraseTrmConsSame'; eauto. rewriteSolveSet. rewriteSolveSet. intros c. 
     inversion c. destruct s1; inv H7. rewrite UnionSwap. rewrite doubleSubtract. auto. 
     rewriteSolveSet. rewriteSolveSet. intros c. inversion c. invertListNeq. }
   }
  }
  Grab Existential Variables. auto. auto. eauto. auto. auto. auto. auto. 
Qed. 

Theorem passThroughSpec : forall M M' T s1 s2 H H' tid E s2' N M'' N'' d,
        spec_multistep_rev H (unspecPool(tUnion T(tCouple(tid,aCons (srAct M' E M'' N'' d) s1,s2,M)
                                                            (2::tid,locked nil, s2', N))))
                           H' (tUnion T(tCouple(tid,aCons (srAct M' E M'' N'' d) s1,s2,M)
                                               (2::tid,locked nil, s2', N))) ->
        spec_multistep_rev H (unspecPool(tUnion T(tSingleton(tid,s1,s2,M'))))
                           H' (tUnion T(tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H0.   
  {symmetry in x. apply eqUnspec in x. unfoldTac. rewrite Union_commutative in x. 
   simpl in x. destruct s1; simpl in *; contradiction. }
  {inv H. 
   {unfoldTac; exMid tid tid0. 
    {rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. 
     eapply IHspec_multistep_rev. Focus 2. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. auto. repeat rewrite coupleUnion. 
     repeat rewrite unspecUnionComm. repeat rewrite unspecEmpty. 
     erewrite unspecSpecSame; eauto. }
    {exMid tid0 (2::tid). 
     {rewrite pullOutR in x . apply UnionEqTID in x. invertHyp. 
      eapply IHspec_multistep_rev. Focus 2. rewrite <- Union_associative. 
      rewrite <- coupleUnion. auto. repeat rewrite coupleUnion. 
      repeat rewrite unspecUnionComm. simpl. auto. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. 
      econstructor. Focus 2. eapply SBasicStep; eauto. rewriteUnspec. 
      unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. unspecsEq''.
      rewrite UnionSwap. rewrite doubleSubtract. auto. rewriteSolveSet. rewriteSolveSet. 
      intros c. inversion c. invertListNeq. intros c. invertListNeq. }
    }
   }
   {exMid tid tid0; unfoldTac.  
    {repeat rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {apply UnionCoupleNeq in x; auto. Focus 2. intros c. inversion c. 
     destruct b; inv H3. Focus 2. introsInv. falseNeq. Focus 2. introsInv. 
     rewrite pullOutL in x. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
     destruct b; inv H3. Focus 2. introsInv. destruct s1; inv H4. Focus 2. intros c. 
     inversion c. destruct s1; inv H3. Focus 2. introsInv. falseNeq. 
     invertHyp. takeTStep. econstructor. Focus 2. eapply SFork; eauto. rewriteUnspec.
     unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite UnionSwap. 
     rewrite doubleSubtract. rewrite H. rewrite UnionSwap. repeat rewrite unspecUnionComm. 
     apply EqJMeq. apply UnionEqL'. erewrite SubSwitch. rewrite subtractUnspec.
     rewrite unspecSubtractEmpty; auto. rewrite H2. apply InSubNeq. solveSet. intros c. 
     inversion c. destruct b; inv H7. repeat erewrite <- unspecSingleton. 
     erewrite <- eraseTrmConsSame'; eauto. rewriteSolveSet. rewriteSolveSet. intros c. 
     inversion c. destruct s1; inv H7. rewrite UnionSwap. rewrite doubleSubtract. auto. 
     rewriteSolveSet. rewriteSolveSet. intros c. inversion c. invertListNeq. }
   }
   {exMid TID tid. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid TID (2::tid). 
     {unfoldTac. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct b; inv H. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
      eapply SGet; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
      eapply IHspec_multistep_rev; eauto. unspecsEq''. 
      erewrite <- eraseTrmConsSame'; eauto. destruct b; constructor. 
      rewrite UnionSwap. rewrite doubleSubtract; auto. rewriteSolveSet. 
      rewriteSolveSet. intros c. inversion c. invertListNeq. intros c. invertListNeq. }
    }
   }
   {exMid TID tid. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid TID (2::tid). 
     {unfoldTac. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct b; inv H. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
      eapply SPut; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
      eapply IHspec_multistep_rev; eauto. unspecsEq''. 
      erewrite <- eraseTrmConsSame'; eauto. destruct b; constructor. 
      rewrite UnionSwap. rewrite doubleSubtract; auto. rewriteSolveSet. 
      rewriteSolveSet. intros c. inversion c. invertListNeq. intros c. invertListNeq. }
    }
   }
   {exMid tid0 tid. 
    {unfoldTac. rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq. }
    {exMid tid0 (2::tid). 
     {unfoldTac. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
      destruct b; inv H. }
     {apply UnionCoupleNeqTID in x; auto. invertHyp. takeTStep. econstructor. Focus 2. 
      eapply SNew; eauto. rewriteUnspec. unfoldTac. rewrite UnionSwap. 
      eapply IHspec_multistep_rev; eauto. unspecsEq''. 
      erewrite <- eraseTrmConsSame'; eauto. destruct b; constructor. 
      rewrite UnionSwap. rewrite doubleSubtract; auto. rewriteSolveSet. 
      rewriteSolveSet. intros c. inversion c. invertListNeq. intros c. invertListNeq. }
    }
   }
   {exMid tid tid0; unfoldTac.  
    {repeat rewrite pullOutL in x. apply UnionEqTID in x. invertHyp. stacksNeq.
     apply UnionEqTID in H. invertHyp. rewrite coupleUnion in H0. 
     repeat rewrite unspecUnionComm in *. rewrite unspecEmpty in H0. unfoldTac. 
     rewrite union_empty_r in H0. erewrite <- eraseTrmConsSame' in H0; eauto. }
    {apply UnionCoupleNeq in x; auto. Focus 2. intros c. inversion c. 
     destruct b; inv H3. Focus 2. introsInv. falseNeq. Focus 2. introsInv. 
     rewrite pullOutL in x. rewrite pullOutR in x. apply UnionEqTID in x. invertHyp. 
     destruct b; inv H3. Focus 2. introsInv. destruct s1; inv H4. Focus 2. intros c. 
     inversion c. destruct s1; inv H3. Focus 2. introsInv. falseNeq. 
     invertHyp. takeTStep. econstructor. Focus 2. eapply SSpec; eauto. rewriteUnspec.
     unfoldTac. rewrite UnionSwap. eapply IHspec_multistep_rev; eauto. rewrite UnionSwap. 
     rewrite doubleSubtract. rewrite H. rewrite UnionSwap. repeat rewrite unspecUnionComm. 
     apply EqJMeq. apply UnionEqL'. erewrite SubSwitch. rewrite subtractUnspec.
     rewrite unspecSubtractEmpty; auto. rewrite H2. apply InSubNeq. solveSet. intros c. 
     inversion c. destruct b; inv H7. repeat erewrite <- unspecSingleton. 
     erewrite <- eraseTrmConsSame'; eauto. rewriteSolveSet. rewriteSolveSet. intros c. 
     inversion c. destruct s1; inv H7. rewrite UnionSwap. rewrite doubleSubtract. auto. 
     rewriteSolveSet. rewriteSolveSet. intros c. inversion c. invertListNeq. }
   }
  }
  Grab Existential Variables. auto. auto. eauto. auto. auto. auto. auto. 
Qed. 

Theorem AddUnion : forall (A:Type) T e, 
                     Add A T e = Union A T (Single A e).
Proof.
  intros. reflexivity. 
Qed. 

Theorem rollbackWF : forall H H' T TR TR' tidR acts,
                       wellFormed H (tUnion T TR) ->
                       rollback tidR acts H TR H' TR' ->
                       wellFormed H' (tUnion T TR'). 
Proof.
  intros. induction H1. 
  {auto. }
  {subst. inv H0.  apply IHrollback. unfoldTac. econstructor; eauto. 
   erewrite unspecHeapRBRead; eauto. rewrite AddUnion in *. rewrite Union_associative in H1. 
   copy H1. rewrite smultiSmultiRevEq in H1. eapply passThroughRead in H1; eauto. 
   repeat rewrite Union_associative. rewrite smultiSmultiRevEq. eauto. }
  {subst. inv H0. apply IHrollback. unfoldTac. econstructor; eauto. rewrite AddUnion. 
   repeat rewrite Union_associative in *. rewrite smultiSmultiRevEq in *. 
   eapply passThroughFork; eauto. }
  {subst. inv H0. apply IHrollback. unfoldTac. econstructor; eauto. 
   erewrite unspecHeapRBWrite; eauto. rewrite AddUnion in *. 
   repeat rewrite Union_associative in *. rewrite smultiSmultiRevEq in *.  
   eapply passThroughWrite; eauto. }
  {subst. inv H0. apply IHrollback. unfoldTac. econstructor; eauto. 
   erewrite <- unspecHeapRBNew; eauto. rewrite AddUnion in *. 
   repeat rewrite Union_associative in *. 
   rewrite smultiSmultiRevEq in *. eapply passThroughNew; eauto. }
  {subst. inv H0. apply IHrollback. unfoldTac. econstructor; eauto. rewrite AddUnion in *.
   repeat rewrite Union_associative in *. rewrite smultiSmultiRevEq in *.
   eapply passThroughSpec; eauto. }
Qed. 


