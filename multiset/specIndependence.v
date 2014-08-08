Require Import erasure. 
Require Import IndependenceCommon. 

Theorem simSpecJoin : forall H T H' T' tid s1 s2 M' M'',
                        spec_multistep H (tUnion T (tSingleton(tid,s1,s2,M'))) H' 
                                       (tUnion T' (tSingleton(tid,s1,s2,M''))) ->
                        spec_multistep H T H' T'. 
Proof.
  intros. dependent induction H0. 
  {unfoldTac. apply UnionEqTID in x. invertHyp. constructor. }
  {startIndCase. destructThread x0. exMid tid H6. 
   {apply UnionEqTID in H2. invertHyp. inv H. 
    {eauto. }
    {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
    {eapply monotonicActions in H0; try solveSet. destruct s1; simpl in *; omega. }
   }
   {apply UnionNeqTID in H2; auto. invertHyp. rewrite H8. econstructor. 
    eapply specStepChangeUnused. eauto. eapply IHspec_multistep; auto.
    rewrite H1. rewrite UnionSubtract. unfoldTac. rewrite UnionSwap. eauto. }
  }
Qed. 

Theorem wrapDistributeApp : forall s a N E e p, 
                              wrapActs(s++[a]) N E e p = wrapActs(s) N E e p++ wrapActs[a] N E e p.
Proof.
  induction s; intros. 
  {simpl. destruct a; auto. }
  {simpl. destruct a; auto; destruct a0; auto; rewrite IHs; auto. }
Qed. 

Theorem wrapEraseTrm : forall s M M' N N' E p,
                         eraseTrm s M M' -> 
                         eraseTrm (wrapActs s N E N' p) 
                                  (fill E (specJoin (ret N) M)) (fill E (specJoin (ret N) M')). 
Proof.
  intros. inv H; try solve[rewrite wrapDistributeApp; constructor]. 
  {simpl. constructor. }
Qed. 

Theorem specFastForward : forall H T H' T' tid x0 x s2' N N0 M M' M'',
    eraseTrm (x0++[x]) N M' ->                                                
    spec_multistep H (tUnion T (tSingleton(tid,specStack nil N0, s2', M)))
                   H' (tUnion T' (tSingleton(tid,specStack(x0++[x]) N0, s2', M''))) ->
    exists H'' T'',
      spec_multistep H (tUnion T (tSingleton(tid,specStack nil N0, s2', M))) 
                     H'' (tUnion T'' (tSingleton(tid,specStack nil N0, s2', M'))) /\
      spec_multistep H'' (tUnion T'' (tSingleton(tid, specStack nil N0, s2', M')))
                     H' (tUnion T' (tSingleton(tid,specStack(x0++[x]) N0, s2',M''))). 
Proof.
  intros. dependent induction H1. 
  {apply UnionEqTID in x. invertHyp. inv H. invertListNeq. }
  {startIndCase. destructThread x2. exMid tid H7. 
   {apply UnionEqTID in H3. invertHyp. inv H. 
    {eapply IHspec_multistep in H0; auto. invertHyp. exists x2. exists x3. 
     split. econstructor. eapply SBasicStep; eauto. eauto. eauto. }
    {copy H1; firstActTac H1. subst. apply eraseTrmApp in H0. inv H0. econstructor. 
     econstructor. split. constructor. econstructor. eapply SFork; eauto. eauto. }
    {copy H1; firstActTac H1. subst. apply eraseTrmApp in H0. inv H0. econstructor. 
     econstructor. split. constructor. econstructor. eapply SGet; eauto. eauto. }
    {copy H1; firstActTac H1. subst. apply eraseTrmApp in H0. inv H0. econstructor. 
     econstructor. split. constructor. econstructor. eapply SPut; eauto. eauto. }
    {copy H1; firstActTac H1. subst. apply eraseTrmApp in H0. inv H0. econstructor. 
     econstructor. split. constructor. econstructor. eapply SNew; eauto. eauto. }
    {copy H1; firstActTac H1. subst. apply eraseTrmApp in H0. inv H0. econstructor. 
     econstructor. split. constructor. econstructor. eapply SSpec; eauto. eauto. }
   }
   {apply UnionNeqTID in H3; auto. invertHyp. eapply IHspec_multistep in H0; eauto. 
    invertHyp. econstructor. econstructor. split. rewrite H9. unfoldTac. 
    rewrite UnionSwap. econstructor. eapply specStepChangeUnused. eauto. unfoldTac. 
    rewrite UnionSwap. eauto. eauto. rewrite H2. rewrite UnionSubtract.
    unfoldTac. rewrite UnionSwap. eauto. }
  }
Qed. 

Ltac monoActs H :=
  eapply monotonicActions in H;[idtac|solveSet|solveSet].

Theorem simTSteps : forall H T H' T' tid s1 s2 s1' s2' N M M' tid',
                      spec_multistep H (tUnion T (tSingleton(tid,s1,s2,M)))
                                     H' (tUnion T' (tSingleton(tid,s1,s2,M'))) ->
                      spec_multistep H (tUnion T (tSingleton(tid',s1',s2',N)))
                                     H' (tUnion T' (tSingleton(tid',s1',s2',N))). 
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {startIndCase. destructThread x0. exMid tid H6. 
   {apply UnionEqTID in H2. invertHyp. inv H. 
    {eauto. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
   }
   {apply UnionNeqTID in H2. invertHyp. rewrite H8. unfoldTac. rewrite UnionSwap. 
    econstructor. eapply specStepChangeUnused. eauto. unfoldTac. rewrite UnionSwap. 
    eapply IHspec_multistep; eauto. rewrite H1. rewrite UnionSubtract.
    rewrite UnionSwap; auto. auto. }
  }
Qed. 

Fixpoint joinCtxts E1 E2 :=
  match E1 with
      | bindCtxt E M => bindCtxt (joinCtxts E E2) M
      | handleCtxt E M => handleCtxt (joinCtxts E E2) M
      | appCtxt E M => appCtxt (joinCtxts E E2) M
      | appValCtxt E M => appValCtxt (joinCtxts E E2) M
      | pairCtxt E M => pairCtxt (joinCtxts E E2) M
      | pairValCtxt E M => pairValCtxt (joinCtxts E E2) M
      | fstCtxt E => fstCtxt (joinCtxts E E2)
      | sndCtxt E => sndCtxt (joinCtxts E E2)
      | specRunCtxt E M => specRunCtxt (joinCtxts E E2) M
      | specJoinCtxt E M => specJoinCtxt (joinCtxts E E2) M
      | holeCtxt => E2
  end. 

Theorem notValFill : forall E e, ~ val e -> ~val (fill E e). 
Proof.
  induction E; intros; simpl; try solve[introsInv].
  {intros c. inv c. apply IHE in H. contradiction. }
  {intros c. inv c. apply IHE in H. contradiction. }
  {auto. }
Qed. 

Theorem decomposeNotVal : forall t E e, decompose t E e -> E <> holeCtxt -> ~val t. 
Proof.
  intros. induction H; try solve[introsInv].
  {intros c. inv c. contradiction. }
  {introsInv. contradiction. }
Qed. 

Theorem decomposeFurther : forall E E' e e' e'',
                                  ctxtWF e E -> decompose e' E' e'' -> ~ val e' ->
                                  decompose (fill E e') (joinCtxts E E') e''.
Proof.
  induction E; intros. 
  {simpl. constructor. inv H. eapply notValFill. auto. inv H. eapply IHE; eauto. }
  {simpl. inv H. constructor. auto. apply notValFill; auto. eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {inv H. simpl. constructor; eauto. apply notValFill; eauto. }
  {simpl. auto. }
Qed. 


Theorem joinFill : forall E1 E2 e, fill (joinCtxts E1 E2) e = fill E1 (fill E2 e). 
Proof.
  induction E1; intros; try solve[simpl; rewrite IHE1; eauto]. 
  simpl. auto. 
Qed. 

Theorem decomposeJoin : forall e e' e'' E E', 
                          ctxtWF e E -> decompose e' E' e'' -> ~val e'' ->
                          decompose (fill E e') (joinCtxts E E') e''. 
Proof.
  intros. induction H; try solve[
  simpl; constructor; auto; apply decomposeEq in H0; subst;
  repeat apply notValFill; auto].
  {simpl. auto. }
Qed. 

Theorem fillDecompose : forall E t E' e' x,
                          decompose t E' e' -> ctxtWF x E -> ~val e' ->
                          fill E t = fill (joinCtxts E E') e' /\
                          decompose (fill (joinCtxts E E') e') (joinCtxts E E') e'. 
Proof.
  induction E; intros. 
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor. apply notValFill. auto. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. inv H0. eapply IHE in H; eauto. invertHyp. split. rewrite H0. auto. 
   constructor; auto. apply notValFill. auto. }
  {simpl. copy H. apply decomposeEq in H. subst. split; auto. }
Qed. 

Theorem basicStepNotVal : forall M M', 
                            basic_step M M' -> ~val M. 
Proof.
  intros. inv H;
          try solve[apply decomposeEq in H0; subst; apply notValFill; introsInv].
Qed.  
 
Theorem nonEmptySpecStack : forall H H' tid s1 s1' a s2 M M' T T' N,
                 spec_multistep H T H' T' -> tIn T (tid,specStack (s1++[a]) N,s2,M) -> 
                 tIn T' (tid,specStack(s1') N,s2,M') -> exists s, s1' = s ++ [a]. 
Proof.
  intros. genDeps{s1';s1;s2;a;M;M';tid}. induction H0; intros. 
  {assert(thread_lookup p2 tid (tid,specStack(s1++[a]) N,s2,M)). econstructor. eauto. auto. 
   assert(thread_lookup p2 tid (tid,specStack(s1') N,s2,M')). econstructor. eauto. auto.
   eapply uniqueThreadPool in H; eauto. inv H. eauto. }
  {unfoldTac. invUnion. inv H1. 
   {eapply IHspec_multistep. invUnion. left; eauto. eauto. }
   {copy H. apply specStepSingleton in H. invertHyp. inv H3; try contradiction. inv H1. 
    {eapply IHspec_multistep; eauto. invUnion. right. simpl; eauto. }
    {eapply IHspec_multistep; eauto. invUnion. right. simpl. rewrite app_comm_cons. 
     eauto. }
    {eapply IHspec_multistep; eauto. invUnion. right. simpl. rewrite app_comm_cons. 
     eauto. }
    {eapply IHspec_multistep; eauto. invUnion. right. simpl. rewrite app_comm_cons. 
     eauto. }
    {eapply IHspec_multistep; eauto. invUnion. right. simpl. rewrite app_comm_cons. 
     eauto. }
    {eapply IHspec_multistep; eauto. invUnion. right. simpl. rewrite app_comm_cons. 
     eauto. }
   }
  }
Qed. 

Theorem nonNilSpecStack : forall s1 s1' s2 x M M' tid N H H' T T' z,
        eraseTrm (s1'++[x]) z M' ->
        spec_multistep H (tUnion T (tSingleton(tid,specStack nil N,s2, M')))
                       H' (tUnion T' (tSingleton(tid,specStack s1 N,s2,M))) ->
        M <> M' -> s1 <> nil. 
Proof. 
  intros. dependent induction H1.  
  {inv H0; invertListNeq; apply app_inj_tail in H1; invertHyp; apply UnionEqTID in x; 
   invertHyp; inv H; exfalso; apply H2; auto. }
  {startIndCase. destructThread x1. exMid tid H8. 
   {apply UnionEqTID in H4. invertHyp. apply eraseTrmApp in H0. inv H. 
    {inv H0; clear d0; inv H13; falseDecomp. }
    {inv H0; clear d1; try falseDecomp. eapply nonEmptySpecStack in H1.
     Focus 2. simpl. rewrite app_nil_l. solveSet. Focus 2. solveSet. invertHyp. 
     introsInv. invertListNeq. }
    {inv H0; clear d1; try falseDecomp. eapply nonEmptySpecStack in H1.
     Focus 2. simpl. rewrite app_nil_l. solveSet. Focus 2. solveSet. invertHyp. 
     introsInv. invertListNeq. }
    {inv H0; clear d1; try falseDecomp. eapply nonEmptySpecStack in H1.
     Focus 2. simpl. rewrite app_nil_l. solveSet. Focus 2. solveSet. invertHyp. 
     introsInv. invertListNeq. }
    {inv H0; clear d1; try falseDecomp. eapply nonEmptySpecStack in H1.
     Focus 2. simpl. rewrite app_nil_l. solveSet. Focus 2. solveSet. invertHyp. 
     introsInv. invertListNeq. }
    {inv H0; clear d1; try falseDecomp. eapply nonEmptySpecStack in H1.
     Focus 2. simpl. rewrite app_nil_l. solveSet. Focus 2. solveSet. invertHyp. 
     introsInv. invertListNeq. }
   }
   {apply UnionNeqTID in H4; auto. invertHyp. eapply IHspec_multistep; eauto. 
    rewrite H3. unfoldTac. rewrite UnionSwap. eauto. }
  }
Qed. 

Ltac replaceTac :=
     match goal with
         | |- basic_step _ (fill ?E (specJoin ?x (fill ?E' ?y))) =>
           replace (specJoin x (fill E' y)) with (fill (specJoinCtxt E' x) y); auto
     end. 

Theorem simBasicStep' : forall M M' N1 E e,
                          basic_step M M' -> ctxtWF e E -> ~val M -> 
                          basic_step (fill E (specJoin (ret N1) M))
                                     (fill E (specJoin (ret N1) M')).
Proof.
  intros. inv H. 
  {eapply fillDecompose in H0. invertHyp. rewrite H. Focus 2. constructor; 
   auto. eauto. replaceTac. rewrite <- joinFill. econstructor. eauto. introsInv. }
  {eapply fillDecompose in H0. invertHyp. rewrite H. Focus 2. constructor; eauto. 
   replaceTac. rewrite <- joinFill. econstructor. eauto. introsInv. }
  {eapply fillDecompose in H0. invertHyp. rewrite H. Focus 2. constructor; eauto. 
   replaceTac. rewrite <- joinFill. eapply basicProjR. eauto. introsInv. }
  {eapply fillDecompose in H0. invertHyp. rewrite H. Focus 2. constructor; eauto. 
   replaceTac. rewrite <- joinFill. eapply basicBind. eauto. introsInv. }
  {eapply fillDecompose in H0. invertHyp. rewrite H. Focus 2. constructor; eauto. 
   replaceTac. rewrite <- joinFill. eapply basicBindRaise. eauto. introsInv. }
  {eapply fillDecompose in H0. invertHyp. rewrite H. Focus 2. constructor; eauto. 
   replaceTac. rewrite <- joinFill. eapply basicHandle. eauto. introsInv. }
  {eapply fillDecompose in H0. invertHyp. rewrite H. Focus 2. constructor; eauto. 
   replaceTac. rewrite <- joinFill. eapply basicHandleRet. eauto. introsInv. }
Qed. 

Theorem basicStepNeq : forall s1 x M M' M'' x0,
                         eraseTrm (s1++[x]) M x0 ->
                         basic_step M' M'' -> x0 <> M'. 
Proof.
  intros. inv H0; inv H; try solve[invertListNeq];
  apply lastElementEq in H2; subst; intros c; subst; eapply uniqueCtxtDecomp in H1; eauto; invertHyp; solveByInv. 
Qed.   


Inductive destructAct : action -> trm -> ctxt -> action -> trm -> ctxt -> Prop :=
|destRead : forall x t E t' E' d' d, 
              destructAct(rAct x t E d) t E (rAct x t' E' d') t' E'
|destWrite : forall x t E t' E' M d' d, 
               destructAct(wAct x t E M d) t E (wAct x t' E' M d') t' E'
|destNew : forall t' E' t E d x d', 
             destructAct(nAct t E d x) t E (nAct t' E' d' x) t' E'
|destFork : forall t E M d n t' E' d', 
              destructAct(fAct t E M d n) t E (fAct t' E' M d' n) t' E'
|destSR : forall t E M N d t' E' d', 
            destructAct(srAct t E M N d) t E (srAct t' E' M N d') t' E'. 
Hint Constructors destructAct. 
Theorem foldWrapActs : forall a b l E0 M e E N1 p,
      destructAct a (fill E (specJoin (ret N1) M)) 
                  (joinCtxts E (specJoinCtxt E0 (ret N1))) 
                  b M E0 ->
      unlocked(a::wrapActs l N1 E e p) = unlocked(wrapActs(b:: l) N1 E e p).
Proof.
  intros. inv H. 
  {simpl. proofsEq d0 (wrapDecompose' E M E0 (get (fvar x)) e N1 d'0 p). 
   auto. }
  {simpl. proofsEq d0 (wrapDecompose' E M E0 (put (fvar x) M0) e N1 d'0 p). 
   auto. }
  {simpl. proofsEq d0 (wrapDecompose' E M E0 new e N1 d'0 p). auto. }
  {simpl. proofsEq d0 (wrapDecompose' E M E0 (fork M0) e N1 d'0 p); auto. }
  {simpl. proofsEq d0 (wrapDecompose' E M E0 (spec M0 N) e N1 d'0 p); auto. }
Qed. 

Theorem numForks'Wrap : forall s1 N1 E e p,
                         numForks' (wrapActs s1 N1 E e p) = numForks' s1. 
Proof.
  induction s1; intros. 
  {auto. }
  {simpl. destruct a; eauto. simpl. erewrite IHs1. eauto. }
Qed. 

Theorem simSpecJoin' : forall H T H' T' H'' T'' tid s2 M M' y s1 s1' N0 N1 E e p x z,  
   eraseTrm (s1'++[y]) z x ->                 
   spec_multistep H'' (tUnion T'' (tSingleton(tid,specStack nil N0, s2, x))) 
                  H (tUnion T (tSingleton(tid,specStack s1 N0,s2,M))) -> 
   spec_multistep H (tUnion T (tSingleton(tid,specStack s1 N0, s2, M)))
                  H' (tUnion T' (tSingleton(tid,specStack(s1'++[y]) N0, s2, M'))) -> 
   ~val e ->
   spec_multistep H (tUnion T (tSingleton(tid,unlocked (wrapActs s1 N1 E e p),s2,fill E (specJoin(ret N1)M))))
                  H' (tUnion T' (tSingleton(tid,unlocked(wrapActs(s1'++[y]) N1 E e p),s2,fill E (specJoin(ret N1)M')))).
Proof.
  intros. dependent induction H2. 
  {apply UnionEqTID in x. invertHyp. inv H. constructor. }
  {startIndCase. destructThread x1. exMid H9 tid. 
   {apply UnionEqTID in H5. invertHyp. inv H. 
    {copy H13. eapply simBasicStep' in H; eauto. Focus 2. copy H.
     apply basicStepNotVal in H. auto. econstructor. eapply SBasicStep; eauto.
     eapply nonNilSpecStack in H1. destruct s1. exfalso; apply H1. auto. 
     destruct a; simpl; constructor. eauto. eapply basicStepNeq in H13; eauto. 
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SBasicStep. eauto. eauto. constructor. }
    {econstructor. apply SFork with(E:=joinCtxts E (specJoinCtxt E0(ret N1)))(M:=M0).
     auto. unfoldTac. rewrite coupleUnion. rewrite Union_associative. 
     rewrite UnionSwap. rewrite joinFill. simpl. erewrite foldWrapActs; auto. 
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SFork; eauto. simpl. rewrite UnionSwap. 
     rewrite <- Union_associative. rewrite <- coupleUnion. repeat rewrite numForks'Wrap. 
     constructor. rewrite <- Union_associative. rewrite <- coupleUnion. 
     rewrite couple_swap. rewrite numForks'Wrap. simpl. auto. }
    {econstructor. eapply SGet with(E:=joinCtxts E (specJoinCtxt E0(ret N1))); eauto. 
     rewrite joinFill. simpl. erewrite foldWrapActs; auto. 
     eapply IHspec_multistep; simpl; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SGet; eauto. constructor. }
    {econstructor. eapply SPut with(E:=joinCtxts E (specJoinCtxt E0(ret N1))); eauto. 
     rewrite joinFill. simpl. erewrite foldWrapActs; auto. 
     eapply IHspec_multistep; simpl; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SPut; eauto. constructor. }
    {econstructor. eapply SNew with(E:=joinCtxts E (specJoinCtxt E0(ret N1))); eauto. 
     rewrite joinFill. simpl. erewrite foldWrapActs; auto. 
     eapply IHspec_multistep; simpl; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SNew; eauto. constructor. }
    {econstructor. eapply SSpec with(E:=joinCtxts E (specJoinCtxt E0(ret N1)));eauto. 
     rewrite joinFill. simpl. erewrite foldWrapActs; auto. unfoldTac. 
     rewrite couple_swap. rewrite coupleUnion. rewrite Union_associative.
     eapply IHspec_multistep; simpl; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SSpec; eauto. rewrite <- Union_associative. 
     rewrite <- coupleUnion. rewrite couple_swap. constructor.
     rewrite <- Union_associative. rewrite <- coupleUnion. rewrite couple_swap. 
     auto. }
   }
   {apply UnionNeqTID in H5. invertHyp. rewrite H11. unfoldTac. rewrite UnionSwap. 
    econstructor. eapply specStepChangeUnused. eauto. unfoldTac. rewrite UnionSwap. 
    eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
    rewrite H11. rewrite UnionSwap. econstructor. eapply specStepChangeUnused. 
    eauto. unfoldTac. rewrite UnionSwap. constructor. rewrite H4. 
    rewrite UnionSubtract. rewrite UnionSwap. eauto. auto. }
  }
  Grab Existential Variables. 
  {eapply decomposeJoin; eauto. constructor. auto. auto. copy d. 
   apply decomposeEq in H. subst. apply notValFill. introsInv. eauto. 
   introsInv. }
  {eapply decomposeJoin; eauto. constructor. auto. copy d. 
   apply decomposeEq in H. subst. apply notValFill. introsInv. eauto. 
   introsInv. }
  {eapply decomposeJoin; eauto. constructor. auto. copy d. 
   apply decomposeEq in H. subst. apply notValFill. introsInv. eauto. 
   introsInv. }
  {eapply decomposeJoin; eauto. constructor. auto. copy d. 
   apply decomposeEq in H. subst. apply notValFill. introsInv. eauto. 
   introsInv. }
  {eapply decomposeJoin; eauto. constructor. auto. copy d. 
   apply decomposeEq in H. subst. apply notValFill. introsInv. eauto. 
   introsInv. }
Qed. 

