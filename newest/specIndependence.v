Require Import SfLib.           
Require Import NonSpec.   
Require Import Spec.  
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import hetList. 
Require Import Coq.Program.Equality. 
Require Import unspec. 
Require Import sets. 
Require Import classifiedStep. 
Require Import Coq.Sets.Powerset_facts. 
Require Import Heap. 

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


Theorem simSpecJoin : forall H T H' T' tid s1 s2 M' M'',
                        spec_multistep H (tUnion T (tSingleton(tid,s1,s2,M'))) H' 
                                       (tUnion T' (tSingleton(tid,s1,s2,M''))) ->
                        spec_multistep H T H' T'. 
Proof.
  intros. dependent induction H0. 
  {unfoldTac. apply UnionEqTID in x. invertHyp. constructor. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H4. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor.
   apply H2 in H4. inv H4. 
   {copy H5. apply pullOut in H5. rewrite H5. econstructor. eapply specStepChangeUnused. 
    eauto. eapply IHspec_multistep. Focus 2. auto. apply UnionSingletonEq in H1. rewrite H1. 
    unfoldTac. rewrite UnionSwap. auto. auto. }
   {inv H5. inv H. 
    {unfoldTac; invertHyp. inv H4. eapply IHspec_multistep; eauto. apply UnionEqTID in H1. 
     invertHyp. auto. }
     {unfoldTac; invertHyp. inv H7. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
     {unfoldTac; invertHyp. inv H4. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
     {unfoldTac; invertHyp. inv H4. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
     {unfoldTac; invertHyp. inv H4. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
     {unfoldTac; invertHyp. inv H7. eapply monotonicActions in H0. Focus 2. 
      apply Union_intror. constructor. Focus 2. apply Union_intror. constructor.
      destruct s1; simpl in *; omega. }
    }
  }
Qed. 

Inductive eraseTrm : list action -> trm -> trm -> Prop :=
|eraseTrmNil : forall M, eraseTrm nil M M
|eraseTrmRead : forall x t E d s M, eraseTrm (s++[rAct x t E d]) M t
|eraseTrmWrite : forall x t E M d N s, eraseTrm (s++[wAct x t E M d]) N t
|eraseTrmNew : forall x t E d s M, eraseTrm (s++[nAct t E d x]) M t
|eraseTrmFork : forall t E M d N s, eraseTrm (s++[fAct t E M d]) N t
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

Ltac eraseTrmTac s1 M := assert(exists M', eraseTrm s1 M M') by apply eEraseTrm; invertHyp.  

Theorem EqJMeq : forall (T:Type) (x y:T), x = y -> JMeq x y.
Proof.
  intros. subst. auto. Qed. 


Ltac specActEq H := 
  eapply firstSpecActEq in H; [idtac|apply Union_intror; rewrite app_nil_l; constructor|
                               apply Union_intror; constructor]. 

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


Theorem eraseTrmApp : forall x a M M', 
                        eraseTrm (x ++ [a]) M M' -> actionTerm a M'. 
Proof.
  intros. inv H; try solve[apply lastElementEq in H1; subst; constructor].
  invertListNeq. 
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
  {copy x. unfoldSetEq H2. copy H. apply specStepSingleton in H2. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x2)) x2). apply Union_intror. constructor. apply H3 in H2. 
   inv H2. 
   {eapply IHspec_multistep in H0. Focus 3. auto. Focus 2. apply UnionSingletonEq in x; auto.  
    rewrite x. unfoldTac. rewrite UnionSwap. auto. invertHyp. exists x3. exists x4. split; auto.
    apply pullOut in H5. unfoldTac. rewrite H5. rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap. eauto. }
   {inv H5. apply UnionEqTID in x. invertHyp. clear H2 H5 H7. inversion H; subst. 
    {unfoldTac; invertHyp. inv H2. eapply IHspec_multistep in H0. Focus 3. 
     auto. Focus 2. auto. invertHyp. exists x. exists x2. split; eauto. econstructor. 
     eapply SBasicStep; eauto. assumption. }
    {unfoldTac; invertHyp. inv H7. copy H1. specActEq H1. subst. 
     apply eraseTrmApp in H0. inv H0.  exists h'. exists T. split. constructor. 
     econstructor. eapply SFork. eauto. }
    {unfoldTac; invertHyp. inv H2. copy H1. specActEq H1. subst. exists h. exists T. 
     apply eraseTrmApp in H0. inv H0. split. constructor. econstructor. 
     eauto. eauto. }
    {unfoldTac; invertHyp. inv H2. copy H1. specActEq H1. subst. exists h. exists T. 
     apply eraseTrmApp in H0. inv H0. split. constructor. econstructor. 
     eauto. eauto. }
    {unfoldTac; invertHyp. inv H2. copy H1. specActEq H1. subst. exists h. exists T. 
     apply eraseTrmApp in H0. inv H0. split. constructor. econstructor. 
     eauto. eauto. }
    {unfoldTac; invertHyp. inv H7. copy H1. specActEq H1. subst. apply eraseTrmApp in H0. 
     inv H0. exists h'. exists T. split. constructor. econstructor. eauto. eauto. }
   }
  }
Qed. 

Ltac monoActs H :=
  eapply monotonicActions in H;[idtac|apply Union_intror; constructor|apply Union_intror;constructor].

Theorem simTSteps : forall H T H' T' tid s1 s2 s1' s2' N M M' tid',
                      spec_multistep H (tUnion T (tSingleton(tid,s1,s2,M)))
                                     H' (tUnion T' (tSingleton(tid,s1,s2,M'))) ->
                      spec_multistep H (tUnion T (tSingleton(tid',s1',s2',N)))
                                     H' (tUnion T' (tSingleton(tid',s1',s2',N))). 
Proof.
  intros. dependent induction H0. 
  {apply UnionEqTID in x. invertHyp. constructor. }
  {copy x. unfoldSetEq x. copy H. apply specStepSingleton in H4. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x)) x). apply Union_intror. constructor. 
   apply H2 in H4. inv H4. 
   {copy H5. apply pullOut in H5. rewrite H5. unfoldTac. rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused. eauto. unfoldTac. rewrite <- UnionSwap.
    eapply IHspec_multistep; eauto. apply UnionSingletonEq in H1. rewrite H1.
    rewrite UnionSwap. eauto. auto. }
   {inv H5. inv H; unfoldTac; invertHyp; invThreadEq.   
    {eapply IHspec_multistep; eauto. apply UnionEqTID in H1. invertHyp. eauto. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
    {monoActs H0. destruct s1; simpl in *; omega. }
   }
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
 
Theorem subtractSingle : forall X T x1, 
              (Subtract X (Union X (Subtract X T x1) (Singleton X x1)) x1) =
              Subtract X T x1. 
Proof.
  intros. eqSets. 
  {inv H. inv H0. auto. inv H. exfalso. apply H1. constructor. }
  {inv H. constructor. constructor. constructor. auto. auto. auto. }
Qed. 
Theorem nonEmptyStack : forall s1 s1' s2 x M M' tid N H H' T T' z,
        eraseTrm (s1'++[x]) z M' ->
        spec_multistep H (tUnion T (tSingleton(tid,specStack nil N,s2, M')))
                       H' (tUnion T' (tSingleton(tid,specStack s1 N,s2,M))) ->
        M <> M' -> s1 <> nil. 
Proof. 
  intros. dependent induction H1.  
  {Admitted. 

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

Theorem simSpecJoin' : forall H T H' T' H'' T'' tid tid' s2 s2' M M' y s1 s1' N0 N1 E e p x z,  
        eraseTrm (s1'++[y]) z x ->                 
        spec_multistep H'' (tUnion T'' (tSingleton(tid,specStack nil N0, s2, x))) 
                       H (tUnion T (tSingleton(tid,specStack s1 N0,s2,M))) -> 
        spec_multistep H (tUnion T (tSingleton(tid,specStack s1 N0, s2, M)))
                       H' (tUnion T' (tSingleton(tid,specStack(s1'++[y]) N0, s2, M'))) -> ~val e ->
        spec_multistep H (tUnion T (tSingleton(tid',unlocked (wrapActs s1 N1 E e p),s2',fill E (specJoin(ret N1)M))))
           H' (tUnion T' (tSingleton(tid',unlocked(wrapActs(s1'++[y]) N1 E e p),s2',fill E (specJoin(ret N1)M')))).
Proof.
  intros. dependent induction H2. 
  {apply UnionEqTID in x. invertHyp. inv H. constructor. }
  {copy x. unfoldSetEq H4. copy H. apply specStepSingleton in H4. invertHyp. 
   assert(tIn (tUnion T0 (tSingleton x1)) x1). apply Union_intror. constructor. 
   apply H5 in H4. inv H4. 
   {copy H7. apply pullOut in H7. rewrite H7. unfoldTac. rewrite UnionSwap. 
    econstructor. eapply specStepChangeUnused. eauto. unfoldTac. 
    rewrite <- UnionSwap. eapply IHspec_multistep; eauto. eapply spec_multi_trans. 
    eassumption. rewrite H7. rewrite UnionSwap. econstructor. 
    eapply specStepChangeUnused. eauto. rewrite subtractSingle. rewrite UnionSwap. 
    constructor. apply UnionSingletonEq in x. rewrite x. unfoldTac. 
    rewrite UnionSwap. auto. auto. }
   {inv H7. apply UnionEqTID in x. invertHyp. 
    inv H; unfoldTac; invertHyp; invThreadEq.  
    {copy H10. eapply simBasicStep' in H; eauto. Focus 2. copy H.
     apply basicStepNotVal in H. auto. econstructor. eapply SBasicStep; eauto.
     eapply nonEmptyStack in H1. destruct s1. exfalso; apply H1. auto. 
     destruct a; simpl; constructor. eauto. eapply basicStepNeq in H10; eauto. 
     eapply IHspec_multistep; eauto. eapply spec_multi_trans. eassumption. 
     econstructor. eapply SBasicStep. eauto. eauto. constructor. }
    {econstructor. Admitted. 


 





