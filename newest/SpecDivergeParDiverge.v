Require Import erasure.   
Require Import progStepImpliesSpec. 
Require Import progStepWF. 

(*Definitions*)
CoInductive ParDiverge : pHeap -> pPool -> Prop :=
|divergeStep : forall T1 T2 T2' H H',
                 pstep H T1 T2 (pOK H' T1 T2') -> 
                 ParDiverge H' (pUnion T1 T2') -> ParDiverge H (pUnion T1 T2)
.

CoInductive ParDiverge' : pHeap -> pPool -> Prop :=
|divergeStep' : forall H H' T T',
                 pstepPlus H T H' T' -> ParDiverge' H' T' -> ParDiverge' H T. 

Theorem ParDivergeEq : forall H T, ParDiverge H T <-> ParDiverge' H T. 
Proof. 
  intros. split; intros. 
  {genDeps{T; H}. cofix. intros. inv H0. econstructor. econstructor. eauto. 
   constructor. eapply ParDivergeEq; eassumption. }
  {genDeps{T; H}. cofix CH. intros. inv H0. inv H2. inv H4. 
   {econstructor. eassumption. eapply CH. eauto. }
   {assert(ParDiverge' H'0 (pUnion T t0)). econstructor. econstructor. 
    eassumption. eassumption. assumption. econstructor. eassumption. 
    eapply CH. rewrite <- H2. eauto. }
  }
Qed. 

Theorem eActTerm : forall x, exists M, actionTerm x M. 
Proof.
  intros. destruct x; repeat econstructor. 
Qed. 

Ltac actTermTac x := assert(exists M, actionTerm x M) by apply eActTerm; invertHyp. 

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

Theorem unspecLastActPool : forall tid s a s2 M' M, 
                         actionTerm a M' ->
                         unspecPool(tSingleton(tid,unlocked(s++[a]),s2,M)) = 
                         tSingleton(tid,unlocked nil,s2,M'). 
Proof.
  induction s; intros. 
  {simpl. inv H; auto. }
  {simpl. destruct (s++[a0])eqn:eq. 
   {invertListNeq. }
   {rewrite <- eq. rewrite getLastApp. inv H; auto. }
  }
Qed. 

Theorem actionTrmConsSame'' : forall a M' N s1 s2 tid,
                             actionTerm a M' -> 
                             unspecPool(tSingleton(tid,unlocked s1,s2,M')) = 
                             unspecPool(tSingleton(tid,aCons a (unlocked s1),s2,N)). 
Proof.
  induction s1; intros. 
  {simpl. inv H; auto.  }
  {simpl. destruct s1. auto. erewrite getLastNonEmpty; eauto. }
Qed. 

Theorem actionTrmConsSame' : forall a M' N s1 s2 tid,
                             actionTerm a M' -> 
                             unspecPool(tSingleton(tid,s1,s2,M')) = 
                             unspecPool(tSingleton(tid,aCons a s1,s2,N)). 
Proof.
  intros. destruct s1; auto. apply actionTrmConsSame''. auto. 
Qed. 

Theorem unspecEmpty : forall tid s1 s2 M, 
                unspecPool(tSingleton(tid,locked s1,s2,M)) = (Empty_set thread).
Proof.
  intros. simpl. auto. 
Qed. 

Ltac sswfHelper := eapply spec_multi_trans;[eassumption|econstructor].

Hint Constructors actionTerm spec_multistep. 

Theorem specStepWF : forall H T H' t t',
                       wellFormed H (tUnion T t) -> spec_step H T t H' T t' ->
                       wellFormed H' (tUnion T t'). 
Proof.
  intros. inv H1. 
  {inv H0. econstructor. rewrite unspecUnionComm in *. destruct s1. 
   {simpl in *. sswfHelper; auto. eapply SBasicStep; eauto. }
   {destructLast l. inv H3. invertHyp. actTermTac x. erewrite unspecLastActPool in *; eauto. 
    sswfHelper; eauto. eapply SBasicStep; eauto. }
   {simpl in *. sswfHelper; eauto. eapply SBasicStep; eauto. }
  }
  {unfoldTac. inv H0. econstructor. rewrite coupleUnion. repeat rewrite unspecUnionComm in *.
   destruct b. 
   {simpl in *. sswfHelper. eapply SFork; eauto. constructor. }
   {erewrite <- actionTrmConsSame'. rewrite unspecEmpty. unfoldTac. rewrite union_empty_r. 
    sswfHelper. eapply SFork; eauto. constructor. auto. }
   {simpl in *.  sswfHelper. eapply SFork; eauto. constructor. }
  }
  {inv H0. econstructor. rewrite unspecUnionComm in *. destruct b. 
   {simpl in *. erewrite unspecHeapRBRead; eauto. sswfHelper. eapply SGet; eauto. constructor. }
   {erewrite unspecHeapRBRead; eauto. erewrite <- actionTrmConsSame'; auto. sswfHelper. 
    eapply SGet; eauto. constructor. }
   {simpl in *. erewrite unspecHeapRBRead; eauto. sswfHelper. eapply SGet; eauto. constructor. }
  }
  {inv H0. constructor. rewrite unspecHeapAddWrite; auto. rewrite unspecUnionComm in *.
   destruct b. 
   {simpl in *. sswfHelper. eapply SPut; eauto. constructor. }
   {erewrite <- actionTrmConsSame'; eauto. sswfHelper. eapply SPut; eauto. constructor. }
   {simpl in *. sswfHelper. eapply SPut; eauto. constructor. }
  }
  {inv H0. constructor. rewrite unspecHeapExtend. rewrite unspecUnionComm in *. destruct b. 
   {sswfHelper. eapply SNew; eauto. constructor. }
   {erewrite <- actionTrmConsSame'; eauto. sswfHelper. eapply SNew; eauto. constructor. }
   {sswfHelper. eapply SNew; eauto. constructor. }
  }
  {inv H0. constructor. unfoldTac. rewrite coupleUnion. repeat rewrite unspecUnionComm in *. 
   rewrite unspecEmpty. unfoldTac. rewrite union_empty_r. destruct b. 
   {sswfHelper. eapply SSpec; eauto. constructor. }
   {erewrite <- actionTrmConsSame'; eauto. sswfHelper. eapply SSpec; eauto. constructor. }
   {sswfHelper. eapply SSpec; eauto. constructor. }
  }
Qed. 

Theorem specMultiWF : forall H T H' T', wellFormed H T -> spec_multistep H T H' T' ->
                                        wellFormed H' T'. 
Proof.
  intros. induction H1. 
  {auto. }
  {eapply specStepWF in H; eauto. }
Qed. 

Theorem pstepDiffUnused : forall H H' T T' t t',
                            pstep H T t (pOK H' T t') ->
                            pstep H T' t (pOK H' T' t'). 
Proof.
  intros. Hint Constructors pstep. inv H0; eauto. 
Qed. 

Theorem pstepSingleton : forall H T1 T2 H' T2', 
                           pstep H T1 T2 (pOK H' T1 T2') -> exists t, T2 = Single ptrm t. 
Proof.
  intros. inv H0; eauto. 
Qed.
 
CoInductive SpecDiverge : sHeap -> pool-> Prop :=
|specDiverge : forall T1 T2 T2' H H' H'' T,
                 spec_multistep H T H' (tUnion T1 T2) -> 
                 prog_step H' T1 T2 (OK H'' T1 T2') -> 
                 SpecDiverge H'' (tUnion T1 T2') -> SpecDiverge H T.

Theorem SpecDivergeParDiverge' : forall H T,
                wellFormed H T -> 
                SpecDiverge H T -> ParDiverge' (eraseHeap H) (erasePool T). 
Proof.
  cofix CH. intros. inv H1. copy H3. apply specMultiWF in H3; auto. 
  eapply spec_multistepErase in H1. invertHyp. rewrite H6. rewrite H2.
  rewrite eraseUnionComm in *. copy H4. apply prog_specImpliesNonSpec in H4; auto. 
  invertHyp.  apply prog_stepWF in H1; auto. rewrite eraseUnionComm in *. 
  econstructor. eassumption. eapply CH. eauto. eauto. 
Qed. 

Theorem SpecDivergeParDiverge : forall H T,
              wellFormed H T -> 
              SpecDiverge H T -> ParDiverge (eraseHeap H) (erasePool T). 
Proof.
  intros. apply SpecDivergeParDiverge' in H1. rewrite ParDivergeEq. auto. auto. 
Qed. 








