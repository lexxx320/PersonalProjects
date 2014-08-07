Require Import erasure. 

Ltac existTac e := let n := fresh in
                   try(assert(n:exists e', eraseTerm e' = e) by apply eTerm; invertHyp);
                   try(assert(n:exists e', eraseCtxt e' = e) by apply eCtxt; invertHyp). 

Ltac eTermTac := 
  match goal with
      |H:pbasic_step ?M ?M' |- _ => assert(exists M'', eraseTerm M'' = M') by apply eTerm;
                                   invertHyp
  end. 

Theorem simBasicStep : forall t t', pbasic_step (eraseTerm t) (eraseTerm t') ->
                                    basic_step t t'. 
Proof.
  intros. inv H. 
  {existTac E. existTac e. existTac N. rewrite <-eraseOpenComm in H0.
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. econstructor. 
   rewrite decomposeErase in H2; eauto. }
  {existTac E. existTac V1. existTac V2. rewrite <- eraseFill in H0.
   apply eraseTermUnique in H0. subst. econstructor. rewrite decomposeErase in H2; eauto. 
   simpl. auto. }
  {existTac E. existTac V1. existTac V2. rewrite <- eraseFill in H0.
   apply eraseTermUnique in H0. subst. eapply basicProjR. rewrite decomposeErase in H2; eauto. 
   simpl. auto. }
  {existTac E. existTac N. existTac M.
   replace (papp (eraseTerm x0) (eraseTerm x1)) with (eraseTerm (app x0 x1)) in H0; auto. 
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. eapply basicBind.  
   rewrite decomposeErase in H2; eauto. }
  {existTac E. existTac N. existTac M.
   replace (praise (eraseTerm x1)) with (eraseTerm (raise x1)) in H0; auto. 
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. eapply basicBindRaise.
   rewrite decomposeErase in H2; eauto. simpl. auto. }
  {existTac E. existTac N. existTac M. 
   replace (papp (eraseTerm x0) (eraseTerm x1)) with (eraseTerm (app x0 x1)) in H0; auto. 
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. eapply basicHandle. 
   rewrite decomposeErase in H2; eauto. }
  {existTac E. existTac M. existTac N. replace(pret (eraseTerm x0)) with (eraseTerm (ret x0)) in H0. 
   rewrite <- eraseFill in H0. apply eraseTermUnique in H0. subst. eapply basicHandleRet. 
   rewrite decomposeErase in H2; eauto. simpl. auto. simpl. auto. }
Qed. 

Theorem decompNeq : forall t E e E' e',
                      decompose t E e -> pdecompose (eraseTerm t) E' e' -> 
                      eraseTerm e <> e' -> False. 
Proof.
  intros. rewrite <- decomposeErase in H; eauto. eapply pctxtUnique in H0; eauto. 
  invertHyp. apply H1. auto.
Qed. 

Ltac inv' := unfoldTac; unfold pSingleton in *; 
  match goal with
      |H:Singleton ?X ?T = Empty_set ?X |- _ => apply SingletonNeqEmpty in H; inv H
      |H:Empty_set ?X = Singleton ?X ?T |- _ => symmetry in H; inv'
      |H:Singleton ?X ?t = Singleton ?X ?t' |- _ => apply SingletonEq in H; subst
      |H:eraseTerm ?x = eraseTerm ?y |- _ => apply eraseTermUnique in H; subst
      |H:decompose ?M ?E ?e,H':pdecompose ?M' ?E' ?e' |- _ =>
       eapply decompNeq in H'; eauto; try solveByInv; introsInv
      |_ => invertListNeq
  end. 

Theorem eraseAuxEq : forall T T', erasePoolAux T = T' -> erasePool T T'. 
Proof.
  intros. rewrite <- H. constructor. 
Qed. 

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' H T,
        pstep PH PT pt (pOK PH' PT pt') -> eraseHeap H = PH ->
        erasePool T (Union ptrm PT pt) -> commitPool T -> 
        exists H' T',
          eraseHeap H' = PH' /\ erasePool T' (pUnion PT pt') /\
          multistep H T (Some(H', T')). 
Proof.
  intros. inv H0. 
  {inv H2. 










