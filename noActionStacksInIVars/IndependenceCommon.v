Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import SpecLib. 
Require Import sets. 
Require Import unspec. 
Require Import erasure. 
Require Import classifiedStep. 
Require Import AST. 
Require Import Coq.Program.Equality. 



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

