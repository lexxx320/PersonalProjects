Require Export partial_semantics.  

Inductive heapWF n : heap -> Prop :=
|consWF : forall l v H, heapWF n H -> l <= n -> heapWF n ((l,v)::H)
|nilWF : heapWF n nil. 

Inductive poolWF (n:nat) : pool -> Prop :=
|parWF : forall T1 T2, poolWF n T1 -> poolWF n T2 ->
                       poolWF n (Par T1 T2)
|ThreadWF : forall Hl L e, heapWF n Hl -> poolWF n (Single(Hl,L,e)). 

Hint Constructors heapWF poolWF. 

Ltac inv H := inversion H; subst; clear H. 
Ltac invertHyp :=
  match goal with
      |H:?P /\ ?Q |- _ => inv H; try invertHyp
      |H:exists x, ?P |- _ => inv H; try invertHyp
  end. 
Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 

Theorem heapCountMonotonic : forall n n' H T H' T', 
                               step n H T n' H' T' -> n' >= n. 
Proof.
  intros. induction H0; auto. Qed. 

Theorem heapWFWeakening : forall n n' H, heapWF n H -> n' >= n -> heapWF n' H. 
Proof.
  intros. generalize dependent n'. induction H0; intros; auto. 
  constructor. eauto. omega.
Qed. 

Theorem poolWFWeakening : forall n n' T, poolWF n T -> n' >= n -> poolWF n' T. 
Proof.
  intros. generalize dependent n'. induction H; intros; auto. 
  constructor. eapply heapWFWeakening; eauto. 
Qed. 

Theorem lookupWF : forall H l n v, heapWF n H -> lookup H l = Some v ->
                                   l <= n. 
Proof.
  intros. induction H0. 
  {simpl in H1. destruct (eq_nat_dec l l0). 
   {inv H1. auto. }
   {apply IHheapWF. auto. }
  }
  {inv H1. }
Qed. 


Ltac solveLocalHeap :=
  match goal with
      |H:poolWF ?n (Single ?x) |- _ => inv H; constructor; auto
  end. 

Require Export Coq.Program.Equality. 

Theorem commitWF : forall n H H' Hl Hl' L L' e e' res, 
                     commit H (Hl,L,e) H' (Hl',L',e') res ->
                     heapWF n H -> heapWF n Hl -> heapWF n H' /\ heapWF n Hl'. 
Proof.
  intros. dependent induction H0; auto. 
  {split; auto. inv H3. eapply IHcommit in H7; eauto. invertHyp. auto. }
  {inv H4. split; auto. }
  {inv H2. split; auto. constructor; auto. eapply IHcommit in H6; eauto.
   invertHyp. auto. }
  {inv H2. split; auto. constructor; auto. eapply IHcommit in H6; eauto. 
   invertHyp. auto. }
  {inv H2. eapply IHcommit in H6; eauto. }
Qed. 

Theorem stepWF : forall n n' H T H' T', 
                   heapWF n H  -> poolWF n T -> step n H T n' H' T' ->
                   heapWF n' H' /\ poolWF n' T'. 
Proof. 
  intros. induction H2; try solve[split; auto; solveLocalHeap]. 
  {inv H1. apply IHstep in H5; auto. invertHyp. split; auto. 
   constructor. auto. eapply poolWFWeakening; eauto. eapply heapCountMonotonic; eauto. }
  {inv H1. apply IHstep in H6; auto. invertHyp. split; auto. 
   constructor; auto. eapply poolWFWeakening; eauto. eapply heapCountMonotonic; eauto. }
  {apply IHstep in H0. invertHyp. split; auto. constructor. inv H5. auto. constructor. 
   inv H1. auto. }
  {split. auto. constructor. constructor. inv H1. auto. eapply lookupWF; eauto. }
  {split. constructor. auto. eapply lookupWF; eauto. solveLocalHeap. }
  {split. auto. solveLocalHeap. constructor. auto. eapply lookupWF. eapply H0. eauto. }
  {split; auto. solveLocalHeap. constructor. auto. eapply lookupWF; eauto. }
  {split. constructor. eapply heapWFWeakening; eauto; omega. omega. solveLocalHeap. 
   eapply heapWFWeakening; eauto. }
  {split. eapply heapWFWeakening; eauto. solveLocalHeap. constructor. 
   eapply heapWFWeakening; eauto. omega. }
  {eapply commitWF in H2; eauto. invertHyp. split. auto. constructor. constructor.
   inv H1. auto. }
  {inv H1. eapply commitWF in H2; eauto. invertHyp. split; auto. }
Qed. 

Theorem multistepWF : forall n n' H T H' T',
                   heapWF n H  -> poolWF n T -> multistep n H T n' H' T' ->
                   heapWF n' H' /\ poolWF n' T'. 
Proof.                         
  intros. induction H2. 
  {split; auto. }
  {apply stepWF in H2; auto. invertHyp. apply IHmultistep; auto. }
Qed. 


Theorem commit_fWF : forall n H0 H H' Hl Hl' L L' e e' res, 
                     commit_f H0 H (Hl,L,e) H' (Hl',L',e') res -> heapWF n H0 ->
                     heapWF n H -> heapWF n Hl -> heapWF n H' /\ heapWF n Hl'. 
Proof.
  intros. dependent induction H1; auto. 
  {split; auto. inv H5. eapply IHcommit_f in H9; eauto. invertHyp. auto. }
  {inv H4. split; auto. constructor; auto. eapply IHcommit_f in H8; eauto.
   invertHyp. auto. }
  {inv H4. split; auto. constructor; auto. eapply IHcommit_f in H8; eauto.
   invertHyp. auto. }
Qed. 

Theorem f_heapCountMonotonic : forall n n' H T H' T', 
                               f_step n H T n' H' T' -> n' >= n. 
Proof.
  intros. induction H0; auto. Qed. 

Theorem f_stepWF : forall n n' H T H' T', 
                   heapWF n H  -> poolWF n T -> f_step n H T n' H' T' ->
                   heapWF n' H' /\ poolWF n' T'. 
Proof. 
  intros. induction H2; try solve[split; auto; solveLocalHeap]. 
  {inv H1. apply IHf_step in H5; auto. invertHyp. split; auto. 
   constructor. auto. eapply poolWFWeakening; eauto. eapply f_heapCountMonotonic; eauto. }
  {inv H1. apply IHf_step in H6; auto. invertHyp. split; auto. 
   constructor; auto. eapply poolWFWeakening; eauto. eapply f_heapCountMonotonic; eauto. }
  {apply IHf_step in H0. invertHyp. split; auto. constructor. inv H5. auto. constructor. 
   inv H1. auto. }
  {split. auto. constructor. constructor. inv H1. auto. eapply lookupWF; eauto. }
  {split. constructor. auto. eapply lookupWF; eauto. solveLocalHeap. }
  {split. auto. solveLocalHeap. constructor. auto. eapply lookupWF. eapply H0. eauto. }
  {split; auto. solveLocalHeap. constructor. auto. eapply lookupWF; eauto. }
  {split. constructor. eapply heapWFWeakening; eauto; omega. omega. solveLocalHeap. 
   eapply heapWFWeakening; eauto. }
  {split. eapply heapWFWeakening; eauto. solveLocalHeap. constructor. 
   eapply heapWFWeakening; eauto. omega. }
  {eapply commit_fWF in H2; eauto. invertHyp. split. auto. constructor. constructor.
   inv H1. auto. }
  {inv H1. eapply commit_fWF in H2; eauto. invertHyp. split; auto. }
Qed. 

