Require Import Spec.
Require Import AST. 
Require Import SfLib. 
Require Import erasure. 
Require Import Coq.Sets.Ensembles. 

Hint Resolve app_comm_cons app_nil_l. 

Ltac inv H := inversion H; subst; clear H.

Theorem unspecLastAct : forall tid maj min min' A s2 M M' t,
                         basicAction A M' min' ->
                         (unspecThread (Tid (maj,min) tid, [A], s2, M) t <->
                          unspecThread (Tid(maj,min') tid, nil, s2, M') t). 
Proof.
  intros. split; intros. 
  {inversion H0; subst; try solve[
   match goal with
        |H:[?A]=?s++[?a], H':basicAction ?ac ?m ?t |- _ => 
         destruct s; inversion H; subst; try invertListNeq; inversion H'; subst
    end; apply decomposeEq in H8; subst; constructor]. 
  }
  {inversion H0; subst; try invertListNeq.
   inversion H; subst; try solve[ 
   match goal with
       |H:decompose ?M ?E ?e |- _ => copy H; apply decomposeEq in H; subst; econstructor; eauto
   end].   
  }
Qed. 



Theorem listAlign : forall (T:Type) l (x y :T) l' (e:T),
                      x::y::l = l' ++ [e] ->
                      exists l'', (y::l) = l'' ++ [e]. 
Proof.
  induction l; intros. 
  {destruct l'. inversion H. exists nil. inversion H.
   destruct l'. inversion H2. auto. inversion H2. destruct l'; inversion H4. }
  {destruct l'. 
   {inversion H. }
   {inversion H. exists l'. assumption. }
  }
Qed. 

Theorem unspecTwoActs : forall tid maj min min' A1 As s2 M M' t,
                         unspecThread (Tid (maj, min) tid, (A1::As), s2, M') t <->
                         unspecThread (Tid (maj, min') tid, (A1::As), s2, M) t. 
Proof.
  intros. split; intros. 
  {inversion H; subst;
   match goal with
       |H:?A::?As=?s++[?a] |- _ => rewrite H; eauto
   end. }
  {inversion H; subst;
   match goal with
       |H:?A::?As=?s++[?a] |- _ => rewrite H; eauto
   end. }
Qed. 

Theorem unspecTwoActs' : forall tid maj min min' A1 A2 As s2 M M' t,
                         unspecThread (Tid (maj, min) tid, (A1::A2::As), s2, M') t <->
                         unspecThread (Tid (maj, min') tid, (A2 :: As), s2, M) t. 
Proof.
  intros. split; intros. 
  {inversion H; subst;  
   match goal with
     |H:?A1::?A2::?As=?s++[?a] |- _ =>
      apply listAlign in H; inversion H as [Ex1 Ex2]; rewrite Ex2; eauto
   end. 
  }
  {inversion H; subst; 
   match goal with
       |H:?A::?As=?s++[?a] |- _ => rewrite H in *; eauto 
   end. 
  }
Qed.

Theorem unspecDeterm : forall t t' t'', unspecThread t t' -> unspecThread t t'' -> t' = t''. 
Proof.
  intros. 
  inversion H; subst; try solve[inversion H0; subst; try solve[auto; invertListNeq];
   try solve[match goal with
       |H:?s++[?a]=?s'++[?a'], H':decompose ?M ?E ?e |- _ => 
        apply lastElementEq in H; inversion H; subst; eapply uniqueCtxtDecomp in H'; eauto;
        inversion H'; subst; auto
   end]]. 
  {inversion H0; subst; try solve[invertListNeq].
   apply lastElementEq in H10. inversion H10; subst. eapply uniqueCtxtDecomp in H9; eauto. 
   inversion H9. inversion H3; subst. auto. }
  {inversion H0; subst; try solve[invertListNeq]. apply lastElementEq in H10. inversion H10; subst. 
   eapply uniqueCtxtDecomp in H9; eauto. inversion H9. inversion H3; subst; auto. }
Qed. 

Theorem unspecSingleton : forall t t', 
                            unspecThread t (Some t') ->
                            unspecPoolAux (tSingleton t) = tSingleton t'.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst. inversion H3; subst. 
   clear H4. clear H3. eapply unspecDeterm in H2; eauto. inversion H2; subst. clear H2. 
   constructor. }
  {destruct t. destruct p. destruct p. destruct t0. destruct p. econstructor. econstructor.
   econstructor. eauto. inversion H0; subst; auto. }
Qed. 

Theorem unspecUnionComm : forall T1 T2, unspecPoolAux (tUnion T1 T2) = 
                                        tUnion (unspecPoolAux T1) (unspecPoolAux T2).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inv H. inv H0. inv H2. inv H. 
   {econstructor. econstructor; eauto. }
   {apply Union_intror. econstructor; eauto. }
  }
  {inv H. 
   {inv H0. inv H. inv H2. econstructor; eauto. econstructor. econstructor. 
    eauto. eauto. }
   {inv H0. inv H. inv H2. econstructor; eauto. econstructor. apply Union_intror. 
    eauto. eauto. }
  }
Qed. 

Theorem unspecPoolEmpty : forall t, unspecThread t None -> unspecPoolAux (tSingleton t) = tEmptySet. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H3; subst. inversion H4; subst. 
   clear H3 H4. eapply unspecDeterm in H2; eauto. inversion H2. }
  {inversion H0. }
Qed. 