Require Import NonSpec. 
Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import SfLib. 

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

Theorem appNil : forall (T:Type) (x:T), [x] = nil ++ [x]. 
Proof.
  intros. auto. Qed. 

Theorem unspecBasicAction1 : forall a M M' s2 tid tid' T,
                               basicAction a M' tid' ->
                               unspecPoolAux(tAdd T (tid, [a], s2, M)) = 
                               unspecPoolAux(tAdd T (tid', nil, s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {destruct tid'. destruct p. econstructor. econstructor. eapply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecLastAct. eassumption. eassumption. } 
  }
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {destruct tid. destruct p. econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecLastAct; eauto. }
  }
Qed. 


Theorem unspecBasicAction2 : forall a b s1' s2 M M' tid tid' T,
                              basicAction a M' tid' ->
                              unspecPoolAux(tAdd T (tid, a::b::s1', s2, M)) = 
                              unspecPoolAux(tAdd T (tid', b::s1', s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {destruct tid'. destruct p. econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecTwoActs. eassumption. }
  }
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {destruct tid. destruct p. econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecTwoActs. eassumption. }
  }
Qed. 

Theorem rollbackWellFormed : forall tid As H T H' T', 
                               wellFormed H T -> rollback tid As H T H' T' ->
                               wellFormed H' T'. 
Proof.
  intros. induction H1; subst. 
  {assumption. }
  {apply IHrollback. inversion H0; subst. inversion H2; subst. destruct s1'. 
   {eapply wf with (T' := (unspecPoolAux (tAdd T (tid', [rAct x tid'' M'], s2, M)))). 
    erewrite unspecBasicAction1. econstructor. constructor. eapply unspecHeapRBRead; eauto. 
    
