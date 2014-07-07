Require Import NonSpec.   
Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import SfLib.  
Require Import unspec. 
Require Import sets. 

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

Ltac copy H := 
  match type of H with
      |?x => assert(x) by assumption
  end. 

(*Helper theorems for reasoning about the erasure of heaps being rolled back*)
Theorem unspecHeapRBNew : forall H H' x S A,
                           unspecHeap H H' ->
                           Heap.heap_lookup x H = Some(sempty (S::A)) ->
                           unspecHeap (Heap.remove H x) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst; clear H1. inversion H0; subst. assumption. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem unspecHeapRBRead : forall H H' x sc tid ds S A t N,
                   unspecHeap H H' ->
                   Heap.heap_lookup x H = Some (sfull sc (tid::ds) (S::A) t N) ->
                   unspecHeap (Heap.replace x (sfull sc ds (S::A) t N) H) H'. 
Proof. 
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst. clear H1. inversion H0; subst; eauto. 
    apply beq_nat_true in eq. subst. eauto. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem unspecHeapRBWrite : forall H H' x sc S A tid N,
                      unspecHeap H H' ->
                      Heap.heap_lookup x H = Some(sfull sc nil (S::A) tid N) ->
                      unspecHeap (Heap.replace x (sempty sc) H) H'. 
Proof.
  induction H; intros. 
  {simpl in H0. inversion H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inversion H1; subst. clear H1. inversion H0; subst. 
    econstructor. assumption. apply beq_nat_true in eq. subst. auto. }
   {inversion H0; eauto. }
  }
Qed. 

Theorem unspecBasicAction1 : forall a M M' s2 T i j j' l,
                               basicAction a M' j' ->
                               unspecPoolAux(tAdd T (Tid(i,j)l, [a], s2, M)) = 
                               unspecPoolAux(tAdd T (Tid(i,j')l, nil, s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {econstructor. econstructor. eapply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecLastAct. eassumption. eassumption. } 
  }
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecLastAct; eauto. }
  }
Qed. 


Theorem unspecBasicAction2 : forall a b s1' s2 M M' T i j j' l,
                              basicAction a M' j' ->
                              unspecPoolAux(tAdd T (Tid(i,j) l, a::b::s1', s2, M)) = 
                              unspecPoolAux(tAdd T (Tid(i,j')l, b::s1', s2, M')). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecTwoActs'. eassumption. }
  }
  {inversion H0; subst. inversion H1; subst. inversion H4; subst; clear H4. inversion H3; subst. 
   {econstructor. econstructor. econstructor. eassumption. reflexivity. assumption. }
   {econstructor. econstructor. apply Union_intror. econstructor. 
    reflexivity. inversion H4; subst; clear H4. eapply unspecTwoActs'. eassumption. }
  }
Qed. 

Theorem unspecAdd : forall T t t', unspecThread t (Some t') -> 
                                   unspecPoolAux(tAdd T t) = tAdd(unspecPoolAux T) t'. 
Proof.
  intros. unfold tAdd. unfold Add. rewrite unspecUnionComm. erewrite unspecSingleton. 
  eauto. eauto. Qed. 

Inductive splitMultistep : sHeap -> pool -> pool -> config -> Prop :=
|splitRefl : forall h p1 p2, splitMultistep h p1 p2 (OK h p1 p2)
|splitStepL : forall h h' p1 p2 t1 t2 t2' config, 
                p1 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t1 p2) t2 (OK h' (tUnion t1 p2) t2') ->
                splitMultistep h' (tUnion t1 t2') p2 config ->
                splitMultistep h p1 p2 config
|splitStepR : forall h h' p1 p2 t1 t2 t2' config, 
                p2 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t1 p1) t2 (OK h' (tUnion t1 p1) t2') ->
                splitMultistep h' p1 (tUnion t1 t2') config ->
                splitMultistep h p1 p2 config
|errorL : forall h p1 p2 t1 t2 , 
                p1 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t1 p2) t2 Error ->
                splitMultistep h p1 p2 Error
|errorR : forall h p1 p2 t1 t2 , 
                p1 = tUnion t1 t2 -> Disjoint thread t1 t2 ->
                step h (tUnion t2 p2) t1 Error ->
                splitMultistep h p1 p2 Error
.


Axiom multistepUnion : forall T1 T2 H H' T1' T2',
                         multistep H tEmptySet (tUnion T1 T2) (OK H' tEmptySet (tUnion T1' T2')) ->
                         splitMultistep H T1 T2 (OK H' T1' T2'). 


Theorem moveToUnused : forall t T T' H H', 
              multistep H tEmptySet (tUnion T (tSingleton t)) (OK H' tEmptySet (tUnion T' (tSingleton t))) <->
              multistep H (tSingleton t) T (OK H' (tSingleton t) T'). 
Proof.
Admitted. 

Theorem multistepDepReader : forall H T t H' T' t' sc ds As tid N x d, 
                               Heap.heap_lookup x H = Some(sfull sc (d::ds) As tid N) ->
                               multistep H T t (OK H' T' t') ->
                               multistep H T t (OK (Heap.replace x (sfull sc ds As tid N) H') T' t). 
Admitted. 

Hint Constructors Union Couple. 

Theorem coupleUnion : forall X t1 t2, Couple X t1 t2 = Union X (Singleton X t1) (Singleton X t2). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H; subst; auto. }
  {inversion H; subst. inversion H0; subst; auto. inversion H0; subst; auto. }
Qed. 

Require Import Coq.Program.Equality.

Theorem SingletonEqUnion : forall X T1 T2 t, Singleton X t = Union X T1 T2 ->
                                             (T1 = Singleton X t /\ T2 = Empty_set X) \/
                                             (T2 = Singleton X t /\ T1 = Empty_set X) \/
                                             (T1 = Singleton X t /\ T2 = Singleton X t). 
Admitted. 


Theorem SingletonNeqEmpty : forall X t, Singleton X t = Empty_set X -> False.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
  assert(Ensembles.In X (Singleton X t) t). constructor. apply H0 in H. inversion H. Qed. 

Theorem AddNeqEmpty : forall X T t, Add X T t = Empty_set X -> False. 
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
  assert(Ensembles.In X (Add X T t) t). apply Union_intror. constructor. apply H0 in H. inversion H. 
Qed. 

Theorem CoupleNeqEmpty : forall X t1 t2, Couple X t1 t2 = Empty_set X -> False.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inv H. 
  assert(Ensembles.In X (Couple X t1 t2) t1). constructor. apply H0 in H. inversion H. Qed. 

Theorem ForkInd' : forall h H' t T T' tid2 tid2' s1 s2 s2' E M M' N N' i j j' l,
             decompose t E (fork N') -> 
             splitMultistep H' T (tSingleton(Tid(i,j')l,s1,s2,t))
                            (OK h T' (tUnion (tSingleton (Tid (i, j) l, fAct tid2 j' M'::s1, s2, M))
                                            (tSingleton (tid2', [specAct], s2', N)))) ->
             multistep H' (tSingleton(Tid(i,j')l,s1,s2,t)) T (OK h (tSingleton(Tid(i,j')l,s1,s2,t)) T').
Proof.
  intros. dependent induction H0. 
  {auto. }
  {econstructor. auto. apply decomposeEq in H. subst. eapply H1. eauto. }
  {apply SingletonEqUnion in H3. inversion H3. 
   {inv H4. inversion H1; subst; try solve[
    match goal with
      |H:tSingleton ?t = Empty_set ?x |- _ => apply SingletonNeqEmpty in H; inversion H
      |H:tCouple ?t1 ?t2 = Empty_set ?x |- _ => apply CoupleNeqEmpty in H; inversion H
      |H:tAdd ?T ?t = Empty_set ?x |- _ => apply AddNeqEmpty in H; inversion H
    end]. }
   {inv H4. 
    {inv H5. assert(h0=h'). admit. subst. eapply IHsplitMultistep; eauto. 

Hint Unfold tSingleton tUnion tCouple.

Theorem passThroughAct : forall a M M' i j j' T T' tid s1 s2 H H',
                           basicAction a M' j' ->
                           splitMultistep H T (unspecPoolAux (tSingleton(Tid(i,j)tid,a::s1,s2,M)))
                                          (OK H' T' (tSingleton(Tid(i,j)tid,a::s1,s2,M))) ->
                           exists T'' H'', 
                             splitMultistep H T (unspecPoolAux (tSingleton(Tid(i,j)tid,a::s1,s2,M)))
                                            (OK H'' T'' (tSingleton(Tid(i,j')tid,s1,s2,M'))). 
Admitted. 

Theorem rollbackWellFormed : forall tid As H T H' T', 
                               wellFormed H T -> rollback tid As H T H' T' ->
                               wellFormed H' T'. 
Proof.
  intros. induction H1; subst. 
  {assumption. }
  { 


admit. }
  {inversion H0; subst. inversion H4; subst. apply IHrollback. econstructor. eauto. eauto. destruct s1'. 
   {erewrite unspecAdd; eauto. unfold tAdd in *. unfold Add in *. unfold tCouple in H7.
    rewrite coupleUnion in H7. repeat rewrite unspecUnionComm in *. erewrite unspecSingleton in H7. 
    rewrite unspecPoolEmpty in H7; eauto. unfold tUnion in H7. rewrite union_empty in H7. 
    Focus 2. eapply unSpecFork; eauto. 


 apply multistepUnion in H7. eapply ForkInd' in H7. 
    rewrite moveToUnused. auto. copy H1. apply decomposeEq in H1. subst. eauto. }
   {unfold tCouple in H7. rewrite coupleUnion in H7. repeat rewrite unspecUnionComm in H7. 
    replace (unspecPoolAux (Singleton thread (tid2', [specAct], s2', N))) with tEmptySet in H7. 
    Focus 2. rewrite unspecPoolEmpty; eauto. unfold tUnion in H7. rewrite union_empty in H7. 
    


             




