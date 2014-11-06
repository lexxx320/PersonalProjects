Require Export heap.     
Require Export Omega. 
Require Export hetList. 
Require Export Coq.Program.Equality. 
Require Export Coq.Logic.ProofIrrelevance. 

Ltac solveByInv :=
  match goal with
      |H:_ |- _ => solve[inv H]
  end. 


(*evaluation context decomposition*)
Inductive decompose : term -> ctxt -> term -> Prop :=
|decompApp : forall e1 e2 E e, decompose e1 E e ->
                               decompose (app e1 e2) (appCtxt e2 E) e
|decompAppVal : forall v e2 E e (prf:value v), 
                  decompose e2 E e -> decompose (app v e2) (appValCtxt v prf E) e
|appHole : forall e v, value v -> decompose (app (lambda e) v) hole (app (lambda e) v)
|decompGet : forall e E e', decompose e E e' -> 
                            decompose (get e) (getCtxt E) e'
|decompGetHole : forall l, decompose (get (loc l)) hole (get (loc l))
|decompPut : forall e1 e2 E e, decompose e1 E e -> 
                               decompose (put e1 e2) (putCtxt e2 E) e
|decompPutVal : forall v e2 E e (prf:value v), 
                  decompose e2 E e -> 
                  decompose (put v e2) (putValCtxt v prf E) e
|decompPutHole : forall n v, value v -> decompose (put (loc n) v) hole (put (loc n) v)
|decompAlloc : forall e E e', decompose e E e' ->
                              decompose (alloc e) (allocCtxt E) e'
|decompAllocHole : forall v, value v -> decompose (alloc v) hole (alloc v)
|decompAtomicHole : forall e, decompose (atomic e) hole (atomic e)
|decompFork : forall e, decompose (fork e) hole (fork e)
|decompInAtomic : forall e e' E, decompose e E e' ->
                            decompose (inatomic e) (inatomicCtxt E) e'
|decompInAtomicHole : forall v, value v -> decompose (inatomic v) hole (inatomic v). 

Theorem decomposeValFalse : forall t E e, value t -> decompose t E e -> False. 
Proof.
  intros. inv H0; try solve[inv H]. 
Qed. 

Ltac decompVal :=
  match goal with
      |H:value ?t, H':decompose ?t ?E ?e |- _ => 
       apply decomposeValFalse in H'; auto; inv H'
  end. 

Theorem decomposeDeterministic : forall t E E' e e', 
                                   decompose t E e -> decompose t E' e' ->
                                   E = E' /\ e = e'. 
Proof.
  intros. genDeps {{E'; e'}}. induction H; intros.
  {inv H0. eapply IHdecompose in H5. invertHyp. auto. decompVal. inv H. }
  {inv H0; try decompVal. eapply IHdecompose in H5. invertHyp.
   assert(prf=prf0). apply proof_irrelevance. subst. auto. }
  {inv H0. inv H5. decompVal. auto. }
  {inv H0. eapply IHdecompose in H2. invertHyp. auto. inv H. }
  {inv H0. inv H1. auto. }
  {inv H0. eapply IHdecompose in H5. invertHyp. eauto. decompVal. inv H. }
  {inv H0. decompVal. eapply IHdecompose in H5. invertHyp.
   assert(prf=prf0). apply proof_irrelevance. subst. auto. decompVal. }
  {inv H0. inv H5. decompVal. auto. }
  {inv H0. eapply IHdecompose in H2. invertHyp. auto. decompVal. }
  {inv H0. decompVal. auto. }
  {inv H0. auto. }
  {inv H0. auto. }
  {inv H0. eapply IHdecompose in H2. invertHyp. auto. decompVal. }
  {inv H0. decompVal. auto. }
Qed.  

Ltac decompSame :=
  match goal with
      |H:decompose ?t ?E ?e,H':decompose ?t ?E' ?e' |- _ =>
       eapply decomposeDeterministic in H; eauto; invertHyp
  end.  

(*fill an evaluation contenxt*)
Fixpoint fill (E:ctxt) (e:term) := 
  match E with
      |appCtxt e' E => app (fill E e) e'
      |appValCtxt v _ E => app v (fill E e)
      |getCtxt E => get (fill E e)
      |putCtxt e' E => put (fill E e) e'
      |putValCtxt v _ E => put v (fill E e)
      |allocCtxt E => alloc (fill E e)
      |inatomicCtxt E => inatomic (fill E e)
      |hole => e 
  end.
Inductive validateRes : Type := 
|commit : heap -> validateRes
|abort : term -> log -> validateRes. 

(*Transactional log validation*)
Inductive validate : stamp -> log -> heap -> stamp -> validateRes -> Prop :=
|validateNil : forall S S' H, validate S nil H S' (commit H)
|validateCommitRead : forall S S' S'' l v E H H' L,
                        lookup H l = Some(v, S') -> S > S' -> 
                        validate S L H S'' (commit H') ->
                        validate S (readItem l E v::L) H S'' (commit H')
|validateAbortPropogate : forall S S' L H x L' e, 
                            validate S L H S' (abort e L') ->
                            validate S (x::L) H S' (abort e L')
|validateAbortRead : forall S S' S'' H L E H' l v v',
              validate S L H S'' (commit H') -> lookup H l = Some(v, S') ->
              S' >= S -> validate S (readItem l E v'::L) H S'' 
                                (abort (fill E(get(loc l))) L)
|validateWrite : forall S S' L H H' l v,
                   validate S L H S' (commit H') ->
                   validate S (writeItem l v::L) H S' (commit ((l, v, S')::H'))
.

Fixpoint logLookup (L:log) (l:location) :=
  match L with
      |readItem _ _ _::L' => logLookup L' l
      |writeItem l' v::L' => if eq_nat_dec l l'
                            then Some v
                            else logLookup L' l
      |nil => None
  end. 

Fixpoint open (e:term) (k:nat) (e':term) :=
  match e with
      |lambda e => lambda (open e (S k) e')
      |loc l => loc l
      |unit => unit
      |var k' => if eq_nat_dec k k'
                then e'
                else var k'
      |app e1 e2 => app (open e1 k e') (open e2 k e')
      |get e => get (open e k e')
      |put e1 e2 => put (open e1 k e') (open e2 k e')
      |alloc e => alloc (open e k e')
      |fork e => fork (open e k e')
      |atomic e => atomic (open e k e')
      |inatomic e => inatomic (open e k e')
  end. 
 
Inductive trans_step (H:heap) : thread -> thread -> Prop :=
|t_readStep : forall S L E l t v e0 S', 
                decompose t E (get (loc l)) -> logLookup L l = None ->
                lookup H l = Some(v, S') -> 
                trans_step H (Some(S, e0), L, t) 
                             (Some(S, e0), readItem l E v::L, fill E v)
|t_readInDomainStep : forall S l v L E t e0,
                      decompose t E (get (loc l)) -> logLookup L l = Some v ->
                      trans_step H (Some(S, e0), L, t) (Some(S, e0), L, fill E v)
|t_writeStep : forall S L E l v t,
               decompose t E (put (loc l) v) -> S <> None ->
               trans_step H (S, L, t) (S, writeItem l v::L, fill E unit)
|t_atomicIdemStep : forall E e t L S,
                     decompose t E (atomic e) -> S <> None ->
                     trans_step H (S, L, t) (S, L, fill E e)
|t_betaStep : forall L E e t v S, 
              decompose t E (app (lambda e) v) -> S <> None ->
              trans_step H (S, L, t) (S, L, fill E (open e 0 v))
.

Inductive rewind_step : thread -> thread -> Prop :=
|r_readStep : forall S L E l t v e0, 
                decompose t E (get (loc l)) -> logLookup L l = None ->
                rewind_step (Some(S, e0), L, t) (Some(S, e0), readItem l E v::L, fill E v)
|r_readInDomainStep : forall S l v L E t e0,
                      decompose t E (get (loc l)) -> logLookup L l = Some v ->
                      rewind_step (Some(S, e0), L, t) (Some(S, e0), L, fill E v)
|r_writeStep : forall S L E l v t,
               decompose t E (put (loc l) v) -> S <> None ->
               rewind_step (S, L, t) (S, writeItem l v::L, fill E unit)
|r_atomicIdemStep : forall E e t L S,
                     decompose t E (atomic e) -> S <> None ->
                     rewind_step (S, L, t) (S, L, fill E e)
|r_betaStep : forall L E e t v S, 
              decompose t E (app (lambda e) v) -> S <> None ->
              rewind_step (S, L, t) (S, L, fill E (open e 0 v))
.

Inductive rewind : thread -> thread -> Prop :=
|rewindRefl : forall t, rewind t t
|rewindStep : forall t t' t'', 
                rewind_step t' t'' -> rewind t t' -> 
                rewind t t''. 

(*If inversion produces the same hypothesis, skip it, otherwise invert all equalities*)
Ltac invertEq :=
  match goal with
      |H:?a = ?b |- _ => let n := fresh
                         in inversion H as n; match type of n with
                                                  |?a = ?b => fail
                                              end
      |H:?a = ?b |- _ => inv H
  end. 

Theorem trans_stepDeterministic : forall H t t' t'',
                                    trans_step H t t' -> trans_step H t t'' -> 
                                    t' = t''. 
Proof.
  intros. inv H0; inv H1; eauto; decompSame; invertEq; repeat(
          match goal with
              |A:lookup ?H ?l = ?v, B:lookup ?H ?l = ?v' |- _ =>
               rewrite A in B; inv B
              |H:logLookup ?L ?l = ?v,H':logLookup ?L ?l = ?v' |- _ =>
               rewrite H in H'; inv H'
          end); eauto. 
Qed. 

Inductive p_step : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|p_transStep : forall C H t t', trans_step H t t' -> 
                           p_step C H (Single t) C H (Single t')
|p_parLStep : forall C H T1 T2 C' H' T1', 
          p_step C H T1 C' H' T1' -> p_step C H (Par T1 T2) C' H' (Par T1' T2)
|p_parRStep : forall C H T1 T2 C' H' T2', 
          p_step C H T2 C' H' T2' -> p_step C H (Par T1 T2) C' H' (Par T1 T2')
|p_forkStep : forall C H E e t, 
              decompose t E (fork e) ->
              p_step C H (Single(None, nil, t)) C H 
                   (Par (Single(None, nil, fill E unit)) (Single(None, nil, e)))

|p_abortStep : forall L S H L' C e e0 e' S', 
           validate S L H S' (abort e' L') ->
           p_step C H (Single(Some(S, e0), L, e))
                  (plus 1 C) H (Single(Some(C, e0), L', e'))
|p_allocStep : forall C H v E t l, 
               lookup H l = None -> decompose t E (alloc v) ->
               p_step C H (Single(None, nil, t)) (plus 1 C) ((l, v, C)::H)
                    (Single(None, nil, fill E (loc l)))
|p_commitStep : forall C H S L v t E H' e0, 
                validate S L H C (commit H') -> decompose t E (inatomic v) ->
                p_step C H (Single(Some(S, e0), L, t)) (plus 1 C) H' (Single(None, nil, fill E v))
|p_atomicStep : forall C H E e t, 
                decompose t E (atomic e) ->
                p_step C H (Single(None, nil, t)) (plus 1 C) H 
                       (Single(Some(C, fill E(inatomic e)),[],fill E (inatomic e)))
|p_betaStep : forall C H E e t v, 
              decompose t E (app (lambda e) v) -> 
              p_step C H (Single(None, nil, t)) C H
                     (Single(None, nil, fill E (open e 0 v))). 

Inductive p_multistep : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|p_multi_refl : forall C H T, p_multistep C H T C H T
|p_multi_step : forall C H T C' H' T' C'' H'' T'', 
                p_step C H T C' H' T' -> p_multistep C' H' T' C'' H'' T'' ->
                p_multistep C H T C'' H'' T''. 

Inductive f_step : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|f_transStep : forall C H t t', trans_step H t t' -> 
                           f_step C H (Single t) C H (Single t')
|f_parLStep : forall C H T1 T2 C' H' T1', 
          f_step C H T1 C' H' T1' -> f_step C H (Par T1 T2) C' H' (Par T1' T2)
|f_parRStep : forall C H T1 T2 C' H' T2', 
          f_step C H T2 C' H' T2' -> f_step C H (Par T1 T2) C' H' (Par T1 T2')
|f_forkStep : forall C H E e t, 
              decompose t E (fork e) ->
              f_step C H (Single(None, nil, t)) C H 
                   (Par (Single(None, nil, fill E unit)) (Single(None, nil, e)))
|f_abortStep : forall L S H L' C e e0 e' S', 
           validate S L H S' (abort e' L') ->
           f_step C H (Single(Some(S, e0), L, e)) (plus 1 C) H (Single(Some(C, e0), nil, e0))
|f_allocStep : forall C H v E t l, 
               lookup H l = None -> decompose t E (alloc v) ->
               f_step C H (Single(None, nil, t)) (plus 1 C) ((l, v, C)::H)
                    (Single(None, nil, fill E (loc l)))
|f_commitStep : forall C H S L v t E H' e0, 
                validate S L H C (commit H') -> decompose t E (inatomic v) ->
                f_step C H (Single(Some(S, e0), L, t)) (plus 1 C) H' (Single(None, nil, fill E v))
|f_atomicStep : forall C H E e t, 
                decompose t E (atomic e) ->
                f_step C H (Single(None, nil, t)) (plus 1 C) H 
                       (Single(Some(C, fill E (inatomic e)), nil, fill E (inatomic e)))
|f_betaStep : forall C H E e t v, 
              decompose t E (app (lambda e) v) -> 
              f_step C H (Single(None, nil, t)) C H 
                     (Single(None, nil, fill E (open e 0 v))). 

Inductive f_multistep : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|f_multi_refl : forall C H T, f_multistep C H T C H T
|f_multi_step : forall C H T C' H' T' C'' H'' T'', 
                f_step C H T C' H' T' -> f_multistep C' H' T' C'' H'' T'' ->
                f_multistep C H T C'' H'' T''. 

Inductive trans_multistep H : thread -> thread -> Prop :=
|trans_refl : forall t, trans_multistep H t t
|trans_multi_step : forall t t' t'', 
                      trans_step H t t' -> trans_multistep H t' t'' ->
                      trans_multistep H t t''. 

Definition postfix {A:Type} (L1 L2 : list A) := exists diff, L2 = diff ++ L1. 

Inductive poolRewind : pool -> Prop :=
|rewindSingleNoTX : forall e, poolRewind (Single(None,nil,e))
|rewindSingleInTX : forall S e0 L e, 
                      rewind (Some(S,e0),nil,e0) (Some(S,e0),L,e) ->
                      poolRewind (Single(Some(S,e0),L,e))
|rewindPar : forall T1 T2, poolRewind T1 -> poolRewind T2 -> poolRewind (Par T1 T2). 

Theorem f_multi_L : forall C H T1 T2 T1' C' H', 
                      f_multistep C H T1 C' H' T1' ->
                      f_multistep C H (Par T1 T2) C' H' (Par T1' T2). 
Proof.
  intros. induction H0.
  {constructor. }
  {econstructor. eapply f_parLStep. eassumption. eassumption. }
Qed. 

Theorem f_multi_R : forall C H T1 T2 T2' C' H', 
                      f_multistep C H T2 C' H' T2' ->
                      f_multistep C H (Par T1 T2) C' H' (Par T1 T2'). 
Proof.
  intros. induction H0.
  {constructor. }
  {econstructor. eapply f_parRStep. eassumption. eassumption. }
Qed. 

Theorem validateValidate : forall S L H S' L' e, 
                             validate S L H S' (abort e L') ->
                             exists H'', validate S L' H S' (commit H''). 
Proof.
  intros. dependent induction H0. 
  {invertHyp. exists x0. auto. }
  {exists H'. assumption. }
Qed. 

Theorem abortLogPostfix : forall S L H S' L' e, 
                            validate S L H S' (abort e L') ->
                           postfix L' L. 
Proof.
  intros. remember (abort e L'). induction H0; try solve[inv Heqv].   
  {apply IHvalidate in Heqv. unfold postfix in *. invertHyp. exists (x::x0). auto. }
  {inv Heqv. unfold postfix. exists [readItem l E v']. auto. }
Qed.
 
Theorem getAbortedAct : forall S L S' H L' e,
                         validate S L H S' (abort e L') ->
                         exists l E L'' v, L = L'' ++ [readItem l E v] ++ L' /\ 
                                            e = fill E (get (loc l)).
Proof.
  intros. dependent induction H0.
  {invertHyp. exists x0. exists x1. exists (x::x2). exists x3. split; auto. }
  {exists l. exists E. exists nil. exists v'. split; auto. }
Qed. 

Theorem decomposeEq : forall E t e, decompose t E e -> t = fill E e. 
Proof.
  induction E; intros; try solve[inv H; simpl;erewrite <- IHE; eauto]. 
  {inv H; auto. }
Qed. 

Theorem lengthsEq : forall (A:Type) (x y : list A), x = y -> length x = length y. 
Proof.
  induction x; intros. 
  {destruct y. auto. inv H. }
  {destruct y. inv H. inv H. simpl. apply f_equal. auto. }
Qed. 

Theorem lastElemEq : forall (A:Type) (l1 l2 : list A) e1 e2, 
                       l1++[e1] = l2 ++ [e2] -> l1 = l2 /\ e1 = e2 .
Proof.
  induction l1; intros; destruct l2.
  {inv H. auto . }
  {inv H. destruct l2; inv H2. }
  {inv H. destruct l1; inv H2. }
  {inv H. eapply IHl1 in H2. invertHyp. auto. }
Qed. 

Theorem destructEnd : forall (A:Type) (x:list A),
                      x = nil \/ exists x' e, x = x' ++ [e]. 
Proof.
  induction x; intros. 
  {auto. }
  {inv IHx. right. exists nil. simpl. exists a. auto. invertHyp. right. 
   exists (a::x0). exists x1. auto. }
Qed. 

Ltac destrEnd x := let n := fresh
                   in assert(n:x=nil \/ exists x' e, x = x' ++ [e]) by apply destructEnd; inv n.
 
Theorem abortRewind : forall S L H S' e' L' e0 e,
                        validate S L H S' (abort e' L') ->
                        rewind (Some (S, e0), [], e0) (Some (S, e0), L, e) ->
                        rewind (Some (S, e0), [], e0) (Some (S, e0), L', e'). 
Proof.
  intros. dependent induction H1. 
  {inv H0. }
  {inv H2; eauto. 
   {inv H0. 
    {eapply IHrewind; eauto. }
    {apply decomposeEq in H6. subst. auto. }
   }
   {inv H0. eauto. }
  }
Qed. 

Theorem rewindDiffStamp : forall S L S' e0 e,
                        rewind (Some (S, e0), [], e0) (Some (S, e0), L, e) ->
                        rewind (Some (S', e0), [], e0) (Some (S', e0), L, e). 
Proof.
  intros. dependent induction H.
  {constructor. }
  {inv H. 
   {econstructor. eapply r_readStep; eauto. eauto. }
   {econstructor. eapply r_readInDomainStep; eauto. eauto. }
   {econstructor. eapply r_writeStep; eauto. intros c. inv c. eauto. }
   {econstructor. eapply r_atomicIdemStep; eauto. intros c. inv c. eauto. }
   {econstructor. eapply r_betaStep; eauto. intros c. inv c. eauto. }
  }
Qed. 

Theorem stepRewind : forall C H T C' H' T', 
                       p_step C H T C' H' T' -> poolRewind T ->
                       poolRewind T'. 
Proof.
  intros. induction H0; try solve[repeat econstructor]. 
  {inv H1. inv H0; exfalso; apply H6; auto. inv H0. 
   {constructor. econstructor; eauto.  eapply r_readStep; eauto. }
   {constructor. econstructor; eauto. eapply r_readInDomainStep; eauto. }
   {econstructor. econstructor; eauto. eapply r_writeStep; eauto. }
   {econstructor. econstructor; eauto. eapply r_atomicIdemStep; eauto. }
   {econstructor. econstructor; eauto. eapply r_betaStep; eauto. }
  }
  {inv H1. constructor; auto. }
  {inv H1. constructor; auto. }
  {inv H1. constructor. eapply abortRewind in H0; eauto. 
   eapply rewindDiffStamp; eauto. }
Qed. 

Inductive f_multistepL : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|f_multi_reflL : forall C H T, f_multistepL C H T C H T
|f_multi_stepL : forall C H T C' H' T' C'' H'' T'', 
                f_step C' H' T' C'' H'' T'' -> f_multistepL C H T C' H' T' ->
                f_multistepL C H T C'' H'' T''. 

Theorem f_multistepLTrans : forall C H T C' H' T' C'' H'' T'', 
                              f_multistepL C H T C' H' T' ->
                              f_multistepL C' H' T' C'' H'' T'' ->
                              f_multistepL C H T C'' H'' T''.
Proof.
  intros. induction H1; auto. econstructor; eauto. 
Qed. 

Theorem f_multistepTrans : forall  C H T C' H' T' C'' H'' T'', 
                             f_multistep C H T C' H' T' ->
                             f_multistep C' H' T' C'' H'' T'' ->
                             f_multistep C H T C'' H'' T''.
Proof.
  intros. induction H0; auto. econstructor; eauto. 
Qed. 

Theorem f_multiLEq : forall C H T C' H' T', 
                       f_multistep C H T C' H' T' <-> 
                       f_multistepL C H T C' H' T'. 
Proof.
  intros. split; intros. 
  {induction H0. constructor. eapply f_multistepLTrans. 
   Focus 2. eauto. econstructor. eauto. constructor. }
  {induction H0. constructor. eapply f_multistepTrans; eauto. 
   econstructor. eauto. constructor. }
Qed. 

Theorem f_multiRewind : forall S L H S' H' C C' e0  e,
                          validate S L H S' (commit H') ->
                          rewind (Some (S, e0), [], e0) (Some (S, e0), L, e) ->
                          f_multistepL C H (Single(Some (C', e0), [], e0)) 
                                      C H (Single(Some (C', e0), L,e)).
Proof.
  intros. generalize dependent H'. dependent induction H1; intros. 
  {inv H0. constructor. }
  {inv H0. 
   {inv H2. econstructor. eapply f_transStep.
    eapply t_readStep; eauto. eauto. }
   {econstructor. eapply f_transStep. eapply t_readInDomainStep; eauto. 
    eauto. }
   {econstructor. eapply f_transStep. eapply t_writeStep; eauto. intros c. 
    inv c. inv H2. eauto. }
   {econstructor. eapply f_transStep. eapply t_atomicIdemStep; eauto. intros c. 
    inv c. eauto. }
   {econstructor. eapply f_transStep. eapply t_betaStep; eauto. intros c. 
    inv c. eauto. }
  }
Qed. 

Theorem partialImpliesFull : forall C H T C' H' T', 
                               p_step C H T C' H' T' -> poolRewind T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0.
  {econstructor. eapply f_transStep. eauto. constructor. }
  {inv H1. apply IHp_step in H4. apply f_multi_L. auto. }
  {inv H1. apply IHp_step in H5. apply f_multi_R. auto. }
  {inv H1. econstructor. eapply f_forkStep; eauto. constructor. }
  {copy H0. inv H1. eapply abortRewind in H2; eauto. copy H0. 
   apply validateValidate in H1. invertHyp. econstructor.
   eapply f_abortStep; eauto. rewrite f_multiLEq.
   eapply f_multiRewind; eauto. }
  {econstructor. eapply f_allocStep; eauto. constructor. }
  {econstructor. eapply f_commitStep; eauto. constructor. }
  {econstructor. eapply f_atomicStep; eauto. constructor. }
  {econstructor. eapply f_betaStep; eauto. constructor. }
Qed. 

Theorem partialImpliesFullMulti : forall C H T C' H' T', 
                               p_multistep C H T C' H' T' -> poolRewind T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0. 
  {constructor. }
  {copy H0. apply stepRewind in H0; auto. apply IHp_multistep in H0.
   eapply partialImpliesFull in H3; eauto. 
   eapply f_multistepTrans; eauto. }
Qed. 



