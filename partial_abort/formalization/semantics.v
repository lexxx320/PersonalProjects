Require Export ast.     
Require Export Coq.Arith.Peano_dec. 
Require Export Omega. 

(*General Purpose tactics*)
Ltac inv H := inversion H; subst; clear H. 
Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 
Ltac invertHyp :=
  match goal with
      |H:exists x, ?P |- _ => inv H; try invertHyp
      |H: ?P /\ ?Q |- _ => inv H; try invertHyp
  end. 

(*evaluation context decomposition*)
Inductive decompose : term -> ctxt -> term -> Prop :=
|decompApp : forall e1 e2 E e, decompose e1 E e ->
                               decompose (app e1 e2) (appCtxt e2 E) e
|decompAppVal : forall v e2 E e, decompose e2 E e -> 
                                 value v -> decompose (app v e2) (appValCtxt v E) e
|appHole : forall e v, value v -> decompose (app (lambda e) v) hole (app (lambda e) v)
|decompGet : forall e E e', decompose e E e' -> 
                            decompose (get e) (getCtxt E) e'
|decompGetHole : forall l, decompose (get (loc l)) hole (get (loc l))
|decompPut : forall e1 e2 E e, decompose e1 E e -> 
                               decompose (put e1 e2) (putCtxt e2 E) e
|decompPutVal : forall v e2 E e, decompose e2 E e -> 
                                 value v -> decompose (put v e2) (putValCtxt v E) e
|decompPutHole : forall n v, value v -> decompose (put (loc n) v) hole (put (loc n) v)
|decompAlloc : forall e E e', decompose e E e' ->
                              decompose (alloc e) (allocCtxt E) e'
|decompAllocHole : forall v, value v -> decompose (alloc v) hole (alloc v)
|decompAtomicHole : forall e, decompose (atomic e) hole (atomic e)
|decompFork : forall e, decompose (fork e) hole (fork e)
|decompInAtomic : forall e e' E, decompose e E e' ->
                            decompose (inatomic e) (inatomicCtxt E) e'
|decompInAtomicHole : forall v, value v -> decompose (inatomic v) hole (inatomic v). 

(*fill an evaluation contenxt*)
Fixpoint fill (E:ctxt) (e:term) := 
  match E with
      |appCtxt e' E => app (fill E e) e'
      |appValCtxt v E => app v (fill E e)
      |getCtxt E => get (fill E e)
      |putCtxt e' E => put (fill E e) e'
      |putValCtxt v E => put v (fill E e)
      |allocCtxt E => alloc (fill E e)
      |inatomicCtxt E => inatomic (fill E e)
      |hole => e 
  end. 

Inductive validateRes : Type := 
|commit : validateRes
|abort : term -> validateRes. 

Fixpoint lookup (H:heap) (l:location) :=
  match H with
      |(l', v, stamp)::H' => if eq_nat_dec l l'
                            then Some (v, stamp)
                            else lookup H' l
      |nil => None
  end. 

(*Transactional log validation*)
Inductive validate : stamp -> log -> heap -> stamp -> heap -> 
                     log -> validateRes -> Prop :=
|validateNil : forall S S' H, validate S nil H S' H nil commit
|validateCommitRead : forall S S' S'' l v E H H' L,
                        lookup H l = Some(v, S') -> S > S' -> 
                        validate S L H S'' H' L commit ->
                        validate S (readItem l E::L) H S'' H' (readItem l E::L) commit
|validateAbortPropogate : forall S S' L H x L' e, 
                            validate S L H S' H L' (abort e) ->
                            validate S (x::L) H S' H L' (abort e)
|validateAbortRead : forall S S' S'' H L E H' l v,
              validate S L H S'' H' L commit -> lookup H l = Some(v, S') ->
              S' >= S -> validate S (readItem l E::L) H S'' H L 
                                (abort (fill E(get(loc l))))
|validateWrite : forall S S' L H H' l v,
                   validate S L H S' H' L commit ->
                   validate S (writeItem l v::L) H S' ((l, v, S')::H) (writeItem l v::L) commit. 

Fixpoint logLookup (L:log) (l:location) :=
  match L with
      |readItem _ _::L' => logLookup L' l
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

Inductive p_step : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|p_parLStep : forall C H T1 T2 C' H' T1', 
          p_step C H T1 C' H' T1' -> p_step C H (Par T1 T2) C' H' (Par T1' T2)
|p_parRStep : forall C H T1 T2 C' H' T2', 
          p_step C H T2 C' H' T2' -> p_step C H (Par T1 T2) C' H' (Par T1 T2')
|p_forkStep : forall C H E e t, 
              decompose t E (fork e) ->
              p_step C H (Single(None, nil, t)) C H 
                   (Par (Single(None, nil, fill E unit)) (Single(None, nil, e)))
|p_readStep : forall C H S S' L E l t v e0, 
              decompose t E (get (loc l)) -> logLookup L l = None ->
              lookup H l = Some(v, S') -> S > S' ->
              p_step C H (Single(Some(S, e0), L, t)) C H (Single(Some(S, e0), readItem l E::L, fill E v))
|p_readInDomainStep : forall C H S S' l v L E v' t e0,
                      decompose t E (get (loc l)) -> logLookup L l = Some v ->
                      lookup H l = Some(v', S') -> S > S' ->
                      p_step C H (Single(Some(S, e0), L, t)) C H (Single(Some(S, e0), L, fill E v))
|p_abortStep : forall L S H L' C e e0 e', 
           validate S L H 0 H L' (abort e') ->
           p_step C H (Single(Some(S, e0), L, e)) (plus 1 C) H (Single(Some(C, e0), L', e'))
|p_writeStep : forall C H S L E l v t,
               decompose t E (put (loc l) v) -> S <> None ->
               p_step C H (Single(S, L, t)) C H (Single(S, writeItem l v::L, fill E unit))
|p_allocStep : forall C H S L v E t l e0, 
               lookup H l = None -> decompose t E (alloc v) ->
               p_step C H (Single(Some(S, e0), L, t)) C ((l, v, S)::H)
                    (Single(Some(S, e0), L, fill E (loc l)))
|p_commitStep : forall C H S L v t E H' e0, 
                validate S L H C H' L commit -> decompose t E (inatomic v) ->
                p_step C H (Single(Some(S, e0), L, t)) (plus 1 C) H' (Single(None, nil, fill E v))
|p_atomicStep : forall C H E e t, 
                decompose t E (atomic e) ->
                p_step C H (Single(None, nil, t)) (plus 1 C) H (Single(Some(C, t), nil, fill E (inatomic e)))
|p_atomicIdemStemp : forall C H E e t L S,
                     decompose t E (atomic e) -> S <> None ->
                     p_step C H (Single(S, L, t)) C H (Single(S, L, fill E e))
|p_betaStep : forall C H L E e t v S, 
              decompose t E (app (lambda e) v) -> 
              p_step C H (Single(S, L, t)) C H (Single(S, L, open e 0 v)). 

Inductive p_multistep : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|p_multi_refl : forall C H T, p_multistep C H T C H T
|p_multi_step : forall C H T C' H' T' C'' H'' T'', 
                p_step C H T C' H' T' -> p_multistep C' H' T' C'' H'' T'' ->
                p_multistep C H T C'' H'' T''. 

Inductive f_step : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|f_parLStep : forall C H T1 T2 C' H' T1', 
          f_step C H T1 C' H' T1' -> f_step C H (Par T1 T2) C' H' (Par T1' T2)
|f_parRStep : forall C H T1 T2 C' H' T2', 
          f_step C H T2 C' H' T2' -> f_step C H (Par T1 T2) C' H' (Par T1 T2')
|f_forkStep : forall C H E e t, 
              decompose t E (fork e) ->
              f_step C H (Single(None, nil, t)) C H 
                   (Par (Single(None, nil, fill E unit)) (Single(None, nil, e)))
|f_readStep : forall C H S S' L E l t v e0, 
              decompose t E (get (loc l)) -> logLookup L l = None ->
              lookup H l = Some(v, S') -> S > S' ->
              f_step C H (Single(Some(S, e0), L, t)) C H (Single(Some(S, e0), readItem l E::L, fill E v))
|f_readInDomainStep : forall C H S S' l v L E v' t e0,
                      decompose t E (get (loc l)) -> logLookup L l = Some v ->
                      lookup H l = Some(v', S') -> S > S' ->
                      f_step C H (Single(Some(S, e0), L, t)) C H (Single(Some(S, e0), L, fill E v))
|f_abortStep : forall L S H L' C e e0 e', 
           validate S L H 0 H L' (abort e') ->
           f_step C H (Single(Some(S, e0), L, e)) (plus 1 C) H (Single(Some(C, e0), nil, e0))
|f_writeStep : forall C H S L E l v t,
               decompose t E (put (loc l) v) -> S <> None ->
               f_step C H (Single(S, L, t)) C H (Single(S, writeItem l v::L, fill E unit))
|f_allocStep : forall C H S L v E t l e0, 
               lookup H l = None -> decompose t E (alloc v) ->
               f_step C H (Single(Some(S, e0), L, t)) C ((l, v, S)::H)
                    (Single(Some(S, e0), L, fill E (loc l)))
|f_commitStep : forall C H S L v t E H' e0, 
                validate S L H C H' L commit -> decompose t E (inatomic v) ->
                f_step C H (Single(Some(S, e0), L, t)) (plus 1 C) H' (Single(None, nil, fill E v))
|f_atomicStep : forall C H E e t, 
                decompose t E (atomic e) ->
                f_step C H (Single(None, nil, t)) (plus 1 C) H (Single(Some(C, t), nil, fill E (inatomic e)))
|f_atomicIdemStemp : forall C H E e t L S,
                     decompose t E (atomic e) -> S <> None ->
                     f_step C H (Single(S, L, t)) C H (Single(S, L, fill E e))
|f_betaStep : forall C H L E e t v S, 
              decompose t E (app (lambda e) v) -> 
              f_step C H (Single(S, L, t)) C H (Single(S, L, open e 0 v)). 

Inductive f_multistep : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|f_multi_refl : forall C H T, f_multistep C H T C H T
|f_multi_step : forall C H T C' H' T' C'' H'' T'', 
                f_step C H T C' H' T' -> f_multistep C' H' T' C'' H'' T'' ->
                f_multistep C H T C'' H'' T''. 
Inductive tIn : pool -> thread -> Prop :=
|in_single : forall t, tIn (Single t) t
|in_left : forall T1 T2 t, tIn T1 t -> tIn (Par T1 T2) t
|in_right : forall T1 T2 t, tIn T2 t -> tIn (Par T1 T2) t. 

Inductive p_threadWF : nat -> heap -> thread -> Prop :=
|noTSValid : forall n H e, p_threadWF n H (None, nil, e)
|threadWFValid : forall S S' C L H H' L' e0 e, 
                   validate S L H S' H' L' commit ->
                   p_multistep C H (Single(Some(S,e0), nil, e0))
                               C H (Single(Some(S,e0), L, e)) ->
                   p_threadWF C H (Some(S, e0), L, e)
|threadWFInvalid : forall S S' C L H H' L' e e0 e',
                     validate S L H S' H' L' (abort e) ->
                     p_multistep C H (Single(Some(S,e0), nil, e0))
                                 C H (Single(Some(S,e0), L', e)) ->
                     p_threadWF C H (Some(S,e0), L, e'). 
                     
Inductive p_poolWF : nat -> heap -> pool -> Prop :=
|p_poolWF_ : forall C H T, (forall t, tIn T t -> p_threadWF C H t) -> p_poolWF C H T. 

Theorem p_wfPar_l : forall T1 T2 C H, 
                      p_poolWF C H (Par T1 T2) -> 
                      p_poolWF C H T1. 
Proof.
  intros. inv H0. constructor. intros. assert(tIn (Par T1 T2) t). 
  constructor. assumption. apply H2 in H1. assumption. 
Qed. 

Theorem p_wfPar_r : forall T1 T2 C H, 
                      p_poolWF C H (Par T1 T2) -> 
                      p_poolWF C H T2. 
Proof.
  intros. inv H0. constructor. intros. assert(tIn (Par T1 T2) t). 
  apply in_right. assumption. apply H2 in H1. assumption. 
Qed. 

Theorem p_wfParConj : forall C H T1 T2, 
                        p_poolWF C H T1 -> p_poolWF C H T2 ->
                        p_poolWF C H (Par T1 T2). 
Proof.
  intros. constructor. intros. inv H0. inv H1. 
  inv H2. apply H4 in H6. assumption. apply H3 in H6. assumption. 
Qed. 
Theorem commitLogUnchanged : forall S L H S' H' L', 
                               validate S L H S' H' L' commit ->
                               L = L'. 
Proof.
  intros. remember commit. induction H0; auto; inv Heqv. 
Qed. 

Theorem abortHeapUnchanged : forall S L H S' H' L' t, 
                               validate S L H S' H' L' (abort t) ->
                               H = H'. 
Proof.
  intros. remember (abort t). induction H0; auto. inv Heqv. 
Qed. 

Ltac InTac :=
  match goal with
    |H:forall t, tIn (Single ?T) t -> ?x |- _ => 
     assert(INHYP:tIn (Single T) T) by constructor; 
       apply H in INHYP
  end. 

Theorem p_multi_trans : forall C H T C' H' T' C'' H'' T'',
                          p_multistep C H T C' H' T' ->
                          p_multistep C' H' T' C'' H'' T'' ->
                          p_multistep C H T C'' H'' T''. 
Proof.
  intros. induction H0; auto. econstructor. eassumption. eauto. 
Qed. 

Theorem validateFailCons : forall S L H S' H' L' e item, 
                             validate S L H S' H' L' (abort e) ->
                             validate S (item::L) H S' H' L' (abort e). 
Proof.
  intros. remember (abort e). generalize dependent item. 
  induction H0; try solve[inv Heqv]; intros. 
  {eapply validateAbortPropogate. apply IHvalidate. assumption. }
  {eapply validateAbortPropogate. eapply validateAbortRead; eauto. }
Qed. 

Theorem validateFailApp : forall L'' S L H S' H' L' e, 
                             validate S (L'' ++ L) H S' H' L' (abort e) ->
                             validate S L' H S' H' L' commit.
Proof.
  Admitted. 

Theorem abortLogPostfix : forall S L H S' H' L' e, 
                            validate S L H S' H' L' (abort e) ->
                            exists L'', L = L'' ++ L'. 
Proof.
  intros. induction H0; try solve[exists nil; eauto].   
  {invertHyp. exists (x::x0). auto. }
  {inversion IHvalidate. exists ([readItem l E]). auto. }
Qed. 

Theorem stepWF : forall C H T C' H' T', 
                   p_poolWF C H T ->
                   p_step C H T C' H' T' -> 
                   p_poolWF C' H' T'. 
Proof.
  intros. induction H1.
  {copy H0. apply p_wfPar_l in H0. apply IHp_step in H0. 
   apply p_wfPar_r in H2. apply p_wfParConj. assumption. 
   admit. }
  {admit. }
  {constructor. intros. inv H2. inv H6. constructor. inv H6. constructor. }
  {constructor. intros. inv H0. inv H5. InTac. inv INHYP. 
   {econstructor. eapply validateCommitRead; eauto. copy H10. 
    apply commitLogUnchanged in H0. subst. eassumption. eapply p_multi_trans. 
    eassumption. econstructor. eapply p_readStep; eauto. constructor. }
   {eapply threadWFInvalid. eapply validateFailCons. eauto. assumption. }
  }
  {constructor. intros. inv H0. inv H5. InTac. inv INHYP. 
   {econstructor. eassumption. eapply p_multi_trans. eassumption. econstructor. 
    eapply p_readInDomainStep; eauto. constructor. }
   {eapply threadWFInvalid; eauto. }
  }
  {constructor. intros. inv H0. inv H2. copy H1. eapply abortLogPostfix in H1.
   




Theorem p_thread_wf_anyHeap : forall C H C' H' t, 
                         p_threadWF C H t ->
                         p_threadWF C' H' t. 
Proof.
  intros. inv H0. 
  {constructor. }
  {eapply threadWFValid. 

Theorem validateHeapMonotonic : forall S H C H' L res,
                                    validate S L H C H' L res  ->
                                    exists H'', H' = H'' ++ H .
Proof.
  intros. induction H0; eauto; try solve[exists nil; eauto].  
  {exists [(l,v,S')]. simpl. reflexivity. }
Qed. 

Theorem heapMonotonic : forall C H T C' H' T', 
                         p_step C H T C' H' T' ->
                         exists H'', H' = H'' ++ H. 
Proof.
  intros. induction H0; eauto; try solve[exists nil; auto].  
  {exists [(l,v,S)]. simpl. reflexivity. }
  {apply validateHeapMonotonic in H0. invertHyp. exists x. auto. }
Qed. 

Theorem lookupExtension : forall Hnew H l v S, 
                            lookup H l  = Some(v, S) ->
                            exists v' S', lookup (Hnew++H) l = Some(v', S'). 
Proof.
  induction Hnew; intros. 
  {simpl. exists v. exists S. assumption. }
  {simpl. destruct a. destruct p. destruct (eq_nat_dec l l0). 
   {subst. exists t. exists s. reflexivity. }
   {eapply IHHnew in H0. invertHyp. exists x. exists x0. assumption. }
  }
Qed.

Theorem gt_dec : forall n n', {n > n'} + {n' >= n}. 
Proof. 
  induction n; intros.  
  {destruct n'. right. omega. right. omega. }
  {destruct n'. left. omega. specialize(IHn n'). inv IHn. 
   left. omega. right. omega. }
Qed. 

Theorem appPostfix : forall (A:Type) (b a : list A), a++b = b -> a = nil. 
Proof.
  induction b; intros. 
  {destruct a. auto. simpl in H. inv H. }
  {apply IHb. destruct a0. simpl. auto. simpl in H. inversion H. 
   


 
Theorem validateHeapExtension : forall S L H S' H' L' res H'' new, 
                      validate S L H S' H' L' res ->
                      H'' = new ++ H ->
                      exists Hnew Lnew res', validate S L H'' S' Hnew Lnew res' /\ 
                                        exists prefix, L' = prefix ++ Lnew.
Proof.
  intros. generalize dependent new. generalize dependent H''. induction H0; intros. 
  {do 4 econstructor. constructor. exists nil. auto. }
  {copy H0. eapply lookupExtension with (Hnew := new) in H0. invertHyp.  
   destruct (gt_dec S x0). 
   {assert(new++H=new++H). auto. apply IHvalidate in H3. invertHyp. 
    destruct x3. 
    {copy H3. apply commitLogUnchanged in H3. 

 subst. econstructor. econstructor. 
     econstructor. eapply validateCommitRead; eauto. }
    {econstructor. econstructor. econstructor. eapply validateAbortPropogate.
     copy H5. apply abortHeapUnchanged in H3. subst. eassumption. }
   }
   {assert(new++H=new++H). auto. apply IHvalidate in H3. invertHyp. destruct x3. 
    {copy H5. apply commitLogUnchanged in H3. subst. econstructor. econstructor. 
     econstructor. eapply validateAbortRead; eauto. }
    {econstructor. econstructor. econstructor. eapply validateAbortPropogate.
     copy H5. apply abortHeapUnchanged in H3. subst. eassumption. }
   }
  }
  {assert(new++H=new++H). auto. apply IHvalidate in H2. invertHyp. econstructor. 
   econstructor. econstructor. eapply validateAbortPropogate.
   copy H2. apply abortHeapUnchanged in H1. subst. eauto. 
   



Theorem p_wf_anyHeap : forall C H C' H' T, 
                         p_poolWF C H T ->
                         p_poolWF C' H' T. 
Proof.
  intros. inv H0. constructor. intros. apply H2 in H0. 























