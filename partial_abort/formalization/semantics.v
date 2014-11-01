Require Export heap.     
Require Export Omega. 
Require Export hetList. 
Require Export Coq.Program.Equality. 

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
|p_allocStep : forall C H v E t l, 
               lookup H l = None -> decompose t E (alloc v) ->
               p_step C H (Single(None, nil, t)) (plus 1 C) ((l, v, C)::H)
                    (Single(None, nil, fill E (loc l)))
|p_commitStep : forall C H S L v t E H' e0, 
                validate S L H C H' L commit -> decompose t E (inatomic v) ->
                p_step C H (Single(Some(S, e0), L, t)) (plus 1 C) H' (Single(None, nil, fill E v))
|p_atomicStep : forall C H E e t, 
                decompose t E (atomic e) ->
                p_step C H (Single(None, nil, t)) (plus 1 C) H (Single(Some(C, fill E (inatomic e)), nil, fill E (inatomic e)))
|p_atomicIdemStep : forall C H E e t L S,
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
|f_allocStep : forall C H v E t l, 
               lookup H l = None -> decompose t E (alloc v) ->
               f_step C H (Single(None, nil, t)) (plus 1 C) ((l, v, C)::H)
                    (Single(None, nil, fill E (loc l)))
|f_commitStep : forall C H S L v t E H' e0, 
                validate S L H C H' L commit -> decompose t E (inatomic v) ->
                f_step C H (Single(Some(S, e0), L, t)) (plus 1 C) H' (Single(None, nil, fill E v))
|f_atomicStep : forall C H E e t, 
                decompose t E (atomic e) ->
                f_step C H (Single(None, nil, t)) (plus 1 C) H 
                       (Single(Some(C, fill E (inatomic e)), nil, fill E (inatomic e)))
|f_atomicIdemStep : forall C H E e t L S,
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

Inductive f_threadWF : nat -> heap -> thread -> Prop :=
|noTSValid : forall n H e, f_threadWF n H (None, nil, e)
|threadWFValid : forall S S' C L H H' L' e0 e, 
                   validate S L H S' H' L' commit -> S < C ->
                   f_multistep C H (Single(Some(S,e0), nil, e0))
                               C H (Single(Some(S,e0), L, e)) ->
                   f_threadWF C H (Some(S, e0), L, e) 
|threadWFInvalid : forall S S' C L H H' L' e e0 e',
                     validate S L H S' H' L' (abort e) -> S < C ->
                     f_multistep C H (Single(Some(S,e0), nil, e0))
                                 C H (Single(Some(S,e0), L', e)) ->
                     f_threadWF C H (Some(S,e0), L, e'). 
             
Definition optLE n on :=
  match on with
      |Some n' => n <= n'
      |None => True
  end. 

Inductive stampMonotonic (n:nat) : heap -> Prop :=
|monoNil : stampMonotonic n nil
|monoCons : forall l v S H, S <= n -> stampMonotonic S H ->
                            stampMonotonic n ((l,v,S)::H). 
 
Inductive f_poolWF : nat -> heap -> pool -> Prop :=
|p_poolWF_ : forall C H T, stampMonotonic C H ->
                           (forall t, tIn T t -> f_threadWF C H t) -> f_poolWF C H T. 

Theorem f_wfPar_l : forall T1 T2 C H, 
                      f_poolWF C H (Par T1 T2) -> 
                      f_poolWF C H T1. 
Proof.
  intros. inv H0. constructor. auto. intros. assert(tIn (Par T1 T2) t). 
  constructor. assumption. apply H3. auto. 
Qed. 

Theorem f_wfPar_r : forall T1 T2 C H, 
                      f_poolWF C H (Par T1 T2) -> 
                      f_poolWF C H T2. 
Proof.
  intros. inv H0. constructor. auto. intros. apply H3. apply in_right. 
  auto. 
Qed. 

Theorem f_wfParConj : forall C H T1 T2, 
                        f_poolWF C H T1 -> f_poolWF C H T2 ->
                        f_poolWF C H (Par T1 T2). 
Proof.
  intros. constructor. inv H0. auto. intros. inv H2. inv H0. auto. 
  inv H1. auto. 
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

Theorem f_multi_trans : forall C H T C' H' T' C'' H'' T'',
                          f_multistep C H T C' H' T' ->
                          f_multistep C' H' T' C'' H'' T'' ->
                          f_multistep C H T C'' H'' T''. 
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

Theorem abortLogPostfix : forall S L H S' H' L' e, 
                            validate S L H S' H' L' (abort e) ->
                            exists L'', L = L'' ++ L'. 
Proof.
  intros. induction H0; try solve[exists nil; eauto].   
  {invertHyp. exists (x::x0). auto. }
  {inversion IHvalidate. exists ([readItem l E]). auto. }
Qed. 

Theorem monotonicWeakening : forall H S S', S > S' -> stampMonotonic S' H ->
                                            stampMonotonic S H. 
Proof.
  induction H; intros. 
  {constructor. }
  {inv H1. constructor. omega. assumption. }
Qed. 

Theorem validateMonotonic : forall C H S L H', 
                              stampMonotonic C H -> 
                              validate S L H C H' L commit ->
                              stampMonotonic (1+C) H'. 
Proof.
  intros. remember commit. induction H1; auto. 
  {eapply monotonicWeakening; eauto. }
  {inv Heqv. }
  {constructor. omega. auto. }
Qed. 

Theorem validateHeapMonotonic : forall S H C H' L res,
                                    validate S L H C H' L res  ->
                                    exists H'', H' = H'' ++ H .
Proof.
  intros. induction H0; eauto; try solve[exists nil; eauto].  
  {exists [(l,v,S')]. simpl. reflexivity. }
Qed. 

Definition getStamp (e:location*term*stamp) := match e with (_, _, x) => x end. 


Theorem lengthsEq : forall (A:Type) (x y : list A), x = y -> length x = length y. 
Proof.
  induction x; intros. 
  {destruct y. auto. inv H. }
  {destruct y. inv H. inv H. simpl. apply f_equal. auto. }
Qed. 

Theorem consApp : forall (A:Type) (a:A) (c b:list A),
                    a::b=c++b -> exists d, c = a::d. 
Proof.
  induction c; intros. 
  {simpl in H. apply lengthsEq in H. simpl in *. omega. }
  {simpl in H. inversion H. subst a0. exists c. auto. }
Qed. 
 
Theorem validateStampGE : forall H' S L H C,
                            validate S L H C (H'++H) L commit ->
                            Forall (fun x => getStamp x = C) H'. 
Proof.
  intros. dependent induction H0; auto. 
  {destruct H'. constructor. apply lengthsEq in x. simpl in *. 
   rewrite app_length in x. omega. }
  {destruct H'. simpl in x. apply lengthsEq in x. simpl in x. omega. destruct H'. 
   inv x. constructor. auto. constructor. apply lengthsEq in x. simpl in *. 
   rewrite app_length in x. omega. }
Qed. 

Theorem stampHeapMonotonic : forall C H T C' H' T',
                               f_step C H T C' H' T' -> 
                               C' >= C /\ (exists H'', H' = H'' ++ H /\ Forall (fun x => getStamp x = C) H''). 
Proof.
  intros. induction H0; try invertHyp; split; eauto; try solve[exists nil; auto]. 
  {exists [(l,v,C)]. simpl. split; auto.  }
  {copy H0. apply validateHeapMonotonic in H0. invertHyp. exists x. split; auto. 
   eapply validateStampGE in H2. auto. }
Qed. 


Theorem LookupExtensionGE : forall H' H l v S C,
                              lookup H l = Some(v, S) -> S < C -> 
                              Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                              lookup (H'++H) l = Some(v,S) \/ 
                              exists S' v', lookup (H'++H) l = Some(v',S') /\ S' >= C. 
Proof.
  induction H'; intros; auto. simpl in *. destruct a. destruct p.
  destruct (eq_nat_dec l l0). 
  {subst. right. inv H2. repeat econstructor. }
  {eapply IHH' in H0; eauto. inv H2. auto. }
Qed.

Theorem abortCommitExtFalse : forall S L S' new H L' x0 e,
                                validate S L H S' H L' (abort e) ->
                                validate S L (new++H) S' x0 L commit -> False. 


Theorem validateHeapExtension : forall S L H S' H' L' res new C, 
                      Forall (fun x : location * term * stamp => getStamp x = C) new ->
                      S < C ->
                      validate S L H S' H' L' res ->
                      exists Hnew Lnew res', validate S L (new++H) S' Hnew Lnew res' /\ 
                                        exists prefix, L' = prefix ++ Lnew.
Proof.
  intros. induction H2; intros. 
  {do 3 econstructor. split. constructor. exists nil. auto. }
  {copy H1. eapply IHvalidate in H1. invertHyp. destruct x1. 
   {eapply LookupExtensionGE in H2. Focus 3. 
    eauto. Focus 2. omega. inv H2.   
    {econstructor. econstructor. econstructor. split. eapply validateCommitRead; eauto. 
     copy H1. eapply commitLogUnchanged in H1. destruct x2. simpl in *. eauto. 
     apply lengthsEq in H1. simpl in H1. rewrite app_length in H1. omega. 
     exists nil. simpl. auto. }
    {invertHyp. econstructor. econstructor. econstructor. split. eapply validateAbortRead. 
     copy H1. apply commitLogUnchanged in H1. destruct x2. simpl in *. eauto.
     apply lengthsEq in H1. simpl in H1. rewrite app_length in H1. omega. eauto. 
     omega. exists ([readItem l E]). auto. }
   }
   {econstructor. econstructor. econstructor. split. eapply validateAbortPropogate. copy H1.
    eapply abortHeapUnchanged in H1. subst. eauto. exists (readItem l E::x2). auto. }
  }
  {copy H1. apply IHvalidate in H1. invertHyp. destruct x2. 
   {

Theorem f_thread_wf_Extension : forall C H C' H' t, 
                         f_threadWF C H t -> C' >= C ->
                         Forall (fun x : location * term * stamp => getStamp x >= C) H' ->
                         f_threadWF C' (H'++H) t. 
Proof.
  intros. inv H0. 
  {constructor. }
  {




Theorem f_stepWF : forall C H T C' H' T', 
                   f_poolWF C H T ->
                   f_step C H T C' H' T' -> 
                   f_poolWF C' H' T'. 
Proof.
  intros. induction H1.
  {copy H0. apply f_wfPar_l in H0. apply IHf_step in H0. 
   apply f_wfPar_r in H2. apply f_wfParConj. assumption. constructor. inv H0. assumption. 
   intros. inv H2. apply H6 in H3. copy H1. eapply stampHeapMonotonic in H1. invertHyp. 
   
   
   
   admit. }
  {admit. }
  {constructor. inv H0. auto. intros. inv H2. inv H6.
   constructor. inv H6. constructor. }
  {constructor. inv H0. auto.  intros. inv H0. inv H5. InTac. inv INHYP. 
   {econstructor. eapply validateCommitRead; eauto. copy H12. 
    apply commitLogUnchanged in H0. subst. eassumption. auto. eapply f_multi_trans. 
    eassumption. econstructor. eapply f_readStep; eauto. constructor. }
   {eapply threadWFInvalid; eauto. eapply validateFailCons; eauto. }
  }
  {constructor. inv H0. auto. intros. inv H0. inv H5. InTac. inv INHYP. 
   {econstructor. eassumption. auto. eapply f_multi_trans. eassumption. 
    econstructor. eapply f_readInDomainStep; eauto. constructor. }
   {eapply threadWFInvalid; eauto. }
  }
  {constructor. inv H0. eapply monotonicWeakening; eauto. intros. inv H0. 
   inv H2. copy H1. eapply abortLogPostfix in H1.
   econstructor. constructor. omega. constructor. }
  {constructor. inv H0. auto. intros. inv H0. inv H3. InTac. inv INHYP. 
   {exfalso. apply H2. reflexivity. }
   {econstructor. eapply validateWrite; eauto. copy H10. 
    apply commitLogUnchanged in H0. subst. eassumption. auto. eapply f_multi_trans. 
    eassumption. econstructor. eapply f_writeStep; eauto. constructor. }
   {eapply threadWFInvalid. eapply validateFailCons. eauto. auto. eassumption. }
  }
  {constructor. inv H0. constructor. omega. auto. intros. inv H0. inv H3. constructor. }
  {inv H0. constructor. eapply validateMonotonic; eauto. intros. inv H0. constructor. }
  {econstructor. inv H0. eapply monotonicWeakening; eauto. intros. inv H2. 
   econstructor. constructor. omega. econstructor. }
  {constructor. inv H0. auto. intros. inv H3. inv H0. InTac. inv INHYP.
   {econstructor. }
   {eapply threadWFValid. eassumption. auto. eapply f_multi_trans. eassumption. 
    econstructor. eapply f_atomicIdemStep; eauto. constructor. }
   {eapply threadWFInvalid; eauto. }
  }
  {constructor. inv H0. auto. intros. inv H2. inv H0. InTac. inv INHYP. 
   {constructor. }
   {econstructor; eauto. eapply f_multi_trans. eassumption. econstructor. 
    eapply f_betaStep; eauto. constructor. }
   {eapply threadWFInvalid; eauto. }
  } 
  Grab Existential Variables. constructor. constructor. 
Qed. 

Theorem f_multistepWF : forall C H T C' H' T', 
                   f_poolWF C H T ->
                   f_multistep C H T C' H' T' -> 
                   f_poolWF C' H' T'. 
Proof.
  intros. induction H1. auto. eapply f_stepWF in H1; auto. 
Qed. 



Theorem heapMonotonic : forall C H T C' H' T', 
                         f_step C H T C' H' T' ->
                         exists H'', H' = H'' ++ H. 
Proof.
  intros. induction H0; eauto; try solve[exists nil; auto].  
  {exists [(l,v,C)]. simpl. reflexivity. }
  {apply validateHeapMonotonic in H0. invertHyp. exists x. auto. }
Qed. 


Theorem lookupExtension : forall H H' l v S C,
                            lookup H l = Some(v, S) -> stampMonotonic C (H'++H) ->
                            lookup (H'++H) l  = Some(v, S) \/ 
                            (lookup (H'++H) l = Some(v', S') /\ S' >= S)
                                                                      



Admitted. 

Theorem f_wf_anyHeap : forall C H C' H' T, 
                         f_poolWF C H T -> C' >= C -> 
                         f_poolWF C' H' T. 
Proof.
  intros. inv H0. constructor. intros. 
  


Admitted. 






















