Require Export ast.     
Require Export Coq.Arith.Peano_dec. 

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

Inductive validate : stamp -> log -> heap -> stamp -> heap -> log -> validateRes -> Prop :=
|validateNil : forall S S' H, validate S nil H S' H nil commit
|validateCommitRead : forall S S' S'' l v E H H' L,
                        lookup H l = Some(v, S') -> S > S' -> validate S L H S'' H' L commit ->
                        validate S (readItem l E::L) H S'' H' (readItem l E::L) commit
|validateAbortPropogate : forall S S' L H x L' E, 
                            validate S L H S' H L' (abort E) ->
                            validate S (x::L) H S' H L' (abort E)
|validateAbortRead : forall S S' S'' H L E H' l v,
                       validate S L H S'' H' L commit -> lookup H l = Some(v, S') ->
                       S' > S -> validate S (readItem l E::L) H S'' H L (abort (fill E(get(loc l))))
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














