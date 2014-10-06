Require Export ast.     
Require Export Arith. 
Require Export Omega. 

Inductive valOrAtomic : term -> Prop :=
|val_ : forall v, value v -> valOrAtomic v
|atomic_ : forall e, valOrAtomic (atomic e). 

Inductive ntDecompose : term -> nonTCtxt -> term -> Prop :=
|ntDecompApp : forall e1 e2 E e, ntDecompose e1 E e -> ~ valOrAtomic e1 ->
                                 ntDecompose (app e1 e2) (ntApp e2 E) e
|ntDecompAppVal : forall v e2 E e, ntDecompose e2 E e -> ~ valOrAtomic e2 ->
                                   value v -> ntDecompose (app v e2) (ntAppVal v E) e
|ntAppRedex : forall n e v, value v -> ntDecompose (app (lambda n e) v) ntHole (app (lambda n e) v)
|ntDecompGet : forall e E e', ntDecompose e E e' -> ~valOrAtomic e ->
                              ntDecompose (get e) (ntGet E) e'
|ntDecompGetRedex : forall l, ntDecompose (get (loc l)) ntHole (get (loc l))
|ntDecompPut : forall e1 e2 E e, ntDecompose e1 E e -> ~ valOrAtomic e1 ->
                                 ntDecompose (put e1 e2) (ntPut e2 E) e
|ntDecompPutVal : forall v e2 E e, ntDecompose e2 E e -> ~ valOrAtomic e2 ->
                                   value v -> ntDecompose (put v e2) (ntPutVal v E) e
|ntDecompPutRedex : forall n v, value v -> ntDecompose (put (loc n) v) ntHole (put (loc n) v)
|ntDecompAlloc : forall e E e', ntDecompose e E e' -> ~valOrAtomic e ->
                                ntDecompose (alloc e) (ntAlloc E) e'
|ntDecompAllocRedex : forall v, value v -> ntDecompose (alloc v) ntHole (alloc v)
|ntDecompAtomicRedex : forall v, value v -> ntDecompose (atomic v) ntHole (atomic v)
|ntDecompFork : forall e, ntDecompose (fork e) ntHole (fork e). 
 

Inductive tDecompose : term -> TCtxt -> term -> Prop :=
|tDecompApp : forall e1 e2 E e, tDecompose e1 E e -> ~ value e1 ->
                                 tDecompose (app e1 e2) (tApp e2 E) e
|tDecompAppVal : forall v e2 E e, tDecompose e2 E e -> ~ value e2 ->
                                   value v -> tDecompose (app v e2) (tAppVal v E) e
|tAppRedex : forall n e v, value v -> tDecompose (app (lambda n e) v) tHole (app (lambda n e) v)
|tDecompGet : forall e E e', tDecompose e E e' -> ~value e ->
                              tDecompose (get e) (tGet E) e'
|tDecompGetRedex : forall l, tDecompose (get (loc l)) tHole (get (loc l))
|tDecompPut : forall e1 e2 E e, tDecompose e1 E e -> ~ value e1 ->
                                 tDecompose (put e1 e2) (tPut e2 E) e
|tDecompPutVal : forall v e2 E e, tDecompose e2 E e -> ~ value e2 ->
                                   value v -> tDecompose (put v e2) (tPutVal v E) e
|tDecompPutRedex : forall n v, value v -> tDecompose (put (loc n) v) tHole (put (loc n) v)
|tDecompAlloc : forall e E e', tDecompose e E e' -> ~value e ->
                                tDecompose (alloc e) (tAlloc E) e'
|tDecompAllocRedex : forall v, value v -> tDecompose (alloc v) tHole (alloc v)
|tDecompAtomic : forall e E e', tDecompose e E e' -> ~ value e -> 
                                tDecompose (atomic e) (tAtomic E) e'
|tDecompAtomicRedex : forall v, value v -> tDecompose (atomic v) tHole (atomic v)
|tDecompFork : forall e, tDecompose (fork e) tHole (fork e)
. 

Fixpoint ntFill E e :=
  match E with
      |ntHole => e
      |ntApp e' E => app (ntFill E e) e'
      |ntAppVal v E => app v (ntFill E e)
      |ntGet E => get (ntFill E e)
      |ntPut e' E => put (ntFill E e) e'
      |ntPutVal v E => put v (ntFill E e)
      |ntAlloc E => alloc (ntFill E e)
  end. 

Fixpoint tFill E e :=
  match E with
      |tHole => e
      |tApp e' E => app (tFill E e) e'
      |tAppVal v E => app v (tFill E e)
      |tGet E => get (tFill E e)
      |tPut e' E => put (tFill E e) e'
      |tPutVal v E => put v (tFill E e)
      |tAlloc E => alloc (tFill E e)
      |tAtomic E => atomic (tFill E e)
  end.       

Fixpoint lookup (H:heap) x := 
  match H with
      |(y, v)::H' => if eq_nat_dec x y
                     then Some v
                     else lookup H' x
      |nil => None
  end. 

Inductive commitRes : Type := success | abort. 

Inductive commit : heap -> thread -> heap -> thread -> commitRes -> Prop := 
|commitRead : forall H H' Hl L e e' l v,
                commit H (Hl,L,e) H' (Hl,L,e) success -> lookup H l = Some v ->
                commit H ((l,v)::Hl, readItem l v e'::L, e) H' ((l,v)::Hl, readItem l v e'::L, e) success
|abortRead : forall H H' Hl L e e' l v v',
                commit H (Hl,L,e) H' (Hl,L,e) success -> lookup H l = Some v' -> v <> v' ->
                commit H ((l,v)::Hl, readItem l v e'::L, e) H' (Hl, L, e') abort
|commitWrite : forall H H' Hl L e e' l v,
                commit H (Hl,L,e) H' (Hl,L,e) success -> 
                commit H ((l,v)::Hl, writeItem l v e'::L, e) 
                       ((l,v)::H') ((l,v)::Hl, writeItem l v e'::L, e) success
|commitAlloc : forall H H' Hl L e e' l v,
                commit H (Hl,L,e) H' (Hl,L,e) success -> 
                commit H ((l,v)::Hl, allocItem l v e'::L, e) 
                       ((l,v)::H') ((l,v)::Hl, allocItem l v e'::L, e) success
|propogateAbort : forall H Hl L e act l v Hl' L' e',
                commit H (Hl,L,e) H (Hl',L',e') abort -> 
                commit H ((l,v)::Hl, act::L, e) H (Hl',L',e') abort.            

(*n is a pointer to the next "free" location.  This ensures that newly allocated
**locations are fresh with respect to the global heap and all thread private heaps*)
Inductive step (n:nat) : heap -> pool -> nat -> heap -> pool -> Prop := 
|ParL : forall H H' T1 T1' n' T2, 
          step n H T1 n' H' T1' -> step n H (Par T1 T2) n' H' (Par T1' T2)
|ParR : forall H H' T1 T2 T2' n', 
          step n H T2 n' H' T2' -> step n H (Par T1 T2) n' H' (Par T1 T2')
|decompStep : forall H H' E e e' L L' Hl Hl' t n', 
                step n H (Single (Hl, L, e)) n' H' (Single(Hl', L', e')) ->
                ntDecompose t E e ->
                step n H (Single (Hl,L,t)) n' H' (Single(Hl',L',ntFill E e'))
|forkStep : forall H Hl L e,
              step n H (Single (Hl, L, fork e)) n H (Par (Single(Hl,L,unit)) (Single(nil,nil,e)))
|nonTGet : forall H Hl L l v, 
             lookup H l = Some v -> step n H (Single(Hl, L, get (loc l))) n H (Single(Hl,L,v))
|tGetAbsent : forall H Hl L A t l v,
                lookup Hl l = None -> lookup H l = Some v -> tDecompose t A (get (loc l)) ->
                step n H (Single(Hl,L,t)) n H (Single((l,v)::Hl, (readItem l v t)::L, tFill A v))
|tGetPresent : forall H Hl L A t l v,
                 lookup Hl l = Some v -> tDecompose t A (get (loc l)) ->
                step n H (Single(Hl,L,t)) n H (Single(Hl, L, tFill A v))
|nonTPut : forall H Hl L l v v',
             lookup H l = Some v' ->
             step n H (Single(Hl,L,put (loc l) v)) n ((l,v)::H) (Single(Hl,L,unit))
|tPutAbsent : forall H Hl L A t l v v',
                lookup Hl l = None -> lookup H l = Some v' -> tDecompose t A (put (loc l) v) ->
                step n H (Single(Hl,L,t)) n H (Single((l,v)::Hl, (writeItem l v t)::L, tFill A unit))
|tPutPresent : forall H Hl L A t l v v',
                 lookup Hl l = Some v' -> tDecompose t A (put (loc l) v) ->
                 step n H (Single(Hl,L,t)) n H (Single((l,v)::Hl, writeItem l v t::L, tFill A unit))
|nonTAlloc : forall H Hl L v, 
               lookup H n = None -> 
               step n H (Single(Hl,L,alloc v)) (S n) ((n,v)::H) (Single(Hl,L,loc n))
|tAlloc : forall H Hl L v t A,
            lookup H n = None -> lookup Hl n = None -> tDecompose t A (alloc v) ->
            step n H (Single(Hl,L,t)) (S n) H (Single((n,v)::Hl, allocItem n v t::L, tFill A (loc n)))
|commitTransaction : forall H H' L v Hl,
                       commit H (Hl,L,atomic v) H' (Hl,L,atomic v) success -> value v ->
                       step n H (Single(Hl,L,atomic v)) n H' (Single(nil,nil,v))
|abortTransaction : forall H L v Hl Hl' L' e,
                       commit H (Hl,L,atomic v) H (Hl',L',e) abort ->
                       step n H (Single(Hl,L,atomic v)) n H (Single(Hl',L',e))
|nestedTransaction : forall H Hl L A v t,
                       tDecompose t A v -> value v ->
                       step n H (Single(Hl,L,t)) n H (Single(Hl,L,tFill A v)).

Inductive multistep (n:nat) : heap -> pool -> nat -> heap -> pool -> Prop :=
|multi_refl : forall H T, multistep n H T n H T
|multi_step : forall H T n' H' T' n'' H'' T'', 
                step n H T n' H' T' -> multistep n' H' T' n'' H'' T'' ->
                multistep n H T n'' H'' T''. 






