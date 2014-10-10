Require Export ast.      
Require Export Arith. 
Require Export Omega. 

Inductive valOrAtomic : term -> Prop :=
|val_ : forall v, value v -> valOrAtomic v
|atomic_ : forall e e0, valOrAtomic (atomic e e0). 

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
|ntDecompAtomicRedex : forall v e0, value v -> ntDecompose (atomic v e0) ntHole (atomic v e0)
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
|tDecompAtomic : forall e E e' e0, tDecompose e E e' -> ~ value e -> 
                                   tDecompose (atomic e e0) (tAtomic E e0) e'
|tDecompAtomicRedex : forall v e0, value v -> tDecompose (atomic v e0) tHole (atomic v e0)
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
      |tAtomic E e0 => atomic (tFill E e) e0
  end.       

Fixpoint lookup {A:Type} (H:heap A) x : option A := 
  match H with
      |(y, v)::H' => if eq_nat_dec x y
                     then Some v
                     else lookup H' x
      |nil => None
  end. 

Inductive commitRes : Type := success | abort. 

Inductive commit : stamp -> globalHeap -> thread -> globalHeap -> thread -> commitRes -> Prop := 
|commitNil : forall H e C, commit C H (nil,e) H (nil,e) success
|commitRead : forall C C' C'' H H' L e l v ctxt,
                commit C H (L,e) H' (L,e) success -> lookup H l = Some (v, C'') ->
                C' > C'' ->
                commit C H ((l, (v, C', ctxt, R))::L, e) H' 
                       ((l, (v, C', ctxt, R))::L, e) success
|abortRead : forall C C' C'' H H' L ctxt e e' l v v',
                commit C H (L,e) H' (L,e) success -> lookup H l = Some (v', C'') -> 
                C'' > C' -> 
                commit C H ((l, (v, C', ctxt, R))::L, e) H (L, e') abort
|commitWrite : forall H H' L e l v C C' ctxt,
                commit C H (L,e) H' (L,e) success -> 
                commit C H ((l, (v, C', ctxt, W))::L, e) 
                       ((l,(v, C))::H') ((l, (v, C', ctxt, W))::L, e) success
|propogateAbort : forall C H L e act H' L' e',
                commit C H (L,e) H' (L',e') abort -> 
                commit C H (act::L, e) H' (L',e') abort.            

Inductive step (C:stamp) : globalHeap -> pool -> nat -> globalHeap -> pool -> Prop := 
|ParL : forall H H' T1 T1' T2 C', 
          step C H T1 C' H' T1' -> step C H (Par T1 T2) C' H' (Par T1' T2)
|ParR : forall H H' T1 T2 T2' C', 
          step C H T2 C' H' T2' -> step C H (Par T1 T2) C' H' (Par T1 T2')
|decompStep : forall H H' E e e' L L' t C', 
                step C H (Single (L, e)) C' H' (Single(L', e')) ->
                ntDecompose t E e ->
                step C H (Single (L,t)) C' H' (Single(L',ntFill E e'))
|forkStep : forall H e,
              step C H (Single (nil, fork e)) C H 
                   (Par (Single(nil,unit)) (Single(nil,e)))
|nonTGet : forall H l v C', 
             lookup H l = Some (v, C') -> 
             step C H (Single(nil, get (loc l))) C H (Single(nil,v))
|tGetAbsent : forall H L A t l v C',
                lookup L l = None -> lookup H l = Some (v, C') -> tDecompose t A (get (loc l)) ->
                step C H (Single(L,t)) C H (Single((l, (v, C, A, R))::L, tFill A v))
|tGetPresent : forall H L A t l v v' C' C'' A' op,
                 lookup L l = Some (v, C', A', op) -> tDecompose t A (get (loc l)) ->
                 lookup H l = Some (v', C'') -> C' > C'' ->
                 step C H (Single(L,t)) C H (Single(L, tFill A v))
|nonTPut : forall H L l v v',
             lookup H l = Some v' ->
             step C H (Single(L,put (loc l) v)) (S C) ((l,(v, C))::H) (Single(L,unit))
|tPutAbsent : forall H L A t l v v' C',
                lookup L l = None -> lookup H l = Some (v', C') ->
                tDecompose t A (put (loc l) v) ->
                step C H (Single(L,t)) (S C) H 
                     (Single((l, (v, C, A, W))::L, tFill A unit))
|tPutPresent : forall H L A A' t l v v' C' op,
                 lookup L l = Some (v',C',A',op) -> tDecompose t A (put (loc l) v) ->
                 step C H (Single(L,t)) C H 
                      (Single((l,(v,C',A',W))::L, tFill A unit))
|nonTAlloc : forall H v l, 
               lookup H l = None -> 
               step C H (Single(nil,alloc v)) (S C) 
                    ((l,(v, C))::H) (Single(nil,loc l))
|tAlloc : forall H L v t l A,
            lookup H l = None -> tDecompose t A (alloc v) ->
            step C H (Single(L,t)) (S C) ((l, (v, C))::H) 
                 (Single(L, tFill A (loc l)))
|commitTransaction : forall H H' L v e0,
                       commit C H (L,atomic v e0) H' (L,atomic v e0) success -> 
                       value v ->
                       step C H (Single(L,atomic v e0)) (S C) H' (Single(nil,v))
|abortTransaction : forall H L v L' e e0,
                       commit C H (L,atomic v e0) H (L',e) abort ->
                       step C H (Single(L,atomic v e0)) (S C) H (Single(L',e))
|nestedTransaction : forall H L A v t,
                       tDecompose t A v -> value v ->
                       step C H (Single(L,t)) C H (Single(L,tFill A v)).

Inductive multistep (n:nat) : globalHeap -> pool -> nat -> globalHeap -> pool -> Prop :=
|multi_refl : forall H T, multistep n H T n H T
|multi_step : forall H T n' H' T' n'' H'' T'', 
                step n H T n' H' T' -> multistep n' H' T' n'' H'' T'' ->
                multistep n H T n'' H'' T''. 







(*
Inductive commit_f (H0:heap) (e0:term) : heap -> thread -> heap -> thread -> commitRes -> Prop := 
|commit_fNil : forall H e, commit_f H0 e0 H (nil,nil,e) H (nil,nil,e) success
|commit_fRead : forall H H' Hl L e e' l v,
                commit_f H0 e0 H (Hl,L,e) H' (Hl,L,e) success -> lookup H l = Some v ->
                commit_f H0 e0 H ((l,v)::Hl, readItem l v e'::L, e) H' 
                       ((l,v)::Hl, readItem l v e'::L, e) success
|abortRead_f : forall H H' Hl L e e' l v v',
                commit_f H0 e0 H (Hl,L,e) H' (Hl,L,e) success -> 
                lookup H l = Some v' -> v <> v' ->
                commit_f H0 e0 H ((l,v)::Hl, readItem l v e'::L, e) 
                         H0 (nil, nil, e0) abort
|commit_fWrite : forall H H' Hl L e e' l v,
                commit_f H0 e0 H (Hl,L,e) H' (Hl,L,e) success -> 
                commit_f H0 e0 H ((l,v)::Hl, writeItem l v e'::L, e) 
                         ((l,v)::H') ((l,v)::Hl, writeItem l v e'::L, e) success
|commit_fAlloc : forall H H' Hl L e e' l v,
                commit_f H0 e0 H (Hl,L,e) H' (Hl,L,e) success -> 
                commit_f H0 e0 H ((l,v)::Hl, allocItem l v e'::L, e) 
                       ((l,v)::H') ((l,v)::Hl, allocItem l v e'::L, e) success
|propogateAbort_f : forall H Hl L e act l v L' e',
                commit_f H0 e0 H (Hl,L,e) H0 (nil,L',e') abort -> 
                commit_f H0 e0 H ((l,v)::Hl, act::L, e) H0 (nil,L',e') abort.   

Inductive f_step (n:nat) : heap -> pool -> nat -> heap -> pool -> Prop := 
|ParL_f : forall H H' T1 T1' n' T2, 
          f_step n H T1 n' H' T1' -> f_step n H (Par T1 T2) n' H' (Par T1' T2)
|ParR_f : forall H H' T1 T2 T2' n', 
          f_step n H T2 n' H' T2' -> f_step n H (Par T1 T2) n' H' (Par T1 T2')
|decompStep_f : forall H H' E e e' L L' Hl Hl' t n', 
                f_step n H (Single (Hl, L, e)) n' H' (Single(Hl', L', e')) ->
                ntDecompose t E e ->
                f_step n H (Single (Hl,L,t)) n' H' (Single(Hl',L',ntFill E e'))
|forkStep_f : forall H Hl L e,
              f_step n H (Single (Hl, L, fork e)) n H 
                   (Par (Single(Hl,L,unit)) (Single(nil,nil,e)))
|nonTGet_f : forall H Hl L l v, 
             lookup H l = Some v -> f_step n H (Single(Hl, L, get (loc l))) n H (Single(Hl,L,v))
|tGetAbsent_f : forall H Hl L A t l v,
                lookup Hl l = None -> lookup H l = Some v -> tDecompose t A (get (loc l)) ->
                f_step n H (Single(Hl,L,t)) n H (Single((l,v)::Hl, readItem l v t::L, tFill A v))
|tGetPresent_f : forall H Hl L A t l v,
                 lookup Hl l = Some v -> tDecompose t A (get (loc l)) ->
                f_step n H (Single(Hl,L,t)) n H (Single(Hl, L, tFill A v))
|nonTPut_f : forall H Hl L l v v',
             lookup H l = Some v' ->
             f_step n H (Single(Hl,L,put (loc l) v)) n ((l,v)::H) (Single(Hl,L,unit))
|tPutAbsent_f: forall H Hl L A t l v v',
                lookup Hl l = None -> lookup H l = Some v' -> tDecompose t A (put (loc l) v) ->
                f_step n H (Single(Hl,L,t)) n H (Single((l,v)::Hl, writeItem l v t::L, tFill A unit))
|tPutPresent_f : forall H Hl L A t l v v',
                 lookup Hl l = Some v' -> tDecompose t A (put (loc l) v) ->
                 f_step n H (Single(Hl,L,t)) n H (Single((l,v)::Hl, writeItem l v t::L, tFill A unit))
|nonTAlloc_f : forall H Hl L v, 
               lookup H n = None -> 
               f_step n H (Single(Hl,L,alloc v)) (S n) ((n,v)::H) (Single(Hl,L,loc n))
|tAlloc_f : forall H Hl L v t A,
            lookup H n = None -> lookup Hl n = None -> tDecompose t A (alloc v) ->
            f_step n H (Single(Hl,L,t)) (S n) H (Single((n,v)::Hl, allocItem n v t::L, tFill A (loc n)))
|commitTransaction_f : forall H H' L v Hl e0,
                       commit_f H e0 H (Hl,L,atomic v e0) H' (Hl,L,atomic v e0) success -> value v ->
                       f_step n H (Single(Hl,L,atomic v e0)) n H' (Single(nil,nil,v))
|abortTransaction_f : forall H L v Hl e0,
                       commit_f H e0 H (Hl,L,atomic v e0) H (nil,nil,e0) abort ->
                       f_step n H (Single(Hl,L,atomic v e0)) n H (Single(nil,nil, e0))
|nestedTransaction_f : forall H Hl L A v t,
                       tDecompose t A v -> value v ->
                       f_step n H (Single(Hl,L,t)) n H (Single(Hl,L,tFill A v)).
*)

