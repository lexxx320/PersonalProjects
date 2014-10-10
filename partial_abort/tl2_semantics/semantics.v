Require Export ast.      
Require Export Arith. 
Require Export Omega. 

Inductive valOrAtomic : term -> Prop :=
|val_ : forall v, value v -> valOrAtomic v
|atomic_ : forall e, valOrAtomic (atomic e). 

Inductive decompose : term -> ctxt -> term -> Prop :=
|decompApp : forall e1 e2 E e, decompose e1 E e -> ~ valOrAtomic e1 ->
                                 decompose (app e1 e2) (appCtxt e2 E) e
|decompAppVal : forall v e2 E e, decompose e2 E e -> ~ valOrAtomic e2 ->
                                   value v -> decompose (app v e2) (appValCtxt v E) e
|decompAppRedex : forall n e v, value v -> decompose (app (lambda n e) v) holeCtxt (app (lambda n e) v)
|decompGet : forall e E e', decompose e E e' -> ~valOrAtomic e ->
                              decompose (get e) (getCtxt E) e'
|decompGetRedex : forall l, decompose (get (loc l)) holeCtxt (get (loc l))
|decompPut : forall e1 e2 E e, decompose e1 E e -> ~ valOrAtomic e1 ->
                                 decompose (put e1 e2) (putCtxt e2 E) e
|decompPutVal : forall v e2 E e, decompose e2 E e -> ~ valOrAtomic e2 ->
                                   value v -> decompose (put v e2) (putValCtxt v E) e
|decompPutRedex : forall n v, value v -> decompose (put (loc n) v) holeCtxt (put (loc n) v)
|decompAlloc : forall e E e', decompose e E e' -> ~valOrAtomic e ->
                                decompose (alloc e) (allocCtxt E) e'
|decompAllocRedex : forall v, value v -> decompose (alloc v) holeCtxt (alloc v)
|decompInAtomic : forall e E e', decompose e E e' -> ~valOrAtomic e ->
                                 decompose (atomic e) (inAtomicCtxt E) e'
|decompAtomicRedex : forall v, value v -> decompose (inatomic v) holeCtxt (inatomic v)
|decompAtomic : forall e, decompose (atomic e) holeCtxt (atomic e)
|decompFork : forall e, decompose (fork e) holeCtxt (fork e).  

Fixpoint fill E e :=
  match E with
      |holeCtxt => e
      |appCtxt e' E => app (fill E e) e'
      |appValCtxt v E => app v (fill E e)
      |getCtxt E => get (fill E e)
      |putCtxt e' E => put (fill E e) e'
      |putValCtxt v E => put v (fill E e)
      |allocCtxt E => alloc (fill E e)
      |inAtomicCtxt E => inatomic (fill E e)
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
|commitNil : forall H e tid C, commit C H (tid, nil,e) H (tid, nil,e) success
|commitRead : forall C C' C'' H H' L e l v ctxt tid,
                commit C H (tid, L,e) H' (tid, L,e) success -> lookup H l = Some (v, C'') ->
                C' > C'' ->
                commit C H (tid, (l, (v, C', ctxt, R))::L, e) H' 
                       (tid, (l, (v, C', ctxt, R))::L, e) success
|abortRead : forall C C' C'' H H' L ctxt e e' l v v' tid,
                commit C H (tid, L,e) H' (tid, L,e) success -> lookup H l = Some (v', C'') -> 
                C'' > C' -> 
                commit C H (tid, (l, (v, C', ctxt, R))::L, e) H (tid, L, e') abort
|commitWrite : forall H H' L e l v C C' ctxt tid,
                commit C H (tid, L,e) H' (tid, L,e) success -> 
                commit C H (tid, (l, (v, C', ctxt, W))::L, e) 
                       ((l,(v, C))::H') (tid, (l, (v, C', ctxt, W))::L, e) success
|propogateAbort : forall C H L e act H' L' e' tid,
                commit C H (tid, L,e) H' (tid, L',e') abort -> 
                commit C H (tid, act::L, e) H' (tid, L',e') abort.            

Inductive traceItem : Type :=
|t_pure : option tid -> traceItem
|t_begin : option tid -> traceItem 
|t_commit : option tid -> traceItem
|t_abort : option tid -> traceItem. 

Definition trace := list traceItem. 


Inductive step (C:stamp) : globalHeap -> pool -> nat -> globalHeap -> pool -> traceItem -> Prop := 
|ParL : forall H H' T1 T1' T2 C' lab, 
          step C H T1 C' H' T1' lab -> step C H (Par T1 T2) C' H' (Par T1' T2) lab
|ParR : forall H H' T1 T2 T2' C' lab, 
          step C H T2 C' H' T2' lab -> step C H (Par T1 T2) C' H' (Par T1 T2') lab
|forkStep : forall H e tid t E,
              decompose t E (fork e) ->
              step C H (Single (tid, nil, t)) C H 
                   (Par (Single(tid, nil,fill E unit)) (Single(tid, nil,e)))
|nonTGet : forall H l v C' t E, 
             lookup H l = Some (v, C') -> decompose t E (get (loc l)) -> 
             step C H (Single(None, nil, t)) C H (Single(None, nil,fill E v))
|tGetAbsent : forall H L E t l v C' tid,
                lookup L l = None -> lookup H l = Some (v, C') -> decompose t E (get (loc l)) ->
                step C H (Single(tid, L,t)) C H (Single(tid, (l, (v, C, E, R))::L, fill E v))
|tGetPresent : forall H L E t l v v' C' C'' E' op tid,
                 lookup L l = Some (v, C', E', op) -> decompose t E (get (loc l)) ->
                 lookup H l = Some (v', C'') -> C' > C'' ->
                 step C H (Single(tid, L,t)) C H (Single(tid, L, fill E v))
|nonTPut : forall H L l v v' t E,
             lookup H l = Some v' -> decompose t E (put (loc l) v) -> 
             step C H (Single(None, L,t)) (S C) ((l,(v, C))::H) (Single(None, L,fill E unit))
|tPutAbsent : forall H L E t l v v' tid C',
                lookup L l = None -> lookup H l = Some (v', C') ->
                decompose t E (put (loc l) v) ->
                step C H (Single(tid, L,t)) (S C) H 
                     (Single(tid, (l, (v, C, E, W))::L, fill E unit))
|tPutPresent : forall H L E E' t l v v' C' op tid,
                 lookup L l = Some (v',C',E',op) -> decompose t E (put (loc l) v) ->
                 step C H (Single(tid, L,t)) C H 
                      (Single(tid, (l,(v,C',E',W))::L, fill E unit))
|nonTAlloc : forall H v l, 
               lookup H l = None -> 
               step C H (Single(None, nil,alloc v)) (S C) 
                    ((l,(v, C))::H) (Single(None, nil,loc l))
|tAlloc : forall H L v t l E tid,
            lookup H l = None -> decompose t E (alloc v) ->
            step C H (Single(tid, L,t)) (S C) ((l, (v, C))::H) 
                 (Single(tid, L, fill E (loc l)))
|enterTransaction : forall H t E e, 
                      decompose t E (atomic e) -> 
                      step C H (Single(None, nil, t)) (S C) H 
                           (Single(Some C, nil, fill E (inatomic e)))
|commitTransaction : forall H H' L t E v tid,
                       commit C H (tid, L,inatomic v) H' (tid, L,inatomic v) success -> 
                       decompose t E (inatomic v) ->
                       step C H (Single(tid, L,t)) (S C) H' (Single(None, nil,fill E v))
|abortTransaction : forall H L v L' e tid t E,
                      decompose t E (inatomic v) ->
                       commit C H (tid, L, t) H (tid, L',e) abort ->
                       step C H (Single(tid, L, t)) (S C) H (Single(Some C, L',e))
|nestedTransaction : forall H L E v t tid,
                       decompose t E v -> value v ->
                       step C H (Single(tid, L,t)) C H (Single(tid, L,fill E v)).

Inductive multistep (n:nat) : globalHeap -> pool -> nat -> globalHeap -> pool -> Prop :=
|multi_refl : forall H T, multistep n H T n H T
|multi_step : forall H T n' H' T' n'' H'' T'', 
                step n H T n' H' T' -> multistep n' H' T' n'' H'' T'' ->
                multistep n H T n'' H'' T''. 








