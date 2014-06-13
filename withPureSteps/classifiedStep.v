Require Import AST.  
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 

(*progressive step that extends the commit frontier*)
Inductive progress_step : sHeap -> pool -> pool -> config -> Prop :=
|CBetaRed : forall E e N tid s2 h T t, 
             decompose t (appValCtxt E (lambda e)) N -> val N = true ->                  
             progress_step h T (tSingleton(tid,nil,s2,t)) (OK h T (tSingleton(tid,nil,s2,fill E (open 0 N e)))) 
|CProjL : forall tid s2 E V1 V2 h T t, 
           decompose t (fstCtxt E) (pair_ V1 V2) -> val V1 = true -> val V2 = true ->
           progress_step h T (tSingleton(tid,nil,s2,t)) (OK h T (tSingleton(tid,nil,s2,fill E V1)))
|CProjR : forall tid s2 E V1 V2 h T t, 
           decompose t (sndCtxt E) (pair_ V1 V2) -> val V1 = true -> val V2 = true ->
           progress_step h T (tSingleton(tid,nil,s2,t)) (OK h T (tSingleton(tid,nil,s2,fill E V2)))
|CBind : forall tid h E T N M s2 t, decompose t (bindCtxt E N) (ret M) ->
  progress_step h T (tSingleton (tid, nil, s2, t)) (OK h T (tSingleton (tid,nil,s2,fill E(AST.app N M))))
|CBindRaise : forall tid h E T N M s2 t, decompose t (bindCtxt E N) (raise M) ->
  progress_step h T (tSingleton (tid,nil,s2,t)) (OK h T (tSingleton (tid,nil,s2,fill E (raise M))))
|CHandle : forall tid h E T N M s2 t, decompose t (handleCtxt E N) (raise M) ->
  progress_step h T (tSingleton (tid,nil,s2,t)) (OK h T (tSingleton (tid,nil,s2,fill E (AST.app  N M))))
|CHandleRet : forall tid h E T N M s2 t, decompose t (handleCtxt E N) (ret M) ->
  progress_step h T (tSingleton (tid,nil,s2,t)) (OK h T (tSingleton (tid,nil,s2,fill E (ret M))))
|CTerminate : forall tid h T M s2, 
               progress_step h T (tSingleton (tid, nil, s2, ret M)) (OK h T tEmptySet)
|CFork : forall tid tid' h T M s2 E t i j, 
          decompose t E (fork M) -> tid' = Tid(1, 1) ((i, j)::tid) -> 
          progress_step h T (tSingleton (Tid(i, j) tid, nil, s2,t)) (OK h T
               (tCouple (Tid(i, S j)tid, [fAct tid' j (fill E(fork M))], s2, fill E(ret unit)) 
               (tid', [specAct], nil, M)))
|CGet : forall tid h h' T N s2 E x s ds writer sc t i j l,
         decompose t E (get (fvar x)) -> heap_lookup x h = Some(sfull sc ds s writer N) -> 
         tid = Tid(i, j) l -> h' = replace x (sfull sc (tid::ds) s writer N) h ->
         progress_step h T (tSingleton (tid, nil, s2, fill E(get (fvar x)))) (OK h' T 
              (tSingleton (bump tid, [rAct x j (fill E(get (fvar x)))], s2, fill E(ret N))) )
|CPut : forall E x N h sc h' s2 tid T t i j l, 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil nil tid N) h -> tid = Tid(i, j) l ->
         progress_step h T (tSingleton (tid, nil, s2, fill E(put (fvar x) N))) (OK h' T
              (tSingleton (bump tid, [wAct x j (fill E(put (fvar x) N))], s2, fill E(ret unit))))
|COverwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds tid tid' S i j l, 
               decompose t E (put (fvar x) N) -> heap_lookup x h = Some (sfull S ds (S'::A) tid' N') ->
               rollback tid' (S'::A) h TR h' TR' -> heap_lookup x h' = Some (sempty S) ->
               h'' = replace x (sfull S nil nil tid N) h' -> tid = Tid(i, j) l ->
               progress_step h T (tAdd TR (tid, nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (tid, nil, wAct x j (fill E(put (fvar x) N))::s2, fill E (ret unit))))
|CNew : forall E h h' x tid t s2 T i j l,
         decompose t E new -> (x, h') = extend (sempty nil) h -> tid = Tid(i, j) l -> 
         progress_step h T (tSingleton (tid, nil, s2, fill E new)) (OK h' T
              (tSingleton (bump tid, [cAct x j (fill E new)], s2, fill E(ret(fvar x)))))
|CSpec : forall E M t N tid' tid s2 T h s1' i j l, 
          decompose t E (spec M N) -> tid' = extendTid tid -> tid = Tid(i, j) l ->
          s1' = [sAct tid' N; specAct] ->
          progress_step h T (tSingleton (tid, nil, s2, fill E (spec M N))) (OK h T
               (tCouple (bump tid, [specRetAct tid' j (fill E (spec M N))], s2,fill E(specReturn M (threadId tid')))
                        (tid', s1', nil, N)))
|CPopSpec : forall (t : trm) (E : ctxt) (M N1 N2 : trm) 
                (tid0 : tid) (maj min min' : nat) (tid' : list (nat * nat))
                (tid'' : tid) (T : pool) (h : sHeap)
                (t1 t2 : tid * list action * specStack * trm)
                (s1 s1' : list action) (s2 s2' : specStack),
              decompose t (specReturnCtxt E (threadId (Tid (maj, min) tid')))
                (ret N1) ->
              s1 = s1' ++ [sAct tid'' M] ->
              t1 =
              (tid0, [], s2,
              fill E (specReturn (ret N1) (threadId (Tid (maj, min) tid')))) ->
              t2 = (Tid (maj, min') tid', s1, s2', ret N2) ->
              progress_step h T (tCouple t1 t2)
                (OK h T
                   (tCouple t1 (Tid (maj, S min') tid', s1', s2', ret N2)))
|CSpecJoin : forall E h s2 s2' tid tid' N1 N2 maj min min' T t1 t2 t,
              decompose t (specReturnCtxt E (threadId(Tid(maj,min) tid'))) (ret N1) ->
              t1 = (tid, nil, s2, fill E(specReturn (ret N1) (threadId (Tid (maj, min) tid')))) ->
              t2 = (Tid (maj, min') tid', nil, s2', ret N2) ->
              progress_step h T (tCouple t1 t2) (OK h T (tSingleton (tid, nil, s2, ret(pair_ N1 N2))))
|CSpecRB : forall t E' h h' tid tid' maj min  min'' T T' E M' s2 s1' a s2' t1 t2 TRB, 
            decompose t (specReturnCtxt E' (threadId(Tid(maj,min'') tid'))) (raise E) ->
            t1 = (tid, nil, s2, fill E'(specReturn (raise E) (threadId (Tid (maj, min'') tid')))) ->
            t2 = (Tid (maj, min) tid', s1' ++ [a], s2', M') -> 
            ~ (exists p, thread_lookup TRB tid p) -> thread_lookup TRB (Tid (maj, min) tid') t2 -> 
            ~ (exists p', thread_lookup T' (Tid (maj, min) tid') p') ->
            rollback (Tid (maj, min) tid') [a] h (tAdd TRB t2) h' T' ->
            progress_step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, nil, s2, fill E'(raise E))))
|CSpecRaise : forall E' N h tid tid' maj min' min'' s2 s2' T E t1 t2 t,
               decompose t (specReturnCtxt E' (threadId(Tid(maj,min'') tid'))) (ret N) ->
               t1 = (tid, nil, s2, t) -> 
               t2 = (Tid (maj, min') tid', nil, s2', raise E) ->
               progress_step h T (tCouple t1 t2) (OK h T (tSingleton (tid, nil, s2, fill E' (raise E))))
|CPopRead : forall tid tid' t s1 s1' s2 M M' N T h x ds, 
             s1 = s1' ++ [rAct x tid' M'] -> heap_lookup x h = Some (sfull nil ds nil t N) ->
             progress_step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (rAct x tid' M')::s2, M)))
|CPopWrite : forall tid tid'  s s' t s1 s1' s2 M M' N T h h' x ds,
              s1 = s1' ++ [wAct x tid' M'] -> heap_lookup x h = Some(sfull s ds s' t N) ->
              h' = replace x (sfull nil ds s' t N) -> 
              progress_step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (wAct x tid' M')::s2, M)))
|CPopNewFull : forall h h' s1 s1' s2 i tid tid' M' ds s s' t M N T, 
                s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = Some(sfull s ds s' t N) ->
                h' = replace i (sfull nil ds s' t N) h -> 
                progress_step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (cAct i tid' M')::s2, M)))
|CPopNewEmpty : forall h h' s1 s1' s2 i tid tid' M' s M T, 
                 s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = Some(sempty s) ->
                  h' = replace i (sempty nil) h -> 
                 progress_step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (cAct i tid' M')::s2, M)))
|CPopFork : forall h s1 s1' s1'' s1''' s2 s2' tid tid' tid1 tid2 M' M N T , 
             s1 = s1' ++ [fAct tid1 tid2 M'] -> s1'' = s1''' ++ [specAct] ->
             progress_step h T (tCouple (tid, s1, s2, M) (tid', s1'', s2', N)) (OK h T 
                  (tCouple (tid, s1', (fAct tid1 tid2 M')::s2, M)
                           (tid', s1''', specAct::s2', N)))
.


Inductive spec_step : sHeap -> pool -> pool -> config -> Prop :=
|BetaRed : forall E e N tid s2 h T t a b, 
             decompose t (appValCtxt E (lambda e)) N -> val N = true ->                  
             spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E (open 0 N e))))
|ProjL : forall tid s2 E V1 V2 h T t a b, 
           decompose t (fstCtxt E) (pair_ V1 V2) -> val V1 = true -> val V2 = true ->
           spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E V1)))
|ProjR : forall tid a b s2 E V1 V2 h T t, 
           decompose t (sndCtxt E) (pair_ V1 V2) -> val V1 = true -> val V2 = true ->
           spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E V2)))
|Bind : forall tid h E T N M a b s2 t, decompose t (bindCtxt E N) (ret M) ->
  spec_step h T (tSingleton (tid, a::b, s2, t)) (OK h T (tSingleton (tid,a::b,s2,fill E(AST.app N M))))
|BindRaise : forall tid h E T N M a b s2 t, decompose t (bindCtxt E N) (raise M) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (raise M))))
|Handle : forall tid h E T N M a b s2 t, decompose t (handleCtxt E N) (raise M) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (AST.app  N M))))
|HandleRet : forall tid h E T N M a b s2 t, decompose t (handleCtxt E N) (ret M) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (ret M))))
|Terminate : forall tid h T M s2, 
               spec_step h T (tSingleton (tid, nil, s2, ret M)) (OK h T tEmptySet)
|Fork : forall tid tid' h T M a b s2 E t i j, 
          decompose t E (fork M) -> tid' = Tid(1, 1) ((i, j)::tid) -> 
          spec_step h T (tSingleton (Tid(i, j) tid, a::b, s2,t)) (OK h T
               (tCouple (Tid(i, S j)tid, fAct tid' j (fill E(fork M))::a::b, s2, fill E(ret unit)) 
               (tid', [specAct], nil, M)))
|Get : forall tid h h' T N a b s2 E x s ds writer sc t i j l,
         decompose t E (get (fvar x)) -> heap_lookup x h = Some(sfull sc ds s writer N) -> 
         tid = Tid(i, j) l -> h' = replace x (sfull sc (tid::ds) s writer N) h ->
         spec_step h T (tSingleton (tid, a::b, s2, fill E(get (fvar x)))) (OK h' T 
              (tSingleton (bump tid, rAct x j (fill E(get (fvar x)))::a::b, s2, fill E(ret N))) )
|Put : forall E x N h sc h' a b s2 tid T t i j l, 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil (a::b) tid N) h -> tid = Tid(i, j) l ->
         spec_step h T (tSingleton (tid, a::b, s2, fill E(put (fvar x) N))) (OK h' T
              (tSingleton (bump tid, wAct x j (fill E(put (fvar x) N))::a::b, s2, fill E(ret unit))))
|New : forall E h h' x tid t a b s2 T i j l,
         decompose t E new -> (x, h') = extend (sempty (a::b)) h -> tid = Tid(i, j) l -> 
         spec_step h T (tSingleton (tid, a::b, s2, fill E new)) (OK h' T
              (tSingleton (bump tid, cAct x j (fill E new)::a::b, s2, fill E(ret(fvar x)))))
|Spec : forall E M t N tid' tid a b s2 T h s1' i j l, 
          decompose t E (spec M N) -> tid' = extendTid tid -> tid = Tid(i, j) l ->
          s1' = [sAct tid' N; specAct] ->
          spec_step h T (tSingleton (tid, a::b, s2, fill E (spec M N))) (OK h T
               (tCouple (bump tid, specRetAct tid' j (fill E (spec M N))::a::b, s2,fill E(specReturn M (threadId tid')))
                        (tid', s1', nil, N)))
.


(*speculative steps cannot raise an error, so no need for config*)
Inductive spec_multistep : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|smulti_refl : forall (h : sHeap) (p1 p2 : pool),
                 spec_multistep h p1 p2 h p1 p2
| smulti_step : forall (c : config) (T1 T2 T1'' T2'' P1 P2 : Ensemble thread)
                       (P2' : pool) (h h' H'' : sHeap),
                  T2 = tUnion P1 P2 ->
                 Disjoint thread P1 P2 ->
                 step h (tUnion P1 T1) P2 (OK h' (tUnion P1 T1) P2') ->
                 spec_multistep h' T1 (tUnion P1 P2') H'' T1'' T2'' -> spec_multistep h T1 T2 H'' T1'' T2''
.
                                                               
