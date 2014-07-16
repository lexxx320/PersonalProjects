Require Import AST.   
Require Import NonSpec.  
Require Import Spec. 
Require Import Heap. 
Require Import sets. 
Require Import Coq.Sets.Ensembles. 

Inductive prog_step : sHeap -> pool -> pool -> config -> Prop :=
|BetaRed : forall E e N tid s2 h T t, 
             decompose t E (AST.app (lambda e) N) ->            
             prog_step h T (tSingleton(tid,nil,s2,t)) 
                  (OK h T (tSingleton(tid,nil,s2,fill E (open 0 N e))))
|ProjL : forall tid s2 E V1 V2 h T t, 
           decompose t E (fst (pair_ V1 V2)) ->
           prog_step h T (tSingleton(tid,nil,s2,t)) 
                (OK h T (tSingleton(tid,nil,s2,fill E V1)))
|ProjR : forall tid s2 E V1 V2 h T t, 
           decompose t E (snd (pair_ V1 V2)) -> 
           prog_step h T (tSingleton(tid,nil,s2,t)) 
                (OK h T (tSingleton(tid,nil,s2,fill E V2)))
|Bind : forall tid h E T N M s2 t, decompose t E (bind (ret M) N) ->
  prog_step h T (tSingleton (tid, nil, s2, t)) 
       (OK h T (tSingleton (tid,nil,s2,fill E(AST.app N M))))
|BindRaise : forall tid h E T N M s2 t, decompose t E (bind (raise M) N)->
  prog_step h T (tSingleton (tid,nil,s2,t)) 
       (OK h T (tSingleton (tid,nil,s2,fill E (raise M))))
|Handle : forall tid h E T N M s2 t, decompose t E (handle (raise M) N) ->
  prog_step h T (tSingleton (tid,nil,s2,t)) 
       (OK h T (tSingleton (tid,nil,s2,fill E (AST.app  N M))))
|HandleRet : forall tid h E T N M s2 t, decompose t E (handle (ret M) N) ->
  prog_step h T (tSingleton (tid,nil,s2,t)) 
       (OK h T (tSingleton (tid,nil,s2,fill E (ret M))))
|Terminate : forall tid h T M s2, 
               prog_step h T (tSingleton (tid, nil, s2, ret M)) (OK h T tEmptySet)
|Fork : forall tid h T M s2 E t (d:decompose t E (fork M)), 
          prog_step h T (tSingleton (tid, nil, s2,t)) 
        (OK h T(tCouple (tid, nil, fAct t E M d :: s2, fill E(ret unit)) 
                        (1::tid, nil, [specAct], M)))
|Get : forall TID h h' T N s2 E x s ds writer t (d:decompose t E (get (fvar x))),
         heap_lookup x h = Some(sfull nil ds s writer N) -> 
         h' = replace x (sfull nil (Add tid ds TID) s writer N) h ->
         prog_step h T (tSingleton (TID, nil, s2, t))
              (OK h' T (tSingleton (TID, nil, rAct x t E d::s2, fill E(ret N))))
|Put : forall E x N h h' s2 TID T t (d:decompose t E (put (fvar x) N)), 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty nil) ->
         h' = replace x (sfull nil (Empty_set tid) nil TID N) h -> 
         prog_step h T (tSingleton (TID, nil, s2, t)) (OK h' T
              (tSingleton (TID, nil, wAct x t E N d::s2, fill E(ret unit))))
|Overwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds TID TID' (d:decompose t E (put (fvar x) N)), 
               heap_lookup x h = Some (sfull nil ds (S'::A) TID' N') ->
               rollback TID' (S'::A) h TR h' TR' ->
               h'' = replace x (sfull nil (Empty_set tid) nil TID N) h' -> 
               prog_step h T (tAdd TR (TID, nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (TID, nil, wAct x t E N d::s2, fill E (ret unit))))
|New : forall E h h' x tid t s2 T (d:decompose t E new),
         (x, h') = extend (sempty nil) h -> 
         prog_step h T (tSingleton (tid, nil, s2, fill E new)) 
              (OK h' T (tSingleton (tid, nil, nAct t E d x::s2, fill E(ret(fvar x)))))
|Spec : forall E M t N tid s2 T h (d:decompose t E (spec M N)), 
          prog_step h T (tSingleton (tid, nil, s2, t)) (OK h T
               (tCouple (tid, nil, srAct t E M N d::s2,t) (tid, nil, [specAct; specAct], N))) 
|SpecJoin : forall t E M N0 N1 tid T h t1 t2 s1 s1' s2 s2',
              decompose t E (specRun (ret N1) N0) -> s1 = s1' ++ [specAct] ->
              t1 = (tid,nil,s2, t) -> t2 = (2::tid,s1,s2',M) ->
              prog_step h T (tCouple t1 t2) 
                   (OK h T (tSingleton(tid,wrapActs s1' N1, s2, fill E (specJoin (ret N1) M)))) 
|SpecRB : forall t E' h h' tid T T' E M' N0 s2 s1' s2' t1 t2 TRB, 
            decompose t E' (specRun (raise E) N0)->
            t1 = (tid,nil,s2,t) -> t2 = (2::tid,s1'++[specAct],s2',M') -> 
            ~ (exists p, thread_lookup TRB (tid) p) -> 
            thread_lookup TRB (2::tid) t2 -> 
            ~ (exists p', thread_lookup T' (2::tid) p') ->
            rollback (2::tid) [specAct] h TRB h' T' ->
            prog_step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, nil, s2, fill E'(raise E))))
|SpecRaise : forall E' N h tid s2 T E t1 t,
               decompose t E' (specJoin(ret N)(raise E)) ->
               t1 = (tid, nil, s2, t) -> 
               prog_step h T (tSingleton t1) 
                    (OK h T (tSingleton (tid, nil, s2, fill E' (raise E))))
|PopRead : forall TID t s1 s1' s2 M M' N T h x ds E d h', 
             s1 = s1' ++ [rAct x M' E d] -> In tid ds TID ->
             heap_lookup x h = Some (sfull nil ds nil t N) ->
             h' = replace x (sfull nil (Subtract tid ds TID) nil t N) h ->
             prog_step h T (tSingleton (TID, s1, s2, M)) (OK h' T (tSingleton (TID, s1', (rAct x M' E d)::s2, M)))
|PopWrite : forall tid t s1 s1' s2 M M' M'' N T h h' x ds a b E d,
              s1 = s1' ++ [wAct x M' E M'' d] -> heap_lookup x h = Some(sfull nil ds (a::b) t N) ->
              h' = replace x (sfull nil ds nil t N) -> 
              prog_step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (wAct x M' E M'' d)::s2, M)))
|PopNewFull : forall h h' s1 s1' s2 i tid M' ds s s' t M N T E d, 
                s1 = s1' ++ [nAct M' E d i] -> heap_lookup i h = Some(sfull s ds s t N) ->
                h' = replace i (sfull nil ds s' t N) h -> 
                prog_step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', nAct M' E d i::s2, M)))
|PopNewEmpty : forall h h' s1 s1' s2 i tid M' s M T E d, 
                 s1 = s1' ++ [nAct M' E d i] -> heap_lookup i h = Some(sempty s) ->
                  h' = replace i (sempty nil) h -> 
                 prog_step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', nAct M' E d i::s2, M)))
|PopFork : forall h s1 s1' s1'' s1''' s2 s2' tid M' M N T M'' E d, 
             s1 = s1' ++ [fAct M' E M'' d] -> s1'' = s1''' ++ [specAct] ->
             prog_step h T (tCouple (tid, s1, s2, M) (1::tid, s1'', s2', N)) (OK h T 
                  (tCouple (tid, s1', fAct M' E M'' d::s2, M)
                           (1::tid, s1''', specAct::s2', N)))
|PopSpec : forall h s1 s1' s1'' s1''' s2 s2' t tid M' M N T E d, 
             s1 = s1' ++ [srAct t E M N d] -> s1'' = s1''' ++ [specAct] ->
             prog_step h T (tCouple (tid, s1, s2, M') (1::tid, s1'', s2', N)) (OK h T 
                  (tCouple (tid, s1', srAct t E M N d::s2, M')
                           (1::tid, s1''', specAct::s2', N)))
.

Inductive spec_step : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|SBetaRed : forall E e N tid s2 h T t a b, 
             decompose t E (AST.app (lambda e) N) ->               
             spec_step h T (tSingleton(tid,a::b,s2,t)) h T (tSingleton(tid,a::b,s2,fill E (open 0 N e)))
|SProjL : forall tid s2 E V1 V2 h T t a b, 
           decompose t E (fst (pair_ V1 V2)) -> 
           spec_step h T (tSingleton(tid,a::b,s2,t)) h T (tSingleton(tid,a::b,s2,fill E V1))
|SProjR : forall tid a b s2 E V1 V2 h T t, 
           decompose t E (snd (pair_ V1 V2)) -> 
           spec_step h T (tSingleton (tid,a::b,s2,t)) h T (tSingleton(tid,a::b,s2,fill E V2))
|SBind : forall tid h E T N M a b s2 t, decompose t E (bind (ret M) N) ->
  spec_step h T (tSingleton (tid, a::b, s2, t)) h T (tSingleton (tid,a::b,s2,fill E(AST.app N M)))
|SBindRaise : forall tid h E T N M a b s2 t, decompose t E (bind (raise M) N) ->
  spec_step h T (tSingleton(tid,a::b,s2,t)) h T (tSingleton (tid,a::b,s2,fill E (raise M)))
|SHandle : forall tid h E T N M a b s2 t, decompose t E (handle (raise M) N) ->
  spec_step h T (tSingleton(tid,a::b,s2,t)) h T (tSingleton (tid,a::b,s2,fill E (AST.app  N M)))
|SHandleRet : forall tid h E T N M a b s2 t, decompose t E (handle (ret M) N) ->
  spec_step h T (tSingleton(tid,a::b,s2,t)) h T (tSingleton (tid,a::b,s2,fill E (ret M)))
|SFork : forall tid h T M b s2 E t (d:decompose t E (fork M)), 
          spec_step h T (tSingleton(tid, b, s2,t)) h T
               (tCouple (tid, fAct t E M d::b, s2, fill E(ret unit)) (1::tid, [specAct], nil, M))
|SGet : forall TID h h' T N b s2 E x s ds writer sc t (d:decompose t E (get(fvar x))),
         heap_lookup x h = Some(sfull sc ds s writer N) -> 
         h' = replace x (sfull sc (Add tid ds TID) s writer N) h ->
         spec_step h T (tSingleton(TID, b, s2, t)) h' T 
              (tSingleton (TID, rAct x t E d::b, s2, fill E(ret N)))
|SPut : forall E x N h sc h' b s2 TID T t (d:decompose t E (put (fvar x) N)), 
         heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc (Empty_set tid) (wAct x t E N d::b) TID N) h ->
         spec_step h T (tSingleton(TID, b, s2, t)) h' T
              (tSingleton (TID, wAct x t E N d::b, s2, fill E(ret unit)))
|SNew : forall E h h' x tid t b s2 T (d:decompose t E new),
         (x, h') = extend (sempty (nAct t E d x::b)) h ->
         spec_step h T (tSingleton(tid, b, s2, t))h' T
              (tSingleton (tid, nAct t E d x::b, s2, fill E(ret(fvar x))))
|SSpec : forall E M t N tid' tid b s2 T h (d:decompose t E (spec M N)), 
          spec_step h T (tSingleton(tid, b, s2, t)) h T
               (tCouple (tid, srAct t E M N d::b, s2,fill E(specRun M N))
                        (tid', [specAct; specAct], nil, N))

.


(*speculative steps cannot raise an error, so no need for config*)
Inductive spec_multistep : sHeap -> pool -> sHeap -> pool -> Prop :=
|smulti_refl : forall (h : sHeap) p2,
                 spec_multistep h p2 h p2
| smulti_step : forall T T' t t' h h' h'',
                  spec_step h T t h' T t' ->
                  spec_multistep h' (tUnion T t') h'' T' ->
                  spec_multistep h (tUnion T t) h'' T'. 


Theorem specStepSingleton : forall h t h' T t', 
                              spec_step h T t h' T t' -> 
                              exists t'', t = tSingleton t''. 
Proof.
  intros. inv H; eauto. Qed. 


