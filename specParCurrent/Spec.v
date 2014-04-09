Require Import AST. 
Require Import Heap. 
Require Import NonSpec. 
Require Import Coq.Sets.Ensembles. 
Require Import Coq.Logic.Classical_Prop. 
Require Import Coq.Program.Equality. 

Require Import sets. 

Fixpoint bump (t : tid) : tid := 
  match t with
    |Tid (maj, min)  t' => Tid (maj, S min) t'
  end.
 
Definition sHeap := heap (ivar_state). 

Inductive ctxt : (term -> term) -> Prop :=
|bindCtxt : forall N c, ctxt c -> ctxt (fun M => bind (c M) N)
|specReturnCtxt : forall N c, ctxt c -> ctxt (fun M => specReturn M N)
|handleCtxt : forall N c, ctxt c -> ctxt (fun M => handle M N)
|hole : forall c, ctxt c -> ctxt (fun M => c M)
.
Hint Constructors ctxt. 

Definition thread := tid * specStack * specStack * term. 

Definition pool := Ensemble thread.

Definition tAdd := Add thread. 
Definition tIn := In thread. 
Definition tUnion := Union thread. 
Definition tCouple := Couple thread. 
Definition tSetminus := Setminus thread. 
Definition tSingleton := Singleton thread. 
Definition tIntersection := Intersection thread. 
Definition tEmptySet := Empty_set thread. 

Inductive rollback : tid -> sHeap -> pool -> sHeap -> pool -> Prop :=
|RBDone : forall T maj min h min' M' tid' M tid s2 t1, 
            ~(tIn T t1) -> t1 = (Tid (maj, min')tid, [sAct tid' M'], s2, M) ->
            rollback (Tid (maj, min)tid) h (tAdd T t1) h T
|RBRead : forall s1 s1' s2 x tid tid' tid'' M M' N h h' h'' T T' sc t A S ds t1, 
            s1 = s1' ++ [rAct x tid'' M'] -> heap_lookup x h = Some (sfull sc (tid''::ds) (S::A) t N) ->
            h' = replace x (sfull sc ds (S::A) t N) h -> 
            ~(tIn T t1) -> t1 = (tid', s1, s2, M) ->
            rollback tid h' (tAdd T (tid'', s1', s2, M')) h'' T' ->
            rollback tid h (tAdd T t1) h'' T'
|RBFork : forall s1 s1' s2 s2' tid tid' tid'' tid2 M M' N T T' h h' t1 t2,
            s1 = s1' ++ [fAct tid2 tid'' M'] -> ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (tid', s1, s2, M) -> t2 = (tid'', [specAct], s2', N) ->
            rollback tid h (tAdd T (tid'', s1', s2, M')) h' T' ->
            rollback tid h (tAdd (tAdd T t1) t2) h' T'
|RBWrite : forall s1 s1' s2 tid tid' tid'' M M' N S A sc T T' h h' h'' x t1,
             s1 = s1' ++ [wAct x tid'' M'] -> heap_lookup x h = Some(sfull sc nil (S::A) tid'' N) ->
             h' = replace x (sempty sc) h -> ~(tIn T t1) ->
             t1 = (tid', s1, s2, M) -> rollback tid h' (tAdd T (tid'', s1', s2, M')) h'' T' ->
             rollback tid h (tAdd T t1) h'' T'
|RBNew : forall s1 s1' s2 tid tid' tid'' M M' S A T T' h h' h'' x t1,
           s1 = s1' ++ [cAct x tid'' M'] -> heap_lookup x h = Some (sempty (S::A)) ->
           h' = remove h x -> ~(tIn T t1) -> t1 = (tid', s1, s2, M) ->
           rollback tid h' (tAdd T (tid'', s1', s2, M')) h'' T' ->
           rollback tid h (tAdd T t1) h'' T'
|RBSpec : forall s1 s1' s2 s2' tid tid2 tid' tid'' tid''' M M' N N' T T' h h' t1 t2,
            s1 = s1' ++ [fAct tid2 tid'' M'] -> ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (tid', s1, s2, M) -> t2 = (tid''', [sAct tid2 N'; specAct], s2', N) ->
            rollback tid h (tAdd T (tid'', s1', s2, M')) h' T' ->
            rollback tid h (tAdd (tAdd T t1) t2) h' T'
.

Hint Constructors rollback. 

Definition extendTid (t:tid) : tid :=
  match t with
      |Tid (a, b) l => Tid (1,1) ((a,b)::l)
  end.


Inductive thread_lookup : pool -> tid -> thread -> Prop :=
|hit : forall T t tid maj min min' s1 s2 M,
         tIn T t -> t = (Tid (maj, min') tid, s1, s2, M) -> thread_lookup T (Tid (maj, min) tid) t.

Hint Constructors thread_lookup. 

Inductive step : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|StepSwitch : forall h T s s',
                tIntersection T s = tEmptySet -> tIntersection T s' = tEmptySet ->
                s' <> s -> step h (tUnion T s) s' h (tUnion T s') s
|Bind : forall tid h E T N M s1 s2,
          ctxt E -> step h T (tSingleton (tid, s1, s2, E(bind (ret M) N))) h T 
                         (tSingleton (bump tid, s1, s2, E(AST.app N M)))
|BindRaise : forall tid h E T N M s1 s2,
               ctxt E -> step h T (tSingleton (tid, s1, s2, E(bind (raise M) N)))
                              h T (tSingleton (bump tid, s1, s2, E(raise M)))
|Handle : forall tid h E T N M s1 s2,
            ctxt E -> step h T (tSingleton (tid, s1, s2, E(handle (raise M) N))) h T
                           (tSingleton (bump tid, s1, s2, E(AST.app N M)))
|HandleRet : forall tid h E T N M s1 s2, 
               ctxt E -> step h T (tSingleton (tid, s1, s2, E(handle(ret M) N))) h T 
                              (tSingleton (bump tid, s1, s2, E(ret M)))
|Terminate : forall tid h T M s2,
               step h T (tSingleton (tid, nil, s2, ret M)) h T tEmptySet
|Fork : forall tid tid' h T M s1 s2 E ,
          ctxt E -> tid' = extendTid tid -> 
          step h T (tSingleton (tid, s1, s2, E(fork M))) h T
               (tCouple (bump tid, fAct tid' tid (E(fork M))::s1, s2, E(ret unit)) 
               (tid', [specAct], nil, M))
|Get : forall tid h h' T N s1 s2 E x s ds writer sc,
         ctxt E -> heap_lookup x h = Some(sfull sc ds s writer N) -> 
         h' = replace x (sfull sc (tid::ds) s writer N) h ->
         step h T (tSingleton (tid, s1, s2, E(get x))) h' T 
              (tSingleton (bump tid, rAct x tid (E(get x))::s1, s2, E(ret N)))
|Put : forall E x N h sc h' s1 s2 tid T , 
         ctxt E -> heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil s1 tid N) h ->
         step h T (tSingleton (tid, s1, s2, E(put x N))) h' T
              (tSingleton (bump tid, wAct x tid (E(put x N))::s1, s2, E(ret unit)))
|New : forall E h h' i tid s1 s2 T,
         ctxt E -> (i, h') = extend (sempty s1) h -> 
         step h T (tSingleton (tid, s1, s2, E new)) h' T
              (tSingleton (bump tid, cAct i tid new::s1, s2, E(ret(var i))))
|Spec : forall E M  N tid' tid s1 s2 T h s1', 
          ctxt E -> tid' = extendTid tid -> s1' = [sAct tid' N; specAct] ->
          step h T (tSingleton (tid, s1, s2, E (spec M N))) h T
               (tCouple (bump tid, fAct tid' tid (E (spec M N))::s1, s2,E(specReturn M (threadId tid')))
                        (tid', s1', nil, N))
|PopSpec : forall E M N1 N2 tid maj min min' tid' tid'' T h t1 t2 s1 s1' s2 s2',
             ctxt E -> s1 = s1' ++ [sAct tid'' M] ->
             t1 = (tid, nil, s2, E(specReturn (ret N1) (threadId (Tid(maj, min) tid')))) ->
             t2 = (Tid(maj, min') tid', s1, s2', ret N2) ->
             step h T (tCouple t1 t2) h T (tCouple t1 (Tid(maj, S min')tid', s1', s2', ret N2))
|SpecJoin : forall E h s2 s2' tid tid' N1 N2 maj min min' T t1 t2,
              ctxt E -> t1 = (tid, nil, s2, E(specReturn (ret N1) (threadId (Tid (maj, min) tid')))) ->
              t2 = (Tid (maj, min') tid', [joinAct], s2', ret N2) ->
              step h T (tCouple t1 t2) h T (tSingleton (bump tid, nil, s2, ret(pair_ N1 N2)))
|SpecRB : forall E' h h' tid tid' maj min  min'' T T' E M' s2 s1' a s2' t1 t2 TRB p p', 
            ctxt E' -> t1 = (tid, nil, s2, E'(specReturn (raise E) (threadId (Tid (maj, min'') tid')))) ->
            t2 = (Tid (maj, min) tid', a::s1', s2', M') -> 
            ~ thread_lookup TRB tid p -> thread_lookup TRB (Tid (maj, min) tid') t2 -> 
            ~ thread_lookup T' (Tid (maj, min) tid') p' ->
            rollback (Tid (maj, min) tid') h (tAdd TRB t2) h' T' ->
            step h T (tAdd TRB t1) h' T (tAdd T' (bump tid, nil, s2, E'(raise E)))
|SpecRaise : forall E' N h tid tid' maj  min' s2 s2' T E t1 t2,
               ctxt E' -> t1 = (tid, nil, s2, N) -> t2 = (Tid (maj, min') tid', [joinAct], s2', raise E) ->
               step h T (tCouple t1 t2) h T (tSingleton (bump tid, nil, s2, E' (raise E)))
|PopRead : forall tid tid' t s1 s1' s2 M M' N T h x ds, 
             s1 = s1' ++ [rAct x tid' M'] -> heap_lookup x h = Some (sfull nil ds nil t N) ->
             step h T (tSingleton (tid, s1, s2, M)) h T (tSingleton (tid, s1', (rAct x tid' M')::s2, M))
|PopWrite : forall tid tid'  s s' t s1 s1' s2 M M' N T h h' x ds,
              s1 = s1' ++ [wAct x tid' M'] -> heap_lookup x h = Some(sfull s ds s' t N) ->
              h' = replace x (sfull nil ds s' t N) -> 
              step h T (tSingleton (tid, s1, s2, M)) h T (tSingleton (tid, s1', (wAct x tid' M')::s2, M))
|PopNewFull : forall h h' s1 s1' s2 i tid tid' M' ds s s' t M N T, 
                s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = Some(sfull s ds s' t N) ->
                h' = replace i (sfull nil ds s' t N) h -> 
                step h T (tSingleton (tid, s1, s2, M)) h T (tSingleton (tid, s1', (cAct i tid' M')::s2, M))
|PopNewEmpty : forall h h' s1 s1' s2 i tid tid' M' s M T, 
                 s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = Some(sempty s) ->
                  h' = replace i (sempty nil) h -> 
                 step h T (tSingleton (tid, s1, s2, M)) h T (tSingleton (tid, s1', (cAct i tid' M')::s2, M))
|PopFork : forall h s1 s1' s1'' s1''' s2 s2' tid tid' tid1 tid2 M' M N T , 
             s1 = s1' ++ [fAct tid1 tid2 M'] -> s1'' = s1''' ++ [specAct] ->
             step h T (tCouple (tid, s1, s2, M) (tid', s1'', s2', N)) h T 
                  (tCouple (tid, s1', (fAct tid1 tid2 M')::s2, M)
                           (tid', s1''', specAct::s2', N))
.

Hint Constructors step. 

Inductive unspecHeap : sHeap -> sHeap -> Prop :=
  |unSpecSE : forall h h' i hd tl, unspecHeap h h' -> 
                                   unspecHeap ((i, sempty (hd::tl)) :: h) h'
  |unSpecCE : forall h h' i, unspecHeap h h' -> 
                             unspecHeap ((i, sempty nil) :: h) ((i, sempty nil) :: h')
  |unspecSF : forall h h' i hd tl d s t N, 
                unspecHeap h h' -> 
                unspecHeap ((i, sfull (hd::tl) d s t N) :: h) h'
  |unspecCCSF : forall h h' i d hd tl t M, 
                  unspecHeap h h' ->
                  unspecHeap ((i, sfull nil d (hd::tl) t M)::h) ((i, sempty nil)::h')
  |unspecCCCF : forall h h' i d t M, 
                  unspecHeap h h' ->
                  unspecHeap ((i, sfull nil d nil t M)::h) 
                             ((i, sfull nil d nil t M)::h')
  |unspecNil : unspecHeap nil nil
.
Hint Constructors unspecHeap. 

Inductive unspecThread : thread -> option thread -> Prop :=
|unspecCommit : forall tid s2 M,
                  unspecThread (tid, nil, s2, M) (Some(tid, nil, s2, M))
|unspecRead : forall tid s1 s1' s2 M i maj min min' c,
                ctxt c -> s1 = s1' ++ [rAct i (Tid (maj, min') tid) (c (get i))] ->
                unspecThread (Tid (maj, min) tid, s1, s2, M) (Some(Tid (maj, min') tid, nil, s2, c(get i)))
|unspecWrite : forall tid s1 s1' s2 M M' i maj min min' c,
                 ctxt c -> s1 = s1' ++ [wAct i (Tid (maj, min') tid) (c (put i M'))] ->
                 unspecThread (Tid (maj, min) tid, s1, s2, M) (Some(Tid (maj, min') tid, nil, s2, (c(put i M'))))
|unspecCreate : forall tid s1 s1' s2 M i maj min min'  c,
                  ctxt c -> s1 = s1' ++ [cAct i (Tid (maj, min') tid) (c new)] ->
                  unspecThread (Tid (maj, min) tid, s1, s2, M) (Some(Tid (maj, min') tid, nil, s2, (c new)))
|unspecSpec : forall c tid s1 s1' s2 M maj min min' M',
                ctxt c -> s1 = s1' ++ [sAct (Tid (maj, min') tid) M'] ->
                unspecThread (Tid (maj, min) tid, s1, s2, M) 
                             (Some(Tid (maj, min') tid, [sAct (Tid (maj, min') tid) M'], s2, M'))
|unSpecFork : forall c tid s1 s1' s2 M tid' M' maj min min',
                  ctxt c -> s1 = s1' ++ [fAct tid' (Tid (maj, min') tid) (c (fork M'))] ->
                  unspecThread (Tid (maj, min) tid, s1, s2, M) 
                               (Some(Tid (maj, min') tid, nil, s2, c(fork M')))
|unspecCreatedSpec : forall s1 s1' s2 M tid,
                       s1 = s1' ++ [specAct] -> unspecThread (tid, s1, s2, M) None
|unspecJoin : forall s1 s1' s2 M tid,
                s1 = s1' ++ [joinAct] -> unspecThread (tid, s1, s2, M) (Some(tid, s1, s2, M))
.

Hint Constructors unspecThread. 

Inductive unspecPool : pool -> pool -> Prop :=
|unspecEmpty : unspecPool (Empty_set thread) (Empty_set thread)
|unspecSome : forall t t' T T', ~(tIn T t) -> unspecPool T T' -> unspecThread t (Some t') ->
                                unspecPool (tAdd T t) (tAdd T' t')
|unspecNone : forall t  T T', ~(tIn T t) -> unspecPool T T' -> unspecThread t None ->
                                unspecPool (tAdd T t) T'
.
Hint Constructors unspecPool. 
(*
Inductive multistep : sHeap -> pool -> sHeap -> pool -> Prop :=
|reflStep : forall h p, multistep h p h p
|multiStep : forall h h' h'' p p' p'', multistep h' p' h'' p'' -> step h p h' p' ->
                                       multistep h p h'' p''
.

Inductive wellFormed : sHeap -> pool -> Prop :=
  |WF : forall h h' p p', unspecHeap h h' -> unspecPool p p' -> multistep h' p' h p ->
                         wellFormed h p. 
Hint Constructors wellFormed. 
*)

Inductive specActions : pool -> Ensemble (tid * specStack) -> Prop :=
|sa : forall T actions, 
        (forall maj min t s1 s2 M, tIn T (Tid (maj, min) t, s1, s2, M) -> 
                                   Ensembles.In (tid * specStack) actions (Tid(maj, 0)t, s1)) ->
        specActions T actions
.

(*
Inductive specActions : pool -> Ensemble (tid * specStack) -> Prop :=
|saEmpty : specActions (Empty_set thread) (Empty_set (tid * specStack))
|saSingle : forall maj min t s1 s2 M,
              specActions (tSingleton (Tid (maj, min) t, s1, s2, M)) 
                          (Singleton (tid * specStack) (Tid (maj, 0) t, s1))
|saCouple : forall maj min t s1 s2 M maj' min' t' s1' s2' M',
              specActions (tCouple (Tid (maj, min) t, s1, s2, M) (Tid (maj', min') t', s1', s2', M'))
                          (Couple (tid * specStack)(Tid (maj, 0) t, s1) (Tid (maj', 0) t', s1'))
|saUnion : forall T1 T2 a1 a2,
             specActions T1 a1 -> specActions T2 a2 -> 
             specActions (tUnion T1 T2) (Union (tid*specStack) a1 a2)
.*)

Hint Constructors specActions. 

Inductive commitActions : pool -> Ensemble (tid * specStack) -> Prop :=
|caEmpty : commitActions (Empty_set thread) (Empty_set (tid * specStack))
|caNonEmpty : forall maj min t s1 s2 M T As,
                ~(tIn T (Tid (maj, min) t, s1, s2, M)) -> 
                commitActions T As -> commitActions (tAdd T (Tid (maj, min) t, s1, s2, M))
                                                    (Add (tid * specStack) As (Tid (maj, 0)t, s2))
.
Hint Constructors commitActions. 


(*Erasure*)
Inductive appears_free_in : id -> term -> Prop :=
|afi_ivar : forall i j, i <> j -> appears_free_in i (ivar j)
|afi_unit : forall i, appears_free_in i unit
|afi_pair : forall i e1 e2, appears_free_in i e1 -> appears_free_in i e2 ->
                            appears_free_in i (pair_ e1 e2)
|afi_var : forall i j, i <> j -> appears_free_in i (var j)
|afi_lambda : forall i j e, i <> j -> appears_free_in i e -> 
                            appears_free_in i (lambda j e)
|afi_app : forall i e1 e2, appears_free_in i e1 -> appears_free_in i e2 ->
                           appears_free_in i (AST.app e1 e2)
|afi_ret : forall i e, appears_free_in i e -> appears_free_in i (ret e)
|afi_bind : forall i e1 e2, appears_free_in i e1 -> appears_free_in i e2 ->
                            appears_free_in i (bind e1 e2)
|afi_fork : forall i e, appears_free_in i e -> appears_free_in i (fork e)
|afi_new : forall i, appears_free_in i new
|afi_put : forall i j e, appears_free_in i e -> appears_free_in i (put j e)
|afi_get : forall i j, appears_free_in i (get j)
|afi_raise : forall i e, appears_free_in i e -> appears_free_in i (raise e)
|afi_handle : forall i e1 e2, appears_free_in i e1 -> appears_free_in i e2 ->
                              appears_free_in i (handle e1 e2)
|afi_done : forall i e, appears_free_in i e -> appears_free_in i (done e)
|afi_spec : forall i e1 e2, appears_free_in i e1 -> appears_free_in i e2 ->
                            appears_free_in i (spec e1 e2)
|afi_spec_return : forall i e1 e2, appears_free_in i e1 -> appears_free_in i e2 ->
                                   appears_free_in i (specReturn e1 e2)
.

Hint Constructors appears_free_in. 
Inductive eraseTerm : term -> pool -> pterm -> Prop :=
|eraseIVar : forall i T, eraseTerm (ivar i) T (pivar i)
|eraseUnit : forall T, eraseTerm unit T punit
|erasePair : forall t1 t1' t2 t2' T, eraseTerm t1 T t1' -> eraseTerm t2 T t2' ->
                                     eraseTerm (pair_ t1 t2) T (ppair t1' t2')
|eraseVar : forall i T, eraseTerm (var i) T (pvar i)
|eraseLambda : forall i e e' T, eraseTerm e T e' -> 
                                eraseTerm (lambda i e) T (plambda i e')
|eraseApp : forall e1 e1' e2 e2' T, eraseTerm e1 T e1' -> eraseTerm e2 T e2' ->
                                    eraseTerm (AST.app e1 e2) T (papp e1' e2')
|eraseRet : forall e e' T, eraseTerm e T e' -> eraseTerm (ret e) T (pret e')
|eraseBind : forall e1 e1' e2 e2' T, eraseTerm e1 T e1' -> eraseTerm e2 T e2' ->
                                     eraseTerm (bind e1 e2) T (pbind e1' e2')
|eraseFork : forall e e' T, eraseTerm e T e' -> eraseTerm (fork e) T (pfork e')
|eraseNew : forall T, eraseTerm new T pnew
|erasePut : forall e e' i T, eraseTerm e T e' -> eraseTerm (put i e) T (pput i e')
|eraseGet : forall i T, eraseTerm (get i) T (pget i)
|eraseRaise : forall e e' T, eraseTerm e T e' -> eraseTerm (raise e) T (praise e')
|eraseHandle : forall e1 e1' e2 e2' T, eraseTerm e1 T e1' -> eraseTerm e2 T e2' ->
                                       eraseTerm (handle e1 e2) T (phandle e1' e2')
|eraseDone : forall e e' T, eraseTerm e T e' -> eraseTerm (done e) T (pdone e')
|eraseSpec : forall e1 e1' e2 e2' T i j, 
               eraseTerm e1 T e1' -> eraseTerm e2 T e2' -> ~(appears_free_in i e2) ->
               eraseTerm (spec e1 e2) T 
   (pbind e1' (plambda i (pbind e2' (plambda j (pret (ppair (pvar i) (pvar j)))))))
|eraseSpecReturn : forall e e' tid tid' tid'' T i j M M' M'' s1 s1' s2 , 
                     eraseTerm e T e' -> s1 = s1' ++ [sAct tid'' M'] ->
                     eraseTerm M' T M'' -> ~(appears_free_in i M') ->
                     thread_lookup T tid (tid', s1, s2, M) ->
                     eraseTerm (specReturn e (threadId tid)) T
   (pbind e' (plambda i (pbind M'' (plambda j (pret (ppair (pvar i) (pvar j)))))))
                                   
.

Hint Constructors eraseTerm. 

Inductive eraseHeap : sHeap -> pHeap -> Prop :=
|eraseSE : forall h h' (i:id) hd tl,
             eraseHeap h h' -> eraseHeap ((i, sempty (hd::tl)) :: h) h'
|eraseCE : forall h h' i ,
             eraseHeap h h' -> eraseHeap ((i, sempty nil)::h) ((i, pempty)::h')
|eraseSF : forall h h' i hd tl d s t N,
             eraseHeap h h' -> eraseHeap ((i, sfull (hd::tl) d s t N)::h) h'
|eraseCCSF : forall h h' i d hd tl t M,
               eraseHeap h h' -> 
               eraseHeap ((i, sfull nil d (hd::tl) t M)::h) ((i, pempty)::h')
|eraseCCCF : forall h h' i d t M M',
               eraseHeap h h' -> eraseTerm M (Empty_set thread) M' ->
               eraseHeap ((i, sfull nil d nil t M)::h) ((i, pfull M')::h')
.

Hint Constructors eraseHeap. 

Inductive eraseThread : thread -> pool -> option ppool -> Prop :=
|tEraseCommit : forall T tid s2 M M', eraseTerm M T M' ->
                                     eraseThread (tid, nil, s2, M) T (Some (pthread M'))
|tEraseRead : forall T tid tid' s1 s1' s2 x M M' M'',
               s1 = s1' ++ [rAct x tid' M'] -> eraseTerm M' T M'' ->
               eraseThread (tid, s1, s2, M) T (Some (pthread M''))
|tEraseWrite : forall tid tid' M M' M'' x s1 s2 s1' T,
                s1 = s1' ++ [wAct x tid' M'] -> eraseTerm M' T M'' ->
                eraseThread (tid, s1, s2, M) T (Some(pthread M''))
|tEraseNew : forall tid tid' M M' M'' x s1 s2 s1' T,
              s1 = s1' ++ [cAct x tid' M'] -> eraseTerm M' T M'' ->
              eraseThread (tid, s1, s2, M) T (Some (pthread M''))
|tEraseSpec : forall tid tid' M M' s1 s2 s1' T,
               s1 = s1' ++ [sAct tid' M'] -> 
               eraseThread (tid, s1, s2, M) T None
|tEraseFork : forall tid tid' tid'' M M' M'' s1 s2 s1' T,
                s1 = s1' ++ [fAct tid' tid'' M'] -> eraseTerm M' T M'' ->
                eraseThread (tid, s1, s2, M) T (Some(pthread M''))
|tEraseJoin : forall tid M M' s1 s1' s2 T,
                     s1 = s1' ++ [joinAct] -> eraseTerm M T M' ->
                     eraseThread (tid, s1, s2, M) T (Some(pthread M'))
|tEraseCreatedSpec : forall tid M s1 s1' s2 T,
                       s1 = s1' ++ [specAct] ->  eraseThread (tid, s1, s2, M) T None
.

Hint Constructors eraseThread. 

Inductive erasePool : pool -> pool -> ppool -> Prop :=
|eraseEmpty : forall T, erasePool (Empty_set thread) T pdot 
|eraseParSome : forall P T T' t t',
                  eraseThread t P (Some t') -> ~(tIn T t) -> erasePool T P T' ->
                  erasePool (tAdd T t) P (ppar T' t') 
|eraseParNone : forall P T T' t,
                  eraseThread t P None -> ~(tIn T t) -> erasePool T P T' ->
                  erasePool (tAdd T t) P T'.

Hint Constructors erasePool. 

(*Erasure is idempotent with respect to unspeculate*)
Theorem eraseUnspecHeapIdem : 
  forall H H' H'', unspecHeap H H' -> eraseHeap H' H'' -> eraseHeap H H''. 
Proof. 
  intros.   
  {generalize dependent H''.  
   induction H0; intros; eauto. 
   {inversion H1; subst. apply IHunspecHeap in H4. constructor. assumption. }
   {inversion H1; subst. apply IHunspecHeap in H4. constructor. assumption. }
   {inversion H1; subst. apply IHunspecHeap in H7. constructor. assumption. 
    assumption. }
  }
Qed. 

Print tAdd. 

Lemma SetAddNotEmpty : forall t T, tAdd T t = Empty_set thread -> False. 
Proof.
  intros. 
  assert(tIn(tAdd T t) t). unfold tIn. unfold In. unfold tAdd. unfold Add. 
  apply Union_intror. constructor. rewrite H in H0. inversion H0. Qed. 

Theorem LastElem : forall (T:Type) l, l = nil \/ (exists l' (e:T), l = l' ++ [e]). 
Proof.
  intros. induction l. 
  {left. reflexivity. }
  {right. inversion IHl. 
   {exists nil. exists a. simpl. subst. reflexivity. }
   {inversion H. inversion H0. exists (a::x). exists x0. subst. simpl. 
    reflexivity. }
  }
Qed. 

Theorem InAdd : forall T t, tIn (tAdd T t) t. 
  intros. unfold tIn. unfold In. unfold tAdd. unfold Add. apply Union_intror. 
  constructor. Qed. 

Hint Resolve InAdd. 

Theorem AddWeakening : forall T t t', tIn T t -> tIn (tAdd T t') t. 
Proof.
  intros. 
  unfold tIn in *. unfold In in *. unfold tAdd in *. unfold Add. 
  apply Union_introl. auto. Qed. 

Hint Resolve AddWeakening. 

Theorem LookupSame :
  forall P P', unspecPool P P' ->
               forall tid T, thread_lookup P' tid T ->
                             exists T', thread_lookup P tid T' /\ unspecThread T' (Some T).
Proof.
  intros P P' H. induction H. 
  {intros. inversion H; subst. inversion H0. }
  {intros. inversion H2; subst. remember (Tid (maj, min') tid0, s1, s2, M). 
   assert(p = t' \/ ~(p = t')). apply classic. inversion H4. 
   {subst. rewrite <- H5 in H1. inversion H1; subst; eauto. }
   {unfold not in *. inversion H2. subst. inversion H12. subst. 
    inversion H3. subst. assert(thread_lookup T' (Tid (maj, min) tid0) (Tid (maj, min'0) tid0, s0, s3, M0)). 
    econstructor. eassumption. reflexivity. apply IHunspecPool in H7. inversion H7. inversion H8. 
    inversion H10; subst. 
    {exists  (Tid (maj, min'0) tid0, [], s3, M0). split. econstructor. inversion H9; subst. 
     apply AddWeakening with (t' := t) in H18. assumption. reflexivity. constructor. }
    {exists (Tid(maj, min0) tid0, s1' ++ [rAct i (Tid(maj, min'0) tid0) (c (get i))], s3, M).
     split. econstructor. inversion H9; subst. apply AddWeakening with (t' := t) in H19. 
     assumption. reflexivity. assumption. }
    {exists (Tid(maj, min0) tid0, s1' ++ [wAct i (Tid(maj, min'0) tid0) (c (put i M'))], s3, M). 
     split. econstructor. inversion H9; subst. apply AddWeakening with (t' := t) in H19. 
     assumption. reflexivity. assumption. }
    {exists  (Tid(maj, min0) tid0, s1' ++ [cAct i (Tid(maj, min'0) tid0) (c new)], s3, M). 
     split. econstructor. inversion H9. eauto. eauto. eauto. }
    {exists  (Tid(maj, min0) tid0, s1' ++ [sAct (Tid(maj, min'0) tid0) M0], s3, M). 
     split. econstructor. inversion H9. eauto. reflexivity. assumption. }
    {exists (Tid(maj, min0) tid0, s1' ++ [fAct tid' (Tid(maj, min'0) tid0) (c (fork M'))], s3, M).
     split. econstructor. inversion H9. eauto. reflexivity. assumption. }
    {exists  (Tid(maj, min'0) tid0, s1' ++ [joinAct], s3, M0). split. econstructor. 
     inversion H9. eauto. reflexivity. assumption. }
    {inversion H6. symmetry in H8. contradiction. }
   }
  }
  {intros. apply IHunspecPool in H2. inversion H2. inversion H3. exists x. 
   split. inversion H4. subst. eapply AddWeakening in H6. econstructor. eassumption. 
   reflexivity. assumption. }
Qed. 

Theorem lastElementsNotEqual : forall (T:Type) l1 l2 (t1 t2:T), t1 <> t2 -> l1++[t1] <> l2++[t2]. 
Proof.
  intros. generalize dependent l2. induction l1. 
  {simpl. unfold not. intros. destruct l2. 
   {simpl in H0. inversion H0. contradiction. }
   {simpl in H0. inversion H0. destruct l2; inversion H3. }
  }
  {unfold not in *. intros. destruct l2. inversion H0. destruct l1; inversion H3. 
   simpl in H0. inversion H0. apply IHl1 in H3. assumption. }
Qed. 
   

Theorem eraseHelper : 
  forall M M' P P', unspecPool P P' -> eraseTerm M P' M' -> eraseTerm M P M'.
Proof.
  intros. induction H0; eauto.  
  {assert(unspecPool P T). assumption. eapply LookupSame with(tid := tid) (T := (tid', s1, s2, M)) in H2. 
   inversion H2. inversion H4. inversion H6; subst; try(solve[destruct s1'; inversion H8]). 
   {destruct s1'; inversion H10. }
   {inversion H8. destruct s1'. simpl in *. inversion H7. subst. 
    {eapply eraseSpecReturn with (tid' := Tid(maj, min) tid0) (s1 := (s1'0 ++ [sAct (Tid(maj, min') tid0) M'])). 
     eapply IHeraseTerm1. assumption. reflexivity. eapply IHeraseTerm2. assumption. assumption. 
     eassumption. }
    {inversion H7. destruct s1'; inversion H11. }
   }
   {apply lastElementsNotEqual in H9. inversion H9. unfold not. intros. inversion H0. }
   {assumption. }
  }
Qed. 