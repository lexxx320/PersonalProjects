Require Import AST.     
Require Import Heap.    
Require Export NonSpec.  
Require Import sets. 
Require Import Coq.Sets.Ensembles. 
Require Import Coq.Logic.Classical_Prop. 
Require Import Coq.Program.Equality. 
Require Import Coq.Sets.Powerset_facts. 
Require Import sets. 

(*Incrememt the minor number of a thread ID*)
Fixpoint bump (t : tid) : tid := 
  match t with
    |Tid (maj, min)  t' => Tid (maj, S min) t'
  end.

(*Representation for specualtive heaps (see Heap.v for details)*)
Definition sHeap := heap (ivar_state).

(*Evaluation Contexts*)
Inductive ctxt : Type :=
|bindCtxt : ctxt -> trm -> ctxt
|specReturnCtxt : ctxt -> tid -> trm -> ctxt 
|specJoinCtxt : ctxt -> trm -> ctxt
|handleCtxt : ctxt -> trm -> ctxt
|appCtxt : ctxt -> trm -> ctxt
|fstCtxt : ctxt -> ctxt 
|sndCtxt : ctxt -> ctxt
|holeCtxt : ctxt.

Inductive val : trm -> Prop :=
|retVal : forall M, val (ret M)
|raiseVal : forall M, val (raise M)
|lamVal : forall M, val (lambda M)
|pairVal : forall M N, val (pair_ M N).

Inductive decompose : trm -> ctxt -> trm -> Prop :=
|decompBind : forall M N E M', ~ val M -> decompose M E M' ->
                               decompose (bind M N) (bindCtxt E N) M'
|decompBindVal : forall M N, val M -> decompose (bind M N) holeCtxt (bind M N)
|decompSpec : forall M N E M' tid, ~ val M -> decompose M E M' -> 
                               decompose (specReturn M tid N) (specReturnCtxt E tid N) M'
|decompSpecVal : forall M tid N, val M ->
                             decompose (specReturn M tid N) holeCtxt (specReturn M tid N)
|decompSpecJoin : forall M N E N', ~val N -> decompose N E N' ->
                              decompose (specJoin M N) (specJoinCtxt E M) N'
|decompSpecjoinVal : forall M N, val N ->
                                 decompose (specJoin M N) holeCtxt (specJoin M N)
|decompHandle : forall M M' N E, ~val M -> decompose M E M' -> 
                                 decompose (handle M N) (handleCtxt E N) M'
|decompHandleVal : forall M N, val M -> decompose (handle M N) holeCtxt (handle M N)
|decompApp : forall M N M' E, ~val M -> decompose M E M' ->
                              decompose (AST.app M N) (appCtxt E N) M'
|decompAppVal : forall M N, val M -> decompose (AST.app M N) holeCtxt (AST.app M N)
|decompFst : forall M E M', ~val M -> decompose M E M' -> 
                            decompose (fst M) (fstCtxt E) M'
|decompFstVal : forall M, val M -> decompose (fst M) holeCtxt (fst M)
|decompSnd : forall M E M', ~val M -> decompose M E M' -> 
                            decompose (snd M) (sndCtxt E) M'
|decompSndVal : forall M, val M -> decompose (snd M) holeCtxt (snd M)
|decompNew : decompose new holeCtxt new
|decompGet : forall i, decompose (get i) holeCtxt (get i)
|decompPut : forall i M, decompose (put i M) holeCtxt (put i M)
|decompFork : forall M, decompose (fork M) holeCtxt (fork M)
.  

Fixpoint fill (c:ctxt) (t:trm) : trm :=
  match c with
      |bindCtxt E N => bind (fill E t) N
      |specReturnCtxt E tid N => specReturn (fill E t) tid N
      |specJoinCtxt E M => specJoin M (fill E t)
      |handleCtxt E N => handle (fill E t) N
      |appCtxt E N => AST.app (fill E t) N
      |fstCtxt E =>fst (fill E t)
      |sndCtxt E => snd (fill E t)
      |holeCtxt => t
  end. 

Inductive basicAction : action -> trm -> nat -> Prop :=
|basicRead : forall x tid M E, decompose M E (get (fvar x)) -> 
                               basicAction (rAct x tid M) M tid
|basicWrite : forall x tid M E N, decompose M E (put (fvar x) N) -> 
                                  basicAction (wAct x tid M) M tid
|basicFork : forall x tid M E N, decompose M E (fork N) -> 
                                 basicAction (fAct x tid M) M tid
|basicNew : forall x tid M E, decompose M E new -> basicAction(cAct x tid M) M tid
|basicSpec : forall M M' N E tid j, decompose M E (spec M' N) ->
                                    basicAction(specRetAct tid j M) M j
.

Ltac cleanup :=
  match goal with
    |H:?x=?y |- _ => inversion H; subst; clear H
  end. 

Theorem decomposeEq : forall M E e, decompose M E e -> M = fill E e.
Proof.
  induction M; intros; try solve[inversion H; subst; auto];
  try solve[inversion H; subst; auto; simpl; apply IHM1 in H5; subst; auto]. 
  {inversion H; subst; auto. simpl. apply IHM1 in H6. subst; auto. }
  {inversion H; subst; auto. simpl. apply IHM2 in H5. subst. auto. }
  {inversion H; subst; auto. apply IHM in H2; subst; auto. }
  {inversion H; subst; auto. apply IHM in H2. subst. auto. } 
Qed. 

Theorem uniqueCtxtDecomp : forall t E e E' e',
                             decompose t E e -> decompose t E' e' ->
                             E = E' /\ e = e'. 
Proof.
  induction t; intros; try solve[inversion H; inversion H0; subst; auto]; try solve[
  inversion H; inversion H0; subst; simpl in *; try contradiction; auto; 
   eapply IHt1 in H6; eauto; inversion H6; subst; auto].
  {inversion H; inversion H0; subst; auto; try contradiction. 
   eapply IHt1 in H7; eauto. inversion H7; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction. 
   eapply IHt2 in H6. inversion H6. rewrite <- H1. rewrite <- H2. 
   auto. assumption. }
  {inversion H; inversion H0; subst; auto; try contradiction. 
   eapply IHt in H3; eauto. 
   inversion H3; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction.
   eapply IHt in H3; eauto. 
   inversion H3; subst; auto. }
Qed. 

Definition thread := tid * specStack * specStack * trm. 
Definition pool := Ensemble thread.
Definition tAdd := Add thread. 
Definition tIn := In thread. 
Definition tUnion := Union thread. 
Definition tCouple := Couple thread. 
Definition tSetminus := Setminus thread. 
Definition tSingleton := Singleton thread. 
Definition tIntersection := Intersection thread. 
Definition tEmptySet := Empty_set thread. 

Inductive rollback : tid -> list action -> sHeap -> pool -> sHeap -> pool -> Prop :=
RBDone : forall T maj min h min' M tid s1 s2 t1,
           tIn T t1 -> t1 = (Tid (maj, min') tid, s1, s2, M) ->
           rollback (Tid (maj,min) tid) s1 h T h T
|RBRead : forall s1 s1' s2 x tid M M' N h h' h'' T T' sc t A S ds t1 SRoll i j j' E l, 
            s1 = rAct x j' M'::s1' -> decompose M' E (get (fvar x)) ->
            heap_lookup x h = Some (sfull sc (Tid(i,j')l::ds) (S::A) t N) ->
            h' = replace x (sfull sc ds (S::A) t N) h -> 
            ~(tIn T t1) -> t1 = (Tid(i,j)l, s1, s2, M) ->
            rollback tid SRoll h' (tAdd T (Tid(i,j')l, s1', s2, M')) h'' T' ->
            rollback tid SRoll h (tAdd T t1) h'' T'
|RBFork : forall s1 s1' s2 s2' tid tid2 tid2' M M' N T T' h h' t1 t2 SRoll i j j' l E N',
            s1 = fAct tid2 j' M'::s1' -> decompose M' E (fork N') -> ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (Tid(i,j)l, s1, s2, M) -> t2 = (tid2', [specAct], s2', N) ->
            rollback tid SRoll h (tAdd T (Tid(i,j')l, s1', s2, M')) h' T' ->
            rollback tid SRoll h (tAdd (tAdd T t1) t2) h' T'
|RBWrite : forall s1 s1' s2 tid M M' N S A sc T T' h h' h'' x t1 SRoll i j j' l E N',
             s1 = wAct x j' M'::s1' -> decompose M' E (put (fvar x) N') ->
             heap_lookup x h = Some(sfull sc nil (S::A) (Tid(i,j')l) N) ->
             h' = replace x (sempty sc) h -> ~(tIn T t1) ->
             t1 = (Tid(i,j)l, s1, s2, M) -> rollback tid SRoll h' (tAdd T (Tid(i,j')l, s1', s2, M')) h'' T' ->
             rollback tid SRoll h (tAdd T t1) h'' T'
|RBNew : forall s1 s1' s2 tid M M' S A T T' h h' h'' x t1 SRoll i j j' l E,
           s1 = cAct x j' M'::s1' -> decompose M' E new -> 
           heap_lookup x h = Some (sempty (S::A)) ->
           h' = remove h x -> ~(tIn T t1) -> t1 = (Tid(i,j)l, s1, s2, M) ->
           rollback tid SRoll h' (tAdd T (Tid(i,j')l, s1', s2, M')) h'' T' ->
           rollback tid SRoll h (tAdd T t1) h'' T'
|RBSpec : forall s1 s1' s2 s2' tid tid2 tid''' M M' M'' N'' N N' E T T' h h' t1 t2 SRoll i j j' l,
            s1 = specRetAct tid2 j' M'::s1' -> decompose M' E (spec M'' N'') ->
            ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (Tid(i,j)l, s1, s2, M) -> t2 = (tid''', [sAct tid2 N'; specAct], s2', N) ->
            rollback tid SRoll h (tAdd T (Tid(i,j')l, s1', s2, M')) h' T' ->
            rollback tid SRoll h (tAdd (tAdd T t1) t2) h' T'
.

Hint Constructors rollback. 

(*Create thread ID for forked child*)
Definition extendTid (t:tid) : tid :=
  match t with
      |Tid (a, b) l => Tid (1,1) ((a,b)::l)
  end.

(*Lookup a thread ID in a pool, yields a thread if a particular thread in the pool
**matches the specified thread ID up to the minor number*)
Inductive thread_lookup : pool -> tid -> thread -> Prop :=
|hit : forall T t tid maj min min' s1 s2 M,
         tIn T t -> t = (Tid (maj, min') tid, s1, s2, M) -> thread_lookup T (Tid (maj, min) tid) t.

Hint Constructors thread_lookup. 

Inductive config : Type :=
|OK : sHeap -> pool -> pool -> config
|Error : config. 

Fixpoint wrapActs acts N :=
  match acts with
      |rAct x i M::acts' => rAct x i (specJoin N M)::wrapActs acts' N
      |wAct x i M::acts' => wAct x i (specJoin N M)::wrapActs acts' N
      |cAct x i M::acts' => cAct x i (specJoin N M)::wrapActs acts' N
      |sAct i M::acts' => sAct i (specJoin N M)::wrapActs acts' N
      |specRetAct tid i M::acts' => specRetAct tid i (specJoin N M)::
                                               wrapActs acts' N
      |fAct x i M::acts' => fAct x i (specJoin N M)::wrapActs acts' N
      |specAct::acts' => specAct::wrapActs acts' N
      |nil => nil
  end. 

Inductive step : sHeap -> pool -> pool -> config -> Prop :=
|BetaRed : forall E e N tid s1 s2 h T t, 
             decompose t E (AST.app (lambda e) N) ->            
             step h T (tSingleton(tid,s1,s2,t)) 
                  (OK h T (tSingleton(tid,s1,s2,fill E (open 0 N e))))
|ProjL : forall tid s1 s2 E V1 V2 h T t, 
           decompose t E (fst (pair_ V1 V2)) ->
           step h T (tSingleton(tid,s1,s2,t)) 
                (OK h T (tSingleton(tid,s1,s2,fill E V1)))
|ProjR : forall tid s1 s2 E V1 V2 h T t, 
           decompose t E (snd (pair_ V1 V2)) -> 
           step h T (tSingleton(tid,s1,s2,t)) 
                (OK h T (tSingleton(tid,s1,s2,fill E V2)))
|Bind : forall tid h E T N M s1 s2 t, decompose t E (bind (ret M) N) ->
  step h T (tSingleton (tid, s1, s2, t)) 
       (OK h T (tSingleton (tid,s1,s2,fill E(AST.app N M))))
|BindRaise : forall tid h E T N M s1 s2 t, decompose t E (bind (raise M) N)->
  step h T (tSingleton (tid,s1,s2,t)) 
       (OK h T (tSingleton (tid,s1,s2,fill E (raise M))))
|Handle : forall tid h E T N M s1 s2 t, decompose t E (handle (raise M) N) ->
  step h T (tSingleton (tid,s1,s2,t)) 
       (OK h T (tSingleton (tid,s1,s2,fill E (AST.app  N M))))
|HandleRet : forall tid h E T N M s1 s2 t, decompose t E (handle (ret M) N) ->
  step h T (tSingleton (tid,s1,s2,t)) 
       (OK h T (tSingleton (tid,s1,s2,fill E (ret M))))
|Terminate : forall tid h T M s2, 
               step h T (tSingleton (tid, nil, s2, ret M)) (OK h T tEmptySet)
|Fork : forall tid tid' h T M s1 s2 E t i j, 
          decompose t E (fork M) -> tid' = Tid(1, 1) ((i, j)::tid) -> 
          step h T (tSingleton (Tid(i, j) tid, s1, s2,t)) 
        (OK h T
            (tCouple (Tid(i, S j)tid, fAct tid' j (fill E(fork M))::s1, s2, fill E(ret unit)) 
                     (tid', [specAct], nil, M)))
|Get : forall tid h h' T N s1 s2 E x s ds writer sc t i j l,
         decompose t E (get (fvar x)) -> 
         heap_lookup x h = Some(sfull sc ds s writer N) -> 
         tid = Tid(i, j) l -> h' = replace x (sfull sc (tid::ds) s writer N) h ->
         step h T (tSingleton (tid, s1, s2, fill E(get (fvar x))))
              (OK h' T (tSingleton (bump tid, rAct x j (fill E(get (fvar x)))::s1, s2, fill E(ret N))) )
|Put : forall E x N h sc h' s1 s2 tid T t i j l, 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil s1 tid N) h -> tid = Tid(i, j) l ->
         step h T (tSingleton (tid, s1, s2, fill E(put (fvar x) N))) (OK h' T
              (tSingleton (bump tid, wAct x j (fill E(put (fvar x) N))::s1, s2, fill E(ret unit))))
|Overwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds tid tid' S i j l, 
               decompose t E (put (fvar x) N) -> heap_lookup x h = Some (sfull S ds (S'::A) tid' N') ->
               rollback tid' (S'::A) h TR h' TR' -> heap_lookup x h' = Some (sempty S) ->
               h'' = replace x (sfull S nil nil tid N) h' -> tid = Tid(i, j) l ->
               step h T (tAdd TR (tid, nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (tid, nil, wAct x j (fill E(put (fvar x) N))::s2, fill E (ret unit))))
|ErorrWrite : forall h T t E x N N' tid tid' ds s2,  
                decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sfull nil ds nil tid' N') ->
                step h T (tSingleton (tid, nil, s2, fill E(put (fvar x) N))) Error
|New : forall E h h' x tid t s1 s2 T i j l,
         decompose t E new -> (x, h') = extend (sempty s1) h -> tid = Tid(i, j) l -> 
         step h T (tSingleton (tid, s1, s2, fill E new)) 
              (OK h' T (tSingleton (bump tid, cAct x j (fill E new)::s1, s2, fill E(ret(fvar x)))))
|Spec : forall E M t N tid' tid s1 s2 T h i j l, 
          decompose t E (spec M N) -> tid' = extendTid tid -> tid = Tid(i, j) l ->
          step h T (tSingleton (tid, s1, s2, fill E (spec M N))) (OK h T
               (tCouple (bump tid, specRetAct tid' j (fill E (spec M N))::s1, s2,fill E(specReturn M tid' N))
                        (tid', [sAct tid' N], nil, N)))
|SpecJoin : forall t E M M' N0 N1 tid maj min min' tid' tid'' T h t1 t2 s1 s1' s2 s2',
              decompose t E (specReturn (ret N1) (Tid(maj,min) tid') N0) ->
              s1 = s1' ++ [sAct tid'' M] ->
              t1 = (tid,nil,s2, t) -> t2 = (Tid(maj,min')tid',s1,s2',M') ->
              step h T (tCouple t1 t2) 
                   (OK h T (tSingleton(tid,wrapActs s1' N1, s2,
                                       fill E (specJoin (ret N1) M))))
|SpecRB : forall t E' h h' tid tid' maj min  min'' T T' E M' N0 s2 s1' a s2' t1 t2 TRB, 
            decompose t E' (specReturn (raise E) (Tid(maj,min'') tid') N0)->
            t1 = (tid,nil,s2,t) -> t2 = (Tid(maj,min) tid',s1'++[a],s2',M') -> 
            ~ (exists p, thread_lookup TRB tid p) -> 
            thread_lookup TRB (Tid (maj, min) tid') t2 -> 
            ~ (exists p', thread_lookup T' (Tid (maj, min) tid') p') ->
            rollback (Tid (maj, min) tid') [a] h (tAdd TRB t2) h' T' ->
            step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, nil, s2, fill E'(raise E))))
|SpecRaise : forall E' N h tid s2 T E t1 t,
               decompose t E' (specJoin(ret N)(raise E)) ->
               t1 = (tid, nil, s2, t) -> 
               step h T (tSingleton t1) 
                    (OK h T (tSingleton (tid, nil, s2, fill E' (raise E))))
|PopRead : forall tid tid' t s1 s1' s2 M M' N T h x ds, 
             s1 = s1' ++ [rAct x tid' M'] -> heap_lookup x h = Some (sfull nil ds nil t N) ->
             step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (rAct x tid' M')::s2, M)))
|PopWrite : forall tid tid'  s s' t s1 s1' s2 M M' N T h h' x ds,
              s1 = s1' ++ [wAct x tid' M'] -> heap_lookup x h = Some(sfull s ds s' t N) ->
              h' = replace x (sfull nil ds s' t N) -> 
              step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (wAct x tid' M')::s2, M)))
|PopNewFull : forall h h' s1 s1' s2 i tid tid' M' ds s s' t M N T, 
                s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = Some(sfull s ds s' t N) ->
                h' = replace i (sfull nil ds s' t N) h -> 
                step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (cAct i tid' M')::s2, M)))
|PopNewEmpty : forall h h' s1 s1' s2 i tid tid' M' s M T, 
                 s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = Some(sempty s) ->
                  h' = replace i (sempty nil) h -> 
                 step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (cAct i tid' M')::s2, M)))
|PopFork : forall h s1 s1' s1'' s1''' s2 s2' tid tid' tid1 tid2 M' M N T , 
             s1 = s1' ++ [fAct tid1 tid2 M'] -> s1'' = s1''' ++ [specAct] ->
             step h T (tCouple (tid, s1, s2, M) (tid', s1'', s2', N)) (OK h T 
                  (tCouple (tid, s1', (fAct tid1 tid2 M')::s2, M)
                           (tid', s1''', specAct::s2', N)))
.

Hint Constructors step. 
 
Inductive multistep : sHeap -> pool -> pool -> config -> Prop :=
|multi_refl : forall h p1 p2, multistep h p1 p2 (OK h p1 p2)
|multi_step : forall c T1 T2 P1 P2 P2' h h',
                T2 = tUnion P1 P2 -> Disjoint thread P1 P2 ->
                step h (tUnion P1 T1) P2 (OK h' (tUnion P1 T1) P2') ->
                multistep h' T1 (tUnion P1 P2') c ->
                multistep h T1 T2 c
|multi_error1 : forall T1 T2 P1 P2 h, 
                  T2 = tUnion P1 P2 -> Disjoint thread P1 P2 ->
                  step h (tUnion P1 P2) P2 Error ->
                  multistep h T1 T2 Error
. 
 
Hint Constructors multistep. 

Inductive unspecHeap : sHeap -> sHeap -> Prop :=
  |unSpecSE : forall h h' i hd tl, unspecHeap h h' -> (*spec empty*)
                                   unspecHeap ((i, sempty (hd::tl)) :: h) h'
  |unSpecCE : forall h h' i, unspecHeap h h' -> (*commit empty*)
                             unspecHeap ((i, sempty nil) :: h) ((i, sempty nil) :: h')
  |unspecSF : forall h h' i hd tl d s t N, 
                unspecHeap h h' -> (*spec created full*)
                unspecHeap ((i, sfull (hd::tl) d s t N) :: h) h'
  |unspecCCSF : forall h h' i d hd tl t M, 
                  unspecHeap h h' ->  (*commit created spec full*)
                  unspecHeap ((i, sfull nil d (hd::tl) t M)::h) ((i, sempty nil)::h')
  |unspecCCCF : forall h h' i d t M, 
                  unspecHeap h h' ->   (*commit created, commit full*)
                  unspecHeap ((i, sfull nil d nil t M)::h) 
                             ((i, sfull nil nil nil t M)::h')
  |unspecNil : unspecHeap nil nil
.
Hint Constructors unspecHeap. 

Inductive unspecThread : thread -> option thread -> Prop :=
|unspecCommit : forall tid s2 M,
                  unspecThread (tid, nil, s2, M) (Some(tid, nil, s2, M))
|unspecRead : forall tid s1 s1' s2 M i maj min min' c t,
             decompose t c (get (fvar i)) -> 
             s1 = s1' ++ [rAct i min' t] ->
             unspecThread (Tid (maj, min) tid, s1, s2, M) 
                          (Some(Tid (maj, min') tid, nil, s2, fill c(get (fvar i))))
|unspecWrite : forall tid s1 s1' s2 M M' i maj min min' c t,
       decompose t c (put (fvar i) M') ->
       s1 = s1' ++ [wAct i min' t] ->
       unspecThread (Tid (maj, min) tid, s1, s2, M) 
                    (Some(Tid (maj, min') tid, nil, s2, (fill c(put (fvar i) M'))))
|unspecCreate : forall tid s1 s1' s2 M i maj min min' c t,
                  decompose t c new -> 
                  s1 = s1' ++ [cAct i min' t] ->
                  unspecThread (Tid (maj, min) tid, s1, s2, M) 
                               (Some(Tid (maj, min') tid, nil, s2, (fill c new)))
|unspecSpec : forall tid s1 s1' s2 M maj min min' M',
   s1 = s1' ++ [sAct (Tid (maj, min') tid) M'] ->
   unspecThread (Tid (maj, min) tid, s1, s2, M) 
                (Some(Tid (maj, min') tid, [sAct (Tid (maj, min') tid) M'], s2, M'))
|unSpecFork : forall c tid s1 s1' s2 M tid' M' maj min min' t,
                  decompose t c (fork M') -> 
                  s1 = s1' ++ [fAct tid' min' t] ->
                  unspecThread (Tid (maj, min) tid, s1, s2, M) 
                               (Some(Tid (maj, min') tid, nil, s2, fill c(fork M')))
|unSpecSpecret : forall t c M M' N maj min min' tid tid' s1 s1' s2, 
             decompose t c (spec M' N) -> s1 = s1' ++ [specRetAct tid' min' t] ->
             unspecThread(Tid(maj,min) tid, s1, s2, M)
                         (Some(Tid(maj,min') tid, nil, s2, t))
|unspecCreatedSpec : forall s1 s1' s2 M tid,
                       s1 = s1' ++ [specAct] -> unspecThread (tid, s1, s2, M) None
.

Hint Constructors unspecThread. 

Inductive unspecPoolAux (T:pool) : pool :=
|unspecAux : forall t t' s1 s2 M, thread_lookup T t (t, s1, s2, M) ->
                                  unspecThread (t, s1, s2, M) (Some t') -> tIn (unspecPoolAux T) t'.

Inductive unspecPool : pool -> pool -> Prop :=
|unspecP : forall T, unspecPool T (unspecPoolAux T).

Hint Constructors unspecPool. 

Inductive wellFormed : sHeap -> pool -> Prop :=
|wf : forall H H' T T', unspecPool T T' -> unspecHeap H H' -> 
                        multistep H' tEmptySet T' (OK H tEmptySet T) ->
                        wellFormed H T
.

Inductive specActionsAux (T:pool) : Ensemble (tid*specStack) :=
|saAux : forall t s1, (exists s2 M, thread_lookup T t (t, s1, s2, M)) ->
                      In (tid*specStack) (specActionsAux T) (t, s1)
.

Inductive specActions : pool -> Ensemble (tid * specStack) -> Prop :=
|sa : forall T, specActions T (specActionsAux T). 

Hint Constructors specActions specActionsAux. 

Inductive commitActionsAux (T:pool) : Ensemble (tid*specStack) :=
|caAux : forall t s2, (exists s1 M, thread_lookup T t (t, s1, s2, M)) -> 
                      In (tid*specStack) (commitActionsAux T) (t, s2).

Inductive commitActions : pool -> Ensemble (tid*specStack) -> Prop :=
|ca : forall T, commitActions T (commitActionsAux T). 

Hint Constructors commitActions commitActionsAux. 

Theorem lastElemNeq : forall (T:Type) s1 s2 (e1 e2:T), 
                        s1 ++ [e1] = s2 ++ [e2] -> e1 <> e2 -> False. 
Proof.
  intros. 
  generalize dependent s2. induction s1. 
  {intros. destruct s2. inversion H. contradiction. inversion H. 
   destruct s2; inversion H3. }
  {intros. destruct s2. inversion H. destruct s1; inversion H3. inversion H. 
   apply IHs1 in H3. assumption. }
Qed. 

Theorem consListNeq : forall (T:Type) (x:T) y, y = x::y -> False.
Proof.
  induction y; intros. 
  {inversion H. }{inversion H. apply IHy in H2. assumption. }Qed. 

Ltac invertListNeq := 
  match goal with
      |H:[] = ?l ++ [?x] |- _ => destruct l; inversion H
      |H:[?x] = ?l ++ [?y] |- _ => destruct l; inversion H; clear H; invertListNeq
      |H:?s1 ++ [?e1] = ?s2 ++ [?e2] |- _ => apply lastElemNeq in H; inversion H; intros c; inversion c
      |H:?y=?x::?y |- _ => apply consListNeq in H; inversion H
      |H:?y=?x::?y |- _ => symmetry in H; apply consListNeq in H; inversion H
  end. 

Theorem eraseSomeLookup : forall T tid t t', unspecThread t (Some t') -> 
                                             thread_lookup T tid t ->
                                             thread_lookup (unspecPoolAux T) tid t'.
Proof.
  intros. remember (Some t'). induction H;try(inversion H0; subst; 
      repeat(match goal with
               |H:Some ?x = Some ?y |- _ => inversion H; clear H
               |H:(?a1,?b1,?c1,?d1) = (?a2,?b2,?c2,?c3) |- _ => inversion H; clear H
          end); econstructor; eauto; econstructor; eauto; subst; econstructor; eauto).  
  {inversion Heqo. } Qed. 
 
Theorem IncludedSingleton : forall T S s, Included T (Singleton T s) S -> In T S s. 
Proof.
  intros. unfold Included in H. assert(In T (Singleton T s) s). constructor. apply H in H0. 
  assumption. Qed. 

Definition commitPool (T:pool) : Prop := forall tid s1 s2 M, tIn T (tid, s1, s2, M) -> s1 = nil. 

Theorem commitPoolUnspecUnchanged : forall T, commitPool T -> T = unspecPoolAux T. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split. 
  {intros. destruct x. destruct p. destruct p. destruct t0. destruct p. 
   econstructor. econstructor. eassumption. reflexivity. unfold commitPool in H. 
   apply H in H0. subst. constructor. }
  {intros. inversion H0. unfold commitPool in H. inversion H1. apply H in H4. 
   subst. inversion H2; try(destruct s1'; inversion H12). 
   {subst. inversion H1. assumption. } 
   {destruct s1'; inversion H4. }
  }
Qed. 

Theorem unspecDistribute : forall t1 t2, 
                             unspecPoolAux(tUnion t1 t2) = 
                             tUnion(unspecPoolAux t1) (unspecPoolAux t2). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H. inversion H0. subst. inversion H3. 
   {constructor. eapply unspecAux. econstructor. eassumption. reflexivity. assumption. }
   {apply Union_intror. econstructor. econstructor. eassumption. reflexivity. assumption. }
  }
  {inversion H. 
   {inversion H0. inversion H2. subst. econstructor. econstructor. econstructor. 
    eassumption. reflexivity. assumption. }
   {inversion H0. inversion H2; subst. econstructor. econstructor. eapply Union_intror. 
    eassumption. reflexivity. assumption. }
  }
Qed. 

Theorem stepUnusedPool : forall t1 t2 t2' p1 h h', 
                           step h (tUnion t1 p1) t2 (OK h' (tUnion t1 p1) t2') <->
                           step h p1 t2 (OK h' p1 t2').
Proof.
  intros. split. 
  {intros. inversion H; eauto. }
  {intros. inversion H; eauto. }
Qed. 

Theorem multistepUnusedPool : forall h h' t1 t2 p1 p1',
                                multistep h (tUnion t1 t2) p1 (OK h' (tUnion t1 t2) p1') <->
                                multistep h t2 p1 (OK h' t2 p1'). 
Proof.
  split. 
  {intros. remember (OK h' (tUnion t1 t2) p1'). induction H. 
   {inversion Heqc. subst. constructor. }
   {inversion Heqc; subst. unfold tUnion in H1. rewrite Union_commutative in H1. apply stepUnusedPool in H1. 
    econstructor.  reflexivity. assumption. unfold tUnion. rewrite Union_commutative. apply stepUnusedPool.
    eassumption. apply IHmultistep in H3. assumption. }
   {inversion Heqc. }
  }
  {intros. remember (OK h' t2 p1'). induction H; eauto. 
   {inversion Heqc; subst. constructor. }
   {eapply multi_step. eassumption. assumption. unfold tUnion. rewrite Union_commutative. 
    rewrite Union_associative. rewrite stepUnusedPool. rewrite Union_commutative. eassumption. 
    apply IHmultistep. assumption. }
   {inversion Heqc. }
  }
Qed. 

Axiom MultistepUntouchedUnused : forall h h' T1 T2 T2' T3,
                                   multistep h T3 (tUnion T1 T2) (OK h' T3 (tUnion T1 T2')) <->
                                   multistep h (tUnion T1 T3) T2 (OK h' (tUnion T1 T3) T2'). 

Theorem WFFrameRule : forall T1 T2 H, commitPool T2 -> (wellFormed H (tUnion T1 T2) <-> 
                                                        wellFormed H T1). 
Proof.
  intros. split; intros. 
  {inversion H1. inversion H3. subst. rewrite unspecDistribute in H5. 
   assert(T2 = unspecPoolAux T2). apply commitPoolUnspecUnchanged. assumption.
   rewrite <- H2 in H5. unfold tUnion in *. rewrite Union_commutative in H5. 
   rewrite Union_commutative with (A:=T1) in H5. apply MultistepUntouchedUnused in H5. 
   unfold tUnion in H5.  rewrite multistepUnusedPool in H5. econstructor. 
   econstructor. eassumption. assumption. }
  {inversion H1. econstructor. econstructor. eassumption. rewrite unspecDistribute. 
   assert(T2 = unspecPoolAux T2). apply commitPoolUnspecUnchanged. assumption. 
   rewrite <- H8. rewrite <- multistepUnusedPool with(t1:=T2) in H5. 
   rewrite <- MultistepUntouchedUnused in H5. inversion H3. subst T'. 
   unfold tUnion in *. rewrite Union_commutative in H5. 
   rewrite Union_commutative with(A:=T2)in H5. assumption. }
Qed.  

Theorem unspecUnspeculatedHeap : forall H H', unspecHeap H H' -> unspecHeap H' H'. 
Proof.
  intros. induction H0; auto. Qed. 

Theorem unspecDependentReader : forall H H',
                                  unspecHeap H H' -> 
                                  forall x sc ds s w N tid, heap_lookup x H = Some (sfull sc ds s w N) ->
                                  unspecHeap (replace x (sfull sc (tid::ds) s w N) H) H'. 
Proof.
  intros H H' U. induction U; intros; auto. 
  {simpl in *. destruct (beq_nat x i). inversion H. eapply IHU in H. 
   constructor. eassumption. }
  {simpl in *. destruct (beq_nat x i). inversion H. constructor. eapply IHU in H. eassumption. }
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H; subst. constructor. assumption. 
   eapply IHU in H. constructor. eassumption. }
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. constructor. assumption. eapply IHU in H. constructor. eassumption. }
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. constructor. assumption. eapply IHU in H. constructor. eassumption. }
Qed. 

Ltac invertExists :=
  match goal with
      |H:exists x, ?X |- _ => inversion H; clear H; try invertExists
  end.

Theorem unspecDependentReader2 : forall h H', unspecHeap h H' -> forall x sc d ds a t N,
                                              heap_lookup x h = Some (sfull sc (d::ds) a t N) -> 
                                              unspecHeap (replace x (sfull sc ds a t N) h) H'.
Proof. 
  intros h H' U. induction U; intros; eauto;
  try solve[simpl in *; destruct(beq_nat x i);[inversion H; eauto|eauto]]. 
  {simpl in *. destruct (beq_nat x i) eqn :eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. constructor. assumption. constructor. eapply IHU; eauto. }
  {simpl in *; destruct (beq_nat x i) eqn:eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. eauto. eauto. }
Qed.   

Theorem unspecSpecfull : forall h H', unspecHeap h H' -> forall x sc S A t N,
                                              heap_lookup x h = Some (sfull sc nil (S::A) t N) -> 
                                              unspecHeap (replace x (sempty sc) h) H'.
Proof. 
  intros h H' U. induction U; intros; eauto; 
  try solve[simpl in *; destruct(beq_nat x i);[inversion H; eauto|eauto]]. 
  {simpl in *. destruct (beq_nat x i) eqn:eq. inversion H; subst. apply beq_nat_true in eq. 
   subst. eauto. eauto. }
Qed. 

Theorem unspecSpecEmpty : forall h H', unspecHeap h H' -> forall x S A, 
                                              heap_lookup x h = Some (sempty (S::A)) -> 
                                              unspecHeap (remove h x) H'.
Proof.
  intros h H' U; induction U; intros; eauto;
  try solve[simpl in *; destruct (beq_nat x i); [inversion H; eauto|eauto]]. Qed. 

Theorem rollbackUnspeculatedHeap : forall H H' H'' tid T T' S, 
                                     unspecHeap H H' -> rollback tid S H T H'' T' -> unspecHeap H'' H'. 
Proof.
  intros. generalize dependent H'. induction H1; intros; subst; auto.
  {eapply IHrollback. eapply unspecDependentReader2 in H6. eassumption. eassumption. }
  {eapply IHrollback. eapply unspecSpecfull in H6; eauto. }
  {eapply IHrollback. eapply unspecSpecEmpty in H6; eauto. }
Qed. 

Theorem inUnspecPool : forall t t', tSingleton t = unspecPoolAux t' -> tIn (unspecPoolAux t') t.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. 
  inversion H; clear H. assert(In thread (tSingleton t) t). constructor. apply H0 in H. 
  assumption. Qed. 

Theorem unspecHeapStep : forall t t' t'' ut T H H' H'' UH,
                           unspecPool t ut -> unspecPool t' ut -> unspecHeap H UH ->
                           unspecHeap H' UH -> unspecPool t'' ut ->
                           step H' T t' (OK H'' T t'') -> unspecHeap H'' UH.
Proof.
  intros. inversion H5; subst; auto. 
  {eapply unspecDependentReader in H3. eassumption. assumption. }
  { admit. }
  {(*overwrite case*)admit. }
  {admit. }
  {eapply rollbackUnspeculatedHeap in H3. eassumption. eassumption. }
Qed. 

Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 
 
Inductive ctxtWF (e:trm) : ctxt -> Prop :=
|bindWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (bindCtxt E N)
|specWF : forall N E t, ctxtWF e E -> ~val (fill E e) ->
                      ctxtWF e (specReturnCtxt E t N)
|specJoinWF : forall N E,ctxtWF e E -> ~val (fill E e) -> 
                         ctxtWF e (specJoinCtxt E N)
|handleWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (handleCtxt E N)
|appWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (appCtxt E N)
|fstWF : forall E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (fstCtxt E)
|sndWF : forall E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (sndCtxt E)
|holEWF : ctxtWF e holeCtxt. 

Theorem decomposeDecomposed : forall E e, ctxtWF e E ->
                                          decompose e holeCtxt e -> 
                                          decompose (fill E e) E e. 
Proof.
  intros. induction H; try solve[simpl; constructor; auto]. 
  {simpl. assumption. }
Qed. 

Hint Constructors ctxtWF. 

Theorem decomposeWF : forall t E e, decompose t E e -> ctxtWF e E. 
Proof.
  induction t; intros; try solve[inversion H]; 
  try solve[inversion H; subst; auto; copy H5; apply IHt1 in H5; constructor; auto; 
   apply decomposeEq in H0; subst; auto].
  {inversion H; subst; auto. econstructor. apply IHt1; auto. apply decomposeEq in H6.
   subst; auto. }
  {inversion H; subst; auto. econstructor. apply IHt2; auto. apply decomposeEq in H5.
   subst. assumption. }
  {inversion H; subst; auto. constructor. apply IHt. auto. 
   apply decomposeEq in H2; subst; auto. }
  {inversion H; subst; auto. constructor. apply IHt. auto. 
   apply decomposeEq in H2; subst; auto. }
Qed. 

Theorem LookupSame :
  forall P P', unspecPool P P' ->
               forall tid T, thread_lookup P' tid T ->
                             exists T', thread_lookup P tid T' /\ unspecThread T' (Some T).
Proof.
  intros. inversion H. rewrite <- H2 in H0. inversion H0. subst. 
  {inversion H3. subst. inversion H2; 
   try(solve[econstructor; split; [subst; inversion H1; eauto;eauto | subst; econstructor;eauto;eauto]]).
  }
Qed. 