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
|specReturnCtxt : ctxt -> trm -> ctxt 
|handleCtxt : ctxt -> trm -> ctxt
|holeCtxt : ctxt.

Fixpoint decompose (t:trm) : (ctxt * trm) :=
  match t with
      |bind M N => let (E, M') := decompose M
                   in (bindCtxt E N, M')
      |specReturn M N => let (E, M') := decompose M
                         in (specReturnCtxt E N, M')
      |handle M N => let (E, M') := decompose M
                     in (handleCtxt E N, M')
      |_ => (holeCtxt, t)
  end. 

Fixpoint fill (c:ctxt) (t:trm) : trm :=
  match c with
      |bindCtxt E N => bind (fill E t) N
      |specReturnCtxt E N => specReturn (fill E t) N
      |handleCtxt E N => handle (fill E t) N
      |holeCtxt => t
  end. 

Theorem decomposeEq : forall M E e, decompose M = (E, e) -> M = fill E e.
Proof.
  induction M; intros; simpl in *; inversion H; subst; try reflexivity; try solve[
  destruct (decompose M1); inversion H; inversion H1; subst; simpl;
   assert((c,e)=(c,e)) by reflexivity; apply IHM1 in H0; subst; reflexivity]. 
Qed. 


Theorem uniqueCtxtDecomp : forall t E e E' e',
                             decompose t = (E, e) -> decompose t = (E', e') ->
                             E = E' /\ e = e'. 
Proof.
  induction t; intros; simpl in *; try(inversion H; inversion H0; subst; 
                                   split; reflexivity);try solve[
  destruct (decompose t1); inversion H; inversion H0; subst; split; auto]. 
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
|RBRead : forall s1 s1' s2 x tid tid' tid'' M M' N h h' h'' T T' sc t A S ds t1 SRoll, 
            s1 = rAct x tid'' M'::s1' -> heap_lookup x h = Some (sfull sc (tid''::ds) (S::A) t N) ->
            h' = replace x (sfull sc ds (S::A) t N) h -> 
            ~(tIn T t1) -> t1 = (tid', s1, s2, M) ->
            rollback tid SRoll h' (tAdd T (tid'', s1', s2, M')) h'' T' ->
            rollback tid SRoll h (tAdd T t1) h'' T'
|RBFork : forall s1 s1' s2 s2' tid tid' tid'' tid2 M M' N T T' h h' t1 t2 SRoll,
            s1 = fAct tid2 tid'' M'::s1' -> ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (tid', s1, s2, M) -> t2 = (tid'', [specAct], s2', N) ->
            rollback tid SRoll h (tAdd T (tid'', s1', s2, M')) h' T' ->
            rollback tid SRoll h (tAdd (tAdd T t1) t2) h' T'
|RBWrite : forall s1 s1' s2 tid tid' tid'' M M' N S A sc T T' h h' h'' x t1 SRoll,
             s1 = wAct x tid'' M'::s1' -> heap_lookup x h = Some(sfull sc nil (S::A) tid'' N) ->
             h' = replace x (sempty sc) h -> ~(tIn T t1) ->
             t1 = (tid', s1, s2, M) -> rollback tid SRoll h' (tAdd T (tid'', s1', s2, M')) h'' T' ->
             rollback tid SRoll h (tAdd T t1) h'' T'
|RBNew : forall s1 s1' s2 tid tid' tid'' M M' S A T T' h h' h'' x t1 SRoll,
           s1 = cAct x tid'' M'::s1' -> heap_lookup x h = Some (sempty (S::A)) ->
           h' = remove h x -> ~(tIn T t1) -> t1 = (tid', s1, s2, M) ->
           rollback tid SRoll h' (tAdd T (tid'', s1', s2, M')) h'' T' ->
           rollback tid SRoll h (tAdd T t1) h'' T'
|RBSpec : forall s1 s1' s2 s2' tid tid2 tid' tid'' tid''' M M' N N' T T' h h' t1 t2 SRoll,
            s1 = fAct tid2 tid'' M'::s1' -> ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (tid', s1, s2, M) -> t2 = (tid''', [sAct tid2 N'; specAct], s2', N) ->
            rollback tid SRoll h (tAdd T (tid'', s1', s2, M')) h' T' ->
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

Inductive step : sHeap -> pool -> pool -> config -> Prop :=
|Bind : forall tid h E T N M s1 s2 t, decompose t = (bindCtxt E N, ret M) ->
  step h T (tSingleton (tid, s1, s2, t)) (OK h T (tSingleton (tid,s1,s2,fill E(AST.app N M))))
|BindRaise : forall tid h E T N M s1 s2 t, decompose t = (bindCtxt E N, raise M) ->
  step h T (tSingleton (tid,s1,s2,t)) (OK h T (tSingleton (tid,s1,s2,fill E (raise M))))
|Handle : forall tid h E T N M s1 s2 t, decompose t = (handleCtxt E N, raise M) ->
  step h T (tSingleton (tid,s1,s2,t)) (OK h T (tSingleton (tid,s1,s2,fill E (AST.app  N M))))
|HandleRet : forall tid h E T N M s1 s2 t, decompose t = (handleCtxt E N, ret M) ->
  step h T (tSingleton (tid,s1,s2,t)) (OK h T (tSingleton (tid,s1,s2,fill E (ret M))))
|Terminate : forall tid h T M s2, 
               step h T (tSingleton (tid, nil, s2, ret M)) (OK h T tEmptySet)
|Fork : forall tid tid' h T M s1 s2 E t, 
          decompose t = (E, fork M) -> tid' = extendTid tid -> 
          step h T (tSingleton (tid, s1, s2,t)) (OK h T
               (tCouple (bump tid, fAct tid' tid (fill E(fork M))::s1, s2, fill E(ret unit)) 
               (tid', [specAct], nil, M)))
|Get : forall tid h h' T N s1 s2 E x s ds writer sc t,
         decompose t = (E, get (fvar x)) -> heap_lookup x h = Some(sfull sc ds s writer N) -> 
         h' = replace x (sfull sc (tid::ds) s writer N) h ->
         step h T (tSingleton (tid, s1, s2, fill E(get (fvar x)))) (OK h' T 
              (tSingleton (bump tid, rAct x tid (fill E(get (fvar x)))::s1, s2, fill E(ret N))) )
|Put : forall E x N h sc h' s1 s2 tid T t, 
         decompose t = (E, put (fvar x) N) -> heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil s1 tid N) h ->
         step h T (tSingleton (tid, s1, s2, fill E(put (fvar x) N))) (OK h' T
              (tSingleton (bump tid, wAct x tid (fill E(put (fvar x) N))::s1, s2, fill E(ret unit))))
|Overwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds tid tid' S, 
               decompose t = (E, put (fvar x) N) -> heap_lookup x h = Some (sfull S ds (S'::A) tid' N') ->
               rollback tid' (S'::A) h TR h' TR' -> heap_lookup x h' = Some (sempty S) ->
               h'' = replace x (sfull S nil nil tid N) h' -> 
               step h T (tAdd TR (tid, nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (tid, nil, wAct x tid (fill E(put (fvar x) N))::s2, fill E (ret unit))))
|ErorrWrite : forall h T t E x N N' tid tid' ds s2,  
                decompose t = (E, put (fvar x) N) -> heap_lookup x h = Some(sfull nil ds nil tid' N') ->
                step h T (tSingleton (tid, nil, s2, fill E(put (fvar x) N))) Error
|New : forall E h h' i tid t s1 s2 T,
         decompose t = (E, new) -> (i, h') = extend (sempty s1) h -> 
         step h T (tSingleton (tid, s1, s2, fill E new)) (OK h' T
              (tSingleton (bump tid, cAct i tid (fill E new)::s1, s2, fill E(ret(fvar i)))))
|Spec : forall E M t N tid' tid s1 s2 T h s1', 
          decompose t = (E, spec M N) -> tid' = extendTid tid -> 
          s1' = [sAct tid' N; specAct] ->
          step h T (tSingleton (tid, s1, s2, fill E (spec M N))) (OK h T
               (tCouple (bump tid, fAct tid' tid (fill E (spec M N))::s1, s2,fill E(specReturn M (threadId tid')))
                        (tid', s1', nil, N)))
|PopSpec : forall t E M N1 N2 tid maj min min' tid' tid'' T h t1 t2 s1 s1' s2 s2',
             decompose t = (specReturnCtxt E (threadId (Tid(maj,min)tid')), ret N1) ->
             s1 = s1' ++ [sAct tid'' M] ->
             t1 = (tid, nil, s2, fill E(specReturn (ret N1) (threadId (Tid(maj, min) tid')))) ->
             t2 = (Tid(maj, min') tid', s1, s2', ret N2) ->
             step h T (tCouple t1 t2) (OK h T (tCouple t1 (Tid(maj, S min')tid', s1', s2', ret N2)))
|SpecJoin : forall E h s2 s2' tid tid' N1 N2 maj min min' T t1 t2 t,
              decompose t = (specReturnCtxt E (threadId(Tid(maj,min) tid')), ret N1) ->
              t1 = (tid, nil, s2, fill E(specReturn (ret N1) (threadId (Tid (maj, min) tid')))) ->
              t2 = (Tid (maj, min') tid', [joinAct], s2', ret N2) ->
              step h T (tCouple t1 t2) (OK h T (tSingleton (tid, nil, s2, ret(pair_ N1 N2))))
|SpecRB : forall t E' h h' tid tid' maj min  min'' T T' E M' s2 s1' a s2' t1 t2 TRB, 
            decompose t = (specReturnCtxt E' (threadId(Tid(maj,min'') tid')), raise E) ->
            t1 = (tid, nil, s2, fill E'(specReturn (raise E) (threadId (Tid (maj, min'') tid')))) ->
            t2 = (Tid (maj, min) tid', s1' ++ [a], s2', M') -> 
            ~ (exists p, thread_lookup TRB tid p) -> thread_lookup TRB (Tid (maj, min) tid') t2 -> 
            ~ (exists p', thread_lookup T' (Tid (maj, min) tid') p') ->
            rollback (Tid (maj, min) tid') [a] h (tAdd TRB t2) h' T' ->
            step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, nil, s2, fill E'(raise E))))
|SpecRaise : forall E' N h tid tid' maj min' min'' s2 s2' T E t1 t2 t,
               decompose t = (specReturnCtxt E' (threadId(Tid(maj,min'') tid')), ret N) ->
               t1 = (tid, nil, s2, t) -> 
               t2 = (Tid (maj, min') tid', [joinAct], s2', raise E) ->
               step h T (tCouple t1 t2) (OK h T (tSingleton (tid, nil, s2, fill E' (raise E))))
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
                decompose t = (c, get (fvar i)) -> 
                s1 = s1' ++ [rAct i (Tid (maj, min') tid) t] ->
                unspecThread (Tid (maj, min) tid, s1, s2, M) 
                             (Some(Tid (maj, min') tid, nil, s2, fill c(get (fvar i))))
|unspecWrite : forall tid s1 s1' s2 M M' i maj min min' c t,
                 decompose t = (c, put (fvar i) M') ->
                 s1 = s1' ++ [wAct i (Tid (maj, min') tid) t] ->
                 unspecThread (Tid (maj, min) tid, s1, s2, M) 
                              (Some(Tid (maj, min') tid, nil, s2, (fill c(put (fvar i) M'))))
|unspecCreate : forall tid s1 s1' s2 M i maj min min' c t,
                  decompose t = (c, new) -> 
                  s1 = s1' ++ [cAct i (Tid (maj, min') tid) t] ->
                  unspecThread (Tid (maj, min) tid, s1, s2, M) (Some(Tid (maj, min') tid, nil, s2, (fill c new)))
|unspecSpec : forall tid s1 s1' s2 M maj min min' M',
                s1 = s1' ++ [sAct (Tid (maj, min') tid) M'] ->
                unspecThread (Tid (maj, min) tid, s1, s2, M) 
                             (Some(Tid (maj, min') tid, [sAct (Tid (maj, min') tid) M'], s2, M'))
|unSpecFork : forall c tid s1 s1' s2 M tid' M' maj min min' t,
                  decompose t = (c, fork M') -> 
                  s1 = s1' ++ [fAct tid' (Tid (maj, min') tid) t] ->
                  unspecThread (Tid (maj, min) tid, s1, s2, M) 
                               (Some(Tid (maj, min') tid, nil, s2, fill c(fork M')))
|unspecCreatedSpec : forall s1 s1' s2 M tid,
                       s1 = s1' ++ [specAct] -> unspecThread (tid, s1, s2, M) None
|unspecJoin : forall s1 s1' s2 M tid,
                s1 = s1' ++ [joinAct] -> unspecThread (tid, s1, s2, M) (Some(tid, s1, s2, M))
.

Hint Constructors unspecThread. 

Inductive unspecPoolAux (T:pool) : pool :=
|unspecAux : forall t t' s1 s2 M, thread_lookup T t (t, s1, s2, M) ->
                                  unspecThread (t, s1, s2, M) (Some t') -> tIn (unspecPoolAux T) t'.

Inductive unspecPool : pool -> pool -> Prop :=
|unspecP : forall T, unspecPool T (unspecPoolAux T).

Hint Constructors unspecPool. 

Inductive wellFormed : sHeap -> pool -> Prop :=
|wf : forall H H' T T', unspecPool T T' -> unspecHeap H H' -> multistep H' tEmptySet T' (OK H tEmptySet T) ->
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

Theorem lastElemNeq : forall (T:Type) s1 s2 (e1 e2:T), s1 ++ [e1] = s2 ++ [e2] -> e1 <> e2 -> False. 
Proof.
  intros. 
  generalize dependent s2. induction s1. 
  {intros. destruct s2. inversion H. contradiction. inversion H. destruct s2; inversion H3. }
  {intros. destruct s2. inversion H. destruct s1; inversion H3. inversion H. apply IHs1 in H3. 
   assumption. }
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
  {eapply IHrollback. eapply unspecDependentReader2 in H5. eassumption. eassumption. }
  {eapply IHrollback. eapply unspecSpecfull in H5; eauto. }
  {eapply IHrollback. eapply unspecSpecEmpty in H5; eauto. }
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

Theorem decomposeDecomposed : forall E e, decompose e = (holeCtxt, e) ->
                                          decompose (fill E e) = (E, e). 
Proof.
  intros. induction E; try solve[
   simpl; destruct (decompose (fill E e)); inversion IHE; subst; reflexivity]. 
  {simpl. assumption. }Qed. 

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