Require Import AST.         
Require Import Heap.     
Require Import NonSpec.  
Require Import sets.  
Require Import SpecLib. 
Require Import Coq.Sets.Ensembles. 
Require Import Coq.Logic.Classical_Prop. 
Require Import Coq.Program.Equality. 
Require Import Coq.Sets.Powerset_facts. 

(*Representation for specualtive heaps (see Heap.v for details)*)
Definition sHeap := heap (ivar_state).

Ltac cleanup :=
  match goal with
    |H:?x=?y |- _ => inversion H; subst; clear H
  end. 

Theorem decomposeEq : forall M E e, decompose M E e -> M = fill E e.
Proof.
  induction M; intros; try solve[inversion H; subst; auto];
  try solve[inversion H; subst; auto; simpl; apply IHM1 in H5; subst; auto].
  {inversion H; subst. apply IHM1 in H5. subst. auto. apply IHM2 in H6; subst; auto. }
  {inversion H; subst; auto. apply IHM1 in H5. subst. auto. apply IHM2 in H6; subst; auto. }
  {inversion H; subst; auto. apply IHM2 in H6; subst; auto. }
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
  {inversion H; inversion H0; subst; auto; try contradiction. eapply IHt1 in H6; eauto. 
   inversion H6; subst; auto. eapply IHt2 in H7; eauto. inversion H7; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction. eapply IHt1 in H6; eauto. 
   inversion H6; subst; auto. eapply IHt2 in H7; eauto. inversion H7; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction. eapply IHt2 in H7; eauto. 
   inversion H7; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction. 
   eapply IHt in H3; eauto. 
   inversion H3; subst; auto. }
  {inversion H; inversion H0; subst; auto; try contradiction.
   eapply IHt in H3; eauto. 
   inversion H3; subst; auto. }
Qed. 

Open Scope type_scope. 

Definition thread := tid * actionStack * actionStack * trm. 
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
RBDone : forall T h M tid s1 s2 t1,
           tIn T t1 -> t1 = (tid, s1, s2, M) ->
           rollback (tid) s1 h T h T
|RBRead : forall s1 s1' s2 x TID TID' M M' N h h' h'' T T' sc t A S ds t1 SRoll E d, 
            s1 = rAct x M' E d::s1' -> In tid ds TID' ->
            heap_lookup x h = Some (sfull sc ds (S::A) t N) ->
            h' = replace x (sfull sc (Subtract tid ds TID') (S::A) t N) h -> 
            ~(tIn T t1) -> t1 = (TID', s1, s2, M) ->
            rollback TID SRoll h' (tAdd T (TID', s1', s2, M')) h'' T' ->
            rollback TID SRoll h (tAdd T t1) h'' T'
|RBFork : forall s1 s1' s2 s2' TID TID' M M' N T T' h h' t1 t2 SRoll E N' d,
            s1 = fAct M' E N' d::s1' ->  ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (TID', s1, s2, M) -> t2 = (1::TID', [specAct], s2', N) ->
            rollback TID SRoll h (tAdd T (TID', s1', s2, M')) h' T' ->
            rollback TID SRoll h (tUnion T (tCouple t1 t2)) h' T'
|RBWrite : forall s1 s1' s2 TID TID' M M' N S A sc T T' h h' h'' x t1 SRoll E N' d,
             s1 = wAct x M' E N' d::s1' ->
             heap_lookup x h = Some(sfull sc (Empty_set tid) (S::A) TID' N) ->
             h' = replace x (sempty sc) h -> ~(tIn T t1) ->
             t1 = (TID', s1, s2, M) -> rollback TID SRoll h' (tAdd T (TID', s1', s2, M')) h'' T' ->
             rollback TID SRoll h (tAdd T t1) h'' T'
|RBNew : forall s1 s1' s2 TID TID' M M' S A T T' h h' h'' x t1 SRoll E d,
           s1 = nAct M' E d x ::s1' -> decompose M' E new -> 
           heap_lookup x h = Some (sempty (S::A)) ->
           h' = remove h x -> ~(tIn T t1) -> t1 = (TID', s1, s2, M) ->
           rollback TID SRoll h' (tAdd T (TID', s1', s2, M')) h'' T' ->
           rollback TID SRoll h (tAdd T t1) h'' T'
|RBSpec : forall s1 s1' s2 s2' TID TID' M M' M'' N'' N E T T' h h' t1 t2 SRoll d,
            s1 = srAct M' E M'' N'' d::s1' ->
            ~(tIn T t1) -> ~(tIn T t2) ->
            t1 = (TID', s1, s2, M) -> t2 = (2::TID', [specAct; specAct], s2', N) ->
            rollback TID SRoll h (tAdd T (TID', s1', s2, M')) h' T' ->
            rollback TID SRoll h (tAdd (tAdd T t1) t2) h' T'
.

Hint Constructors rollback. 

(*Lookup a thread ID in a pool, yields a thread if a particular thread in the pool
**matches the specified thread ID up to the minor number*)
Inductive thread_lookup : pool -> tid -> thread -> Prop :=
|hit : forall T t tid s1 s2 M,
         tIn T t -> t = (tid, s1, s2, M) -> thread_lookup T tid t.

Hint Constructors thread_lookup. 

Inductive config : Type :=
|OK : sHeap -> pool -> pool -> config
|Error : config. 

Hint Constructors val. 

Theorem wrapDecompose : forall t E e M, decompose t E e ->
                                        decompose (specJoin (ret M) t) (specJoinCtxt E (ret M)) e. 
Proof.
  intros. induction H; try solve[constructor; auto;[introsInv| constructor; auto]].
  constructor; auto. introsInv. contradiction. constructor; auto. constructor; auto. 
  introsInv. contradiction. constructor; auto. 
Qed. 

Fixpoint wrapActs (acts:actionStack) (N:trm) := 
  match acts with
      |rAct x M E d::acts'=> rAct x (specJoin (ret N) M) (specJoinCtxt E (ret N)) 
                                  (wrapDecompose M E (get (fvar x)) N d)::wrapActs acts' N
      |wAct x M E M' d::acts' =>
       wAct x (specJoin(ret N) M) (specJoinCtxt E (ret N)) M' 
            (wrapDecompose M E (put (fvar x) M') N d)::wrapActs acts' N
      |nAct M E d x::acts' => nAct (specJoin (ret N) M) (specJoinCtxt E (ret N))
                            (wrapDecompose M E new N d) x :: wrapActs acts' N
      |fAct M E M' d::acts'=> 
       fAct (specJoin(ret N) M) (specJoinCtxt E (ret N)) M'
            (wrapDecompose M E (fork M') N d)::wrapActs acts' N
      |srAct M E M' N' d::acts' =>
       srAct (specJoin (ret N) M) (specJoinCtxt E (ret N)) M' N'
             (wrapDecompose M E (spec M' N') N d)::wrapActs acts' N
      |specAct::acts' => specAct :: wrapActs acts' N
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
|Fork : forall tid h T M s1 s2 E t (d:decompose t E (fork M)), 
          step h T (tSingleton (tid, s1, s2,t)) 
        (OK h T(tCouple (tid, fAct t E M d ::s1, s2, fill E(ret unit)) 
                        (1::tid, [specAct], nil, M)))
|Get : forall TID h h' T N s1 s2 E x s ds writer t (d:decompose t E (get (fvar x))),
         heap_lookup x h = Some(sfull nil ds s writer N) -> 
         h' = replace x (sfull nil (Add tid ds TID) s writer N) h ->
         step h T (tSingleton (TID, s1, s2, t))
              (OK h' T (tSingleton (TID, rAct x t E d::s1, s2, fill E(ret N))))
|Put : forall E x N h h' s1 s2 TID T t (d:decompose t E (put (fvar x) N)), 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty nil) ->
         h' = replace x (sfull nil (Empty_set tid) (wAct x t E N d::s1) TID N) h -> 
         step h T (tSingleton (TID, s1, s2, t)) (OK h' T
              (tSingleton (TID, wAct x t E N d::s1, s2, fill E(ret unit))))
|Overwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds TID TID' (d:decompose t E (put (fvar x) N)), 
               heap_lookup x h = Some (sfull nil ds (S'::A) TID' N') ->
               rollback TID' A h TR h' TR' -> heap_lookup x h' = Some(sempty nil) ->
               h'' = replace x (sfull nil (Empty_set tid) [wAct x t E N d] TID N) h' -> 
               step h T (tAdd TR (TID, nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (TID, [wAct x t E N d], s2, fill E (ret unit))))
|ErrorWrite : forall h T t E x N N' tid tid' ds s2,  
                decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sfull nil ds nil tid' N') ->
                step h T (tSingleton (tid, nil, s2, t)) Error
|New : forall E h h' x tid t s1 s2 T (d:decompose t E new),
         (x, h') = extend (sempty (nAct t E d x::s1)) h -> 
         step h T (tSingleton (tid, s1, s2, fill E new)) 
              (OK h' T (tSingleton (tid, nAct t E d x::s1, s2, fill E(ret(fvar x)))))
|Spec : forall E M t N tid s1 s2 T h (d:decompose t E (spec M N)), 
          step h T (tSingleton (tid, s1, s2, t)) (OK h T
               (tCouple (tid, srAct t E M N d::s1, s2,fill E (specRun M N)) 
                        (tid, [specAct], nil, N))) 
|SpecJoin : forall t E M N0 N1 tid T h t1 t2 s1 s1' s2 s2',
              decompose t E (specRun (ret N1) N0) -> s1 = s1' ++ [specAct] ->
              t1 = (tid,nil,s2, t) -> t2 = (2::tid,s1,s2',M) ->
              step h T (tCouple t1 t2) 
                   (OK h T (tSingleton(tid,wrapActs s1' N1, s2, fill E (specJoin (ret N1) M)))) 
|SpecRB : forall t E' h h' tid T T' E M' N0 s2 s1' s2' t1 t2 TRB, 
            decompose t E' (specRun (raise E) N0)->
            t1 = (tid,nil,s2,t) -> t2 = (2::tid,s1'++[specAct],s2',M') -> 
            ~ (exists p, thread_lookup TRB (tid) p) -> 
            thread_lookup TRB (2::tid) t2 -> 
            ~ (exists p', thread_lookup T' (2::tid) p') ->
            rollback (2::tid) [specAct] h TRB h' T' ->
            step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, nil, s2, fill E'(raise E))))
|SpecRaise : forall E' N h tid s2 T E t1 t,
               decompose t E' (specJoin(ret N)(raise E)) ->
               t1 = (tid, nil, s2, t) -> 
               step h T (tSingleton t1) 
                    (OK h T (tSingleton (tid, nil, s2, fill E' (raise E))))
|PopRead : forall TID t s1 s1' s2 M M' N T h x ds E d h', 
             s1 = s1' ++ [rAct x M' E d] -> In tid ds TID ->
             heap_lookup x h = Some (sfull nil ds nil t N) ->
             h' = replace x (sfull nil (Subtract tid ds TID) nil t N) h ->
             step h T (tSingleton (TID, s1, s2, M)) (OK h' T (tSingleton (TID, s1', (rAct x M' E d)::s2, M)))
|PopWrite : forall tid t s1 s1' s2 M M' M'' N T h h' x ds a b E d,
              s1 = s1' ++ [wAct x M' E M'' d] -> heap_lookup x h = Some(sfull nil ds (a::b) t N) ->
              h' = replace x (sfull nil ds nil t N) -> 
              step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', (wAct x M' E M'' d)::s2, M)))
|PopNewFull : forall h h' s1 s1' s2 i tid M' ds s s' t M N T E d, 
                s1 = s1' ++ [nAct M' E d i] -> heap_lookup i h = Some(sfull s ds s t N) ->
                h' = replace i (sfull nil ds s' t N) h -> 
                step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', nAct M' E d i::s2, M)))
|PopNewEmpty : forall h h' s1 s1' s2 i tid M' s M T E d, 
                 s1 = s1' ++ [nAct M' E d i] -> heap_lookup i h = Some(sempty s) ->
                  h' = replace i (sempty nil) h -> 
                 step h T (tSingleton (tid, s1, s2, M)) (OK h T (tSingleton (tid, s1', nAct M' E d i::s2, M)))
|PopFork : forall h s1 s1' s1'' s1''' s2 s2' tid M' M N T M'' E d, 
             s1 = s1' ++ [fAct M' E M'' d] -> s1'' = s1''' ++ [specAct] ->
             step h T (tCouple (tid, s1, s2, M) (1::tid, s1'', s2', N)) (OK h T 
                  (tCouple (tid, s1', fAct M' E M'' d::s2, M)
                           (1::tid, s1''', specAct::s2', N)))
|PopSpec : forall h s1 s1' s2 t tid M' M N T E d, 
             s1 = s1' ++ [srAct t E M N d] -> 
             step h T (tSingleton(tid, s1, s2, M')) (OK h T (tSingleton(tid, s1', srAct t E M N d::s2, M')))
.

Hint Constructors step. 
 
Inductive multistep : sHeap -> pool -> pool -> config -> Prop :=
|multi_refl : forall h p1 p2, multistep h p1 p2 (OK h p1 p2)
|multi_step : forall c T1 T2 P1 P2 P2' h h',
                T2 = tUnion P1 P2 ->
                step h (tUnion P1 T1) P2 (OK h' (tUnion P1 T1) P2') ->
                multistep h' T1 (tUnion P1 P2') c ->
                multistep h T1 T2 c
|multi_error1 : forall T1 T2 P1 P2 h, 
                  T2 = tUnion P1 P2 ->
                  step h (tUnion P1 P2) P2 Error ->
                  multistep h T1 T2 Error
. 
 
Hint Constructors multistep. 

Inductive specActionsAux (T:pool) : Ensemble (tid*actionStack) :=
|saAux : forall t s1, (exists s2 M, thread_lookup T t (t, s1, s2, M)) ->
                      In (tid*actionStack) (specActionsAux T) (t, s1)
.

Inductive specActions : pool -> Ensemble (tid * actionStack) -> Prop :=
|sa : forall T, specActions T (specActionsAux T). 

Hint Constructors specActions specActionsAux. 

Inductive commitActionsAux (T:pool) : Ensemble (tid*actionStack) :=
|caAux : forall t s2, (exists s1 M, thread_lookup T t (t, s1, s2, M)) -> 
                      In (tid*actionStack) (commitActionsAux T) (t, s2).

Inductive commitActions : pool -> Ensemble (tid*actionStack) -> Prop :=
|ca : forall T, commitActions T (commitActionsAux T). 

Hint Constructors commitActions commitActionsAux. 
 



(*------------------------------------Theorems------------------------------------*)

Theorem IncludedSingleton : forall T S s, Included T (Singleton T s) S -> In T S s. 
Proof.
  intros. unfold Included in H. assert(In T (Singleton T s) s). constructor. apply H in H0. 
  assumption. Qed. 

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
   {subst. unfold tUnion in H0. rewrite Union_commutative in H0. apply stepUnusedPool in H0. 
    econstructor. reflexivity. unfold tUnion. rewrite Union_commutative. apply stepUnusedPool. 
    eauto. eauto. }
   {inversion Heqc. }
  }
  {intros. remember (OK h' t2 p1'). induction H; eauto. 
   {inversion Heqc; subst. constructor. }
   {eapply multi_step. eassumption.  unfold tUnion. rewrite Union_commutative. 
    rewrite Union_associative. rewrite stepUnusedPool. rewrite Union_commutative. eassumption. 
    apply IHmultistep. assumption. }
   {inversion Heqc. }
  }
Qed. 

Axiom MultistepUntouchedUnused : forall h h' T1 T2 T2' T3,
                                   multistep h T3 (tUnion T1 T2) (OK h' T3 (tUnion T1 T2')) <->
                                   multistep h (tUnion T1 T3) T2 (OK h' (tUnion T1 T3) T2'). 
 
Inductive ctxtWF (e:trm) : ctxt -> Prop :=
|bindWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (bindCtxt E N)
|specWF : forall N E, ctxtWF e E -> ~val (fill E e) ->
                      ctxtWF e (specRunCtxt E N)
|specJoinWF : forall N E,ctxtWF e E -> val N -> ~val (fill E e) -> 
                         ctxtWF e (specJoinCtxt E N)
|handleWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (handleCtxt E N)
|appWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (appCtxt E N)
|appValWF : forall M E, ctxtWF e E -> val M -> ~val (fill E e) -> ctxtWF e (appValCtxt E M)
|pairWF : forall N E, ctxtWF e E -> ~val (fill E e) -> ctxtWF e (pairCtxt E N)
|pairValWF : forall M E, ctxtWF e E -> val M -> ~val (fill E e) -> 
                         ctxtWF e (pairValCtxt E M)
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
  {inversion H; subst. constructor. eauto. apply decomposeEq in H5; subst; auto. 
   constructor; auto. apply decomposeEq in H6; subst; auto. }
  {inversion H; subst. constructor; auto. apply decomposeEq in H5; subst; auto. 
   constructor; auto. apply decomposeEq in H6; subst; auto. constructor. }
  {inversion H; subst; auto. econstructor. apply IHt2; auto. apply decomposeEq in H6.
   subst. assumption. apply decomposeEq in H6; subst; auto. }
  {inversion H; subst; auto. constructor. apply IHt. auto. 
   apply decomposeEq in H2; subst; auto. }
  {inversion H; subst; auto. constructor. apply IHt. auto. 
   apply decomposeEq in H2; subst; auto. }
Qed. 

