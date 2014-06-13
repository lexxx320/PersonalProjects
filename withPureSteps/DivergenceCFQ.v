Require Import AST.  
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 
Require Import erasure. 
Require Import nonspeculativeImpliesSpeculative. 

CoInductive ParDiverge : pHeap -> pPool -> Prop :=
|divergeStep : forall T1 T2 T2' H H',
                 Disjoint ptrm T1 T2 -> pstep H T1 T2 (pOK H' T1 T2') -> 
                 ParDiverge H' (Union ptrm T1 T2') -> ParDiverge H (Union ptrm T1 T2)
.

Inductive commit_step : sHeap -> pool -> pool -> config -> Prop :=
|CBetaRed : forall E e N tid s2 h T t, 
             decompose t (appValCtxt E (lambda e)) N -> val N = true ->                  
             commit_step h T (tSingleton(tid,nil,s2,t)) (OK h T (tSingleton(tid,nil,s2,fill E (open 0 N e)))) 
|CProjL : forall tid s2 E V1 V2 h T t, 
           decompose t (fstCtxt E) (pair_ V1 V2) -> val V1 = true -> val V2 = true ->
           commit_step h T (tSingleton(tid,nil,s2,t)) (OK h T (tSingleton(tid,nil,s2,fill E V1)))
|CProjR : forall tid s2 E V1 V2 h T t, 
           decompose t (sndCtxt E) (pair_ V1 V2) -> val V1 = true -> val V2 = true ->
           commit_step h T (tSingleton(tid,nil,s2,t)) (OK h T (tSingleton(tid,nil,s2,fill E V2)))
|CBind : forall tid h E T N M s2 t, decompose t (bindCtxt E N) (ret M) ->
  commit_step h T (tSingleton (tid, nil, s2, t)) (OK h T (tSingleton (tid,nil,s2,fill E(AST.app N M))))
|CBindRaise : forall tid h E T N M s2 t, decompose t (bindCtxt E N) (raise M) ->
  commit_step h T (tSingleton (tid,nil,s2,t)) (OK h T (tSingleton (tid,nil,s2,fill E (raise M))))
|CHandle : forall tid h E T N M s2 t, decompose t (handleCtxt E N) (raise M) ->
  commit_step h T (tSingleton (tid,nil,s2,t)) (OK h T (tSingleton (tid,nil,s2,fill E (AST.app  N M))))
|CHandleRet : forall tid h E T N M s2 t, decompose t (handleCtxt E N) (ret M) ->
  commit_step h T (tSingleton (tid,nil,s2,t)) (OK h T (tSingleton (tid,nil,s2,fill E (ret M))))
|CTerminate : forall tid h T M s2, 
               commit_step h T (tSingleton (tid, nil, s2, ret M)) (OK h T tEmptySet)
|CFork : forall tid tid' h T M s2 E t i j, 
          decompose t E (fork M) -> tid' = Tid(1, 1) ((i, j)::tid) -> 
          commit_step h T (tSingleton (Tid(i, j) tid, nil, s2,t)) (OK h T
               (tCouple (Tid(i, S j)tid, [fAct tid' j (fill E(fork M))], s2, fill E(ret unit)) 
               (tid', [specAct], nil, M)))
|CGet : forall tid h h' T N s2 E x s ds writer sc t i j l,
         decompose t E (get (fvar x)) -> heap_lookup x h = Some(sfull sc ds s writer N) -> 
         tid = Tid(i, j) l -> h' = replace x (sfull sc (tid::ds) s writer N) h ->
         commit_step h T (tSingleton (tid, nil, s2, fill E(get (fvar x)))) (OK h' T 
              (tSingleton (bump tid, [rAct x j (fill E(get (fvar x)))], s2, fill E(ret N))) )
|CPut : forall E x N h sc h' s2 tid T t i j l, 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil nil tid N) h -> tid = Tid(i, j) l ->
         commit_step h T (tSingleton (tid, nil, s2, fill E(put (fvar x) N))) (OK h' T
              (tSingleton (bump tid, [wAct x j (fill E(put (fvar x) N))], s2, fill E(ret unit))))
|COverwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds tid tid' S i j l, 
               decompose t E (put (fvar x) N) -> heap_lookup x h = Some (sfull S ds (S'::A) tid' N') ->
               rollback tid' (S'::A) h TR h' TR' -> heap_lookup x h' = Some (sempty S) ->
               h'' = replace x (sfull S nil nil tid N) h' -> tid = Tid(i, j) l ->
               commit_step h T (tAdd TR (tid, nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (tid, nil, wAct x j (fill E(put (fvar x) N))::s2, fill E (ret unit))))
|CNew : forall E h h' x tid t s2 T i j l,
         decompose t E new -> (x, h') = extend (sempty nil) h -> tid = Tid(i, j) l -> 
         commit_step h T (tSingleton (tid, nil, s2, fill E new)) (OK h' T
              (tSingleton (bump tid, [cAct x j (fill E new)], s2, fill E(ret(fvar x)))))
|CSpec : forall E M t N tid' tid s2 T h s1' i j l, 
          decompose t E (spec M N) -> tid' = extendTid tid -> tid = Tid(i, j) l ->
          s1' = [sAct tid' N; specAct] ->
          commit_step h T (tSingleton (tid, nil, s2, fill E (spec M N))) (OK h T
               (tCouple (bump tid, [specRetAct tid' j (fill E (spec M N))], s2,fill E(specReturn M (threadId tid')))
                        (tid', s1', nil, N)))
|CSpecJoin : forall E h s2 s2' tid tid' N1 N2 maj min min' T t1 t2 t,
              decompose t (specReturnCtxt E (threadId(Tid(maj,min) tid'))) (ret N1) ->
              t1 = (tid, nil, s2, fill E(specReturn (ret N1) (threadId (Tid (maj, min) tid')))) ->
              t2 = (Tid (maj, min') tid', nil, s2', ret N2) ->
              commit_step h T (tCouple t1 t2) (OK h T (tSingleton (tid, nil, s2, ret(pair_ N1 N2))))
|CSpecRB : forall t E' h h' tid tid' maj min  min'' T T' E M' s2 s1' a s2' t1 t2 TRB, 
            decompose t (specReturnCtxt E' (threadId(Tid(maj,min'') tid'))) (raise E) ->
            t1 = (tid, nil, s2, fill E'(specReturn (raise E) (threadId (Tid (maj, min'') tid')))) ->
            t2 = (Tid (maj, min) tid', s1' ++ [a], s2', M') -> 
            ~ (exists p, thread_lookup TRB tid p) -> thread_lookup TRB (Tid (maj, min) tid') t2 -> 
            ~ (exists p', thread_lookup T' (Tid (maj, min) tid') p') ->
            rollback (Tid (maj, min) tid') [a] h (tAdd TRB t2) h' T' ->
            commit_step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, nil, s2, fill E'(raise E))))
|CSpecRaise : forall E' N h tid tid' maj min' min'' s2 s2' T E t1 t2 t,
               decompose t (specReturnCtxt E' (threadId(Tid(maj,min'') tid'))) (ret N) ->
               t1 = (tid, nil, s2, t) -> 
               t2 = (Tid (maj, min') tid', nil, s2', raise E) ->
               commit_step h T (tCouple t1 t2) (OK h T (tSingleton (tid, nil, s2, fill E' (raise E))))
.

CoInductive SpecDiverge : sHeap -> pool-> Prop :=
|specDiverge : forall T1 T2 T2' H H' T,
                 multistep H tEmptySet T (OK H' tEmptySet (tUnion T1 T2)) -> Disjoint thread T1 T2 ->
                 commit_step H T1 T2 (OK H' T1 T2') -> SpecDiverge H' (tUnion T1 T2') ->
                 SpecDiverge H T.


Inductive uneraseTerm : ptrm -> trm -> Prop :=
|uneraseFVar : forall i, uneraseTerm (pfvar i) (fvar i)
|uneraseBVar : forall i, uneraseTerm (pbvar i) (bvar i)
|uneraseUnit : uneraseTerm punit unit
|unerasePair : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                     uneraseTerm (ppair e1' e2') (pair_ e1 e2)
|uneraseLambda : forall e e', uneraseTerm e' e -> uneraseTerm (plambda e') (lambda e)
|uneraseApp : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                    uneraseTerm (papp e1' e2') (AST.app e1 e2)
|uneraseRet : forall e e', uneraseTerm e' e -> uneraseTerm (pret e') (ret e)
|uneraseBind : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                     uneraseTerm (pbind e1' e2') (bind e1 e2)
|uneraseFork : forall e e', uneraseTerm e' e -> uneraseTerm (pfork e') (fork e)
|uneraseNew : uneraseTerm pnew new
|unerasePut : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                    uneraseTerm (pput e1' e2') (put e1 e2)
|uneraseGet : forall e e', uneraseTerm e' e -> uneraseTerm (pget e') (get e)
|uneraseRaise : forall e e', uneraseTerm e' e -> uneraseTerm (praise e') (raise e)
|uneraseHandle : forall e1 e1' e2 e2', uneraseTerm e1' e1 -> uneraseTerm e2' e2 ->
                                       uneraseTerm (phandle e1' e2') (handle e1 e2)
|uneraseDone : forall e e', uneraseTerm e' e -> uneraseTerm (pdone e') (done e)
|uneraseFst : forall e e', uneraseTerm e' e -> uneraseTerm (pfst e') (fst e)
|uneraseSnd : forall e e', uneraseTerm e' e -> uneraseTerm (psnd e') (snd e)
.

Inductive uneraseCtxt : pctxt -> ctxt -> Prop :=
|uneraseBindCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                     uneraseCtxt (pbindCtxt E' N') (bindCtxt E N)
|uneraseHandleCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (phandleCtxt E' N') (handleCtxt E N)
|uneraseAppCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (pappCtxt E' N') (appCtxt E N)
|uneraseAppValCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (pappValCtxt E' N') (appValCtxt E N)
|unerasePairCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (ppairCtxt E' N') (pairCtxt E N)
|unerasePairValCtxt : forall E E' N N', uneraseTerm N' N -> uneraseCtxt E' E -> 
                                       uneraseCtxt (ppairValCtxt E' N') (pairValCtxt E N)
|uneraseFstCtxt : forall E E', uneraseCtxt E' E -> uneraseCtxt (pfstCtxt E') (fstCtxt E)
|uneraseSndCtxt : forall E E', uneraseCtxt E' E -> uneraseCtxt (psndCtxt E') (sndCtxt E)
|uneraseHoleCtxt : uneraseCtxt pholeCtxt holeCtxt
.

Inductive uneraseThread : ptrm -> thread -> Prop :=
|unerase_thread : forall M M' L1 L2, uneraseTerm M' M -> 
                                 (forall t s2, ~Ensembles.In tid L1 t ->
                                               ~Ensembles.In specStack L2 s2 ->
                                               uneraseThread M' (t,nil,s2,M))
. 
 
Inductive unerasePool (T:pPool) : pool :=
|unerase_pool : forall M' t, Ensembles.In ptrm T M' -> uneraseThread M' t ->
                               Ensembles.In thread (unerasePool T) t. 

Theorem uneraseTermDeterminism : forall M t1 t2, uneraseTerm M t1 -> uneraseTerm M t2 -> t1 = t2. 
Proof.
  intros. generalize dependent t2. induction H; intros; try solve[ 
  inversion H0; subst; auto]; try solve[ 
  inversion H1; subst; apply IHuneraseTerm1 in H4; apply IHuneraseTerm2 in H6; subst; auto];
  try solve[inversion H0; subst; apply IHuneraseTerm in H2; subst; auto]. 
Qed. 

Theorem uneraseSingleton : forall t M tid s2, uneraseTerm t M -> 
                                              unerasePool(pSingleton t) = tSingleton(tid,nil,s2,M).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H2; subst. inversion H1; subst. 
   apply uneraseTermDeterminism with(t1:=M)in H3. subst. admit. auto. }
  {inversion H0; subst. econstructor. econstructor. uneraseTac. }
Qed. 

Inductive uneraseHeap : pHeap -> sHeap -> Prop :=
|uneraseConsFull : forall M M' i H H', 
                  uneraseTerm M' M -> uneraseHeap H' H ->
                  uneraseHeap((i, pfull M')::H') ((i, sfull nil nil nil (Tid(0,0)nil) M)::H)
|uneraseConsEmpty : forall i H H', uneraseHeap H' H -> uneraseHeap ((i,pempty)::H') ((i,sempty nil)::H)
|uneraseNil : uneraseHeap nil nil
.

Hint Constructors uneraseTerm uneraseCtxt uneraseHeap. 

Theorem eUneraseTerm : forall e', exists e, uneraseTerm e' e.
Proof.
  induction e'; try solve[repeat econstructor]; try solve[invertExists; econstructor; eauto].  
Qed. 

Theorem eUneraseCtxt : forall E', exists E, uneraseCtxt E' E. 
Proof.
  induction E'; try solve[assert(exists p', uneraseTerm p p') by apply eUneraseTerm; invertExists; 
  econstructor; eauto]; try solve[invertExists; econstructor; eauto]. 
  econstructor. eauto. Qed. 

Theorem eHeap' : forall H, exists H', uneraseHeap H H'. 
Proof.
  induction H; intros. 
  {exists nil. constructor. }
  {inversion IHlist. destruct a. destruct p. 
   {exists ((i, sempty nil)::x). constructor. assumption. }
   {assert(exists M, uneraseTerm p M). apply eUneraseTerm. invertExists. 
    exists((i, sfull nil nil nil (Tid(0,0)nil) x0)::x). constructor. assumption. assumption. }
  }
Qed. 

Ltac unerase e := try(assert(exists e', uneraseCtxt e e') by apply eUneraseCtxt);
                 try(assert(exists e', uneraseTerm e e') by apply eUneraseTerm); 
                 try(assert(exists e', uneraseHeap e e') by apply eHeap');invertHyp. 

Theorem unerasePoolUnion : forall T1 T2 T1' T2', 
                             unerasePool T1 = T1' -> unerasePool T2 = T2' ->
                             unerasePool (Union ptrm T1 T2) = Union thread T1' T2'. 
Proof.                             
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H1; subst. inversion H2; subst. 
   {inversion H3; subst. apply Union_introl. econstructor. eassumption. assumption. }
   {inversion H3; subst. apply Union_intror. econstructor. eassumption. assumption. }
  }
  {inversion H1; subst. 
   {inversion H2. econstructor. eapply Union_introl. eassumption. eassumption. }
   {inversion H2. econstructor. eapply Union_intror. eassumption. assumption. }
  }
Qed. 

Ltac uneraseTac :=
  match goal with
      | |- uneraseThread ?x ?t => apply unerase_thread with (L1 := Empty_set tid)(L2:=Empty_set specStack);
                                 try auto; try(intros c; inversion c)
  end. 

Theorem eUneraseThreadWithTrm : forall t M, uneraseTerm t M -> 
                                            exists tid s2, uneraseThread t (tid,nil,s2,M). 
Proof.
  induction t; intros; try solve[exists (Tid(0,0)nil); exists nil; uneraseTac]. 
Qed. 

Theorem uneraseTermDet : forall M1 M2 x, uneraseTerm M1 x -> uneraseTerm M2 x -> M1 = M2. 
Proof.
  induction M1; intros; try solve[inversion H; subst; inversion H0; subst; auto]; try solve[ 
  inversion H; subst; inversion H0; subst; apply IHM1_1 in H6; auto; apply IHM1_2 in H7; auto; 
  subst; auto]; try solve[ 
  inversion H; subst; inversion H0; subst; apply IHM1 in H4; subst; auto]. 
Qed. 

Theorem uneraseThreadDet : forall M1 M2 x, uneraseThread M1 x -> uneraseThread M2 x -> M1 = M2. 
Proof.
  intros. inversion H; inversion H0; subst. inversion H10; subst. 
  apply uneraseTermDet with(M1:=M2)in H1. subst. reflexivity. assumption. Qed. 

Theorem uneraseDisjoint : forall T1 T2, Disjoint ptrm T1 T2 -> Disjoint thread (unerasePool T1)(unerasePool T2).
Proof.
  intros. inversion H. constructor. intros. intros c. inversion c. subst. 
  inversion H1; subst. inversion H2; subst. unfold not in H0. 
  apply uneraseThreadDet with (M1:=M'0)in H4. subst. assert(Ensembles.In ptrm (Intersection ptrm T1 T2) M'). 
  constructor; auto. apply H0 in H4. assumption. assumption. Qed. 

(*thread ids and action stacks could be different, but that doesn't really matter*)
Axiom uneraseThreadDeterminism : forall M t1 t2, uneraseThread M t1 -> uneraseThread M t2 -> t1 = t2. 


Theorem eUnerasePool : forall t M, 
                       uneraseTerm t M -> exists tid s2, unerasePool(pSingleton t) = 
                                                         tSingleton (tid,nil,s2,M). 
Proof.
  intros. apply eUneraseThreadWithTrm in H. invertExists. exists x. exists x0. 
  apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. apply uneraseThreadDeterminism with(t1:=x1) in H. subst. constructor. 
   inversion H1; subst. assumption. }
  {inversion H0; subst. econstructor. econstructor. assumption. }
Qed. 

Theorem uneraseFill : forall E E' e e', uneraseCtxt E' E -> uneraseTerm e' e -> 
                                        uneraseTerm (pfill E' e') (fill E e).
Proof.
  intros. generalize dependent e. generalize dependent e'. induction H; intros; auto; 
  try solve[simpl; constructor; auto]. Qed. 

Ltac instantiateTrm := 
  match goal with 
      |H:pdecompose ?t (pappValCtxt ?E ?N) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt; 
       assert(NHyp:exists N', uneraseTerm N N') by apply eUneraseTerm; 
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
      |H:pdecompose ?t (pfstCtxt ?E) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt; 
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
      |H:pdecompose ?t (psndCtxt ?E) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt; 
         assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
      |H:pdecompose ?t (pbindCtxt ?E ?N) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt;
       assert(NHyp:exists N', uneraseTerm N N') by apply eUneraseTerm; 
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
    |H:pdecompose ?t (phandleCtxt ?E ?N) ?e |- _ => 
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt;
       assert(NHyp:exists N', uneraseTerm N N') by apply eUneraseTerm; 
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
      |H:pdecompose ?t ?E ?e |- _ =>
       assert(CTXT:exists E', uneraseCtxt E E') by apply eUneraseCtxt;
       assert(eHyp:exists e', uneraseTerm e e') by apply eUneraseTerm; invertExists
  end.

Theorem uneraseValEq : forall M M', uneraseTerm M' M -> val M = pval M'. 
Proof.
  intros. induction H; auto. simpl. rewrite IHuneraseTerm1. rewrite IHuneraseTerm2. auto. Qed. 


Theorem uneraseDecompose : forall E E' e e' t, pdecompose t E' e' -> uneraseCtxt E' E ->
                                               uneraseTerm e' e -> decompose (fill E e) E e.
Proof.
  intros. generalize dependent E. generalize dependent e. induction H; intros; 
  try solve[inversion H0; subst; simpl; constructor; eapply IHpdecompose; auto]. 
  {inversion H2; subst. simpl. constructor. apply pdecomposeEq in H0. subst. 
   rewrite <- H. apply uneraseValEq. apply uneraseFill; auto. apply IHpdecompose; auto. }
  {inversion H2; subst. simpl. constructor. rewrite <- H. apply uneraseValEq. auto. 
   apply IHpdecompose; auto. }
  {inversion H2; subst. simpl. constructor. apply pdecomposeEq in H0. subst. 
   rewrite <- H. apply uneraseValEq. apply uneraseFill; auto. apply IHpdecompose; auto. }
  {inversion H3; subst. simpl. constructor. rewrite <- H. apply uneraseValEq; auto. 
   apply pdecomposeEq in H1. subst. rewrite <- H0. apply uneraseValEq; auto.
   apply uneraseFill; auto. apply IHpdecompose; auto. }
  {inversion H0; subst. simpl. constructor. rewrite <- H. apply uneraseValEq. assumption. }
Qed. 

Theorem uneraseOpen : forall e arg arg' e' n, uneraseTerm arg arg' -> uneraseTerm e e' ->
                                              uneraseTerm (popen n arg e) (open n arg' e'). 
Proof.
  induction e; intros; try solve[inversion H0; subst; auto]; 
  try solve[inversion H0; subst; simpl; auto]. 
  {inversion H0; subst. simpl. destruct (beq_nat n i); auto. }
Qed. 

Theorem parDivergeSpecDiverge : forall H T H' T' , ParDiverge H T -> eraseHeap H' H -> unerasePool T = T' ->
                                                   SpecDiverge H' T'. 
Proof. 
  cofix. intros. inversion H0; subst. inversion H5; subst. 
  {erewrite unerasePoolUnion; eauto. instantiateTrm. inversion H2; subst. 
   assert(uneraseTerm (pfill (pappValCtxt E (plambda e)) arg) (fill (appValCtxt x1 (lambda e0)) x)). 
   apply uneraseFill; auto. apply eUnerasePool in H7. invertHyp. copy H10. apply pdecomposeEq in H10. 
   subst. econstructor. apply multi_refl. apply uneraseDisjoint; auto. rewrite H7. constructor. 
   eapply uneraseDecompose; eauto. rewrite <- H11. apply uneraseValEq. assumption.
   eapply parDivergeSpecDiverge. eapply H6. eassumption. eapply unerasePoolUnion; auto. 
   apply uneraseSingleton. apply uneraseFill; auto. apply uneraseOpen; auto. }
  Admitted. 


Theorem parDivergeSpecDivergeExists : forall H T, 
                                        ParDiverge H T ->
                                        exists H' T', eraseHeap H' H -> erasePool T' T ->
                                                      SpecDiverge H' T'. 
Proof. 
  pcofix. cofix. 


  intros. assert(exists H', uneraseHeap H H'). apply eHeap'. invertHyp. exists x. 
  exists (unerasePool T). intros. eapply parDivergeSpecDiverge. eassumption. 
  assumption. reflexivity. Qed. 


   


