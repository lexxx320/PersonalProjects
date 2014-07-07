Require Import AST.  
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 
Require Import erasure. 

(*progressive progress_step that extends the commit frontier*)
Inductive progress_step : sHeap -> pool -> pool -> config -> Prop :=
|CBetaRed : forall E e N tid s2 h T t, 
             decompose t E (AST.app (lambda e) N) ->            
             progress_step h T (tSingleton(tid,nil,s2,t)) 
                  (OK h T (tSingleton(tid,nil,s2,fill E (open 0 N e))))
|CProjL : forall tid s2 E V1 V2 h T t, 
           decompose t E (fst (pair_ V1 V2)) ->
           progress_step h T (tSingleton(tid,nil,s2,t)) 
                (OK h T (tSingleton(tid,nil,s2,fill E V1)))
|CProjR : forall tid s2 E V1 V2 h T t, 
           decompose t E (snd (pair_ V1 V2)) -> 
           progress_step h T (tSingleton(tid,nil,s2,t)) 
                (OK h T (tSingleton(tid,nil,s2,fill E V2)))
|CBind : forall tid h E T N M s2 t, decompose t E (bind (ret M) N) ->
  progress_step h T (tSingleton (tid, nil, s2, t)) 
       (OK h T (tSingleton (tid,nil,s2,fill E(AST.app N M))))
|CBindRaise : forall tid h E T N M s2 t, decompose t E (bind (raise M) N)->
  progress_step h T (tSingleton (tid,nil,s2,t)) 
       (OK h T (tSingleton (tid,nil,s2,fill E (raise M))))
|CHandle : forall tid h E T N M s2 t, decompose t E (handle (raise M) N) ->
  progress_step h T (tSingleton (tid,nil,s2,t)) 
       (OK h T (tSingleton (tid,nil,s2,fill E (AST.app  N M))))
|CHandleRet : forall tid h E T N M s2 t, decompose t E (handle (ret M) N) ->
  progress_step h T (tSingleton (tid,nil,s2,t)) 
       (OK h T (tSingleton (tid,nil,s2,fill E (ret M))))
|CTerminate : forall tid h T M s2, 
               progress_step h T (tSingleton (tid, nil, s2, ret M)) (OK h T tEmptySet)
|CFork : forall tid tid' h T M s2 E t i j, 
          decompose t E (fork M) -> tid' = Tid(1, 1) ((i, j)::tid) -> 
          progress_step h T (tSingleton (Tid(i, j) tid, nil, s2,t)) 
        (OK h T
            (tCouple (Tid(i, S j)tid, nil, fAct tid' j (fill E(fork M))::s2, fill E(ret unit)) 
                     (tid', nil, [specAct], M)))
|CGet : forall tid h h' T N s2 E x ds writer t i j l,
         decompose t E (get (fvar x)) -> 
         heap_lookup x h = Some(sfull nil ds nil writer N) -> 
         tid = Tid(i, j) l -> h' = replace x (sfull nil (tid::ds) nil writer N) h ->
         progress_step h T (tSingleton (tid, nil, s2, fill E(get (fvar x))))
              (OK h' T (tSingleton (bump tid, nil, rAct x j (fill E(get (fvar x)))::s2, fill E(ret N))))
|CPut : forall E x N h h' s2 tid T t i j l, 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty nil) ->
         h' = replace x (sfull nil nil nil tid N) h -> tid = Tid(i, j) l ->
         progress_step h T (tSingleton (tid, nil, s2, fill E(put (fvar x) N))) 
                       (OK h' T (tSingleton (bump tid, nil, wAct x j (fill E(put (fvar x) N))::s2, fill E(ret unit))))
|COverwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds tid tid' S i j l, 
               decompose t E (put (fvar x) N) -> heap_lookup x h = Some (sfull S ds (S'::A) tid' N') ->
               rollback tid' (S'::A) h TR h' TR' -> heap_lookup x h' = Some (sempty S) ->
               h'' = replace x (sfull S nil nil tid N) h' -> tid = Tid(i, j) l ->
               progress_step h T (tAdd TR (tid, nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (tid, nil, wAct x j (fill E(put (fvar x) N))::s2, fill E (ret unit))))
|CErorrWrite : forall h T t E x N N' tid tid' ds s2,  
                decompose t E (put (fvar x) N) -> 
                heap_lookup x h = Some(sfull nil ds nil tid' N') ->
                progress_step h T (tSingleton (tid, nil, s2, fill E(put (fvar x) N)))
                              Error
|CNew : forall E h h' x tid t s2 T i j l,
         decompose t E new -> (x, h') = extend (sempty nil) h -> tid = Tid(i, j) l -> 
         progress_step h T (tSingleton (tid, nil, s2, fill E new)) 
              (OK h' T (tSingleton (bump tid, nil, cAct x j (fill E new)::s2, fill E(ret(fvar x)))))
|CSpec : forall E M t N tid' tid s2 T h i j l, 
          decompose t E (spec M N) -> tid' = extendTid tid -> tid = Tid(i, j) l ->
          progress_step h T (tSingleton (tid, nil, s2, fill E (spec M N))) (OK h T
               (tCouple (bump tid, nil, specRetAct tid' j (fill E (spec M N))::s2,fill E(specReturn M tid' N))
                        (tid', [specAct], nil, N)))
|CSpecJoin : forall t E M M' N0 N1 tid maj min min' tid' T h t1 t2 s1 s1' s2 s2',
              decompose t E (specReturn (ret N1) (Tid(maj,min) tid') N0) ->
              s1 = s1' ++ [specAct] ->
              t1 = (tid,nil,s2, t) -> t2 = (Tid(maj,min')tid',s1,s2',M') ->
              progress_step h T (tCouple t1 t2) 
                   (OK h T (tSingleton(tid,wrapActs s1' N1, s2,
                                       fill E (specJoin (ret N1) M))))
|CSpecRB : forall t E' h h' tid tid' maj min  min'' T T' E M' N0 s2 s1' a s2' t1 t2 TRB, 
            decompose t E' (specReturn (raise E) (Tid(maj,min'') tid') N0)->
            t1 = (tid,nil,s2,t) -> t2 = (Tid(maj,min) tid',s1'++[a],s2',M') -> 
            ~ (exists p, thread_lookup TRB tid p) -> 
            thread_lookup TRB (Tid (maj, min) tid') t2 -> 
            ~ (exists p', thread_lookup T' (Tid (maj, min) tid') p') ->
            rollback (Tid (maj, min) tid') [a] h (tAdd TRB t2) h' T' ->
            progress_step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, nil, s2, fill E'(raise E))))
|CSpecRaise : forall E' N h tid s2 T E t1 t,
               decompose t E' (specJoin(ret N)(raise E)) ->
               t1 = (tid, nil, s2, t) -> 
               progress_step h T (tSingleton t1) 
                    (OK h T (tSingleton (tid, nil, s2, fill E' (raise E))))
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
             decompose t E (AST.app (lambda e) N) ->               
             spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E (open 0 N e))))
|ProjL : forall tid s2 E V1 V2 h T t a b, 
           decompose t E (fst (pair_ V1 V2)) -> 
           spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E V1)))
|ProjR : forall tid a b s2 E V1 V2 h T t, 
           decompose t E (snd (pair_ V1 V2)) -> 
           spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E V2)))
|Bind : forall tid h E T N M a b s2 t, decompose t E (bind (ret M) N) ->
  spec_step h T (tSingleton (tid, a::b, s2, t)) (OK h T (tSingleton (tid,a::b,s2,fill E(AST.app N M))))
|BindRaise : forall tid h E T N M a b s2 t, decompose t E (bind (raise M) N) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (raise M))))
|Handle : forall tid h E T N M a b s2 t, decompose t E (handle (raise M) N) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (AST.app  N M))))
|HandleRet : forall tid h E T N M a b s2 t, decompose t E (handle (ret M) N) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (ret M))))
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
|Spec : forall E M t N tid' tid a b s2 T h i j l, 
          decompose t E (spec M N) -> tid' = extendTid tid -> tid = Tid(i, j) l ->
          spec_step h T (tSingleton (tid, a::b, s2, fill E (spec M N))) (OK h T
               (tCouple (bump tid, specRetAct tid' j (fill E (spec M N))::a::b, s2,fill E(specReturn M tid' N))
                        (tid', [specAct], nil, N)))
.


(*speculative steps cannot raise an error, so no need for config*)
Inductive spec_multistep : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|smulti_refl : forall (h : sHeap) (p1 p2 : pool),
                 spec_multistep h p1 p2 h p1 p2
| smulti_step : forall (c : config) (T1 T2 T1'' T2'' P1 P2 : Ensemble thread)
                       (P2' : pool) (h h' H'' : sHeap),
                  T2 = tUnion P1 P2 ->
                 Disjoint thread P1 P2 ->
                 spec_step h (tUnion P1 T1) P2 (OK h' (tUnion P1 T1) P2') ->
                 spec_multistep h' T1 (tUnion P1 P2') H'' T1'' T2'' -> spec_multistep h T1 T2 H'' T1'' T2''
.
                                                               
Theorem eraseUnionComm : forall T1 T2, 
                           erasePoolAux (Union thread T1 T2) = 
                           Union ptrm (erasePoolAux T1)(erasePoolAux T2).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. cleanup. inversion H3; subst. 
   {constructor. econstructor. econstructor. eassumption. reflexivity. eauto. auto. }   {apply Union_intror. econstructor. econstructor. eassumption. auto. 
    eassumption. assumption. }
  }
  {inversion H; subst. 
   {inversion H0; subst. inversion H1; subst. cleanup. econstructor. econstructor. 
    econstructor. eassumption. reflexivity. eassumption. assumption. }
   {inversion H0; subst. inversion H1; subst. cleanup. econstructor. econstructor. 
    apply Union_intror. eassumption. auto. eassumption. assumption. }
  }
Qed. 

Theorem listAlign : forall (T:Type) l (x y :T) l' (e:T),
                      x::y::l = l' ++ [e] ->
                      exists l'', (y::l) = l'' ++ [e]. 
Proof.
  induction l; intros. 
  {destruct l'. inversion H. exists nil. inversion H.
   destruct l'. inversion H2. auto. inversion H2. destruct l'; inversion H4. }
  {destruct l'. 
   {inversion H. }
   {inversion H. exists l'. assumption. }
  }
Qed. 

Hint Resolve app_comm_cons. 

Theorem eraseTwoActs : forall tid tid' A1 A2 As s2 M M' t,
                         eraseThread (tid', (A1::A2::As), s2, M') t <->
                         eraseThread (tid, (A2 :: As), s2, M) t. 
Proof.
  intros. split; intros. 
  {inversion H; subst; match goal with
       |H:?A1::?A2::?As=?s++[?a] |- _ => apply listAlign in H; invertExists
        end; match goal with
               |H:?A::?As=?x++[?a] |- eraseThread(?t,?A::?As,?s2,?m) ?M =>
                rewrite H; destruct t; destruct p
             end; eauto. 
  }
  {inversion H; subst; rewrite H5; eauto. }
Qed. 

Ltac eraseThreadTac :=
  match goal with
      | |- eraseThread (?t,?s++[rAct ?x ?m ?M],?s2,?z) ?y  => eapply tEraseRead
      | |- eraseThread (?t,?s++[wAct ?x ?m ?M],?s2,?z) ?y => eapply tEraseWrite
      | |- eraseThread (?t,?s++[cAct ?x ?m ?M],?s2,?z) ?y => eapply tEraseNew
      | |- eraseThread (?t,?s++[fAct ?x ?m ?M],?s2,?z) ?y => eapply tEraseFork
      | |- eraseThread (?t,?s++[specRetAct ?x ?m ?M],?s2,?z) ?y => 
        eapply tEraseSpecRet
      | |- eraseThread (?t,?s++[specAct],?s2,?z) ?y => eapply tEraseCreatedSpec
  end. 

Theorem eraseSpecThreadSame : forall tid tid' a b s2 M M' t, 
                                eraseThread (tid,a::b,s2,M) t <->
                                eraseThread (tid',a::b,s2,M') t.
Proof.
  intros. split; intros; 
  inversion H; subst; try solve[rewrite H5; eraseThreadTac; eauto]. Qed. 

Theorem threadErasePoolErase : forall t t' t'', 
                                 eraseThread t t'' -> eraseThread t' t'' ->
                                 erasePoolAux (tSingleton t) = 
                                 erasePoolAux (tSingleton t').
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H1; subst. inversion H2; subst. cleanup. destruct t'. destruct p. 
   destruct p. destruct t1. destruct p. econstructor. 
   econstructor. econstructor. auto. eassumption. inversion H5; subst. 
   clear H5. eapply erasureDeterminism in H3; eauto. subst. auto. }
  {inversion H1; subst. inversion H2; subst. cleanup. inversion H5; subst. 
   destruct t. destruct p. destruct p. destruct t0. destruct p. econstructor. 
   econstructor. econstructor. auto. eassumption. 
   eapply erasureDeterminism in H3; eauto. subst. auto. }
Qed. 

Theorem threadErasePoolEraseCouple : forall t1 t2 t1' t2' t1'' t2'', 
                                 eraseThread t1 t1'' -> eraseThread t1' t1'' ->
                                 eraseThread t2 t2'' -> eraseThread t2' t2'' ->
                                 erasePoolAux (tCouple t1 t2) = 
                                 erasePoolAux (tCouple t1' t2').
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H3; subst. inversion H4; subst. cleanup. inversion H7; subst. 
   {destruct t1'. destruct p. destruct p. destruct t0. destruct p. econstructor. 
    econstructor. econstructor. auto. eassumption. 
    eapply erasureDeterminism in H5; eauto. subst. auto. }
   {destruct t2'. destruct p. destruct p. destruct t0. destruct p. econstructor. 
    econstructor. apply Couple_r. auto. eassumption. 
    eapply erasureDeterminism in H5; eauto. subst. auto. }
  }
  {inversion H3; subst. inversion H4; subst. cleanup. inversion H7; subst. 
   {destruct t1. destruct p. destruct p. destruct t0. destruct p. econstructor. 
    econstructor. econstructor. auto. eauto. eapply erasureDeterminism in H5; eauto. 
    subst. auto. }
   {destruct t2. destruct p. destruct p. destruct t0. destruct p. econstructor. 
    econstructor. econstructor. auto. eauto. eapply erasureDeterminism in H5; eauto. 
    subst. auto. }
  }
Qed. 

Theorem erasePoolDeterminism : forall T T' T'', 
                                 erasePool T T' -> erasePool T T'' ->
                                 T' = T''. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. assumption. }
  {inversion H; subst. inversion H0; subst. assumption. }
Qed. 

Theorem throwoutSpec : forall t tid s1 s2 M,
                         erasePoolAux(tCouple t (tid,s1++[specAct],s2,M)) = 
                         erasePoolAux(tSingleton t). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. cleanup. inversion H3; subst. 
   {econstructor. econstructor. constructor. auto. eassumption. assumption. }
   {inversion H1; try invertListNeq. subst. inversion H2. }
  }
  {inversion H; subst. inversion H0; subst. cleanup. inversion H3; subst. 
   clear H3. econstructor. econstructor. apply Couple_l. auto. eauto. auto. }
Qed. 

Theorem eraseHeapDependentRead : forall H H' x sc ds s w N t,
             eraseHeap H H' ->
             heap_lookup x H = Some(sfull sc ds s w N) ->
             eraseHeap (replace x (sfull sc (t::ds) s w N) H) H'. 
Proof.
  intros. induction H0; subst; try solve[
  simpl in *; destruct (beq_nat x i) eqn:eq;
   [inversion H1|apply IHeraseHeap in H1; constructor; assumption]]. 
  {simpl in *. destruct (beq_nat x i); auto. inversion H1; subst. constructor. 
   assumption. }
  {simpl in *. destruct (beq_nat x i) eqn:eq; auto. apply beq_nat_true in eq. 
   subst. inversion H1; subst. constructor. assumption. }
  {simpl in *. destruct (beq_nat x i) eqn:eq; auto. apply beq_nat_true in eq. 
   inversion H1; subst. constructor; auto. }
  {simpl in H1. inversion H1. }
Qed. 

Theorem eraseHeapWrite : forall H H' x sc a b tid N,
                           eraseHeap H H' ->
                           heap_lookup x H = Some (sempty sc) ->
                           eraseHeap (replace x (sfull sc nil (a::b) tid N) H) H'. 
Proof.
  intros. induction H0; try solve[ 
  simpl in *; destruct(beq_nat x i); auto; inversion H1; subst; auto].  
  {simpl in *. destruct (beq_nat x i) eqn:eq; auto. inversion H1; subst. 
   apply beq_nat_true in eq. subst. auto. }
  {simpl in *. inversion H1. }
Qed. 

Theorem eraseHeapNew : forall H H' H'' x a b,
                         eraseHeap H H' -> 
                         (x, H'') = extend (sempty (a::b)) H ->
                         eraseHeap H'' H'. 
Proof.
  intros. induction H0; try solve[simpl in *; inversion H1; subst; auto]. 
Qed. 

Theorem specSingleStepErase : forall H T H' T' H'' T'' P,
                                spec_step H P T (OK H' P T') ->
                                eraseHeap H H'' -> erasePool T T'' -> 
                                eraseHeap H' H'' /\ erasePool T' T''.
Proof.
  intros. inversion H0; subst; try solve[
  split;[assumption|idtac]; inversion H2; subst; eapply erasePoolEraseThread in H2; 
   [invertHyp; erewrite threadErasePoolErase;[constructor|eassumption|auto];
   rewrite eraseSpecThreadSame; eassumption|constructor]]. 
  {split. assumption. inversion H2; subst. eapply erasePoolEraseThread in H2. 
   Focus 2. econstructor. invertHyp. erewrite <- throwoutSpec.
   erewrite threadErasePoolEraseCouple. econstructor. rewrite eraseSpecThreadSame. 
   eassumption. rewrite eraseTwoActs. eassumption. eapply tEraseCreatedSpec; eauto.
   eapply tEraseCreatedSpec. rewrite app_nil_l. auto. }
  {split. apply eraseHeapDependentRead; auto. inversion H2; subst. 
   eapply erasePoolEraseThread in H2. invertHyp. erewrite threadErasePoolErase. 
   constructor. eassumption. rewrite eraseTwoActs. eassumption. constructor. }
  {split. apply eraseHeapWrite; auto. inversion H2; subst. 
   eapply erasePoolEraseThread in H2. invertHyp. erewrite threadErasePoolErase. 
   constructor. eassumption. rewrite eraseTwoActs. eassumption. constructor. }
  {split. eapply eraseHeapNew; eauto. inversion H2; subst. 
   eapply erasePoolEraseThread in H2. invertHyp. erewrite threadErasePoolErase. 
   constructor. eassumption. rewrite eraseTwoActs. eassumption. constructor. }
  {split. assumption. inversion H2; subst. eapply erasePoolEraseThread in H2. 
   Focus 2. econstructor. invertHyp. erewrite <- throwoutSpec.
   erewrite threadErasePoolEraseCouple. econstructor. eassumption. 
   rewrite eraseTwoActs. eassumption. eapply tEraseCreatedSpec. 
   auto. eapply tEraseCreatedSpec. rewrite app_nil_l. auto. }
  Grab Existential Variables. repeat constructor. repeat constructor. 
  repeat constructor. repeat constructor. repeat constructor. repeat constructor. 
  repeat constructor. repeat constructor. Qed. 

Theorem spec_multistepErase : forall H T H' T' H'' T'',
                                spec_multistep H tEmptySet T H' tEmptySet T' ->
                                eraseHeap H H'' -> erasePool T T'' -> 
                                eraseHeap H' H'' /\ erasePool T' T''.
Proof.
  intros. remember tEmptySet. generalize dependent H''. generalize dependent T''. 
  induction H0; subst; auto; intros. inversion H3; subst. 
  apply specSingleStepErase with(H'':=H''0)(T'':= erasePoolAux P2)in H1; auto. 
  inversion H1. apply IHspec_multistep; auto. rewrite eraseUnionComm in H3.  
  inversion H5; subst. rewrite eraseUnionComm. rewrite <- H8. 
  rewrite <- eraseUnionComm. constructor. Qed. 
