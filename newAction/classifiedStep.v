Require Import AST.   
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import Heap. 
Require Import sets. 
Require Import erasure. 


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
|Get : forall tid h h' T N s2 E x s ds writer t (d:decompose t E (get (fvar x))),
         heap_lookup x h = Some(sfull nil ds s writer N) -> 
         h' = replace x (sfull nil (tid::ds) s writer N) h ->
         prog_step h T (tSingleton (tid, nil, s2, t))
              (OK h' T (tSingleton (tid, nil, rAct x t E d::s2, fill E(ret N))))
|Put : forall E x N h h' s2 tid T t (d:decompose t E (put (fvar x) N)), 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty nil) ->
         h' = replace x (sfull nil nil nil tid N) h -> 
         prog_step h T (tSingleton (tid, nil, s2, t)) (OK h' T
              (tSingleton (tid, nil, wAct x t E N d::s2, fill E(ret unit))))
|Overwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds tid tid' (d:decompose t E (put (fvar x) N)), 
               heap_lookup x h = Some (sfull nil ds (S'::A) tid' N') ->
               rollback tid' (S'::A) h TR h' TR' ->
               h'' = replace x (sfull nil nil nil tid N) h' -> 
               prog_step h T (tAdd TR (tid, nil, s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (tid, nil, wAct x t E N d::s2, fill E (ret unit))))
|New : forall E h h' x tid t s2 T (d:decompose t E new),
         (x, h') = extend (sempty nil) h -> 
         prog_step h T (tSingleton (tid, nil, s2, fill E new)) 
              (OK h' T (tSingleton (tid, nil, nAct t E d x::s2, fill E(ret(fvar x)))))
|Spec : forall E M t N tid s2 T h (d:decompose t E (spec M N)), 
          prog_step h T (tSingleton (tid, nil, s2, t)) (OK h T
               (tCouple (tid, nil, srAct t E M N d::s2,t) (tid, nil, [specAct], N))) 
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
            rollback (2::tid) [specAct] h (tAdd TRB t2) h' T' ->
            prog_step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, nil, s2, fill E'(raise E))))
|SpecRaise : forall E' N h tid s2 T E t1 t,
               decompose t E' (specJoin(ret N)(raise E)) ->
               t1 = (tid, nil, s2, t) -> 
               prog_step h T (tSingleton t1) 
                    (OK h T (tSingleton (tid, nil, s2, fill E' (raise E))))
|PopRead : forall tid t s1 s1' s2 M M' N T h x ds E d h', 
             s1 = s1' ++ [rAct x M' E d] -> heap_lookup x h = Some (sfull nil (tid::ds) nil t N) ->
             h' = replace x (sfull nil ds nil t N) h ->
             prog_step h T (tSingleton (tid, s1, s2, M)) (OK h' T (tSingleton (tid, s1', (rAct x M' E d)::s2, M)))
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
.

Inductive spec_step : sHeap -> pool -> pool -> config -> Prop :=
|SBetaRed : forall E e N tid s2 h T t a b, 
             decompose t E (AST.app (lambda e) N) ->               
             spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E (open 0 N e))))
|SProjL : forall tid s2 E V1 V2 h T t a b, 
           decompose t E (fst (pair_ V1 V2)) -> 
           spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E V1)))
|SProjR : forall tid a b s2 E V1 V2 h T t, 
           decompose t E (snd (pair_ V1 V2)) -> 
           spec_step h T (tSingleton(tid,a::b,s2,t)) (OK h T (tSingleton(tid,a::b,s2,fill E V2)))
|SBind : forall tid h E T N M a b s2 t, decompose t E (bind (ret M) N) ->
  spec_step h T (tSingleton (tid, a::b, s2, t)) (OK h T (tSingleton (tid,a::b,s2,fill E(AST.app N M))))
|SBindRaise : forall tid h E T N M a b s2 t, decompose t E (bind (raise M) N) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (raise M))))
|SHandle : forall tid h E T N M a b s2 t, decompose t E (handle (raise M) N) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (AST.app  N M))))
|SHandleRet : forall tid h E T N M a b s2 t, decompose t E (handle (ret M) N) ->
  spec_step h T (tSingleton (tid,a::b,s2,t)) (OK h T (tSingleton (tid,a::b,s2,fill E (ret M))))
|SFork : forall tid h T M a b s2 E t (d:decompose t E (fork M)), 
          spec_step h T (tSingleton (tid, a::b, s2,t)) (OK h T
               (tCouple (tid, fAct t E M d::a::b, s2, fill E(ret unit)) (1::tid, [specAct], nil, M)))
|SGet : forall tid h h' T N a b s2 E x s ds writer sc t (d:decompose t E (get(fvar x))),
         heap_lookup x h = Some(sfull sc ds s writer N) -> 
         h' = replace x (sfull sc (tid::ds) s writer N) h ->
         spec_step h T (tSingleton (tid, a::b, s2, t)) (OK h' T 
              (tSingleton (tid, rAct x t E d::a::b, s2, fill E(ret N))) )
|SPut : forall E x N h sc h' a b s2 tid T t (d:decompose t E (put (fvar x) N)), 
         heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc nil (a::b) tid N) h ->
         spec_step h T (tSingleton (tid, a::b, s2, t)) (OK h' T
              (tSingleton (tid, wAct x t E N d::a::b, s2, fill E(ret unit))))
|SNew : forall E h h' x tid t a b s2 T (d:decompose t E new),
         (x, h') = extend (sempty (a::b)) h ->
         spec_step h T (tSingleton (tid, a::b, s2, t)) (OK h' T
              (tSingleton (tid, nAct t E d x::a::b, s2, fill E(ret(fvar x)))))
|SSpec : forall E M t N tid' tid a b s2 T h (d:decompose t E (spec M N)), 
          spec_step h T (tSingleton (tid, a::b, s2, t)) (OK h T
               (tCouple (tid, srAct t E M N d::a::b, s2,fill E(specRun M N))
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
    
Theorem eraseSpecThreadSame : forall tid tid' a b s2 M M' t, 
                                eraseThread (tid,a::b,s2,M) t <->
                                eraseThread (tid',a::b,s2,M') t.
Proof.
  intros. split; intros; 
  inversion H; subst; try solve[rewrite H5; eraseThreadTac; eauto]. Qed. 

Theorem erasePoolDeterminism : forall T T' T'', 
                                 erasePool T T' -> erasePool T T'' ->
                                 T' = T''. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. assumption. }
  {inversion H; subst. inversion H0; subst. assumption. }
Qed. 

Theorem eraseHeapDependentRead : forall H H' x sc ds s w N t,
             eraseHeap H = H' ->
             heap_lookup x H = Some(sfull sc ds s w N) ->
             eraseHeap (replace x (sfull sc (t::ds) s w N) H) = H'. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. apply beq_nat_true in eq. subst.  destruct sc. destruct s. auto. auto. auto. }
   {destruct i0. destruct a. simpl. erewrite IHlist; eauto. simpl. 
    auto. simpl. destruct a. destruct a0. erewrite IHlist; eauto. erewrite IHlist; eauto. 
    auto. }
  }
Qed. 

Theorem eraseHeapWrite : forall H H' x sc a b tid N,
                           eraseHeap H = H' ->
                           heap_lookup x H = Some (sempty sc) ->
                           eraseHeap (replace x (sfull sc nil (a::b) tid N) H) = H'. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i)eqn:eq. 
   {inv H1. apply beq_nat_true in eq. subst.  destruct sc; auto. }
   {simpl. destruct i0. destruct a. erewrite IHlist; eauto. auto. 
    destruct a. destruct a1. erewrite IHlist; eauto. erewrite IHlist; eauto. 
    auto. }
  }
Qed. 


Theorem eraseHeapNew : forall H H' H'' x a b,
                         eraseHeap H = H' -> 
                         (x, H'') = extend (sempty (a::b)) H ->
                         eraseHeap H'' = H'. 
Proof.
  induction H; intros. simpl in *. inv H0. auto. simpl in *. destruct a. inv H1. 
  auto. 
Qed. 

Ltac helper := 
  match goal with
      | |- erasePool (tSingleton ?t) (erasePoolAux (tSingleton ?t')) => 
        assert(exists t'', eraseThread t t'') by apply eraseThreadTotal; invertHyp
  end. 

Theorem listAlign2 : forall (T:Type) b a, exists (c : list T) d, a::b = c++[d]. 
Proof.
  induction b; intros. 
  {eauto. }
  {specialize (IHb a). invertHyp. rewrite H0. exists (a0::x). exists x0. auto. }
Qed. 

Ltac alignTac a b := assert(exists c d, a::b = c++[d]) by apply listAlign2; invertHyp.


Theorem specSingleStepErase : forall H T H' T' H'' T'' P,
                                spec_step H P T (OK H' P T') ->
                                eraseHeap H = H'' -> erasePool T T'' -> 
                                eraseHeap H' = H'' /\ erasePool T' T''.
Proof.
  intros.
  inversion H0; subst. 
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eapply eraseSpecSame. eauto. auto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eapply eraseSpecSame. eauto. auto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eapply eraseSpecSame. eauto. auto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eapply eraseSpecSame. eauto. auto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eapply eraseSpecSame. eauto. auto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eapply eraseSpecSame. eauto. auto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eapply eraseSpecSame. eauto. auto. }


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






