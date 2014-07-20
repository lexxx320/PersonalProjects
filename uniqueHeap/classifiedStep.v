Require Import AST.   
Require Import NonSpec.   
Require Import Spec.  
Require Import Heap. 
Require Import sets. 
Require Import Coq.Sets.Ensembles. 

Inductive SPEC : actionStack -> Prop :=
|lockSpec : forall s, SPEC (locked s)
|unlockedSpec : forall a b, SPEC(unlocked (a::b)). 

Inductive prog_step : sHeap -> pool -> pool -> config -> Prop :=
|BasicStep : forall tid s2 h T t t',
               basic_step t t' ->
               prog_step h T (tSingleton(tid,unlocked nil, s2,t))
                         (OK h T (tSingleton(tid,unlocked nil,s2,t')))
|Fork : forall tid h T M s2 E t (d:decompose t E (fork M)), 
          prog_step h T (tSingleton (tid, (unlocked nil), s2,t)) 
        (OK h T(tCouple (tid, (unlocked nil), fAct t E M d :: s2, fill E(ret unit)) 
                        (1::tid, (unlocked nil), [], M)))
|Get : forall TID h h' T N s2 E x s ds writer t (d:decompose t E (get (fvar x))),
         heap_lookup x h = Some(sfull (unlocked nil) ds s writer N) -> 
         h' = replace x (sfull (unlocked nil) (Add tid ds TID) s writer N) h ->
         prog_step h T (tSingleton (TID, (unlocked nil), s2, t))
              (OK h' T (tSingleton (TID, (unlocked nil), rAct x t E d::s2, fill E(ret N))))
|Put : forall E x N h h' s2 TID T t (d:decompose t E (put (fvar x) N)), 
         decompose t E (put (fvar x) N) -> heap_lookup x h = Some(sempty (unlocked nil)) ->
         h' = replace x (sfull (unlocked nil) (Empty_set tid) (unlocked nil) TID N) h -> 
         prog_step h T (tSingleton (TID, (unlocked nil), s2, t)) (OK h' T
              (tSingleton (TID, (unlocked nil), wAct x t E N d::s2, fill E(ret unit))))
|Overwrite : forall t E x N N' h h' h'' T TR TR' S' A s2 ds TID TID' (d:decompose t E (put (fvar x) N)), 
               heap_lookup x h = Some (sfull (unlocked nil) ds (aCons S' A) TID' N') ->
               rollback TID' (aCons S' A) h TR h' TR' ->
               h'' = replace x (sfull (unlocked nil) (Empty_set tid) (unlocked nil) TID N) h' -> 
               prog_step h T (tAdd TR (TID, (unlocked nil), s2, fill E(put (fvar x) N))) (OK h'' T
                    (tAdd TR' (TID, (unlocked nil), wAct x t E N d::s2, fill E (ret unit))))
|New : forall E h h' x tid t s2 T (d:decompose t E new) (p:heap_lookup x h = None),
         h' = extend x (sempty (unlocked nil)) h p -> 
         prog_step h T (tSingleton (tid, (unlocked nil), s2, fill E new)) 
              (OK h' T (tSingleton (tid, (unlocked nil), nAct t E d x::s2, fill E(ret(fvar x)))))
|Spec : forall E M t N tid s2 T h (d:decompose t E (spec M N)), 
          prog_step h T (tSingleton (tid, (unlocked nil), s2, t)) (OK h T
               (tCouple (tid, (unlocked nil), srAct t E M N d::s2,t) (tid, (unlocked nil), [], N))) 
|SpecJoin : forall t E M N0 N1 tid T h t1 t2 s1 s2 s2',
              decompose t E (specRun (ret N1) N0) ->
              t1 = (tid,(unlocked nil),s2, t) -> t2 = (2::tid,locked s1,s2',M) ->
              prog_step h T (tCouple t1 t2) 
                   (OK h T (tSingleton(tid,unlocked (wrapActs s1 N1), s2, fill E (specJoin (ret N1) M)))) 
|SpecRB : forall t E' h h' tid T T' E M' N0 s2 s1 s2' t1 t2 TRB, 
            decompose t E' (specRun (raise E) N0)->
            t1 = (tid,(unlocked nil),s2,t) -> t2 = (2::tid,locked s1,s2',M') -> 
            ~ (exists p, thread_lookup TRB (tid) p) -> 
            thread_lookup TRB (2::tid) t2 -> 
            ~ (exists p', thread_lookup T' (2::tid) p') ->
            rollback (2::tid) (locked nil) h TRB h' T' ->
            prog_step h T (tAdd TRB t1) (OK h' T (tAdd T' (tid, (unlocked nil), s2, fill E'(raise E))))
|SpecRaise : forall E' N h tid s2 T E t1 t,
               decompose t E' (specJoin(ret N)(raise E)) ->
               t1 = (tid, (unlocked nil), s2, t) -> 
               prog_step h T (tSingleton t1) 
                    (OK h T (tSingleton (tid, (unlocked nil), s2, fill E' (raise E))))
|PopRead : forall TID t s1 s1' s2 M M' N T h x ds E d h', 
             s1 = unlocked (s1' ++ [rAct x M' E d]) -> In tid ds TID ->
             heap_lookup x h = Some (sfull (unlocked nil) ds (unlocked nil) t N) ->
             h' = replace x (sfull (unlocked nil) (Subtract tid ds TID) (unlocked nil) t N) h ->
             prog_step h T (tSingleton (TID, s1, s2, M)) 
                       (OK h' T (tSingleton (TID, unlocked s1', (rAct x M' E d)::s2, M)))
|PopWrite : forall tid t s1 s1' s2 M M' M'' N T h h' x ds a b E d,
              s1 = unlocked(s1' ++ [wAct x M' E M'' d]) -> 
              heap_lookup x h = Some(sfull (unlocked nil) ds (aCons a b) t N) ->
              h' = replace x (sfull (unlocked nil) ds (unlocked nil) t N) -> 
              prog_step h T (tSingleton (tid, s1, s2, M))
                        (OK h T (tSingleton (tid, unlocked s1', (wAct x M' E M'' d)::s2, M)))
|PopNewFull : forall h h' s1 s1' s2 i tid M' ds s s' t M N T E d, 
                s1 = unlocked(s1' ++ [nAct M' E d i]) ->
                heap_lookup i h = Some(sfull s ds s t N) ->
                h' = replace i (sfull (unlocked nil) ds s' t N) h -> 
                prog_step h T (tSingleton (tid, s1, s2, M)) 
                          (OK h T (tSingleton (tid, unlocked s1', nAct M' E d i::s2, M)))
|PopNewEmpty : forall h h' s1 s1' s2 i tid M' s M T E d, 
                 s1 = unlocked(s1' ++ [nAct M' E d i]) -> heap_lookup i h = Some(sempty s) ->
                  h' = replace i (sempty (unlocked nil)) h -> 
                 prog_step h T (tSingleton (tid, s1, s2, M))
                           (OK h T (tSingleton (tid, unlocked s1', nAct M' E d i::s2, M)))
|PopFork : forall h s1 s1' s1'' s2 s2' tid M' M N T M'' E d, 
             s1 = unlocked(s1' ++ [fAct M' E M'' d]) -> 
             prog_step h T (tCouple (tid, s1, s2, M) (1::tid, locked s1'', s2', N)) (OK h T 
                  (tCouple (tid, unlocked s1', fAct M' E M'' d::s2, M)
                           (1::tid, unlocked s1'', s2', N)))
|PopSpec : forall h s1 s1' s2 t tid M' M N T E d, 
             s1 = unlocked(s1' ++ [srAct t E M N d]) ->
             prog_step h T (tSingleton (tid, s1, s2, M')) (OK h T 
                  (tSingleton (tid, unlocked s1', srAct t E M N d::s2, M')))
.

Inductive spec_step : sHeap -> pool -> pool -> sHeap -> pool -> pool -> Prop :=
|SBasicStep : forall h T tid s1 s2 t t',
                basic_step t t' -> SPEC s1 ->
                spec_step h T (tSingleton(tid,s1,s2,t)) h T (tSingleton(tid,s1,s2,t'))
|SFork : forall tid h T M b s2 E t (d:decompose t E (fork M)), 
          spec_step h T (tSingleton(tid, b, s2,t)) h T
               (tCouple (tid, aCons(fAct t E M d) b, s2, fill E(ret unit)) (1::tid, locked nil, nil, M))
|SGet : forall TID h h' T N b s2 E x s ds writer sc t (d:decompose t E (get(fvar x))),
         heap_lookup x h = Some(sfull sc ds s writer N) -> 
         h' = replace x (sfull sc (Add tid ds TID) s writer N) h ->
         spec_step h T (tSingleton(TID, b, s2, t)) h' T 
              (tSingleton (TID, aCons (rAct x t E d) b, s2, fill E(ret N)))
|SPut : forall E x N h sc h' b s2 TID T t (d:decompose t E (put (fvar x) N)), 
         heap_lookup x h = Some(sempty sc) ->
         h' = replace x (sfull sc (Empty_set tid) (aCons (wAct x t E N d) b) TID N) h ->
         spec_step h T (tSingleton(TID, b, s2, t)) h' T
              (tSingleton (TID, aCons (wAct x t E N d) b, s2, fill E(ret unit)))
|SNew : forall E h h' x tid t b s2 T (d:decompose t E new)
               (p:heap_lookup x h = None),
         h' = extend x (sempty (aCons (nAct t E d x) b)) h p ->
         spec_step h T (tSingleton(tid, b, s2, t))h' T
              (tSingleton (tid, aCons (nAct t E d x) b, s2, fill E(ret(fvar x))))
|SSpec : forall E M t N tid' tid b s2 T h (d:decompose t E (spec M N)), 
          spec_step h T (tSingleton(tid, b, s2, t)) h T
               (tCouple (tid, aCons (srAct t E M N d) b, s2,fill E(specRun M N))
                        (tid', locked nil, nil, N))

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

Theorem specStepCommitFullIVar:  forall x H H' ds tid M T t t',
         spec_step H T t H' T t' ->
         heap_lookup x H = Some(sfull (unlocked nil) ds (unlocked nil) tid M) ->
         exists ds', heap_lookup x H' = 
                     Some(sfull (unlocked nil) ds' (unlocked nil) tid M). 
Proof. 
  intros. inversion H0; subst; try solve[econstructor; eauto]. 
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H2 in H1. inv H1. 
    exists (Add AST.tid ds TID). erewrite HeapLookupReplace; eauto. }
   {eapply lookupReplaceNeq in H1; eauto. intros c. apply beq_nat_false in eq. 
    contradiction. }
  }
  {destruct (beq_nat x x0) eqn:eq. 
   {apply beq_nat_true in eq. subst. rewrite H2 in H1. inv H1. }
   {eapply lookupReplaceNeq in H1; eauto. apply beq_nat_false in eq. auto. }
  }
  {destruct H; simpl in *. destruct h. 
   {inv H1. } 
   {assert(x<>x0). intros c. subst. rewrite p in H1. inv H1. 
    rewrite <- beq_nat_false_iff in H. rewrite H. exists ds. eassumption. }
  }
Qed.