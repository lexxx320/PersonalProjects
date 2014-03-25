Require Export List.
Export ListNotations.
 
Require Export Heap. 
Require Export AST. 


Inductive pool : Type :=
  |thread : tid -> list action -> list action -> term -> pool
  |dot : pool
  |par : pool -> pool -> pool.

Fixpoint bump (t : tid) : tid := 
  match t with
    |tidNil => tidNil
    |tidCons t' maj min => tidCons t' maj (min+1)
  end.

Open Scope list_scope. 

Inductive rollback : tid -> heap -> pool -> heap -> pool -> Prop :=
|RBDone : forall t maj min h min' M' tid' M T s2, 
            rollback (tidCons t maj min) h (par (thread (tidCons t maj min') [sAct tid' M'] s2 M) T)
                     h (par (thread (tidCons t maj min') [sAct tid' M'] s2 M) T)
|RBRead : forall s1 s1' s2 x tid tid' tid'' M M' N h h' h'' T T' sc t A S ds, 
            s1 = s1' ++ [rAct x tid'' M'] -> heap_lookup x h = full sc (tid''::ds) (S::A) t N ->
            h' = replace x (full sc ds (S::A) t N) -> 
            rollback tid h (par (thread tid'' s1' s2 M') T) h'' T'->
            rollback tid h (par(thread tid' s1 s2 M) T) h'' T'
|RBFork : forall s1 s1' s2 s2' tid tid' tid'' tid2 M M' N T T' h h',
            s1 = s1' ++ [fAct tid2 tid'' M'] -> 
            rollback tid h (par (thread tid'' s1' s2 M') T) h' T' ->
            rollback tid h (par (par (thread tid' s1 s2 M) (thread tid'' [specAct] s2' N)) T) h' T'
|RBWrite : forall s1 s1' s2 tid tid' tid'' M M' N S A sc T T' h h' h'' x,
             s1 = s1' ++ [wAct x tid'' M'] -> heap_lookup x h = full sc nil (S::A) tid'' N ->
             h' = replace x (empty sc) h -> rollback tid h' (par (thread tid'' s1' s2 M') T) h'' T' ->
             rollback tid h (par (thread tid' s1 s2 M) T) h'' T'
|RBNew : forall s1 s1' s2 tid tid' tid'' M M' S A T T' h h' h'' x,
           s1 = s1' ++ [cAct x tid'' M'] -> heap_lookup x h = empty (S::A) ->
           h' = remove h x -> rollback tid h' (par (thread tid'' s1' s2 M') T) h'' T' ->
           rollback tid h (par (thread tid' s1 s2 M) T) h'' T'
|RBSpec : forall s1 s1' s2 s2' tid tid2 tid' tid'' tid''' M M' N N' T T' h h',
            s1 = s1' ++ [fAct tid2 tid'' M'] -> 
            rollback tid h (par (thread tid'' s1' s2 M') T) h' T' ->
            rollback tid h (par (par (thread tid' s1 s2 M) 
                                             (thread tid''' [sAct tid2 N'; specAct] s2' N)) T) h' T'
.
 
Inductive congr : pool -> pool -> Prop :=
  |comm : forall t1 t2, congr (par t1 t2) (par t2 t1)
  |assoc : forall t1 t2 t3, congr (par (par t1 t2) t3) (par t1 (par t2 t3))
  |assoc2 : forall t1 t2 t3, congr(par t1 (par t2 t3)) (par (par t1 t2) t3)
  |refl : forall t1, congr t1 t1
.

Inductive step : heap -> pool -> heap -> pool -> Prop :=
(*
  |CommStep1 : forall h t1 t2, step h (par t1 t2) h (par t2 t1) 
  |AssocStep1 : forall h t1 t2 t3,
                  step h (par (par t1 t2) t3) h (par t1 (par t2 t3))
  |AssocStep2 : forall h t1 t2 t3,
                  step h (par t1 (par t2 t3)) h (par (par t1 t2) t3) 
*)
  |BindStep : forall t1 t1' t2 h h' s1 s2 s1' s2' tid tid' T, 
                step h (par (thread tid s1 s2 t1) T) h' (par (thread (bump tid) s1' s2' t1') T)->
                step h (par (thread tid s1 s2 (bind t1 t2)) T) h' 
                     (par (thread (bump tid') s1' s2' (bind t1' t2)) T)
  |Bind : forall t1 t2 h s1 s2 tid T,
            step h (par (thread tid s1 s2 (bind (ret t1) t2)) T) h 
                 (par (thread (bump tid) s1 s2 (app t2 t1)) T)
  |Fork : forall t1 h s1 s2 tid T, 
            step h (par (thread tid s1 s2 (fork t1)) T) h 
                   (par (par (thread (bump tid) (fAct (tidCons tid 1 1) tid (fork t1) :: s1) s2 (ret unit))
                                       (thread (tidCons tid 1 1) nil nil t1)) T)
  |Get : forall  h i M s1 s2 tid ds sc s t h' T,  
           heap_lookup i h = full sc ds s t M -> h' = replace i (full sc (tid :: ds) s t M) h ->
           step h (par (thread tid s1 s2 (get i)) T) h' 
                (par (thread (bump tid) (rAct i tid (get i) :: s1) s2 (ret M)) T)
  |Put : forall h h' i M s1 s2 tid sc T,
           heap_lookup i h = empty sc -> h' = replace i (full sc nil s1 tid M) h ->
           step h (par (thread tid s1 s2 (put i M)) T) h' 
                (par (thread (bump tid) (wAct i tid (put i M) :: s1) s2 (ret unit)) T)
  |Spec : forall h tid tid' s1 s2 T M N,
            tid' = tidCons tid 1 1 ->
            step h (par (thread tid s1 s2 (spec M N)) T) h 
                 (par (par (thread (bump tid) s1 s2 (specReturn M N tid')) (thread tid' nil nil N)) T) 
  |PopSpec : forall h s1 s1' s2 s2' tid tid' tid'' M M0 N1 N2 T maj min min', 
               s1 = s1' ++ [sAct tid'' M] ->
               step h (par (par (thread tid nil s2 (specReturn (ret N1) M0 (tidCons tid' maj min))) 
                                        (thread (tidCons tid' maj min') s1 s2' (ret N2))) T) 
                    h (par (par (thread (bump tid) nil s2 (specReturn (ret N1) M0 (tidCons tid' maj min)))
                                        (thread (tidCons tid' maj (min'+1)) (joinAct::s1')
                                                ((sAct tid'' M)::s2') (ret N2))) T)
  |SpecJoin : forall h s2 s2' tid tid' N1 N2 M0 maj min T,
                step h (par (par(thread tid nil s2 (specReturn (ret N1) M0 (tidCons tid' maj min)))
                                        (thread tid' [joinAct] s2' (ret N2))) T)
                     h (par (thread (bump tid) nil s2 (ret (pair N1 N2))) T)
  |SpecRB : forall h h' tid tid' tid'' maj min min' min'' T T' E M' M'' M0 s1 s2 s1' s2', 
              rollback (tidCons tid' maj min) h (par (thread (tidCons tid' maj min) s1' s2' M') T) 
                       h' (par (thread (tidCons tid' maj min') [sAct tid'' M''] s2' M') T') ->
              step h (par (par (thread tid s1 s2 (specReturn (raise E) M0 (tidCons tid' maj min'')))
                                       (thread (tidCons tid' maj min) s1' s2' M')) T)
                   h' (par (thread (bump tid) s1 s2 (raise E)) T')
  |SpecRaise : forall h tid tid' maj min min' s2 s2' T E N1 M0,
                 step h (par (par (thread tid nil s2 (specReturn (ret N1) M0 (tidCons tid' maj min)))
                                          (thread (tidCons tid' maj min') [joinAct] s2' (raise E))) T)
                      h (par (thread (bump tid) nil s2 (raise E)) T)
  |New : forall h h' i tid s1 s2,
           h' = replace i (empty s1) h ->
           step h (thread tid s1 s2 new) h' (thread (bump tid) (cAct i tid new :: s1) s2 (ret (var i)))
  |Raise : forall h tid s1 s2 M N,
             step h (thread tid s1 s2 (bind (raise M) N)) h (thread (bump tid) s1 s2 (raise M))
  |Handle : forall h tid s1 s2 M N,
              step h (thread tid s1 s2 (handle (raise M) N)) h (thread (bump tid) s1 s2 (app N M))
  |PopRead : forall h tid tid' s1 s1' s2 M M' i ds t N,
               s1 = s1' ++ [rAct i tid' M'] -> heap_lookup i h = full nil ds nil t N ->
               step h (thread tid s1 s2 M) h (thread (bump tid) s1' ((rAct i tid' M')::s2) M)
  |PopWrite : forall h tid tid' s1 s1' s2 M' M ds s N i,
                s1 = s1' ++ [wAct i tid' M'] -> heap_lookup i h = full nil ds s tid' N ->
                step h (thread tid s1 s2 M) (replace i (full nil nil nil tid' N) h)
                (thread (bump tid) s1' ((wAct i tid' M') :: s2) M)
  |PopNewFull : forall h s1 s1' s2 i tid tid' M' ds s s' t M N T, 
                  s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = full s ds s' t N ->
                  step h (par (thread tid s1 s2 M) T) (replace i (full nil ds s' t N) h)
                       (par (thread tid s1' ((cAct i tid' M')::s2) M) T)
  |PopNewEmpty : forall h s1 s1' s2 i tid tid' M' s M T, 
                   s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = empty s ->
                   step h (par (thread tid s1 s2 M) T) (replace i (empty nil) h)
                        (par (thread tid s1' ((cAct i tid' M')::s2) M) T)
  |PopFork : forall h s1 s1' s1'' s1''' s2 s2' tid tid' tid1 tid2 M' M N T, 
               s1 = s1' ++ [fAct tid1 tid2 M'] -> s1'' = s1''' ++ [specAct] ->
               step h (par (par (thread tid s1 s2 M) (thread tid' s1'' s2' N)) T)
                    h (par (par (thread (bump tid) s1' ((fAct tid1 tid2 M')::s2) M) 
                                        (thread (bump tid') s1''' (specAct :: s2') N)) T)
  |Terminate : forall h tid s M T, step h (par (thread tid nil s (ret M)) T) h T
  |CongrStep : forall t1 t1' t2 t2' h h', congr t1 t1' -> congr t2 t2' -> step h t1' h' t2' ->
                                        step h t1 h' t2
.

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BindStep" | Case_aux c "Bind" | Case_aux c "Fork" |
    Case_aux c "Get" | Case_aux c "Put" | Case_aux c "Spec" |
    Case_aux c "PopSpec" | Case_aux c "SpecJoin" | Case_aux c "SpecRB" |
    Case_aux c "SpecRaise" | Case_aux c "New" | Case_aux c "Raise" | 
    Case_aux c " Handle" | Case_aux c "PopRead" | Case_aux c "PopWrite" |
    Case_aux c "PopNewFull" | Case_aux c "PopNewEmpty" | Case_aux c "PopFork" |
    Case_aux c "Terminate" | Case_aux c "CongrStep"
].

Inductive unspecHeap : heap -> heap -> Prop :=
  |unSpecSE : forall h h' i hd tl, unspecHeap h h' -> unspecHeap ((i, empty (hd::tl)) :: h') h'
  |unSpecCE : forall h h' i, unspecHeap h h' -> unspecHeap ((i, empty nil) :: h') ((i, empty nil) :: h')
  |unspecSF : forall h h' i hd tl d s t N, unspecHeap h h' -> unspecHeap ((i, full (hd::tl) d s t N) :: h') h'
  |unspecCCSF : forall h h' i d hd tl t M, unspecHeap h h' ->
                                           unspecHeap ((i, full nil d (hd::tl) t M)::h) ((i, empty nil)::h')
  |unspecCCCF : forall h h' i d t M, unspecHeap h h' ->
                                     unspecHeap ((i, full nil d nil t M)::h) ((i, full nil d nil t M)::h')
.

Inductive unspecT : pool -> pool -> Prop :=
  |unSpecDot : unspecT dot dot
  |unSpecPar : forall t1 t1' t2 t2', 
                 unspecT t1 t1' -> unspecT t2 t2' -> unspecT (par t1 t2) (par t1' t2')
  |unSpecCThread : forall tid s1 s2 M,
                    s1 = nil -> unspecT (thread tid s1 s2 M) (thread tid s1 s2 M)
  |unSpecRead : forall tid s1 s1' s2 M i tid' M',
                  s1 = s1' ++ [rAct i tid' M'] ->
                  unspecT (thread tid s1 s2 M) (thread tid' nil s2 M')
  |unSpecWrite : forall tid s1 s1' s2 M i tid' M',
                   s1 = s1' ++ [wAct i tid' M'] ->
                   unspecT (thread tid s1 s2 M) (thread tid' nil s2 M')
  |unSpecCreate : forall tid s1 s1' s2 M i tid' M',
                  s1 = s1' ++ [cAct i tid' M'] ->
                  unspecT (thread tid s1 s2 M) (thread tid' nil s2 M')
  |unSpecSpec : forall tid s1 s1' s2 M tid' M',
                  s1 = s1' ++ [sAct tid' M'] ->
                  unspecT (thread tid s1 s2 M) (thread tid' [sAct tid' M'] s2 M')
  |unSpecFork : forall tid s1 s1' s2 M tid' M' tid'',
                  s1 = s1' ++ [fAct tid' tid'' M'] ->
                  unspecT (thread tid s1 s2 M) (thread tid'' nil s2 M').


Inductive unspec : heap -> pool -> heap -> pool -> Prop :=
  |Unspec : forall h h' p p', unspecHeap h h' -> unspecT p p' -> unspec h p h' p'.


Inductive multistep : heap -> pool -> heap -> pool -> Prop :=
|reflStep : forall h p, multistep h p h p
|multiStep : forall h h' h'' p p' p'', step h p h' p' -> multistep h' p' h'' p'' ->
                               multistep h p h'' p''
.

Inductive wellFormed : heap -> pool -> Prop :=
|WF : forall h h' p p', unspecHeap h h' -> unspecT p p' -> multistep h p h' p' ->
                        wellFormed h p.

Inductive specActions : pool -> list (tid * specStack) -> Prop :=
  |sCompActions : forall T1 T2 a1 a2, specActions T1 a1 -> specActions T2 a2 ->
                                     specActions (par T1 T2) (a1 ++ a2)
  |sThreadActions : forall tid maj min s1 s2 M, 
                     specActions (thread (tidCons tid maj min) s1 s2 M) [(tidCons tid maj 1, s1)]
  |sDotActions : specActions dot nil
.

Inductive commitActions : pool -> list (tid * specStack) -> Prop :=
  |nsCompActions : forall T1 T2 a1 a2, commitActions T1 a1 -> commitActions T2 a2 ->
                                       commitActions (par T1 T2) (a1 ++ a2)
  |nsThreadActions : forall tid maj min s1 s2 M, 
                       commitActions (thread (tidCons tid maj min) s1 s2 M) [(tidCons tid maj 1, s2)]
  |nsDotActions : commitActions dot nil
.

Theorem Reorder1Step : forall H T1 T2 H' T1' T2' sa ca,
                         specActions T2 sa -> specActions T2' sa -> commitActions T2 ca ->
                         commitActions T2' ca -> step H (par T1 T2) H' (par T1' T2) ->
                         step H' (par T1' T2) H' (par T1' T2') ->
                         step H (par T1 T2) H (par T1 T2') /\ 
                         step H (par T1 T2') H' (par T1' T2').
Proof.


Theorem Reorder1Step2 : forall H T1 T2 H' T1' T2' sa ca,
                         specActions T2 sa -> specActions T2' sa -> commitActions T2 ca ->
                         commitActions T2' ca -> step H (par T1 T2) H' (par T1' T2) ->
                         step H' (par T2 T1') H' (par T2' T1') ->
                         step H (par T2 T1) H (par T2' T1) /\ 
                         step H (par T1 T2') H' (par T1' T2').
Proof.
  intros. step_cases(induction H4) Case. 
  {apply IHstep in H5. assumption. }
  {