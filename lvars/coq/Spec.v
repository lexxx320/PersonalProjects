Require Export List.
Export ListNotations.
Require Import Coq.Program.Equality. 
Require Export Heap. 
Require Export AST. 


Inductive pool : Type :=
  |thread : tid -> list action -> list action -> term -> pool
  |dot : pool
  |par : pool -> pool -> pool.

Fixpoint bump (t : tid) : tid := 
  match t with
    |(maj, min) :: t' => (maj, S min) :: t'
    |nil => nil
  end.

Open Scope list_scope.
 
Inductive congr : pool -> pool -> Prop :=
  |comm : forall t1 t2, congr (par t1 t2) (par t2 t1)
  |assoc : forall t1 t2 t3, congr (par (par t1 t2) t3) (par t1 (par t2 t3))
  |refl : forall t1, congr t1 t1
.



Inductive ctxt : (term -> term) -> Prop :=
|bindCtxt : forall N c, ctxt c -> ctxt (fun M => bind (c M) N)
|specReturnCtxt : forall N c, ctxt c -> ctxt (fun M => specReturn M N)
|handleCtxt : forall N c, ctxt c -> ctxt (fun M => handle M N)
|hole : forall c, ctxt c -> ctxt (fun M => c M)
.

Inductive rollback : tid -> heap -> pool -> heap -> pool -> Prop :=
|RBDone : forall t maj min h min' M' tid' M T s2, 
            rollback ((maj, min)::t) h (par (thread ((maj, min') :: t) [sAct tid' M'] s2 M) T)
                     h (par (thread ((maj, min') :: t) [sAct tid' M'] s2 M) T)
|RBRead : forall s1 s1' s2 x tid tid' tid'' M M' N h h' h'' T T' sc t A S ds, 
            s1 = s1' ++ [rAct x tid'' M'] -> heap_lookup x h = full sc (tid''::ds) (S::A) t N ->
            h' = replace x (full sc ds (S::A) t N) h -> 
            rollback tid h' (par (thread tid'' s1' s2 M') T) h'' T'->
            rollback tid h (par(thread tid' s1 s2 M) T) h'' T'
|RBFork : forall s1 s1' s2 s2' tid tid' tid'' tid2 M M' N T T' h h',
            s1 = s1' ++ [fAct tid2 tid'' M'] -> 
            rollback tid h (par (thread tid'' s1' s2 M') T) h' T' ->
            rollback tid h (par (par (thread tid' s1 s2 M) (thread tid'' [specAct] s2' N)) T) h' T'
|RBWrite : forall s1 s1' s2 tid tid' tid'' M M' N S A sc T T' h h' h'' x,
             s1 = s1' ++ [wAct x tid'' M'] -> heap_lookup x h = full sc nil (S::A) tid'' N ->
             h' = replace x (empty sc) h -> 
             rollback tid h' (par (thread tid'' s1' s2 M') T) h'' T' ->
             rollback tid h (par (thread tid' s1 s2 M) T) h'' T'
|RBNew : forall s1 s1' s2 tid tid' tid'' M M' S A T T' h h' h'' x,
           s1 = s1' ++ [cAct x tid'' M'] -> heap_lookup x h = empty (S::A) ->
           h' = remove h x -> 
           rollback tid h' (par (thread tid'' s1' s2 M') T) h'' T' ->
           rollback tid h (par (thread tid' s1 s2 M) T) h'' T'
|RBSpec : forall s1 s1' s2 s2' tid tid2 tid' tid'' tid''' M M' N N' T T' h h',
            s1 = s1' ++ [fAct tid2 tid'' M'] -> 
            rollback tid h (par (thread tid'' s1' s2 M') T) h' T' ->
            rollback tid h (par (par (thread tid' s1 s2 M) 
                                             (thread tid''' [sAct tid2 N'; specAct] s2' N)) T) h' T'
|RBCongr : forall tid h h' T T' T'' T''', 
             congr T T' -> congr T'' T''' -> rollback tid h T' h' T'' ->
             rollback tid h T h' T'''
.

Inductive step : heap -> pool -> heap -> pool -> Prop :=
|Bind : forall t1 t2 h s1 s2 tid E T M,
           ctxt E -> M = E (bind (ret t1) t2) ->
           step h (par (thread tid s1 s2 M) T) h (par (thread (bump tid) s1 s2 (E (app t2 t1))) T)
|BindRaise : forall E M M' N tid s1 s2 T h,
               ctxt E -> M = E (bind (raise M') N) ->
               step h (par (thread tid s1 s2 M) T) h (par (thread (bump tid) s1 s2 (E (raise M'))) T)
|Fork : forall E M M' tid s1 s2 T h , 
          ctxt E -> M = E (fork M') -> 
          step h (par (thread tid s1 s2 M) T) h 
               (par (par (thread (bump tid) (fAct ((1,1)::tid) tid M :: s1) s2 (ret unit))
                         (thread ((1, 1)::tid) nil nil M')) T)
|Get : forall E M x h sc (ds : list tid) s t N h' T s1 s2 ds tid,
         ctxt E -> M = E (get x) -> heap_lookup x h = full sc ds s t N -> 
         h' = replace x (full sc (tid::ds) s t N) h->
         step h (par (thread tid s1 s2 M) T) h' 
              (par (thread (bump tid) (rAct x tid M :: s1) s2 (E(ret N))) T)
|Put : forall E M x N h sc h' s1 s2 tid T ,
         ctxt E -> M = E (put x N) -> heap_lookup x h = empty sc ->
         h' = replace x (full sc nil s1 tid N) h ->
         step h (par (thread tid s1 s2 M) T) h' 
              (par (thread (bump tid) (wAct x tid M::s1) s2 (E(ret unit))) T)
|Spec : forall E M M' N tid' tid s1 s2 T h,
          ctxt E -> M = E (spec M' N) -> tid' = (1, 1)::tid ->
          step h (par (thread tid s1 s2 M) T) h 
               (par (par (thread (bump tid) (fAct tid' tid M::s1) s2 (E(specReturn M' (threadId tid'))))
                         (thread tid' nil nil N)) T)
|PopSpec : forall h s1 s1' E s2 s2' tid tid' tid'' M N1 N2 T maj min min' N, 
             ctxt E -> N = E (specReturn (ret N1) (threadId ((maj, min) :: tid'))) -> 
             s1 = s1' ++ [sAct tid'' M] -> 
             step h (par (par (thread tid nil s2 N) (thread ((maj, min')::tid') s1 s2' (ret N2))) T) 
                  h (par (par (thread (bump tid) nil s2 N) (thread ((maj, S min') :: tid') (joinAct::s1')
                                      ((sAct tid'' M)::s2') (ret N2))) T)
|SpecJoin : forall E N h s2 s2' tid tid' N1 N2 maj min T,
              ctxt E -> N = E (specReturn (ret N1) (threadId ((maj, min)::tid'))) ->
              step h (par (par(thread tid nil s2 N) (thread tid' [joinAct] s2' (ret N2))) T)
                   h (par (thread (bump tid) nil s2 (ret (pair N1 N2))) T)
|SpecRB : forall E' N h h' tid tid' tid'' maj min min' min'' T T' E M' M''  s1 s2 s1' s2', 
            ctxt E' -> N = E' (specReturn (raise E) (threadId ((maj, min'')::tid'))) ->
            rollback ((maj, min)::tid') h (par (thread ((maj, min)::tid') s1' s2' M') T) 
                     h' (par (thread ((maj, min')::tid') [sAct tid'' M''] s2' M') T') ->
            step h (par (par (thread tid s1 s2 N) (thread ((maj, min)::tid') s1' s2' M')) T)
                 h' (par (thread (bump tid) s1 s2 (E' (raise E))) T')
|SpecRaise : forall E' N h tid tid' maj min min' s2 s2' T E N1,
               ctxt E' -> N = E'(specReturn (ret N1) (threadId ((maj, min)::tid'))) ->
               step h (par (par (thread tid nil s2 N)
                                (thread ((maj, min')::tid') [joinAct] s2' (raise E))) T)
                    h (par (thread (bump tid) nil s2 (E' (raise E))) T)
|New : forall E M h h' i tid s1 s2 T,
         ctxt E -> M = E new -> (i, h') = extend (empty s1) h ->
         step h (par (thread tid s1 s2 M) T) h' 
              (par (thread (bump tid) (cAct i tid new :: s1) s2 (E (ret (var i)))) T)
|Handle : forall h tid s1 s2 M N T c E,
            ctxt c -> M = c (handle (raise E) N) ->
            step h (par (thread tid s1 s2 M) T) h (par (thread (bump tid) s1 s2 (c (app N E))) T)
|PopRead : forall h tid tid' s1 s1' s2 M M' i ds t N,
             s1 = s1' ++ [rAct i tid' M'] -> heap_lookup i h = full nil ds nil t N ->
             step h (thread tid s1 s2 M) h (thread (bump tid) s1' ((rAct i tid' M')::s2) M)
|PopWrite : forall h tid tid' s1 s1' s2 M' M ds s N i,
              s1 = s1' ++ [wAct i tid' M'] -> heap_lookup i h = full nil ds s tid' N ->
              step h (thread tid s1 s2 M) (replace i (full nil nil nil tid' N) h)
                   (thread (bump tid) s1' ((wAct i tid' M') :: s2) M)
|PopNewFull : forall h h' s1 s1' s2 i tid tid' M' ds s s' t M N T, 
                s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = full s ds s' t N ->
                h' = replace i (full nil ds s' t N) h -> 
                step h (par (thread tid s1 s2 M) T) h'
                     (par (thread tid s1' ((cAct i tid' M')::s2) M) T)
|PopNewEmpty : forall h h' s1 s1' s2 i tid tid' M' s M T, 
                 s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = empty s ->
                 h' = replace i (empty nil) h ->
                 step h (par (thread tid s1 s2 M) T) h'
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
  |unSpecCThread : forall tid s2 M,
                    unspecT (thread tid nil s2 M) (thread tid nil s2 M)
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
|WF : forall h h' p p', unspecHeap h h' -> unspecT p p' -> multistep h' p' h p ->
                        wellFormed h p.

Inductive specActions : pool -> list (tid * specStack) -> Prop :=
  |sCompActions : forall T1 T2 a1 a2, specActions T1 a1 -> specActions T2 a2 ->
                                     specActions (par T1 T2) (a1 ++ a2)
  |sThreadActions : forall tid maj min s1 s2 M, 
                     specActions (thread ((maj,min)::tid) s1 s2 M) [((maj, 1)::tid, s1)]
  |sDotActions : specActions dot nil
.

Inductive commitActions : pool -> list (tid * specStack) -> Prop :=
  |nsCompActions : forall T1 T2 a1 a2, commitActions T1 a1 -> commitActions T2 a2 ->
                                       commitActions (par T1 T2) (a1 ++ a2)
  |nsThreadActions : forall tid maj min s1 s2 M, 
                       commitActions (thread ((maj, min)::tid) s1 s2 M) [((maj, 1)::tid, s2)]
  |nsDotActions : commitActions dot nil
.




