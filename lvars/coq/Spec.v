Require Export List.
Export ListNotations.
Require Import Coq.Program.Equality. 
Require Import Heap. 
Require Import AST. 
Require Import NonSpec.  


Inductive pool : Type :=
  |thread : tid -> list action -> list action -> term -> pool
  |dot : pool
  |par : pool -> pool -> pool.

Hint Constructors pool. 

Fixpoint bump (t : tid) : tid := 
  match t with
    |(maj, min) :: t' => (maj, S min) :: t'
    |nil => nil
  end.
 
Inductive congr : pool -> pool -> Prop :=
  |comm : forall t1 t2, congr (par t1 t2) (par t2 t1)
  |assoc : forall t1 t2 t3, congr (par (par t1 t2) t3) (par t1 (par t2 t3))
  |refl : forall t1, congr t1 t1
.

Hint Constructors congr. 

Definition sHeap := heap (ivar_state). 

Inductive ctxt : (term -> term) -> Prop :=
|bindCtxt : forall N c, ctxt c -> ctxt (fun M => bind (c M) N)
|specReturnCtxt : forall N c, ctxt c -> ctxt (fun M => specReturn M N)
|handleCtxt : forall N c, ctxt c -> ctxt (fun M => handle M N)
|hole : forall c, ctxt c -> ctxt (fun M => c M)
.
Hint Constructors ctxt. 

Inductive rollback : tid -> sHeap -> pool -> sHeap -> pool -> Prop :=
|RBDone : forall T t maj min h min' M' tid' M s2, 
            rollback ((maj, min)::t) h (par (thread ((maj, min') :: t) [sAct tid' M'] s2 M) T)
                     h (par (thread ((maj, min') :: t) [sAct tid' M'] s2 M) T)
|RBRead : forall s1 s1' s2 x tid tid' tid'' M M' N h h' h'' T T' sc t A S ds, 
            s1 = s1' ++ [rAct x tid'' M'] -> heap_lookup x h = Some (full sc (tid''::ds) (S::A) t N) ->
            h' = replace x (full sc ds (S::A) t N) h -> 
            rollback tid h' (par (thread tid'' s1' s2 M') T) h'' T'->
            rollback tid h (par(thread tid' s1 s2 M) T) h'' T'
|RBFork : forall s1 s1' s2 s2' tid tid' tid'' tid2 M M' N T T' h h',
            s1 = s1' ++ [fAct tid2 tid'' M'] -> 
            rollback tid h (par (thread tid'' s1' s2 M') T) h' T' ->
            rollback tid h (par (par (thread tid' s1 s2 M) (thread tid'' [specAct] s2' N)) T) h' T'
|RBWrite : forall s1 s1' s2 tid tid' tid'' M M' N S A sc T T' h h' h'' x,
             s1 = s1' ++ [wAct x tid'' M'] -> heap_lookup x h = Some(full sc nil (S::A) tid'' N) ->
             h' = replace x (empty sc) h -> 
             rollback tid h' (par (thread tid'' s1' s2 M') T) h'' T' ->
             rollback tid h (par (thread tid' s1 s2 M) T) h'' T'
|RBNew : forall s1 s1' s2 tid tid' tid'' M M' S A T T' h h' h'' x,
           s1 = s1' ++ [cAct x tid'' M'] -> heap_lookup x h = Some (empty (S::A)) ->
           h' = remove h x -> 
           rollback tid h' (par (thread tid'' s1' s2 M') T) h'' T' ->
           rollback tid h (par (thread tid' s1 s2 M) T) h'' T'
|RBSpec : forall s1 s1' s2 s2' tid tid2 tid' tid'' tid''' M M' N N' T T' h h',
            s1 = s1' ++ [fAct tid2 tid'' M'] -> 
            rollback tid h (par (thread tid'' s1' s2 M') T) h' T' ->
            rollback tid h (par (par (thread tid' s1 s2 M) 
                                             (thread tid''' [sAct tid2 N'; specAct] s2' N)) T) h' T'
(*
|RBComm : forall tid h h' T1 T2 T',
            rollback tid h (par T2 T1) h' T' ->
            rollback tid h (par T1 T2) h' T'
.*)
|RBCongr : forall tid h h' T T' T'' T''', 
             congr T T' -> congr T'' T''' -> rollback tid h T' h' T'' ->
             rollback tid h T h' T'''
.

Hint Constructors rollback. 
Inductive step : sHeap -> pool -> sHeap -> pool -> Prop :=
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
         ctxt E -> M = E (get x) -> heap_lookup x h = Some(full sc ds s t N) -> 
         h' = replace x (full sc (tid::ds) s t N) h->
         step h (par (thread tid s1 s2 M) T) h' 
              (par (thread (bump tid) (rAct x tid M :: s1) s2 (E(ret N))) T)
|Put : forall E M x N h sc h' s1 s2 tid T ,
         ctxt E -> M = E (put x N) -> heap_lookup x h = Some(empty sc) ->
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
|HandleRet : forall h tid s1 s2 M N T c M',
               ctxt c -> M = c(handle(ret M') N) ->
               step h (par (thread tid s1 s2 M) T) h 
                    (par (thread (bump tid) s1 s2 (c (ret M'))) T)
|PopRead : forall h tid tid' s1 s1' s2 M M' i ds t N,
             s1 = s1' ++ [rAct i tid' M'] -> heap_lookup i h = Some(full nil ds nil t N) ->
             step h (thread tid s1 s2 M) h (thread (bump tid) s1' ((rAct i tid' M')::s2) M)
|PopWrite : forall h tid tid' s1 s1' s2 M' M ds s N i,
              s1 = s1' ++ [wAct i tid' M'] -> heap_lookup i h = Some(full nil ds s tid' N) ->
              step h (thread tid s1 s2 M) (replace i (full nil nil nil tid' N) h)
                   (thread (bump tid) s1' ((wAct i tid' M') :: s2) M)
|PopNewFull : forall h h' s1 s1' s2 i tid tid' M' ds s s' t M N T, 
                s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = Some(full s ds s' t N) ->
                h' = replace i (full nil ds s' t N) h -> 
                step h (par (thread tid s1 s2 M) T) h'
                     (par (thread tid s1' ((cAct i tid' M')::s2) M) T)
|PopNewEmpty : forall h h' s1 s1' s2 i tid tid' M' s M T, 
                 s1 = s1' ++ [cAct i tid' M'] -> heap_lookup i h = Some(empty s) ->
                 h' = replace i (empty nil) h ->
                 step h (par (thread tid s1 s2 M) T) h'
                      (par (thread tid s1' ((cAct i tid' M')::s2) M) T)
|PopFork : forall h s1 s1' s1'' s1''' s2 s2' tid tid' tid1 tid2 M' M N T, 
             s1 = s1' ++ [fAct tid1 tid2 M'] -> s1'' = s1''' ++ [specAct] ->
             step h (par (par (thread tid s1 s2 M) (thread tid' s1'' s2' N)) T)
                  h (par (par (thread (bump tid) s1' ((fAct tid1 tid2 M')::s2) M) 
                              (thread (bump tid') s1''' (specAct :: s2') N)) T)
|Terminate : forall h tid s M T, step h (par (thread tid nil s (ret M)) T) h 
                                        (par dot T)
|CongrStep : forall t1 t1' t2 t2' h h', 
               step h t1' h' t2' -> congr t1 t1' -> congr t2 t2' ->
               step h t1 h' t2
.

Hint Constructors step. 

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

Inductive unspecHeap : sHeap -> sHeap -> Prop :=
  |unSpecSE : forall h h' i hd tl, unspecHeap h h' -> 
                                   unspecHeap ((i, empty (hd::tl)) :: h) h'
  |unSpecCE : forall h h' i, unspecHeap h h' -> 
                             unspecHeap ((i, empty nil) :: h) ((i, empty nil) :: h')
  |unspecSF : forall h h' i hd tl d s t N, 
                unspecHeap h h' -> 
                unspecHeap ((i, full (hd::tl) d s t N) :: h) h'
  |unspecCCSF : forall h h' i d hd tl t M, 
                  unspecHeap h h' ->
                  unspecHeap ((i, full nil d (hd::tl) t M)::h) ((i, empty nil)::h')
  |unspecCCCF : forall h h' i d t M, 
                  unspecHeap h h' ->
                  unspecHeap ((i, full nil d nil t M)::h) 
                             ((i, full nil d nil t M)::h')
.

Hint Constructors unspecHeap. 

Inductive unspecT : pool -> pool -> Prop :=
  |unSpecDot : unspecT dot dot
  |unSpecPar : forall t1 t1' t2 t2', 
                 unspecT t1 t1' -> unspecT t2 t2' -> unspecT (par t1 t2) (par t1' t2')
  |unSpecCThread : forall tid s2 M,
                    unspecT (thread tid nil s2 M) (thread tid nil s2 M)
  |unSpecRead : forall tid s1 s1' s2 M i M' maj min min',
                  s1 = s1' ++ [rAct i ((maj, min')::tid) M'] -> 
                  unspecT (thread ((maj, min)::tid) s1 s2 M) 
                          (thread ((maj, min')::tid) nil s2 M')
  |unSpecWrite : forall tid s1 s1' s2 M i M' maj min min',
                   s1 = s1' ++ [wAct i ((maj, min')::tid) M'] ->
                   unspecT (thread ((maj, min)::tid) s1 s2 M) 
                           (thread ((maj, min')::tid) nil s2 M')
  |unSpecCreate : forall tid s1 s1' s2 M i maj min min' M',
                  s1 = s1' ++ [cAct i ((maj, min')::tid) M'] ->
                  unspecT (thread ((maj, min)::tid) s1 s2 M) 
                          (thread ((maj, min')::tid) nil s2 M')
  |unSpecSpec : forall tid s1 s1' s2 M maj min min' M',
                  s1 = s1' ++ [sAct ((maj, min')::tid) M'] ->
                  unspecT (thread ((maj, min)::tid) s1 s2 M) 
                          (thread ((maj, min')::tid) [sAct ((maj, min')::tid) M'] s2 M')
  |unSpecFork : forall tid s1 s1' s2 M tid' M' maj min min',
                  s1 = s1' ++ [fAct tid' ((maj, min')::tid) M'] ->
                  unspecT (thread ((maj, min)::tid) s1 s2 M) 
                          (thread ((maj, min')::tid) nil s2 M').
Hint Constructors unspecT. 


Inductive unspec : sHeap -> pool -> sHeap -> pool -> Prop :=
  |Unspec : forall h h' p p', unspecHeap h h' -> unspecT p p' -> unspec h p h' p'.

Hint Constructors unspec. 

Inductive multistep : sHeap -> pool -> sHeap -> pool -> Prop :=
|reflStep : forall h p, multistep h p h p
|multiStep : forall h h' h'' p p' p'', step h p h' p' -> multistep h' p' h'' p'' ->
                               multistep h p h'' p''
.

Hint Constructors multistep. 

Inductive wellFormed : sHeap -> pool -> Prop :=
|WF : forall h h' p p', unspecHeap h h' -> unspecT p p' -> multistep h' p' h p ->
                        wellFormed h p.

Hint Constructors wellFormed. 

Inductive specActions : pool -> list (tid * specStack) -> Prop :=
  |sCompActions : forall T1 T2 a1 a2, specActions T1 a1 -> specActions T2 a2 ->
                                     specActions (par T1 T2) (a1 ++ a2)
  |sThreadActions : forall tid maj min s1 s2 M, 
                     specActions (thread ((maj,min)::tid) s1 s2 M) [((maj, 1)::tid, s1)]
  |sDotActions : specActions dot nil
.

Hint Constructors specActions. 

Inductive commitActions : pool -> list (tid * specStack) -> Prop :=
  |nsCompActions : forall T1 T2 a1 a2, commitActions T1 a1 -> commitActions T2 a2 ->
                                       commitActions (par T1 T2) (a1 ++ a2)
  |nsThreadActions : forall tid maj min s1 s2 M, 
                       commitActions (thread ((maj, min)::tid) s1 s2 M) [((maj, 1)::tid, s2)]
  |nsDotActions : commitActions dot nil
.
Hint Constructors commitActions. 


Inductive thread_lookup : pool -> tid -> option pool -> Prop :=
|hit : forall tid maj min min' s1 s2 M,
         thread_lookup (thread ((maj, min)::tid) s1 s2 M) ((maj, min')::tid) 
                       (Some (thread ((maj, min)::tid) s1 s2 M))
|miss : forall tid maj min tid' maj' min' s1 s2 M,
          tid <> tid' \/ maj <> maj' ->
          thread_lookup (thread ((maj, min)::tid) s1 s2 M) ((maj', min')::tid') 
                        None
|lookupPar : forall T1 T2 tid T, 
               thread_lookup T1 tid (Some T) -> thread_lookup (par T1 T2) tid (Some T)
|lookupPar2 : forall T1 T2 tid T,
                thread_lookup T1 tid None -> thread_lookup T2 tid T ->
                thread_lookup (par T1 T2) tid T
|lookupDot : forall tid, thread_lookup dot tid None
.

Hint Constructors thread_lookup. 

(*Erasure*)
Inductive appears_free_in : id -> term -> Prop :=
|afi_ivar : forall i j, i <> j -> appears_free_in i (ivar j)
|afi_unit : forall i, appears_free_in i unit
|afi_pair : forall i e1 e2, appears_free_in i e1 -> appears_free_in i e2 ->
                            appears_free_in i (pair e1 e2)
|afi_var : forall i j, i <> j -> appears_free_in i (var j)
|afi_lambda : forall i j e, i <> j -> appears_free_in i e -> 
                            appears_free_in i (lambda j e)
|afi_app : forall i e1 e2, appears_free_in i e1 -> appears_free_in i e2 ->
                           appears_free_in i (app e1 e2)
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
                                     eraseTerm (pair t1 t2) T (ppair t1' t2')
|eraseVar : forall i T, eraseTerm (var i) T (pvar i)
|eraseLambda : forall i e e' T, eraseTerm e T e' -> 
                                eraseTerm (lambda i e) T (plambda i e')
|eraseApp : forall e1 e1' e2 e2' T, eraseTerm e1 T e1' -> eraseTerm e2 T e2' ->
                                    eraseTerm (app e1 e2) T (papp e1' e2')
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
                     thread_lookup T tid (Some (thread tid' s1 s2 M)) ->
                     eraseTerm (specReturn e (threadId tid)) T
   (pbind e' (plambda i (pbind M'' (plambda j (pret (ppair (pvar i) (pvar j)))))))
                                   
.

Hint Constructors eraseTerm. 

Inductive eraseHeap : sHeap -> pHeap -> Prop :=
|eraseSE : forall h h' (i:id) hd tl,
             eraseHeap h h' -> eraseHeap ((i, empty (hd::tl)) :: h) h'
|eraseCE : forall h h' i ,
             eraseHeap h h' -> eraseHeap ((i, empty nil)::h) ((i, pempty)::h')
|eraseSF : forall h h' i hd tl d s t N,
             eraseHeap h h' -> eraseHeap ((i, full (hd::tl) d s t N)::h) h'
|eraseCCSF : forall h h' i d hd tl t M,
               eraseHeap h h' -> 
               eraseHeap ((i, full nil d (hd::tl) t M)::h) ((i, pempty)::h')
|eraseCCCF : forall h h' i d t M M',
               eraseHeap h h' -> eraseTerm M dot M' ->
               eraseHeap ((i, full nil d nil t M)::h) ((i, pfull M')::h')
.

Hint Constructors eraseHeap. 
Inductive erasePool : pool -> pool -> ppool -> Prop :=
|eraseDot : forall T, erasePool dot T pdot
|erasePar : forall T1 T2 T1' T2' T,
              erasePool T1 T T1' -> erasePool T2 T T2' ->
              erasePool (par T1 T2) T (ppar T1' T2')
|eraseCommitThread : forall tid s2 M M' T,
                       eraseTerm M T M' -> 
                       erasePool (thread tid nil s2 M) T (pthread M')
|eraseThreadSR : forall tid tid' M M' M'' x s1 s2 s1' T,
                   s1 = s1' ++ [rAct x tid' M'] -> eraseTerm M' T M'' ->
                   erasePool (thread tid s1 s2 M) T (pthread M'')
|eraseThreadSW : forall tid tid' M M' M'' x s1 s2 s1' T,
                   s1 = s1' ++ [wAct x tid' M'] -> eraseTerm M' T M'' ->
                   erasePool (thread tid s1 s2 M) T (pthread M'')
|eraseThreadSC : forall tid tid' M M' M'' x s1 s2 s1' T,
                   s1 = s1' ++ [cAct x tid' M'] -> eraseTerm M' T M'' ->
                   erasePool (thread tid s1 s2 M) T (pthread M'')
|eraseThreadSS : forall tid tid' M M' s1 s2 s1' T,
                   s1 = s1' ++ [sAct tid' M'] -> 
                   erasePool (thread tid s1 s2 M) T pdot
|eraseThreadSF : forall tid tid' tid'' M M' M'' s1 s2 s1' T,
                   s1 = s1' ++ [fAct tid' tid'' M'] -> eraseTerm M' T M'' ->
                   erasePool (thread tid s1 s2 M) T (pthread M'')
|eraseThreadJoin : forall tid M M' s1 s1' s2 T,
                     s1 = s1' ++ [joinAct] -> eraseTerm M T M' ->
                     erasePool (thread tid s1 s2 M) T (pthread M')
|eraseThreadSpec : forall tid M s1 s1' s2 T,
                     s1 = s1' ++ [specAct] -> 
                     erasePool (thread tid s1 s2 M) T (pdot)
.

Hint Constructors erasePool. 

Inductive Erase : sHeap -> pool -> pHeap -> ppool -> Prop :=
  |erase : forall h t h' t', erasePool t t t' -> eraseHeap h h' ->
                             Erase h t h' t'.

Hint Constructors Erase. 

Theorem eraseUnspecHeapIdem : 
  forall H H' H'', unspecHeap H H' -> eraseHeap H' H'' -> eraseHeap H H''. 
Proof. 
  intros.   
  {generalize dependent H''. 
   induction H0; intros; try(solve[eauto]). 
   {inversion H1; subst. apply IHunspecHeap in H4. constructor. assumption. }
   {inversion H1; subst. apply IHunspecHeap in H4. constructor. assumption. }
   {inversion H1; subst. apply IHunspecHeap in H7. constructor. assumption. 
    assumption. }
  }
Qed. 

Theorem Helper4 : 
  forall P P', unspecT P P' -> 
               forall tid, thread_lookup P' tid None ->
                           thread_lookup P tid None.
Proof.
  intros. induction H; try(solve[eauto]);
  try(inversion H0; subst; apply miss; assumption).  
  {constructor. inversion H0; subst. apply IHunspecT1 in H4. 
   assumption. inversion H0; subst. apply IHunspecT2 in H7. 
   assumption. }
Qed. 

Theorem Helper3 : 
  forall P P',
    unspecT P P' -> forall tid T',
    thread_lookup P' tid (Some T') -> 
    exists T,thread_lookup P tid (Some T). 
Proof. 
  intros P P' H. induction H; intros. 
  {inversion H. }
  {inversion H1; subst. apply IHunspecT1 in H5. inversion H5. 
   econstructor. constructor. eassumption. econstructor. 
   apply IHunspecT2 in H7. inversion H7. eapply lookupPar2. 
   eapply Helper4 in H. eassumption. assumption. eapply H2. 

Theorem Helper3 : 
  forall P P',
    unspecT P P' -> forall tid T T',
    thread_lookup P' tid (Some T') -> 
    thread_lookup P tid (Some T). 
Proof. 
  intros P P' H. induction H; intros. 
  {inversion H. }
  {inversion H1; subst. eapply IHunspecT1 in H5. constructor. 
   eassumption. eapply IHunspecT2 in H7. apply lookupPar2. 
   eapply Helper4 in H. eassumption. eassumption. eassumption. }
  {inversion H; subst. apply hit. 



Theorem eraseHelper : 
  forall M M' P P', unspecT P P' -> eraseTerm M P' M' -> eraseTerm M P M'.
Proof.
  intros. induction H0; try(solve[eauto]). 
  {econstructor. apply IHeraseTerm1 in H. assumption. 
   reflexivity. apply IHeraseTerm2 in H. eassumption. 
   assumption. subst. 
   eapply Helper3 with (tid := tid) 
                         (T := (thread tid' (s1' ++ [sAct tid'' M']) s2 M)) 
     in H. eassumption. eassumption. } 
Qed. 



Theorem eraseUnspecPoolIdem :
  forall T T' T'' P P', unspecT P P' -> unspecT T T' -> erasePool T' P' T'' ->
                        erasePool T P T''. 
Proof. 
  intros. generalize dependent P.  generalize dependent T''. 
  dependent induction H0; try(solve[eauto]). 
  {intros. inversion H1. constructor. }
  {intros. inversion H1; subst. eapply IHunspecT1 in H3. 
   eapply IHunspecT2 in H6. constructor; eassumption. assumption. assumption. }
  {intros. inversion H1; subst. constructor. 



Admitted. (*
  {intros. admit. (* inversion H0; subst; try(destruct s1'0; inversion H7). 
   econstructor. reflexivity. assumption.*) }
  {intros. inversion H0; subst; try(destruct s1'0; inversion H7). 
   eapply eraseThreadSW. reflexivity. assumption. }
  {intros. inversion H0; subst; try(destruct s1'0; inversion H7). 
   eapply eraseThreadSC. reflexivity. assumption. }
  {intros. inversion H0; subst; destruct s1'0; inversion H7
   ; try(destruct s1'0; inversion H2). subst. econstructor. 
   reflexivity. }
  {intros. inversion H0; subst; try(destruct s1'0; inversion H7). 
   eapply eraseThreadSF. reflexivity. assumption. }
Qed. *)

Theorem ErasureUSIdempotence : 
  forall H T H' T' H'' T'', unspec H T H' T' -> Erase H' T' H'' T'' ->
                            Erase H T H'' T''. 
Proof.
  intros. inversion H0; subst. inversion H1; subst. 
  constructor. eapply eraseUnspecPoolIdem in H3. 
  eassumption. eassumption. eapply eraseUnspecHeapIdem in H2. 
  eassumption. assumption. Qed. 
  