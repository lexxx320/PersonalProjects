Require Import AST. 
Require Import Heap.

Definition pHeap := heap pivar_state. 

Inductive ppool : Type :=
  |pthread : pterm -> ppool
  |pdot : ppool
  |ppar : ppool -> ppool -> ppool.

Inductive pctxt : (pterm -> pterm) -> Prop :=
|pBindCtxt : forall c N, pctxt c -> pctxt (fun M => pbind M N)
|pHandleCtxt : forall c N, pctxt c -> pctxt (fun M => phandle M N)
.

Print pterm. 
Inductive pstep : pHeap -> ppool -> pHeap -> ppool -> Prop :=
|PBind : forall E t M N h T,
              pctxt E -> t = E (pbind (pret M) N) ->
              pstep h (ppar (pthread t) T) h (ppar (pthread (E (papp N M))) T)
|PBindRaise : forall E t M N h T,
                   pctxt E -> t = E (pbind (praise M) N) ->
                   pstep h (ppar (pthread t) T) h (ppar (pthread (E(praise M))) T)
|PHandle : forall E t M N h T,
             pctxt E -> t = E(phandle (praise M) N) ->
             pstep h (ppar (pthread t) T) h (ppar (pthread (E (papp N M))) T)
|PHandleRet : forall E t M N h T,
                pctxt E -> t = E(phandle (pret M) N) ->
                pstep h (ppar (pthread t) T) h (ppar (pthread (E (pret M))) T)
|PFork : forall E t M T h,
              pctxt E -> t = E (pfork M) ->
              pstep h (ppar (pthread t) T) h (ppar (ppar (pthread (E (pret punit)))
                                                         (pthread M)) T)
|PGet : forall E M t h T x,
             pctxt E -> t = E(pget x) -> heap_lookup x h = Some(pfull M) ->
             pstep h (ppar (pthread t) T) h (ppar (pthread (E (pret M))) T)
|PPut : forall E t M h h' T x,
             pctxt E -> t = E(pput x M) -> heap_lookup x h = Some pempty ->
             h' = replace x (pfull M) h ->
             pstep h (ppar (pthread t ) T) h' (ppar (pthread (E (pret punit))) T)
|PNew : forall E t h h' T x,
             pctxt E -> t = E pnew -> (x, h') = extend pempty h ->
             pstep h (ppar (pthread t) T) h' (ppar (pthread (E(pret (pvar x)))) T)
|PTerminate : forall h T M,
                pstep h (ppar (pthread (pret M)) T) h (ppar pdot T)
.





