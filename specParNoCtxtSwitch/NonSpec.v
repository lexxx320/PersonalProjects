Require Import AST. 
Require Import Heap.
Require Import Coq.Sets.Ensembles. 

Definition pHeap := heap pivar_state. 

Definition pctxt := pterm -> pterm.

Inductive pvalue : pterm -> Prop :=
|pretValue : forall M, pvalue (pret M)
|praiseValue : forall M, pvalue (praise M)
|pgetValue : forall i, pvalue (pget i)
|pputValue : forall i M, pvalue (pput i M)
|pdoneValue : forall M, pvalue (pdone M)
|pnewValue : pvalue pnew
.
 
Inductive pdecompose : pterm -> pctxt -> pterm -> Prop :=
|bindCtxt : forall E M N M', ~pvalue M -> pdecompose M E M' ->
                           pdecompose (pbind M N) (fun x => pbind (E x) N) M'
|bindCtxtValue : forall M N, pvalue M -> pdecompose (pbind M N) (fun x => x) (pbind M N)
|handleCtxt : forall M M' N E,
                ~pvalue M -> pdecompose M E M' ->
                pdecompose (phandle M N) (fun x => phandle (E x) N) M'
|handleCtxtValue : forall M N, pvalue M -> pdecompose (phandle M N) (fun x=>x) 
                                                    (phandle M N)
.
Definition pPool := Ensemble pterm. 
Definition pSingleton := Singleton pterm. 
Definition pUnion := Union pterm. 

Inductive pstep : pHeap -> pPool -> pPool -> pHeap -> pPool -> pPool -> Prop :=
|PBind : forall E t M N h T, 
           pdecompose t E (pbind (pret M) N) -> 
           pstep h T (pSingleton t) h T (pSingleton(E(papp N M)))
|PBindRaise : forall E t M N h T,
                pdecompose t E (pbind (praise M) N) -> 
                pstep h T (pSingleton t) h T (pSingleton (E(praise M)))
|pHandle : forall E t M N h T,
             pdecompose t E (phandle (praise M) N) -> 
             pstep h T (pSingleton t) h T (pSingleton (E(papp N M)))
|pHandleRet : forall E t M N h T,
                pdecompose t E (phandle (pret M) N) -> 
                pstep h T (pSingleton t) h T (pSingleton (E(pret M)))
|pFork : forall E t M h T,
           pdecompose t E (pfork M) -> 
           pstep h T (pSingleton t) h (Add pterm T M) (pSingleton (E(pret punit)))
|PGet : forall E M t h T x,
          heap_lookup x h = Some(pfull M) -> pdecompose t E (pget x) -> 
          pstep h T (pSingleton t) h T (pSingleton (E(pret M)))
|PPut : forall E t M h h' T x,
          pdecompose t E (pput x M) -> heap_lookup x h = Some pempty ->
          h' = replace x (pfull M) h ->
          pstep h T (pSingleton t) (replace x (pfull M) h) T (pSingleton (E (pret punit)))
|PNew : forall E t h h' T x,
             pdecompose t E pnew -> (x, h') = extend pempty h ->
             pstep h T (pSingleton t) h' T (pSingleton (E (pret (pvar x))))
|PTerminate : forall h T M, pstep h T (pSingleton (pret M)) h T (Empty_set pterm)
                
.

Inductive pmultistep : pHeap -> pPool -> pPool -> pHeap -> pPool -> pPool -> Prop :=
|multi_refl : forall h p1 p2, pmultistep h p1 p2 h p1 p2
|multi_step : forall T1 T2 T2' h h' h'' t t',
                ~ In pterm T2 t -> pstep h (pUnion T1 T2) (pSingleton t) h' (pUnion T1 T2) t' ->
                pmultistep h' T1 (pUnion T2 t') h'' T1 T2' ->
                pmultistep h T1 (Add pterm T2 t) h'' T1 T2'
.












