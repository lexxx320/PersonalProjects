Require Import Spec. 
Require Import NonSpec. 

Print unspecHeap. 

Inductive eraseTerm : term -> pterm -> Prop :=
.

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
               eraseHeap h h' -> eraseTerm M M' ->
               eraseHeap ((i, full nil d nil t M)::h) ((i, pfull M')::h')
.

Print pool. 

Print action. 

Inductive erasePool : pool -> ppool -> Prop :=
|erasePar : forall T1 T2 T1' T2',
              erasePool T1 T1' -> erasePool T2 T2' ->
              erasePool (par T1 T2) (ppar T1' T2')
|eraseCommitThread : forall tid s2 M M',
                       eraseTerm M M' -> erasePool (thread tid nil s2 M) (pthread M')
|eraseThreadSR : forall tid tid' M M' M'' x s1 s2 s1',
                   s1 = s1' ++ [rAct x tid' M'] -> eraseTerm M' M'' ->
                   erasePool (thread tid s1 s2 M) (pthread M'')
|eraseThreadSW : forall tid tid' M M' M'' x s1 s2 s1',
                   s1 = s1' ++ [wAct x tid' M'] -> eraseTerm M' M'' ->
                   erasePool (thread tid s1 s2 M) (pthread M'')
|eraseThreadSC : forall tid tid' M M' M'' x s1 s2 s1',
                   s1 = s1' ++ [cAct x tid' M'] -> eraseTerm M' M'' ->
                   erasePool (thread tid s1 s2 M) (pthread M'')
|eraseThreadSS : forall tid tid' M M' M'' s1 s2 s1',
                   s1 = s1' ++ [sAct tid' M'] -> eraseTerm M' M'' ->
                   erasePool (thread tid s1 s2 M) (pthread M'')
.




