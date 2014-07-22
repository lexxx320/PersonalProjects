Require Import AST.    
Require Import NonSpec.   
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import SfLib. 
Require Import Heap. 
Require Import sets. 
Require Import hetList.
Require Import SpecLib.  
Require Import unspec. 
Require Import classifiedStep. 

Fixpoint eraseTerm (t:trm) : ptrm :=
  match t with
    |fvar i => pfvar i
    |bvar i => pbvar i
    |unit => punit
    |pair_ e1 e2 => ppair (eraseTerm e1) (eraseTerm e2)
    |lambda e => plambda (eraseTerm e)
    |AST.app e1 e2 => papp (eraseTerm e1) (eraseTerm e2)
    |ret e => pret (eraseTerm e)
    |bind e1 e2 => pbind (eraseTerm e1) (eraseTerm e2)
    |fork e => pfork (eraseTerm e)
    |new => pnew
    |put i e => pput (eraseTerm i) (eraseTerm e)
    |get i => pget (eraseTerm i)
    |raise e => praise (eraseTerm e)
    |handle e1 e2 => phandle (eraseTerm e1) (eraseTerm e2)
    |fst e => pfst (eraseTerm e)
    |snd e => psnd (eraseTerm e)
    |spec e1 e2 => pspec (eraseTerm e1) (eraseTerm e2)
    |specRun e1 e2 => pspecRun (eraseTerm e1) (eraseTerm e2)
    |specJoin e1 e2 => pspecJoin (eraseTerm e1) (eraseTerm e2)
  end. 

Fixpoint raw_eraseHeap (h:rawHeap ivar_state) : rawHeap pivar_state :=
   match h with
     | nil => []
     | (i, sempty a) :: H' =>
       if commit a
       then (i, pempty) :: raw_eraseHeap H'
       else raw_eraseHeap H'
     | (i, sfull a1 _ a3 a4 a5) :: H' =>
       if commit a1
       then
         if commit a3
         then (i, pfull (eraseTerm a5)) :: raw_eraseHeap H'
         else (i, pempty) :: raw_eraseHeap H'
       else raw_eraseHeap H'
  end.

Theorem eraseUnique : forall H S,
                        unique ivar_state S H ->
                        unique pivar_state S (raw_eraseHeap H). 
Proof.
  induction H; intros. 
  {simpl. constructor. }
  {simpl. destruct a. 
   {destruct i0. 
    {destruct (commit a). 
     {inv H0. constructor. auto. eauto. }
     {inv H0. eapply IHlist. eapply uniqueSubset; eauto. unfold Included. 
      intros. constructor; auto. }
    }
    {destruct (commit a). 
     {destruct (commit a0). 
      {inv H0. auto. }
      {inv H0. constructor. auto. auto. }
     }
     {inv H0. eapply IHlist. eapply uniqueSubset; eauto. unfold Included. intros. 
      constructor. auto.  }
    }
   }
  }
Qed. 

Definition eraseHeap H := 
  match H with
      heap_ h' prf => heap_ pivar_state (raw_eraseHeap h')
                            (eraseUnique h' (Empty_set AST.id) prf)
  end. 

Inductive eraseThread : thread -> pPool -> Prop :=
|tEraseCommit : forall tid s2 M, eraseThread (tid, unlocked nil, s2, M) (pSingleton  (eraseTerm M))
|tEraseRead : forall tid s1 s1' s2 x M M' E (d:decompose M' E (get (fvar x))),
               s1 = unlocked (s1' ++ [rAct x M' E d]) -> 
               eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseWrite : forall tid M M' x s1 s2 s1' E N (d:decompose M' E (put (fvar x) N)),
                s1 = unlocked(s1' ++ [wAct x M' E N d]) ->
                eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseNew : forall tid M M' x s1 s2 s1' E (d:decompose M' E new),
              s1 = unlocked(s1' ++ [nAct M' E d x]) -> 
              eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseFork : forall tid M M' s1 s2 s1' E N (d:decompose M' E (fork N)),
                s1 = unlocked(s1' ++ [fAct M' E N d]) -> 
                eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseSpecRet : forall tid M M' s1 s2 s1' E N N' (d:decompose M' E (spec N N')),
                s1 = unlocked(s1' ++ [srAct M' E N N' d]) -> 
                eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseLocked : forall tid M s1 s2,
                       eraseThread (tid, locked s1, s2, M) (Empty_set ptrm)
|tEraseSpecStack : forall tid M s1 s2 N,
                     eraseThread(tid,specStack s1 N,s2,M) (Empty_set ptrm)
.

Hint Constructors eraseThread. 

Inductive erasePoolAux (T:pool) : pPool :=
|eraseAux : forall t t' s1 s2 M, 
              thread_lookup T t (t, s1, s2, M) -> 
              eraseThread (t, s1, s2, M) t' ->
              Included ptrm t' (erasePoolAux T). 

Hint Constructors erasePoolAux. 

Inductive erasePool : pool -> pPool -> Prop :=
|eraseP : forall T, erasePool T (erasePoolAux T).

Hint Constructors erasePool. 

Fixpoint eraseCtxt (c:ctxt) : pctxt :=
  match c with
    |appCtxt E N => pappCtxt (eraseCtxt E) (eraseTerm N)
    |appValCtxt E N => pappValCtxt (eraseCtxt E) (eraseTerm N)
    |pairCtxt E N => ppairCtxt (eraseCtxt E) (eraseTerm N)
    |pairValCtxt E N => ppairValCtxt (eraseCtxt E) (eraseTerm N)
    |bindCtxt E N => pbindCtxt (eraseCtxt E) (eraseTerm N)
    |specRunCtxt E N => pspecRunCtxt (eraseCtxt E) (eraseTerm N)
    |specJoinCtxt E N => pspecJoinCtxt (eraseCtxt E) (eraseTerm N)
    |handleCtxt E N => phandleCtxt (eraseCtxt E) (eraseTerm N)
    |fstCtxt E => pfstCtxt (eraseCtxt E)
    |sndCtxt E => psndCtxt (eraseCtxt E)
    |holeCtxt => pholeCtxt
  end. 

Ltac eraseThreadTac :=
  match goal with
      | |- eraseThread (?tid, unlocked[rAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseRead
      | |- eraseThread (?tid, unlocked[wAct ?a ?b ?c ?d ?e], ?s2, ?N) ?m => eapply tEraseWrite
      | |- eraseThread (?tid, unlocked[nAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseNew
      | |- eraseThread (?tid, unlocked[fAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseFork
      | |- eraseThread (?tid, unlocked[srAct ?a ?b ?c ?d ?e], ?s2, ?N) ?m => eapply tEraseSpecRet
      | |- eraseThread (?tid, locked ?x, ?s2, ?N) ?m => eapply tEraseLocked
      | |- eraseThread (?tid, unlocked(?z++[rAct ?a ?b ?c ?d]), ?s2, ?N) ?m => eapply tEraseRead
      | |- eraseThread (?tid, unlocked(?z++[wAct ?a ?b ?c ?d ?e]), ?s2, ?N) ?m => eapply tEraseWrite
      | |- eraseThread (?tid, unlocked(?z++[nAct ?a ?b ?c ?d]), ?s2, ?N) ?m => eapply tEraseNew
      | |- eraseThread (?tid, unlocked(?z++[fAct ?a ?b ?c ?d]), ?s2, ?N) ?m => eapply tEraseFork
      | |- eraseThread (?tid, unlocked(?z++[srAct ?a ?b ?c ?d ?e]), ?s2, ?N) ?m => eapply tEraseSpecRet
  end. 

(*------------------------------------Theorems------------------------------------*)

Theorem eraseThreadTotal : forall t, exists p, eraseThread t p. 
Proof.
  intros. destruct t. destruct p. destruct p. destruct a. 
  eauto. destructLast l0. eauto. invertHyp. destruct x; econstructor; simpl in *; eraseThreadTac; auto.
  eauto. 
Qed. 

Axiom erasePoolEraseThread : forall T T' t, erasePool T T' -> tIn T t -> 
                                              exists t', eraseThread t t'. 

Theorem raw_eraseUnspecHeapIdem : forall H, raw_eraseHeap (raw_unspecHeap H) = raw_eraseHeap H. 
Proof.
  induction H; intros. 
  {auto. }
  {simpl in *. destruct a. destruct i0. 
   {simpl. destruct (commit a)eqn:eq. simpl. rewrite eq. rewrite IHlist. auto. eauto. }
   {destruct (commit a)eqn:eq1; auto. destruct (commit a0)eqn:eq2; auto. simpl. rewrite eq1. 
    rewrite eq2. rewrite IHlist; auto. simpl. rewrite eq1. rewrite IHlist. auto. }
  }
Qed. 

(*Erasure is idempotent with respect to unspeculate*)
Theorem eraseUnspecHeapIdem : forall H, eraseHeap (unspecHeap H) = eraseHeap H. 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. apply raw_eraseUnspecHeapIdem. 
Qed. 

Hint Unfold Included. 

Ltac decompErase :=
  match goal with
      |H:decompose ?t ?E ?e |- _ => apply decomposeEq in H; subst; auto
  end. 

Theorem eraseUnspecPoolAuxEq : forall T, erasePoolAux (unspecPoolAux T) = 
                                         erasePoolAux T. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. cleanup. 
   match goal with
       |H:thread_lookup (unspecPoolAux ?T) ?TID ?t |- _ =>
        assert(US:unspecPool T (unspecPoolAux T)) by constructor;
          eapply LookupSame with(tid:=TID) in US; inversion US as [EX1 EX2];
          inversion EX2; clear EX2
   end. Focus 2. eassumption. destruct EX1. destruct p. destruct p. 
   inv H4. inv H7. econstructor; eauto. inv H5; try(apply SingletonEq in H11; inv H11). 
   {assumption. }
   {inversion H1; subst; try invertListNeq. 
    {eapply tEraseRead. auto. }
   }
   {inversion H1; subst; try invertListNeq. eapply tEraseWrite; eauto. }
   {inversion H1; subst; try invertListNeq. eapply tEraseNew; eauto. }
   {inversion H1; subst; try invertListNeq. eapply tEraseFork; eauto. }
   {inversion H1; subst; try invertListNeq. eapply tEraseSpecRet; eauto. }
   {symmetry in H11. apply SingletonNeqEmpty in H11. inv H11. }
   {inv H1; subst; try solveByInv. }
  }
  {inversion H; subst. inversion H0; subst. cleanup. inversion H1; subst. 
   {econstructor; eauto. econstructor; eauto. econstructor; eauto. constructor. }
   {econstructor. econstructor. econstructor. eauto. econstructor; eauto. constructor. 
    auto. eauto. auto. }
   {econstructor. econstructor. econstructor. eauto. eapply unspecWrite; eauto. constructor. 
    auto. auto. auto. }
   {econstructor. econstructor. econstructor. eauto. eapply unspecCreate; eauto. constructor. 
    auto. auto. auto. }
   {econstructor. econstructor. econstructor. eauto. eapply unspecFork; eauto. constructor. 
    auto. auto. auto. }
   {econstructor. econstructor. econstructor. eauto. eapply unspecSpecret; eauto. constructor. 
    auto. auto. auto. }
   {inv H2. }
   {inv H2. }
  }
Qed. 


Theorem eraseUnspecPoolIdem : forall T T' T'',
                                unspecPool T T' -> erasePool T' T'' ->
                                erasePool T T''. 
Proof.
  intros. inversion H. inversion H0; subst. rewrite eraseUnspecPoolAuxEq. 
  constructor. Qed. 

Ltac applyHyp :=
  match goal with
      |H : forall a : _, ?X -> ?Y, H' : ?Z |- _ => apply H in H'
  end. 

Theorem eraseFill : forall E e, 
                           eraseTerm (fill E e) = (pfill (eraseCtxt E) (eraseTerm e)). 
Proof.
  induction E; intros; try solve[simpl; rewrite IHE; auto]; auto. 
Qed. 

Theorem inErasure : forall T T' t, erasePoolAux T = T' -> Ensembles.In ptrm T' t ->
                                   Ensembles.In ptrm (erasePoolAux T) t. 
Proof.
  intros. subst. inv H0.  econstructor. eauto. eauto. auto. Qed. 

Hint Constructors thread_lookup erasePoolAux Singleton eraseThread. 

Theorem eraseThreadDeterminsim : forall t t' t'', eraseThread t t' -> eraseThread t t'' -> t' = t''. 
Proof.
intros. inv H; inv H0; auto; try solve[invertListNeq]; inv H5;
  match goal with
               |H:[] = [] ++ [?x] |- _ => inversion H       
               |H:[] = ?x ++ [?y] |- _ => destruct x; inversion H
               |H:?s1++[?x]=?s2++[?y]|-_ => apply lastElementEq in H; inversion H
  end; subst; auto. 
Qed. 

Theorem erasePoolSingleton : forall t pt, eraseThread t pt -> erasePoolAux(tSingleton t) = pt. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inv H0. inv H1. inv H4. inv H0. eapply eraseThreadDeterminsim in H2; eauto. subst. auto. }
  {destruct t. destruct p. destruct p. econstructor. econstructor. constructor. 
   auto. eauto. auto. }
Qed. 

Hint Constructors pval val. 

Theorem eraseVal : forall e, val e <-> pval (eraseTerm e). 
Proof.
  induction e; intros; try solve[split; intros; simpl in *; subst; inversion H]. 
  {split; intros. simpl in *; subst. inversion H; subst. constructor. apply IHe1; auto. 
   apply IHe2; auto. simpl in *. subst. inversion H; subst. constructor; auto.
   rewrite IHe1. auto. rewrite IHe2. auto. }
  {split; intros. simpl in *; subst; auto. constructor. }
  {split; intros; simpl in *; subst; auto. }
  {split; intros; simpl in *; subst; auto. }
Qed. 

Theorem eraseNotVal : forall e, ~val e <-> ~pval (eraseTerm e). 
Proof.
  intros. induction e; try solve[split; intros; subst; introsInv]. 
  {split; intros; simpl in *; subst. introsInv. apply H.
   {constructor. rewrite eraseVal. auto. subst. rewrite eraseVal; auto. }
   {introsInv; subst. apply H. constructor; rewrite <- eraseVal; auto. }
  }
  {split; intros; simpl in *; subst. exfalso. apply H. constructor. exfalso. apply H; auto. }
  {split; intros; simpl in *; subst; exfalso; apply H; auto. }
  {split; intros; simpl in *; subst; exfalso; apply H; auto. }
Qed.  

Theorem eraseCtxtWF : forall E e, ctxtWF e E <-> pctxtWF (eraseTerm e) (eraseCtxt E). 
Proof.
  induction E; intros. 
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseFill; rewrite <- eraseNotVal; auto. }
   {inversion H; subst. constructor. simpl in *. apply IHE; auto. rewrite eraseNotVal. 
    rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseVal; auto. 
   rewrite <- eraseFill. rewrite <- eraseNotVal. auto. }
   {simpl in H. inversion H; subst. constructor. apply IHE. auto. rewrite eraseVal. auto. 
    rewrite eraseNotVal. rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseFill; rewrite <- eraseNotVal; auto. }
   {inversion H; subst. constructor. simpl in *. apply IHE; auto. rewrite eraseNotVal. 
    rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseVal; auto. 
   rewrite <- eraseFill. rewrite <- eraseNotVal. auto. }
   {simpl in H. inversion H; subst. constructor. apply IHE. auto. rewrite eraseVal. auto. 
    rewrite eraseNotVal. rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseFill; rewrite <- eraseNotVal; auto. }
   {inversion H; subst. constructor. simpl in *. apply IHE; auto. rewrite eraseNotVal. 
    rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseFill; rewrite <- eraseNotVal; auto. }
   {inversion H; subst. constructor. simpl in *. apply IHE; auto. rewrite eraseNotVal. 
    rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseVal; auto. 
   rewrite <- eraseFill. rewrite <- eraseNotVal. auto. }
   {simpl in H. inversion H; subst. constructor. apply IHE. auto. rewrite eraseVal. auto. 
    rewrite eraseNotVal. rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseFill; rewrite <- eraseNotVal; auto. }
   {inversion H; subst. constructor. simpl in *. apply IHE; auto. rewrite eraseNotVal. 
    rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseFill; rewrite <- eraseNotVal; auto. }
   {inversion H; subst. constructor. simpl in *. apply IHE; auto. rewrite eraseNotVal. 
    rewrite eraseFill. auto. }
  }
  {split; intros; simpl. 
   {inversion H; subst. constructor. apply IHE; auto. rewrite <- eraseFill; rewrite <- eraseNotVal; auto. }
   {inversion H; subst. constructor. simpl in *. apply IHE; auto. rewrite eraseNotVal. 
    rewrite eraseFill. auto. }
  }
  {split; intros; simpl; auto. }
Qed. 


Theorem eTerm : forall t', exists t, eraseTerm t = t'. 
Proof.
  induction t'; try invertHyp.
  {exists (fvar i). auto. }
  {exists (bvar i). auto. }
  {exists unit. auto. }
  {exists (pair_ x0 x). auto. }
  {exists (lambda x); auto. }
  {exists (AST.app x0 x); auto. }
  {exists (ret x); auto. }
  {exists (bind x0 x); auto. }
  {exists (fork x); auto. }
  {exists new; auto. }
  {exists (put x0 x); auto. }
  {exists (get x); auto. }
  {exists (raise x); auto. }
  {exists (handle x0 x); auto. }
  {exists (fst x); auto. }
  {exists (snd x); auto. }
  {exists (spec x0 x); auto. }
  {exists (specRun x0 x); auto. }
  {exists (specJoin x0 x); auto. }
Qed. 

Theorem eCtxt : forall E', exists E, eraseCtxt E = E'. 
Proof.
  induction E'; try invertHyp. 
  {assert(exists p', eraseTerm p' = p). apply eTerm. invertHyp. 
   exists (bindCtxt x x0); auto. }
  {assert(exists p', eraseTerm p' = p). apply eTerm. invertHyp. 
   exists (handleCtxt x x0); auto. }
  {assert(exists p', eraseTerm p' = p). apply eTerm. invertHyp. 
   exists (appCtxt x x0); auto. }
  {assert(exists p', eraseTerm p' = p). apply eTerm. invertHyp. 
   exists (appValCtxt x x0); auto. }
  {assert(exists p', eraseTerm p' = p). apply eTerm. invertHyp. 
   exists (pairCtxt x x0); auto. }
  {assert(exists p', eraseTerm p' = p). apply eTerm. invertHyp. 
   exists (pairValCtxt x x0); auto. }
  {exists (fstCtxt x). auto. }
  {exists (sndCtxt x); auto. }
  {assert(exists p', eraseTerm p' = p). apply eTerm. invertHyp. 
   exists (specRunCtxt x x0); auto. }
  {assert(exists p', eraseTerm p' = p). apply eTerm. invertHyp. 
   exists (specJoinCtxt x x0); auto. }
  {exists holeCtxt. auto. }
Qed. 
  
Theorem eThread : forall t', exists t, eraseThread t (pSingleton t').
Proof.
  induction t'; 
  match goal with
      | |- exists t, eraseThread t (pSingleton ?M) => 
        assert(E:exists M', eraseTerm M' = M) by apply eTerm; inversion E as [Ex1 Ex2];
        rewrite <- Ex2; exists (nil,unlocked nil,nil,Ex1); auto
  end. 
Qed. 


Theorem eraseUnionComm : forall T1 T2, erasePoolAux (tUnion T1 T2) = 
                                       Union ptrm (erasePoolAux T1) (erasePoolAux T2).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inv H. inv H0. inv H3. inv H. 
   {econstructor. econstructor. econstructor. eauto. eauto. eauto. auto. }
   {apply Union_intror. econstructor. econstructor; eauto. eauto. auto. }
  }
  {inv H. 
   {inv H0. inv H. inv H3. econstructor. econstructor. econstructor. eauto. auto. eauto. auto. }
   {inv H0. inv H. inv H3. econstructor. econstructor. apply Union_intror. eauto. 
    eauto. eauto. auto. }
  }
Qed.


Theorem eraseTermUnique : forall M M', eraseTerm M = eraseTerm M' -> M = M'. 
Proof.
  induction M; intros; try solve[destruct M'; inversion H; auto]; try solve[ 
  destruct M'; inv H; erewrite IHM1; eauto; erewrite IHM2; eauto]; try solve[ 
  destruct M'; inv H; erewrite IHM; eauto]. 
Qed. 

Hint Constructors decompose. 

Theorem decomposeErase : forall M E e M' E' e',
                            eraseTerm M = M' -> eraseCtxt E = E' -> eraseTerm e = e' ->
                            (pdecompose M' E' e' <-> decompose M E e). 
Proof. 
  intros. split; intros. 
  {genDeps{E; e; M'; E'; e'; M}. 
   induction M; intros; subst; try solve[simpl in H2; inversion H2]; try solve[
   simpl in H2; inv H2; try solve[repeat match goal with
        |H:?x = eraseCtxt ?E |- _ => destruct E; inv H
        |H:eraseTerm ?M = eraseTerm ?M' |- _ => apply eraseTermUnique in H; subst
        |H:?x = eraseTerm ?M |- _ => destruct M; inv H
        | |- val ?t => apply eraseVal; eauto
        | |- ~val ?t => apply eraseNotVal; eauto
        |_ => constructor
    end; eauto]]. }
  {genDeps{E; e; M'; E'; e'; M}. induction M; intros; try solve[inversion H2]; try solve[ 
   inv H2; simpl in *; repeat (match goal with
      |H:?x = eraseCtxt ?E |- _ => destruct E; inv H
      |H:eraseTerm ?M = eraseTerm ?M' |- _ => apply eraseTermUnique in H; subst
      | |- pval ?t => apply eraseVal; eauto
      | |- ~pval ?t => apply eraseNotVal; eauto
      |_ => constructor
   end); eauto]. }
Qed. 

Hint Resolve app_nil_l. 

Theorem eraseLastAct : forall A s2 M M' t tid,
                         actionTerm A M' ->
                         (eraseThread (tid, unlocked[A], s2, M) t <->
                          eraseThread (tid, unlocked nil, s2, M') t). 
Proof.
  intros. split; intros. 
  {inv H0; try solve[destruct s1'; simpl in *; inv H6;[inv H;auto; inv H6|invertListNeq]]. }
  {inv H0; try invertListNeq. inv H; auto; try solve[eraseThreadTac; rewrite app_nil_l; eauto].  }
Qed. 

Theorem eraseTwoActs : forall tid tid' A1 A2 As s2 M M' t,
                         eraseThread (tid, aCons A1 (aCons A2 As), s2, M') t <->
                         eraseThread (tid', (aCons A2 As), s2, M) t. 
Proof.
  intros. split; intros. 
  {inv H; destruct As; simpl in *; try invertListNeq; try solveByInv.
   {inv H5. apply listAlign in H0. invertHyp. rewrite H. eauto. }
   {inv H5. apply listAlign in H0. invertHyp. rewrite H. eauto. }
   {inv H5. apply listAlign in H0. invertHyp. rewrite H. eauto. }
   {inv H5. apply listAlign in H0. invertHyp. rewrite H. eauto. }
   {inv H5. apply listAlign in H0. invertHyp. rewrite H. eauto. }
   {auto. }
   {inv H2. auto. }
  }
  {inv H; destruct As; simpl in *; try invertListNeq; try(inv H5; rewrite H0;
   rewrite app_comm_cons; eauto); try solveByInv; eauto. }
Qed. 

Theorem eraseOpenComm : forall e e' n, eraseTerm (open n e e') = popen n (eraseTerm e) (eraseTerm e'). 
Proof.
  induction e'; auto; try solve[intros; simpl; rewrite IHe'1; rewrite IHe'2; auto]; 
  try solve[intros; simpl; rewrite IHe'; auto].
  {intros. simpl. destruct (beq_nat n i); auto. }
Qed. 

Theorem eraseSpecSame : forall tid tid' y x a s2 s2' t t' t'',
                          eraseThread (tid, unlocked(x++[a]), s2, t) t' ->
                          eraseThread (tid', unlocked(y++[a]), s2', t'') t'. 
Proof.
  intros. inv H. invertListNeq.
  {inv H5. apply lastElementEq in H0. subst. eauto. }
  {inv H5. apply lastElementEq in H0. subst. eauto. }
  {inv H5. apply lastElementEq in H0. subst. eauto. }
  {inv H5. apply lastElementEq in H0. subst. eauto. }
  {inv H5. apply lastElementEq in H0. subst. eauto. }
Qed. 

Theorem raw_eraseHeapDependentRead : forall H x sc ds s w N ds',
                                       raw_heap_lookup x H = Some(sfull sc ds s w N) ->
                                       raw_eraseHeap(raw_replace x (sfull sc ds' s w N) H) = raw_eraseHeap H. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. destruct (commit sc) eqn:eq1; auto. destruct (commit s)eqn:eq2. simpl. 
    apply beq_nat_true in eq. subst; auto. rewrite eq1. rewrite eq2. auto. simpl. rewrite eq1.  
    rewrite eq2. apply beq_nat_true in eq. subst; auto. simpl. rewrite eq1. auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed. 

Theorem eraseHeapDependentRead : forall H x sc ds s w N ds',
                                       heap_lookup x H = Some(sfull sc ds s w N) ->
                                       eraseHeap(replace x (sfull sc ds' s w N) H) = eraseHeap H. 
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq. eapply raw_eraseHeapDependentRead. 
  eauto. 
Qed. 

Theorem raw_eraseHeapWrite : forall H x sc a b TID N ds, 
                               raw_heap_lookup x H = Some(sempty sc) ->
                               raw_eraseHeap (raw_replace x (sfull sc ds (aCons a b) TID N) H) = raw_eraseHeap H. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq.
   {inv H0. apply beq_nat_true in eq. subst.  destruct (commit sc) eqn:eq2; auto. simpl. 
    rewrite eq2. destruct b; simpl; auto. simpl. rewrite eq2. auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed. 

Theorem eraseHeapWrite : forall H x sc a b TID N ds, 
                               heap_lookup x H = Some(sempty sc) ->
                               eraseHeap (replace x (sfull sc ds (aCons a b) TID N) H) = eraseHeap H. 
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq. apply raw_eraseHeapWrite. auto. 
Qed. 

Theorem raw_eraseHeapNew : forall H a b x,
                         raw_eraseHeap (raw_extend x (sempty (aCons a b)) H) = 
                         raw_eraseHeap H.
Proof. 
  induction H; intros. 
  {simpl. destruct b; simpl; auto. }
  {simpl in *. destruct a. simpl. destruct b; auto. }
Qed.
  
Theorem eraseHeapNew : forall x H a b p,
                         eraseHeap (extend x (sempty (aCons a b)) H p) =
                         eraseHeap H.                  
Proof.
  intros. destruct H. simpl in *.  
  eapply rawHeapsEq. eapply raw_eraseHeapNew. 
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


Ltac helper := 
  match goal with
      | |- erasePool ?t (erasePoolAux (tSingleton ?t')) => 
        assert(exists t'', eraseThread t' t'') by apply eraseThreadTotal; invertHyp
  end. 

Theorem listAlign2 : forall (T:Type) b a, exists (c : list T) d, a::b = c++[d]. 
Proof.
  induction b; intros. 
  {eauto. }
  {specialize (IHb a). invertHyp. rewrite H0. exists (a0::x). exists x0. auto. }
Qed. 

Ltac alignTac a b := assert(exists c d, a::b = c++[d]) by apply listAlign2; invertHyp. 
 
Theorem specSingleStepErase : forall H T H' T' T'' P,
                                spec_step H P T H' P T' -> erasePool T T'' -> 
                                eraseHeap H' = eraseHeap H /\ erasePool T' T''.
Proof.
  intros.
  inversion H0; subst. 
  {split; auto. inv H1. inv H3. 
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. }
   {helper. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. alignTac a b. 
    rewrite H. eapply eraseSpecSame. rewrite H in H1. eauto. }
  }
  {split; auto. inv H1. unfoldTac. rewrite coupleUnion. destruct b. 
   {erewrite erasePoolSingleton; eauto. erewrite eraseUnionComm. simpl. 
    repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_l. auto. }
   {destruct l. 
    {simpl. erewrite erasePoolSingleton; eauto. rewrite eraseUnionComm. 
     erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
     rewrite union_empty_r. auto. eraseThreadTac. rewrite app_nil_l; eauto. }
    {fold tSingleton. helper. erewrite erasePoolSingleton; eauto. rewrite eraseUnionComm. 
     erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. rewrite union_empty_r. 
     eauto. uCons a l; auto. rewrite eraseTwoActs. eauto. }
   }
   {erewrite erasePoolSingleton; eauto. rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto.
    erewrite erasePoolSingleton; eauto. rewrite union_empty_r. auto. simpl. auto. }
  }
  {split; auto; inv H1. eapply eraseHeapDependentRead; eauto. destruct b. 
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. simpl. auto. }
   {destruct l. 
    {simpl. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
     eraseThreadTac. rewrite app_nil_l. auto. }
    {helper. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto.
     uCons a l; auto. rewrite eraseTwoActs; eauto. }
   }
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. simpl; auto. }
  }
  {split; auto; inv H1. eapply eraseHeapWrite; eauto. destruct b. 
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. simpl. auto. }
   {destruct l. 
    {simpl. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
     eraseThreadTac. rewrite app_nil_l. auto. }
    {helper. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto.
     uCons a l; auto. rewrite eraseTwoActs; eauto. }
   }
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. simpl. auto. }
  }
  {split; auto; inv H1. eapply eraseHeapNew; eauto. destruct b. 
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. simpl. auto. }
   {destruct l. 
    {simpl. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
     eraseThreadTac. rewrite app_nil_l. auto. }
    {helper. erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto.
     uCons a l; auto. rewrite eraseTwoActs; eauto. }
   }
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. simpl; auto. }
  }
  {split; auto. inv H1. unfoldTac. rewrite coupleUnion. destruct b. 
   {erewrite erasePoolSingleton; eauto. erewrite eraseUnionComm. simpl. 
    repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_l. auto. }
   {destruct l. 
    {simpl. erewrite erasePoolSingleton; eauto. rewrite eraseUnionComm. 
     erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. 
     rewrite union_empty_r. auto. eraseThreadTac. rewrite app_nil_l; eauto. }
    {fold tSingleton. helper. erewrite erasePoolSingleton; eauto. rewrite eraseUnionComm. 
     erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. rewrite union_empty_r. 
     eauto. uCons a l; auto. rewrite eraseTwoActs. eauto. }
   }
   {erewrite erasePoolSingleton; eauto. rewrite eraseUnionComm. erewrite erasePoolSingleton; eauto.
    erewrite erasePoolSingleton; eauto. rewrite union_empty_r. auto. simpl; auto. }
  }
Qed. 

Theorem spec_multistepErase : forall H T H' T' T'',
                                spec_multistep H T H' T' -> erasePool T T'' -> 
                                eraseHeap H' = eraseHeap H /\ erasePool T' T''.
Proof. 
  intros. genDeps{T''}. induction H0; subst; auto; intros. 
  inv H1. apply specSingleStepErase with (T'':=erasePoolAux t) in H; auto. 
  inv H. rewrite <- H1. apply IHspec_multistep. rewrite eraseUnionComm. inv H2. 
  rewrite <- eraseUnionComm. constructor.  
Qed. 



