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

Fixpoint eraseHeap (h:sHeap) : pHeap :=
  match h with
      |(i, sempty (hd::tl))::h' => eraseHeap h'
      |(i, sempty nil)::h' => (i, pempty)::eraseHeap h'
      |(i, sfull (hd::tl) d s t N)::h' => eraseHeap h'
      |(i, sfull nil d (a::b) t M)::h' => (i, pempty)::eraseHeap h'
      |(i, sfull nil d nil t M)::h' => (i, pfull (eraseTerm M))::eraseHeap h'
      |nil => nil
  end. 

Inductive eraseThread : thread -> pPool -> Prop :=
|tEraseCommit : forall tid s2 M, eraseThread (tid, nil, s2, M) (pSingleton  (eraseTerm M))
|tEraseRead : forall tid s1 s1' s2 x M M' E (d:decompose M' E (get (fvar x))),
               s1 = s1' ++ [rAct x M' E d] -> 
               eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseWrite : forall tid M M' x s1 s2 s1' E N (d:decompose M' E (put (fvar x) N)),
                s1 = s1' ++ [wAct x M' E N d] ->
                eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseNew : forall tid M M' x s1 s2 s1' E (d:decompose M' E new),
              s1 = s1' ++ [nAct M' E d x] -> 
              eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseFork : forall tid M M' s1 s2 s1' E N (d:decompose M' E (fork N)),
                s1 = s1' ++ [fAct M' E N d] -> 
                eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseSpecRet : forall tid M M' s1 s2 s1' E N N' (d:decompose M' E (spec N N')),
                s1 = s1' ++ [srAct M' E N N' d] -> 
                eraseThread (tid, s1, s2, M) (pSingleton (eraseTerm M'))
|tEraseCreatedSpec : forall tid M s1 s1' s2,
                       s1 = s1' ++ [specAct] ->  eraseThread (tid, s1, s2, M) (Empty_set ptrm)
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
      | |- eraseThread (?tid, [rAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseRead
      | |- eraseThread (?tid, [wAct ?a ?b ?c ?d ?e], ?s2, ?N) ?m => eapply tEraseWrite
      | |- eraseThread (?tid, [nAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseNew
      | |- eraseThread (?tid, [fAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseFork
      | |- eraseThread (?tid, [srAct ?a ?b ?c ?d ?e], ?s2, ?N) ?m => eapply tEraseSpecRet
      | |- eraseThread (?tid, [specAct], ?s2, ?N) ?m => eapply tEraseCreatedSpec
      | |- eraseThread (?tid, ?z++[rAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseRead
      | |- eraseThread (?tid, ?z++[wAct ?a ?b ?c ?d ?e], ?s2, ?N) ?m => eapply tEraseWrite
      | |- eraseThread (?tid, ?z++[nAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseNew
      | |- eraseThread (?tid, ?z++[fAct ?a ?b ?c ?d], ?s2, ?N) ?m => eapply tEraseFork
      | |- eraseThread (?tid, ?z++[srAct ?a ?b ?c ?d ?e], ?s2, ?N) ?m => eapply tEraseSpecRet
      | |- eraseThread (?tid, ?z++[specAct], ?s2, ?N) ?m => eapply tEraseCreatedSpec
  end. 

(*------------------------------------Theorems------------------------------------*)

Theorem eraseThreadTotal : forall t, exists p, eraseThread t p. 
Proof.
  intros. destruct t. destruct p. destruct p. destructLast a0. 
  {exists (pSingleton(eraseTerm t)). constructor. }
  {inv H0. inv H. destruct x; try solve[econstructor; eraseThreadTac; eauto]. }
Qed. 

Axiom erasePoolEraseThread : forall T T' t, erasePool T T' -> tIn T t -> 
                                              exists t', eraseThread t t'. 

(*Erasure is idempotent with respect to unspeculate*)
Theorem eraseUnspecHeapIdem : 
  forall H H', unspecHeap H H' -> eraseHeap H' = eraseHeap H. 
Proof.
  induction H; intros. 
  {inversion H; subst. simpl in *. auto. }
  {inversion H0; subst; auto. 
   {simpl. rewrite IHlist; auto. }
   {simpl. rewrite IHlist; auto. }
   {simpl. rewrite IHlist; auto. }
  }
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
  }
  {inversion H; subst. inversion H0; subst. cleanup. inversion H1; subst. 
   {econstructor; eauto. econstructor; eauto. econstructor; eauto. constructor. }
   {econstructor. econstructor. econstructor. eauto. econstructor; eauto. constructor. 
    auto. eauto. auto. }
   {econstructor. econstructor. econstructor. eauto. eapply unspecWrite; eauto. constructor. 
    auto. auto. auto. }
   {econstructor. econstructor. econstructor. eauto. eapply unspecCreate; eauto. constructor. 
    auto. auto. auto. }
   {econstructor. econstructor. econstructor. eauto. eapply unSpecFork; eauto. constructor. 
    auto. auto. auto. }
   {econstructor. econstructor. econstructor. eauto. eapply unSpecSpecret; eauto. constructor. 
    auto. auto. auto. }
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

Axiom uniqueThreadPool : forall T tid t t', 
                           thread_lookup T tid t -> thread_lookup T tid t' -> t = t'. 

Theorem erasureDeterminism : forall t t1' t2', 
                               eraseThread t t1' -> 
                               eraseThread t t2' -> t1' = t2'.
Proof.
  intros. induction H; inversion H0;subst; auto;
  try(match goal with
               |H:[] = [] ++ [?x] |- _ => inversion H       
               |H:[] = ?x ++ [?y] |- _ => destruct x; inversion H
               |H:?s1++[?x]=?s2++[?y]|-_ => apply lastElementEq in H; inversion H
             end); subst; auto. 
Qed. 

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
  intros. inv H; inv H0; auto; try solve[invertListNeq]; try solve[ 
  apply lastElementEq in H5; inv H5; auto]. 
Qed. 

Theorem erasePoolSingleton : forall t pt, eraseThread t pt -> erasePoolAux(tSingleton t) = pt. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inv H0. inv H1. inv H4. inv H0. eapply eraseThreadDeterminsim in H2; eauto. subst. auto. }
  {destruct t. destruct p. destruct p. econstructor. econstructor. constructor. 
   auto. eauto. auto. }
Qed. 

Theorem termErasePoolErase : forall tid M s2,
                               erasePoolAux (tSingleton(tid,nil,s2,M)) = 
                               (pSingleton (eraseTerm M)). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. cleanup. inversion H3; subst.
   inv H3. inv H1; try invertListNeq. auto. }
  {inversion H; subst. repeat econstructor; eauto. }
Qed. 

Ltac introsInv := let n := fresh in intros n; inversion n. 
 
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
        rewrite <- Ex2; exists (nil,nil,nil,Ex1); auto
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
                         (eraseThread (tid, [A], s2, M) t <->
                          eraseThread (tid, nil, s2, M') t). 
Proof.
  intros. split; intros. 
  {inv H0; try solve[destruct s1'; simpl in *; inv H6;[inv H;auto; inv H6|invertListNeq]]. }
  {inv H0; try invertListNeq. inv H; auto; try solve[eraseThreadTac; eauto].  }
Qed. 

Theorem eraseTwoActs : forall tid tid' A1 A2 As s2 M M' t,
                         eraseThread (tid, (A1::A2::As), s2, M') t <->
                         eraseThread (tid', (A2 :: As), s2, M) t. 
Proof.
  intros. split; intros. 
  {inv H; try solve[apply listAlign in H5; invertHyp; rewrite H; eraseThreadTac; eauto]. }
  {inv H; try solve[rewrite H5; rewrite app_comm_cons; eraseThreadTac; eauto]. }
Qed. 

Theorem eraseOpenComm : forall e e' n, eraseTerm (open n e e') = popen n (eraseTerm e) (eraseTerm e'). 
Proof.
  induction e'; auto; try solve[intros; simpl; rewrite IHe'1; rewrite IHe'2; auto]; 
  try solve[intros; simpl; rewrite IHe'; auto].
  {intros. simpl. destruct (beq_nat n i); auto. }
Qed. 

Theorem eraseSpecSame : forall tid tid' y x a s2 s2' t t' t'',
                          eraseThread (tid, x++[a], s2, t) t' ->
                          eraseThread (tid', y++[a], s2', t'') t'. 
Proof.
  intros. inversion H; subst; try solve[apply lastElementEq in H5; subst; eraseThreadTac; auto].
  {invertListNeq. }
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
 
Theorem specSingleStepErase : forall H T H' T' H'' T'' P,
                                spec_step H P T H' P T' ->
                                eraseHeap H = H'' -> erasePool T T'' -> 
                                eraseHeap H' = H'' /\ erasePool T' T''.
Proof.
  intros.
  inversion H0; subst. 
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eauto. eapply eraseSpecSame. eauto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eauto. eapply eraseSpecSame. eauto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eauto. eapply eraseSpecSame. eauto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eauto. eapply eraseSpecSame. eauto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eauto. eapply eraseSpecSame. eauto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eauto. eapply eraseSpecSame. eauto. }
  {split; auto; inv H2; alignTac a b. rewrite H. helper. erewrite erasePoolSingleton; eauto. 
   erewrite erasePoolSingleton. eauto. eapply eraseSpecSame. eauto. }
  {split; auto. inv H2. destruct b. 
   {erewrite erasePoolSingleton; eauto. unfoldTac. rewrite coupleUnion. rewrite eraseUnionComm. 
    repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. auto. }
   {alignTac a b. rewrite H. erewrite erasePoolSingleton; eauto. unfoldTac. rewrite coupleUnion.
    assert(exists t', eraseThread (tid,x++[x0],s2,t) t'). apply eraseThreadTotal. invertHyp.
    rewrite eraseUnionComm. repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. 
    eauto. rewrite app_comm_cons. eapply eraseSpecSame. eauto. }
  }
  {split; auto; inv H2. eapply eraseHeapDependentRead; eauto. destruct b. 
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. }
   {alignTac a b. rewrite H1. helper. erewrite erasePoolSingleton; eauto. 
    erewrite erasePoolSingleton. eauto. rewrite app_comm_cons. eapply eraseSpecSame. eauto. }
  }
  {split; auto; inv H2. eapply eraseHeapWrite; eauto. destruct b. 
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. }
   {alignTac a b. rewrite H1. helper. erewrite erasePoolSingleton; eauto. 
    erewrite erasePoolSingleton. eauto. rewrite app_comm_cons. eapply eraseSpecSame. eauto. }
  }
  {split; auto; inv H2. eapply eraseHeapNew; eauto. eauto.destruct b. 
   {erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton; eauto. }
   {alignTac a b. rewrite H1. helper. erewrite erasePoolSingleton; eauto. 
    erewrite erasePoolSingleton. eauto. rewrite app_comm_cons. eapply eraseSpecSame. eauto. }
  }
  {split; auto; inv H2; alignTac a b. eapply eraseHeapWrite; eauto. rewrite H1. helper. 
   erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton. eauto. 
   rewrite app_comm_cons. eapply eraseSpecSame. eauto. }
  {split; auto; inv H2; alignTac a b. eapply eraseHeapNew; eauto. rewrite H1. helper. 
   erewrite erasePoolSingleton; eauto. erewrite erasePoolSingleton. eauto. 
   rewrite app_comm_cons. eapply eraseSpecSame. eauto. } 
  {split; auto. inv H2. alignTac a b. rewrite H. helper. 
   assert(erasePoolAux(tUnion(tSingleton(tid, srAct t E M N d:: a :: b, s2, fill E (specRun M N)))
                             (tSingleton (tid', [specAct], [], N))) =  
          erasePoolAux(Singleton thread(tid,a::b,s2,t))). 
   rewrite eraseUnionComm.  repeat erewrite erasePoolSingleton; eauto. rewrite union_empty_r. 
   rewrite H. eauto. rewrite eraseTwoActs. rewrite H. eauto. rewrite<- H. 
   unfoldTac. rewrite <- H1. rewrite coupleUnion. constructor. }
Qed.

Theorem spec_multistepErase : forall H T H' T' H'' T'',
                                spec_multistep H T H' T' ->
                                eraseHeap H = H'' -> erasePool T T'' -> 
                                eraseHeap H' = H'' /\ erasePool T' T''.
Proof. 
  intros. genDeps{H''; T''}. induction H0; subst; auto; intros. 
  inv H2. apply specSingleStepErase with (H'':=eraseHeap h)(T'':=erasePoolAux t) in H; auto. 
  inv H. apply IHspec_multistep. rewrite eraseUnionComm. inv H2. rewrite <- eraseUnionComm. 
  constructor. auto. 
Qed. 



