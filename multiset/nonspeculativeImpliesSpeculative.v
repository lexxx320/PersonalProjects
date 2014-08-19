Require Import erasure. 
Require Import IndependenceCommon.

Fixpoint specTerm (t:ptrm) := 
  match t with
      |pfvar x => fvar x
      |pbvar x => bvar x
      |punit => unit
      |ppair e1 e2 => pair_ (specTerm e1) (specTerm e2)
      |plambda e => lambda (specTerm e)
      |papp e1 e2 => AST.app (specTerm e1) (specTerm e2)
      |pret e => ret (specTerm e)
      |pbind e1 e2 => bind (specTerm e1) (specTerm e2)
      |pfork e => fork (specTerm e)
      |pnew => new
      |pput e1 e2 => put (specTerm e1) (specTerm e2)
      |pget e => get (specTerm e)
      |praise e => raise (specTerm e)
      |phandle e1 e2 => handle (specTerm e1) (specTerm e2)
      |pfst e => fst (specTerm e)
      |psnd e => snd (specTerm e)
      |pspec e1 e2 => spec (specTerm e1) (specTerm e2)
      |pspecRun e1 e2 => specRun (specTerm e1) (specTerm e2)
      |pspecJoin e1 e2 => specJoin (specTerm e1) (specTerm e2)
      |pdone e => done (specTerm e)
  end. 

Fixpoint gather t tid :=
    match t with
      |pfvar x => Empty_set thread
      |pbvar x => Empty_set thread
      |punit => Empty_set thread
      |ppair e1 e2 => tUnion (gather e1 tid) (gather e2 tid)
      |plambda e => gather e tid
      |papp e1 e2 => tUnion (gather e1 tid) (gather e2 tid)
      |pret e => gather e tid
      |pbind e1 e2 => tUnion (gather e1 tid) (gather e2 tid)
      |pfork e => gather e tid
      |pnew => Empty_set thread
      |pput e1 e2 => tUnion (gather e1 tid) (gather e2 tid)
      |pget e => gather e tid
      |praise e => gather e tid
      |phandle e1 e2 => tUnion (gather e1 tid) (gather e2 tid)
      |pfst e => gather e tid
      |psnd e => gather e tid
      |pspec e1 e2 => tUnion (gather e1 tid) (gather e2 tid)
      |pspecRun e1 e2 => tUnion (tUnion (gather e1 tid) (gather e2 (2::tid)))
                                (tSingleton(2::tid,specStack nil (specTerm e2),nil,specTerm e2))
      |pspecJoin e1 e2 => tUnion (gather e1 tid) (gather e2 tid)
      |pdone e => gather e tid
    end. 


Inductive speculate : pPool -> pool -> Prop :=
|specCons : forall t Ts Ts' tid s2, speculate Ts Ts' ->
                                    speculate (t::Ts) (tUnion (gather t tid)((tid,unlocked nil,s2,specTerm t)::Ts'))
|specNil : speculate nil nil.

Fixpoint gatherThreads T :=
  match T with
      |t::Ts => tUnion (gather t nil) (gatherThreads Ts)
      |nil => nil
  end. 

Fixpoint raw_specHeap (H:rawHeap pivar_state):= 
  match H with 
      |(i, pempty)::H' => (i, sempty COMMIT)::raw_specHeap H'
      |(i, pfull M)::H' => (i, sfull COMMIT nil COMMIT nil (specTerm M))::raw_specHeap H'
      |nil => nil
  end. 

Theorem specUnique : forall H S,
                       unique pivar_state S H -> 
                       unique ivar_state S (raw_specHeap H). 
Proof.
  induction H; intros. 
  {constructor. }
  {inv H0. simpl. destruct v. constructor. auto. eauto. constructor; auto. }
Qed. 

Definition specHeap H :=
  match H with
      |heap_ h p => 
       heap_ ivar_state (raw_specHeap h) (specUnique h (Ensembles.Empty_set AST.id) p)
  end. 

Theorem specUnionComm : forall T1 T2 T,
                          speculate (pUnion T1 T2) T ->
                          exists T1' T2', (speculate T1) T1' /\ (speculate T2) T2' /\
                          T = tUnion T1' T2' . 
Proof.
  induction T1; intros. 
  {simpl in *. econstructor. econstructor. split; eauto. constructor. 
   split; eauto. }
  {simpl in *. inv H.  
   {eapply IHT1 in H3. invertHyp. econstructor. econstructor. split.
    econstructor; eauto. split; eauto. unfoldTac. rewrite <- Union_associative. 
    reflexivity. }
  }
Qed. 

Theorem gatherDecomp : forall t E N M tid,
                         pdecompose t E (pspecRun N M) ->
                         exists T, gather t tid = T /\ 
                                   tIn T (2::tid, specStack nil (specTerm M), nil, specTerm M). 
Proof.
  induction t; intros; try solveByInv; try solve[inv H;
    match goal with
      |H:forall E N M tid, pdecompose ?t E (pspecRun N M) -> ?x, H':pdecompose ?t ?E' ?e' |- _ =>
       eapply H in H'; invertHyp; econstructor; split; eauto; simpl; solveSet
    end; solveSet]. 
  {inversion H; subst. 
   {eapply IHt1 in H5. invertHyp. econstructor. split. auto. simpl. solveSet. 
    left. invUnion. left. eauto. }
   {econstructor. split. auto. simpl. solveSet. }
  }
Qed. 

Theorem singleton : forall (t:thread), [t] = tSingleton t. auto. Qed. 


Theorem specUnionL : forall T1 T2 T1' T2', 
                       speculate T1 T1' -> speculate T2 T2' ->
                       speculate (pUnion T1 T2) (tUnion T1' T2'). 
Proof.
  induction T1; intros. 
  {simpl. inv H. simpl. auto. }
  {inv H. eapply IHT1 in H0; eauto. simpl. unfoldTac. rewrite <- Union_associative.  
   eapply specCons. eauto. }
Qed. 

Fixpoint specCtxt E := 
  match E with
      |pbindCtxt E e => bindCtxt (specCtxt E) (specTerm e)
      |phandleCtxt E e => handleCtxt (specCtxt E) (specTerm e)
      |pappCtxt E e => appCtxt (specCtxt E) (specTerm e)
      |pappValCtxt E e => appValCtxt (specCtxt E) (specTerm e)
      |ppairCtxt E e => pairCtxt (specCtxt E) (specTerm e)
      |ppairValCtxt E e => pairValCtxt (specCtxt E) (specTerm e)
      |pfstCtxt E => fstCtxt (specCtxt E)
      |psndCtxt E => sndCtxt (specCtxt E)
      |pspecRunCtxt E e => specRunCtxt (specCtxt E) (specTerm e)
      |pspecJoinCtxt E e => specJoinCtxt (specCtxt E) (specTerm e)
      |pholeCtxt => holeCtxt
  end. 

Theorem consNil : forall (T:Type) (a:T), [a] = a::nil. auto. Qed. 

Theorem eSpecTerm : forall e, exists e', specTerm e' = e. 
Proof.
  induction e; intros; try invertHyp. 
  {exists (pfvar i). auto. }
  {exists (pbvar i). auto. }
  {exists punit; auto. }
  {exists (ppair x0 x). auto. }
  {exists (plambda x); auto. }
  {exists (papp x0 x); auto. }
  {exists (pret x); auto. }
  {exists (pbind x0 x); auto. }
  {exists (pfork x); auto. }
  {exists pnew; auto. }
  {exists (pput x0 x); auto. }
  {exists (pget x); auto. }
  {exists (praise x); auto. }
  {exists (phandle x0 x); auto. }
  {exists (pspec x0 x); auto. }
  {exists (pspecRun x0 x); auto. }
  {exists (pspecJoin x0 x); auto. }
  {exists (pfst x); auto. }
  {exists (psnd x); auto. }
  {exists (pdone x); auto. }
Qed.  

Theorem eSpecCtxt : forall E, exists E', specCtxt E' = E. 
Proof.
  induction E; intros; try invertHyp. 
Admitted. 

Ltac existTac e := let n := fresh in
                   try(assert(n:exists e', specTerm e = e') by apply eSpecTerm; invertHyp);
                   try(assert(n:exists e', specCtxt e = e') by apply eSpecCtxt; invertHyp). 

Theorem specFill : forall E e, specTerm (pfill E e) = fill (specCtxt E) (specTerm e). 
Admitted.  

Theorem gatherDrop : forall t E N M tid,
                       pdecompose t E (pspecRun N M) ->
                       gather (pfill E (pspecJoin N M)) (2::tid) = 
                       Subtract thread (gather t tid)
                                (2::tid,specStack nil (specTerm M),nil,specTerm M).
Proof.
  induction t; intros; try solve[inv H]. 
  {inv H. eapply IHt1 in H5. simpl. rewrite H5. 
   Admitted. 

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' T,
        pstep PH PT pt (pOK PH' PT pt') -> 
        speculate (pUnion PT pt) T -> 
        exists T', multistep (specHeap PH) T (Some(specHeap PH', T')) /\
                   speculate (pUnion PT pt') T'. 
Proof.
  intros. inv H. 
  {apply specUnionComm in H0.  admit. }
  {admit. }
  {apply specUnionComm in H0. invertHyp. inv H0. 
   inv H4. copy H5. eapply gatherDecomp with (tid:=tid)in H0. invertHyp. 
   unfoldTac. apply pullOut in H2. rewrite H2. rewrite <- Union_associative. 
   rewrite singleton. rewrite <- coupleUnion. rewrite couple_swap. 
   rewrite Union_associative. econstructor. split. eapply multi_step. 
   eapply SpecJoin with (N0:=specTerm M)
                          (M:=specTerm M)(N1:=specTerm N)(E:=specCtxt E); eauto. 
   simpl. constructor. unfoldTac.
   rewrite <- Union_associative. unfold pUnion. apply specUnionL. auto. 
   copy H5. eapply gatherDrop with(tid:=tid)in H5. rewrite <- H5. 
   



   unfold pSingle. unfold Single. replace (specJoin (ret (specTerm N)) (specTerm M)) with
                                  (specTerm (pspecJoin (pret N) M)); auto. 
   rewrite <- specFill. econstructor. constructor. 



















(*------------------------------------------------------------------------------------------*)


Fixpoint commitPool' (T:pool)  := 
  match T with
      |(_, unlocked nil, _, _)::T' => commitPool' T'
      |(_, specStack nil _,_,_)::T' => commitPool' T'
      |nil => True
      |_ => False
  end. 
Theorem decompNeq : forall t E e E' e',
                      decompose t E e -> pdecompose (eraseTerm t) E' e' -> 
                      eraseTerm e <> e' -> False. 
Proof.
  intros. rewrite <- decomposeErase in H; eauto. eapply pctxtUnique in H0; eauto. 
  invertHyp. apply H1. auto.
Qed. 

Theorem appSingle : forall (T:Type) (a:T) b, a::b = [a]++b. 
reflexivity. Qed. 

Theorem eraseSplit : forall T PT t, 
                       commitPool' T -> 
                       erasePool T = pUnion PT (pSingle t) ->
                       exists T1 T2,
                         T = tUnion T1 T2 /\ erasePool T1 = PT /\ erasePool T2 = (pSingle t).
Proof.
  induction T; intros. 
  {simpl in *. unfold pUnion in *. rewrite Union_commutative in H0. inv H0. }
  {destruct PT. 
   {destructThread a. destruct H6. 
    {simpl in *. inv H. }
    {destruct l. simpl in *. inv H0. econstructor. exists (tSingleton(H5,unlocked nil,H4,H2)). 
     split. Focus 2. split. auto. simpl. auto. unfoldTac. rewrite Union_commutative. 
     auto. contradiction. }
    {destruct l. 
     {simpl in *. inv H0. eapply IHT in H. Focus 2. unfold pUnion. rewrite union_empty_l. 
      eauto. invertHyp. exists (tSingleton(H5,specStack nil t0,H4, H2)). econstructor. split. 
      simpl. auto. split. auto. auto. }
     {contradiction. }
    }
   }
   {

 econstructor. econstructor. split. Focus 2. split. eassumption. 
      eauto. 


contradiction. }
   }
   {destructThread a. destruct H6; try contradiction. destruct l; try contradiction.
    simpl in *. inv H0. eapply IHT in H6; auto. invertHyp. econstructor. 
    exists x0. exists x1. exists x2. split. 
    rewrite appSingle. rewrite Union_associative. reflexivity. split; auto. }
  }
Qed. 

Theorem parImpliesSpec : forall PT pt PH' pt' H T,
                           pstep (eraseHeap H) PT pt (pOK PH' PT pt') -> 
                           erasePool T = (pUnion PT pt) -> commitPool T ->
                           exists H' T', multistep H T (Some(H', T')) /\
                                         eraseHeap H' = PH' /\ erasePool T' = pUnion PT pt'. 
Proof.
  intros. inv H0. 
  

Theorem decompNeq : forall t E e E' e',
                      decompose t E e -> pdecompose (eraseTerm t) E' e' -> 
                      eraseTerm e <> e' -> False. 
Proof.
  intros. rewrite <- decomposeErase in H; eauto. eapply pctxtUnique in H0; eauto. 
  invertHyp. apply H1. auto.
Qed. 

Theorem appSingle : forall (T:Type) (a:T) b, a::b = [a]++b. 
reflexivity. Qed. 

Theorem eraseSplit : forall T PT t, 
                       commitPool T -> 
                       erasePool T = pUnion PT (pSingle t) ->
                       exists T' tid s2 M, 
                         T = tUnion T' (tSingleton (tid,unlocked nil, s2, M)) /\
                         erasePool T' = PT /\ eraseTerm M = t. 
Proof.
  induction T; intros. 
  {simpl in *. unfold pUnion in *. rewrite Union_commutative in H0. inv H0. }
  {destruct PT. 
   {destructThread a. destruct H6. 
    {simpl in *. inv H. }
    {destruct l. simpl in *. inv H0. econstructor. econstructor. econstructor. 
     econstructor. split. 
     unfoldTac. rewrite Union_commutative. simpl. eauto. split; auto. 
     simpl in *. contradiction. }
    {simpl in *. contradiction. }
   }
   {destructThread a. destruct H6; try contradiction. destruct l; try contradiction.
    simpl in *. inv H0. eapply IHT in H6; auto. invertHyp. econstructor. 
    exists x0. exists x1. exists x2. split. 
    rewrite appSingle. rewrite Union_associative. reflexivity. split; auto. }
  }
Qed. 

Theorem eraseEmpty : forall tid s1 s2 M N, 
                       erasePool(tSingleton(tid,specStack s1 N,s2,M)) = Empty_set ptrm. 
Proof.
  reflexivity. Qed. 

Fixpoint specTerm (t:ptrm) := 
  match t with
      |pfvar x => fvar x
      |pbvar x => bvar x
      |punit => unit
      |ppair e1 e2 => pair_ (specTerm e1) (specTerm e2)
      |plambda e => lambda (specTerm e)
      |papp e1 e2 => AST.app (specTerm e1) (specTerm e2)
      |pret e => ret (specTerm e)
      |pbind e1 e2 => bind (specTerm e1) (specTerm e2)
      |pfork e => fork (specTerm e)
      |pnew => new
      |pput e1 e2 => put (specTerm e1) (specTerm e2)
      |pget e => get (specTerm e)
      |praise e => raise (specTerm e)
      |phandle e1 e2 => handle (specTerm e1) (specTerm e2)
      |pfst e => fst (specTerm e)
      |psnd e => snd (specTerm e)
      |pspec e1 e2 => spec (specTerm e1) (specTerm e2)
      |pspecRun e1 e2 => specRun (specTerm e1) (specTerm e2)
      |pspecJoin e1 e2 => specJoin (specTerm e1) (specTerm e2)
      |pdone e => done (specTerm e)
  end. 

Inductive speculate : pPool -> pool -> Prop :=
|specNil : speculate (Empty_set ptrm) (Empty_set thread)
|specCons : forall t E M N Ts Ts' s2,
              pdecompose t E (pspecRun M N) -> speculate Ts Ts' ->
              speculate (t::Ts) ((nil,unlocked nil,nil,specTerm t)
                                   ::([2],specStack nil (specTerm N),s2,specTerm N)::Ts')
|specCons' : forall t Ts Ts' t' s2,
              (~ exists M N E, pdecompose t E (pspecRun M N)) -> speculate Ts Ts' ->
               t' = specTerm t -> speculate (t::Ts) ((nil,unlocked nil,s2,t')::Ts')
.

Fixpoint raw_specHeap (H:rawHeap pivar_state):= 
  match H with 
      |(i, pempty)::H' => (i, sempty COMMIT)::raw_specHeap H'
      |(i, pfull M)::H' => (i, sfull COMMIT nil COMMIT nil (specTerm M))::raw_specHeap H'
      |nil => nil
  end. 

Theorem specUnique : forall H S,
                       unique pivar_state S H -> 
                       unique ivar_state S (raw_specHeap H). 
Proof.
  induction H; intros. 
  {constructor. }
  {inv H0. simpl. destruct v; econstructor; auto. }
Qed. 

Definition specHeap H :=
  match H with
      |heap_ h p => 
       heap_ ivar_state (raw_specHeap h) (specUnique h (Ensembles.Empty_set AST.id) p)
  end. 

Theorem specUnionComm : forall T1 T2 T,
                          speculate (pUnion T1 T2) T ->
                          exists T1' T2', (speculate T1) T1' /\ (speculate T2) T2' /\
                          T = tUnion T1' T2' . 
Proof.
  induction T1; intros. 
  {simpl in *. econstructor. econstructor. split; eauto. constructor. 
   split; eauto. }
  {simpl in *. inv H. 
   {eapply IHT1 in H4. invertHyp. econstructor. econstructor. split.
    econstructor; eauto. split; eauto. reflexivity. }
   {eapply IHT1 in H3. invertHyp. econstructor. econstructor. split. 
    eapply specCons'; eauto. split; eauto. reflexivity. }
  }
Qed. 

Fixpoint specCtxt E := 
  match E with
      |pbindCtxt E e => bindCtxt (specCtxt E) (specTerm e)
      |phandleCtxt E e => handleCtxt (specCtxt E) (specTerm e)
      |pappCtxt E e => appCtxt (specCtxt E) (specTerm e)
      |pappValCtxt E e => appValCtxt (specCtxt E) (specTerm e)
      |ppairCtxt E e => pairCtxt (specCtxt E) (specTerm e)
      |ppairValCtxt E e => pairValCtxt (specCtxt E) (specTerm e)
      |pfstCtxt E => fstCtxt (specCtxt E)
      |psndCtxt E => sndCtxt (specCtxt E)
      |pspecRunCtxt E e => specRunCtxt (specCtxt E) (specTerm e)
      |pspecJoinCtxt E e => specJoinCtxt (specCtxt E) (specTerm e)
      |pholeCtxt => holeCtxt
  end. 

Hint Constructors decompose. 


Theorem specVal : forall M, pval M <-> val (specTerm M). 
Proof.
  induction M; intros; split; intros; simpl in *; try solveByInv; try solve[
  match goal with
      |H:pval ?t |- _ => inv H; constructor;[apply IHM1; auto|apply IHM2; auto]
      |H:val ?t |- _ => inv H; constructor;[apply IHM1; auto|apply IHM2; auto]
  end]; try solve[constructor]. 
Qed. 

Theorem notSpecVal : forall M, ~pval M <-> ~val (specTerm M). 
Proof.
  induction M; intros; split; intros; simpl in *; try solve[introsInv]; 
  introsInv; apply H; constructor; apply specVal; auto. 
Qed. 

Theorem specTermUnique : forall M M', specTerm M = specTerm M' -> M = M'. 
Proof.
  induction M; intros; destruct M'; simpl in *; inv H; auto; try solve[
  apply IHM1 in H1; apply IHM2 in H2; subst; auto];
  apply IHM in H1; subst; auto. 
Qed. 

Theorem decomposeSpec : forall M E e M' E' e',
                            specTerm M = M' -> specCtxt E = E' -> specTerm e = e' ->
                            (pdecompose M E e <-> decompose M' E' e'). 
Proof. 
  intros. split; intros. 
  {genDeps{E; e; M'; E'; e'; M}. 
   induction M; intros; subst; try solve[simpl in H2; inversion H2]; 
   try solve[
         simpl in H2; inv H2; try solve[repeat match goal with
        |H:?x = specCtxt ?E |- _ => destruct E; inv H
        |H:?x = specTerm ?M |- _ => destruct M; inv H
        | |- val ?t => apply specVal; eauto
        | |- ~val ?t => apply notSpecVal; eauto
        |_ => constructor
    end; eauto]]. }
  {genDeps{E; e; M'; E'; e'; M}.
   induction M; intros; subst; try solve[inv H2].
   {simpl in *. inv H2. destruct E; inv H1. apply specTermUnique in H2. subst. 
    eapply IHM1 in H5; eauto. constructor. apply notSpecVal; eauto. eauto. 
    destruct E; inv H1. apply specTermUnique in H2. subst. eapply IHM2 in H6; eauto. 
    constructor; auto. apply specVal; auto. apply notSpecVal; auto. }
   {simpl in *. inv H2. destruct E; inv H1. apply specTermUnique in H2. subst. 
    eapply IHM1 in H5; eauto. constructor. apply notSpecVal; eauto. eauto. 
    destruct E; inv H1. apply specTermUnique in H2. subst. eapply IHM2 in H6; eauto. 
    constructor; auto. apply specVal; auto. apply notSpecVal; auto.
    destruct E; inv H1. destruct e; inv H3. apply specTermUnique in H0.
    apply specTermUnique in H1. subst. constructor; (apply specVal; auto). }
   {simpl in *. inv H2. destruct E; inv H1. apply specTermUnique in H2. subst. 
    eapply IHM1 in H5; eauto. constructor. apply notSpecVal; eauto. eauto. 
    destruct E; inv H3. destruct e; inv H4. apply specTermUnique in H2. 
    apply specTermUnique in H1. subst. constructor. apply specVal; auto. }
   {Admitted. 

Theorem eSpecTerm : forall e, exists e', specTerm e' = e. 
Proof.
  induction e; intros.
  {exists (pfvar i). auto. }
  {Admitted. 
 
Theorem eSpecCtxt : forall E, exists E', specCtxt E' = E. 
Admitted. 

Ltac existTac e := let n := fresh in
                   try(assert(n:exists e', eraseTerm e' = e) by apply eTerm; invertHyp);
                   try(assert(n:exists e', eraseCtxt e' = e) by apply eCtxt; invertHyp);
                   try(assert(n:exists e', specTerm e' = e) by apply eSpecTerm; invertHyp);
                   try(assert(n:exists e', specCtxt e' = e) by apply eSpecCtxt; invertHyp). 


Ltac eTermTac := 
  match goal with
      |H:pbasic_step ?M ?M' |- _ => existTac M' 
  end. 

Theorem specFill : forall E e, specTerm (pfill E e) = fill (specCtxt E) (specTerm e). 
Admitted.  

Theorem specOpen : forall e e' n, 
                     specTerm (popen n e e') = open n (specTerm e) (specTerm e').
Admitted. 

Theorem eraseSpecTerm : forall t, eraseTerm(specTerm t) = t. 
Proof.
  induction t; auto; try solve[ simpl; rewrite IHt1; rewrite IHt2; auto];
  simpl; rewrite IHt; auto. 
Qed. 


Theorem raw_eraseSpecHeap : forall H, raw_eraseHeap (raw_specHeap H) = H. 
Proof.
  induction H; intros; auto; simpl; destruct a; destruct p; simpl; rewrite IHlist; auto.
  rewrite eraseSpecTerm. auto. 
Qed. 

Theorem eraseSpecHeap : forall H, eraseHeap (specHeap H) = H. 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. eapply raw_eraseSpecHeap; eauto. 
Qed. 


Theorem eraseSpecPool : forall T T',
                          speculate T T' -> erasePool T' = T. 
Proof.
  induction T; intros. 
  {inv H. auto. }
  {inv H. 
   {simpl. rewrite eraseSpecTerm. rewrite IHT; eauto. }
   {simpl. rewrite eraseSpecTerm. rewrite IHT; eauto. }
  }
Qed.

Theorem eraseSpecCtxt : forall E, eraseCtxt (specCtxt E) = E. 
Proof.
  induction E; auto; simpl; rewrite IHE; repeat rewrite eraseSpecTerm; auto.
Qed. 

Ltac pFalseDecomp := 
  match goal with
      |H:pdecompose ?t ?E ?e,H':pdecompose ?t' ?E' ?e' |- _ =>
       eapply pctxtUnique in H; eauto; invertHyp; solveByInv
  end. 


Theorem consApp : forall (T:Type) (a:T) b, a::b = [a]++b. auto. Qed. 

Theorem AddUnion : forall (A:Type) T t, Union A T (Single A t) = Add A T t. auto. Qed. 


Theorem raw_specHeapLookupFull : forall H x M, 
                               raw_heap_lookup x H = Some(pfull M) ->
                               raw_heap_lookup x (raw_specHeap H) =
                               Some(sfull COMMIT nil COMMIT nil (specTerm M)). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct p; simpl; rewrite eq; auto. }
  }
Qed. 

Theorem specHeapLookupFull : forall H x M, 
                               heap_lookup x H = Some(pfull M) ->
                               heap_lookup x (specHeap H) = Some(sfull COMMIT nil COMMIT nil (specTerm M)). 
Proof.
  intros. destruct H. simpl. eapply raw_specHeapLookupFull; eauto. 
Qed. 

Theorem raw_specHeapLookupEmpty : forall H x, 
                               raw_heap_lookup x H = Some pempty ->
                               raw_heap_lookup x (raw_specHeap H) =
                               Some(sempty COMMIT).
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct p; simpl; rewrite eq; auto. }
  }
Qed. 

Theorem specHeapLookupEmpty : forall H x, 
                               heap_lookup x H = Some pempty->
                               heap_lookup x (specHeap H) = Some(sempty COMMIT) .
Proof.
  intros. destruct H. simpl. eapply raw_specHeapLookupEmpty; eauto. 
Qed. 

Theorem raw_specHeapLookupNone : forall H x, 
                               raw_heap_lookup x H = None ->
                               raw_heap_lookup x (raw_specHeap H) = None.
Proof.
  induction H; intros. 
  {auto. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. }
   {destruct p; simpl; rewrite eq; auto. }
  }
Qed. 

Theorem specHeapLookupNone : forall H x, 
                               heap_lookup x H = None ->
                               heap_lookup x (specHeap H) = None.
Proof.
  intros. destruct H. simpl. eapply raw_specHeapLookupNone; eauto. 
Qed. 


Theorem raw_specHeapWriteEq : forall x H M,
             raw_heap_lookup x H = Some pempty ->
             raw_eraseHeap (raw_replace x (sfull COMMIT nil COMMIT nil (specTerm M)) (raw_specHeap H)) = 
             raw_replace x (pfull M) H. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. simpl. rewrite eraseSpecTerm. 
    rewrite raw_eraseSpecHeap. auto. }
   {destruct p. simpl. rewrite eq. simpl. erewrite IHlist; eauto. simpl. 
    rewrite eq. simpl. erewrite IHlist; eauto. rewrite eraseSpecTerm. auto. }
  }
Qed. 

Theorem specHeapWriteEq : forall x H M,
                            heap_lookup x H = Some pempty ->
                            eraseHeap (replace x (sfull COMMIT nil COMMIT nil (specTerm M)) (specHeap H)) = 
                            replace x (pfull M) H. 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. eapply raw_specHeapWriteEq; eauto. 
Qed. 


Theorem specUnionComm' : forall T1 T2 T1' T2',
                           speculate T1 T1' -> speculate T2 T2' ->
                           speculate (pUnion T1 T2) (tUnion T1' T2'). 
Proof.
  induction T1; intros. 
  {inv H. simpl. auto. }
  {inv H. 
   {eapply specCons; eauto. }
   {eapply specCons'; eauto. }
  }
Qed. 

Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' T,
        pstep PH PT pt (pOK PH' PT pt') ->
        speculate (pUnion PT pt) T -> 
        exists H' T',
          multistep (specHeap PH) T (Some(H', T')) /\
          eraseHeap H' = PH' /\ speculate (pUnion PT pt') T'. 
Proof.
  intros. inv H. 
  {apply specUnionComm in H0. invertHyp. inv H5. 
   {inv H0.
    {inv H6. pFalseDecomp. }
    {inv H5. erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
     eapply multi_step. eapply BasicStep. eapply basicBeta. simpl in *. eauto. 
     constructor. split. rewrite eraseSpecHeap. auto. apply specUnionComm'; auto.
     econstructor. admit. constructor. rewrite specFill. rewrite specOpen. auto. }
   }
   {inv H0.
    {inv H6. pFalseDecomp. }
    {inv H5. erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
     eapply multi_step. eapply BasicStep. eapply basicProjL. simpl in *. eauto. 
     constructor. split. rewrite eraseSpecHeap. auto. apply specUnionComm'; auto.
     econstructor. intros c. admit. constructor. rewrite specFill. rewrite specOpen. auto. }
   }




Theorem nonspecImpliesSpec : forall PH PH' PT pt pt' T,
        pstep PH PT pt (pOK PH' PT pt') ->
        speculate (pUnion PT pt) T -> 
        exists H' T',
          multistep (specHeap PH) T (Some(H', T')) /\
          eraseHeap H' = PH' /\ erasePool T' = (pUnion PT pt').
Proof.
  intros. inv H. 
  {apply specUnionComm in H0. invertHyp. inv H5. 
   {inv H0; inv H6. pFalseDecomp. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply basicBeta. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. 
    rewrite eraseOpenComm. repeat rewrite eraseSpecTerm. 
    rewrite eraseSpecCtxt. auto. }
   {inv H0; inv H6. eapply pctxtUnique in H1; eauto. invertHyp. solveByInv. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply basicProjL. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. 
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
   {inv H0; inv H6. eapply pctxtUnique in H1; eauto. invertHyp. solveByInv. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply basicProjR. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. 
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
   {inv H0; inv H6. eapply pctxtUnique in H1; eauto. invertHyp. solveByInv. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply basicBind. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. simpl. 
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
   {inv H0; inv H6. eapply pctxtUnique in H1; eauto. invertHyp. solveByInv. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply basicBindRaise. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. simpl. 
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
   {inv H0; inv H6. eapply pctxtUnique in H1; eauto. invertHyp. solveByInv. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply basicHandle. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. simpl.
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
   {inv H0; inv H6. eapply pctxtUnique in H1; eauto. invertHyp. solveByInv. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply basicHandleRet. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. simpl.
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
   {inv H0; inv H6. eapply pctxtUnique in H1; eauto. invertHyp. solveByInv. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply specJoinRaise. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. simpl.
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
   {inv H0; inv H6. eapply pctxtUnique in H1; eauto. invertHyp. solveByInv. 
    erewrite decomposeSpec in H1; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply BasicStep. eapply specJoinRet. simpl in *. eauto. 
    constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
    simpl. apply eraseSpecPool in H. rewrite H. rewrite eraseFill. simpl.
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
  }
  {apply specUnionComm in H0. invertHyp. inv H0; inv H6. pFalseDecomp.
   erewrite decomposeSpec in H5; auto.  
   econstructor. econstructor. split. eapply multi_step. eapply Spec.Spec with (d:=H5).  
   eapply multi_step. eapply PopSpec. simpl. rewrite app_nil_l; auto. 
   constructor. split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. 
   simpl. rewrite eraseFill. simpl. repeat rewrite eraseSpecTerm. 
   rewrite eraseSpecCtxt. apply eraseSpecPool in H. subst. auto. }
  {apply specUnionComm in H0. invertHyp. inv H0. 
   {eapply pctxtUnique in H5; eauto. invertHyp. inv H1. inv H6. 
    erewrite decomposeSpec in H3; eauto. econstructor. econstructor. 
    split. eapply multi_step. eapply SpecJoin with (p:=H3); eauto. simpl. constructor. 
    split. rewrite eraseSpecHeap; auto. rewrite eraseUnionComm. 
    apply eraseSpecPool in H. subst. simpl. rewrite eraseFill. simpl. 
    repeat rewrite eraseSpecTerm. rewrite eraseSpecCtxt. auto. }
   {assert(exists M N E, pdecompose t E (pspecRun M N)). eauto. 
    contradiction. }
  }
  {apply specUnionComm in H0. invertHyp. inv H0.
   {inv H6. eapply pctxtUnique in H5; eauto. invertHyp. inv H1.
    erewrite decomposeSpec in H3; eauto. econstructor. 
    econstructor. split. eapply multi_step. rewrite consApp. rewrite Union_commutative.
    simpl. replace  [([2],specStack [] (specTerm M), @nil action, specTerm M);
     ([], unlocked [], [], specTerm t)] with (tCouple([2], specStack [] (specTerm M), [], specTerm M)
     ([], unlocked [], [], specTerm t)). 
    replace (tCouple ([2], specStack [] (specTerm M), [], specTerm M)
        ([], unlocked [], [], specTerm t)) with 
    (tUnion (Empty_set thread)(tCouple ([2], specStack [] (specTerm M), [], specTerm M) 
        ([], unlocked [], [], specTerm t))). eapply SpecRB. simpl in *; eassumption.  
    eauto. eauto. eapply RBDone. solveSet. eauto. simpl. auto. auto. constructor. 
    split. rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. simpl. 
    apply eraseSpecPool in H. subst. rewrite eraseFill. simpl. rewrite eraseSpecTerm. 
    rewrite eraseSpecCtxt. auto. }
   {assert(exists M N E, pdecompose t E (pspecRun M N)). eauto. 
    contradiction. }
  }
  {apply specUnionComm in H0. invertHyp. inv H0. 
   {inv H6. pFalseDecomp. }
   {inv H6. erewrite decomposeSpec in H5; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply Fork with (d:=H5); eauto. eapply multi_step. 
    eapply PopFork; auto. rewrite app_nil_l. simpl. auto. constructor. split. 
    rewrite eraseSpecHeap. auto. rewrite eraseUnionComm. apply eraseSpecPool in H.
    subst. simpl. rewrite eraseFill. repeat rewrite eraseSpecTerm. 
    rewrite eraseSpecCtxt. auto. }
  }
  {apply specUnionComm in H0. invertHyp. inv H0. 
   {pFalseDecomp. }
   {inv H5. erewrite decomposeSpec in H7; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply Get with (d:=H7); eauto. eapply specHeapLookupFull; eauto.
    eapply multi_step. eapply PopRead. rewrite app_nil_l; simpl. auto. auto. 
    Focus 2. erewrite HeapLookupReplace; eauto. repeat rewrite app_nil_l. 
    rewrite app_nil_r. eauto. eapply specHeapLookupFull; eauto. introsInv. auto.
    rewrite replaceOverwrite. constructor. split. rewrite replaceSame. 
    Focus 2. simpl. eapply specHeapLookupFull; eauto. rewrite eraseSpecHeap; auto. 
    rewrite eraseUnionComm. simpl. rewrite eraseFill. simpl. rewrite eraseSpecTerm. 
    rewrite eraseSpecCtxt. apply eraseSpecPool in H; subst. auto. }
  }
  {apply specUnionComm in H0. invertHyp. inv H0. 
   {pFalseDecomp. }
   {inv H6. erewrite decomposeSpec in H3; eauto. econstructor. econstructor. split. 
    eapply multi_step. eapply Put with (d:=H3); eauto. eapply specHeapLookupEmpty; eauto.
    eapply multi_step. eapply PopWrite. rewrite app_nil_l; simpl. auto. auto. 
    Focus 2. auto. Focus 2. constructor. erewrite HeapLookupReplace; eauto. 
    eapply specHeapLookupEmpty; eauto. split. rewrite replaceOverwrite. Focus 2. 
    rewrite eraseUnionComm. simpl. rewrite eraseFill. simpl. rewrite eraseSpecCtxt. 
    apply eraseSpecPool in H; subst. auto. eapply specHeapWriteEq; eauto. }
  }
  {apply specUnionComm in H0. invertHyp. inv H0. 
   {pFalseDecomp. }
   {inv H5. erewrite decomposeSpec in H6; eauto. econstructor. econstructor. split. 
    eapply multi_step. copy H6. apply decomposeEq in H0. rewrite H0. 
    eapply New with (d:=H6)(x:=x); eauto. 
    eapply multi_step. eapply PopNewEmpty. rewrite app_nil_l; simpl. auto. 
    erewrite lookupExtend; eauto. auto. constructor. split. Focus 2. 
    rewrite eraseUnionComm. simpl. rewrite eraseFill. simpl. rewrite eraseSpecCtxt. 
    apply eraseSpecPool in H; subst. auto. destruct PH. simpl. apply rawHeapsEq. 
    rewrite <- beq_nat_refl. simpl. unfold raw_extend. rewrite raw_eraseSpecHeap. 
    auto. }
  }
  Grab Existential Variables. apply specHeapLookupNone; auto. 
Qed. 

Theorem nonspecImpliesSpecStar : forall PH PH' PT PT' T,
        pmultistep PH PT (Some(PH', PT')) ->
        speculate PT T -> 
        exists H' T',
          multistep (specHeap PH) T (Some(H', T')) /\
          eraseHeap H' = PH' /\ erasePool T' = PT'.
Proof.
  intros. generalize dependent T. remember (Some(PH',PT')). induction H; intros.  
  {inv Heqo. econstructor. econstructor. split. constructor. split.
   rewrite eraseSpecHeap; auto. inv H0; auto. 
   {simpl. rewrite eraseSpecTerm. apply eraseSpecPool in H1. subst. auto. }
   {simpl. rewrite eraseSpecTerm. apply eraseSpecPool in H1. subst. auto. }
  }
  {eapply nonspecImpliesSpec in H0; eauto. invertHyp. 



