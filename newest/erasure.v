Require Export unspec. 

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
    |done e => pdone (eraseTerm e)
  end. 

Fixpoint raw_eraseHeap (h:rawHeap ivar_state) : rawHeap pivar_state :=
   match h with
     | nil => []
     | (i, sempty COMMIT)::H' => (i, pempty) :: raw_eraseHeap H'
     | (i, sempty SPEC)::H' => raw_eraseHeap H'
     | (i, sfull COMMIT _ COMMIT _ N)::H' => (i, pfull (eraseTerm N))::raw_eraseHeap H'
     | (i, sfull COMMIT _ SPEC _ _)::H' => (i, pempty)::raw_eraseHeap H'
     | (i, sfull SPEC _ _ _ _) :: H' => raw_eraseHeap H'
   end. 

Theorem eraseUnique : forall H S,
                        unique ivar_state S H ->
                        unique pivar_state S (raw_eraseHeap H). 
Proof.
  induction H; intros. 
  {simpl. constructor. }
  {simpl. destruct a. 
   {destruct i0. 
    {inv H0. destruct s; eauto. eapply uniqueSubset; eauto. constructor. auto. }
    {inv H0. destruct s. eapply uniqueSubset; eauto. constructor. auto. destruct s0. 
     constructor; auto. constructor; auto. }
   }
  }
Qed. 

Definition eraseHeap H := 
  match H with
      heap_ h' prf => heap_ pivar_state (raw_eraseHeap h')
                            (eraseUnique h' (Ensembles.Empty_set AST.id) prf)
  end. 

Definition eraseThread (t:thread) :=
  match t with
      |(tid,unlocked nil,s2,M) => pSingle (eraseTerm M)
      |(tid,unlocked (a::b),s2,M) => pSingle(eraseTerm(getTrm(last (a::b) a)))
      |(tid,locked l, s2, M) => Empty_set ptrm
      |(tid,specStack l N, s2, M) => Empty_set ptrm
  end. 

Fixpoint erasePool (T:pool) :=
  match T with
      |t::ts => eraseThread t++erasePool ts
      |nil => nil
  end. 

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

(*------------------------------------Theorems------------------------------------*)

Theorem raw_eraseUnspecHeapIdem : forall H, raw_eraseHeap (raw_unspecHeap H) = raw_eraseHeap H. 
Proof.
  induction H; intros. 
  {auto. }
  {simpl in *. destruct a. destruct i0. 
   {simpl. destruct s. auto. simpl. rewrite IHlist; auto. }
   {destruct s; auto. destruct s0. simpl. rewrite IHlist; auto. simpl. 
    rewrite IHlist; auto. }
  }
Qed. 

(*Erasure is idempotent with respect to unspeculate*)
Theorem eraseUnspecHeapIdem : forall H, eraseHeap (unspecHeap H) = eraseHeap H. 
Proof.
  intros. destruct H. simpl. apply rawHeapsEq. apply raw_eraseUnspecHeapIdem. 
Qed. 

Ltac decompErase :=
  match goal with
      |H:decompose ?t ?E ?e |- _ => apply decomposeEq in H; subst; auto
  end. 

Theorem eraseUnionComm : forall T1 T2, 
                erasePool(tUnion T1 T2) = pUnion (erasePool T1)(erasePool T2). 
Proof.
  induction T1; intros. 
  {simpl. auto. }
  {simpl. destruct a. destruct p. destruct p. destruct a; simpl; auto. 
   destruct l0. rewrite IHT1; eauto. simpl. rewrite IHT1; eauto. }
Qed. 

Theorem eraseUnspecPoolAuxEq : forall T, erasePool (unspecPool T) = 
                                         erasePool T. 
Proof.
  induction T; intros. 
  {simpl. auto. }
  {simpl. rewrite eraseUnionComm. destruct a. destruct p. destruct p. 
   destruct a; simpl; auto. destruct l0; simpl. rewrite IHT; auto. 
   rewrite IHT; eauto. }
Qed. 

Ltac applyHyp :=
  match goal with
      |H : forall a : _, ?X -> ?Y, H' : ?Z |- _ => apply H in H'
  end. 

Theorem eraseFill : forall E e, 
                           eraseTerm (fill E e) = (pfill (eraseCtxt E) (eraseTerm e)). 
Proof.
  induction E; intros; try solve[simpl; rewrite IHE; auto]; auto. 
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
  {exists (done x). auto. }
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
  
Theorem eThread : forall t', exists t, eraseThread t = (pSingle t').
Proof.
  induction t'; match goal with
      | |- exists t, eraseThread t = (pSingle ?M) => 
        assert(E:exists M', eraseTerm M' = M) by apply eTerm; 
          inversion E as [Ex1 Ex2];
          rewrite <- Ex2; exists (nil,unlocked nil,nil,Ex1); auto
  end. 
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

Theorem eraseLastAct : forall A s2 M M' tid,
                         actionTerm A M' ->
                         eraseThread (tid, unlocked[A], s2, M) =
                          eraseThread (tid, unlocked nil, s2, M'). 
Proof.
  intros. inv H; auto. 
Qed. 

Theorem eraseTwoActs : forall tid tid' A1 A2 As s2 M M',
                         eraseThread (tid, aCons A1 (aCons A2 As), s2, M') =
                         eraseThread (tid', (aCons A2 As), s2, M) . 
Proof.
  intros. destruct As; simpl; auto. 
  destruct l; auto. erewrite getLastNonEmpty. eauto. 
Qed. 

Theorem eraseOpenComm : forall e e' n, eraseTerm (open n e e') = popen n (eraseTerm e) (eraseTerm e'). 
Proof.
  induction e'; auto; try solve[intros; simpl; rewrite IHe'1; rewrite IHe'2; auto]; 
  try solve[intros; simpl; rewrite IHe'; auto].
  {intros. simpl. destruct (beq_nat n i); auto. }
Qed. 

Theorem raw_eraseHeapDependentRead : forall H x sc ds s w N ds',
                raw_heap_lookup x H = Some(sfull sc ds s w N) ->
                raw_eraseHeap(raw_replace x (sfull sc ds' s w N) H) = raw_eraseHeap H. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {simpl. apply beq_nat_true in eq. subst. inv H0. destruct sc; auto. }
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

Theorem raw_eraseHeapWrite : forall H x sc TID N ds, 
                               raw_heap_lookup x H = Some(sempty sc) ->
                               raw_eraseHeap (raw_replace x (sfull sc ds SPEC TID N) H) = raw_eraseHeap H. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq.
   {inv H0. apply beq_nat_true in eq. subst.  destruct sc; auto. }
   {simpl. erewrite IHlist; eauto. }
  }
Qed.  

Theorem eraseHeapWrite : forall H x sc TID N ds, 
                               heap_lookup x H = Some(sempty sc) ->
                               eraseHeap (replace x (sfull sc ds SPEC TID N) H) = eraseHeap H. 
Proof.
  intros. destruct H; simpl in *. apply rawHeapsEq. apply raw_eraseHeapWrite. auto. 
Qed. 

Theorem eraseHeapNew : forall x H p,
                         eraseHeap (Heap.extend x (sempty SPEC) H p) =
                         eraseHeap H.                  
Proof.
  intros. destruct H. simpl in *.  eapply rawHeapsEq. auto. 
Qed. 

Theorem listAlign2 : forall (T:Type) b a, exists (c : list T) d, a::b = c++[d]. 
Proof.
  induction b; intros. 
  {eauto. }
  {specialize (IHb a). invertHyp. rewrite H0. exists (a0::x). exists x0. auto. }
Qed. 

Ltac alignTac a b := assert(exists c d, a::b = c++[d]) by apply listAlign2; invertHyp.
 
Theorem unspecSpecStep : forall H t H' T t', 
                           spec_step H T t H' T t' ->  
                           unspecHeap H = unspecHeap H' /\ unspecPool t' = unspecPool t. 
Proof.
  intros. inversion H0; subst.
  {split; eauto. inv H2; simpl; eauto. }
  {split; auto. destruct b; simpl; auto. destruct l; auto.
   erewrite getLastNonEmpty'. simpl. eauto. }
  {split. symmetry. eapply unspecHeapRBRead; eauto. destruct b; simpl; auto. 
   destruct l; auto. erewrite getLastNonEmpty'; simpl; eauto. }
  {split. symmetry. eapply unspecHeapAddWrite; eauto. destruct b; simpl; auto. 
   destruct l; auto. erewrite getLastNonEmpty'; simpl; eauto. }
  {split. symmetry. eapply unspecHeapExtend; eauto. destruct b; simpl; auto. 
   destruct l; auto. erewrite getLastNonEmpty'; simpl; eauto. }
  {split; auto. destruct b; simpl; auto. destruct l; auto. 
   erewrite getLastNonEmpty'; simpl; eauto. }
  Grab Existential Variables. auto. auto. auto. auto. auto. 
Qed. 

Theorem specSingleStepErase : forall H T H' T' P,
                                spec_step H P T H' P T' -> 
                                erasePool T' = erasePool T /\ 
                                eraseHeap H' = eraseHeap H .
Proof.
  intros.
  inversion H0; subst. 
  {split; auto. inv H2; simpl; auto. }
  {split; auto. destruct b; simpl; auto. destruct l; auto. erewrite getLastNonEmpty'. 
   simpl; eauto. }
  {split. destruct b; simpl; auto. destruct l; auto. erewrite getLastNonEmpty'; simpl; auto. 
   erewrite eraseHeapDependentRead; eauto. }
  {split. destruct b; simpl; auto. destruct l; auto.
   erewrite getLastNonEmpty'; simpl; auto. erewrite eraseHeapWrite; eauto. }
  {split. destruct b; simpl; auto. destruct l; auto. 
   erewrite getLastNonEmpty'; simpl; auto. erewrite eraseHeapNew; eauto. }
  {split; auto. destruct b; simpl; auto. destruct l; auto. 
   erewrite getLastNonEmpty'; simpl; auto. }
  Grab Existential Variables. auto. auto. auto. auto. auto. 
Qed. 

Theorem spec_multistepErase : forall H T H' T',
                                spec_multistep H T H' T' -> erasePool T = erasePool T' /\
                                eraseHeap H = eraseHeap H'. 
Proof. 
  intros. induction H0; subst; auto; intros. 
  eapply specSingleStepErase in H. invertHyp. split. rewrite eraseUnionComm. 
  rewrite <- H3. rewrite <- eraseUnionComm. auto. rewrite <- H4. rewrite H2. 
  auto. 
Qed. 

Theorem raw_lookupEraseSpecFull : forall x H ds tid N, 
                                raw_heap_lookup x H = Some(sfull COMMIT ds SPEC tid N) ->
                                raw_heap_lookup x (raw_eraseHeap H) = Some pempty. 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct s. erewrite IHlist; eauto. simpl. rewrite eq. 
    erewrite IHlist; eauto. destruct s. eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupEraseSpecFull : forall x H ds tid N, 
                                heap_lookup x H = Some(sfull COMMIT ds SPEC tid N) ->
                                heap_lookup x (eraseHeap H) = Some pempty. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseSpecFull. eauto. 
Qed.  
 
Theorem raw_eraseHeapCommitWrite : forall H x ds t N,
                                 raw_heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                                 raw_eraseHeap(raw_replace x (sfull COMMIT ds COMMIT t N) H) = 
                                 raw_replace x (pfull (eraseTerm N)) (raw_eraseHeap H). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {simpl. erewrite IHlist; eauto. destruct i0. destruct s; auto.  simpl. rewrite eq. 
    auto. destruct s;auto. destruct s0; simpl; rewrite eq; auto. }
  }
Qed. 

Theorem eraseHeapCommitWrite : forall H x ds t N,
                                 heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                                 eraseHeap(replace x (sfull COMMIT ds COMMIT t N) H) = 
                                 replace x (pfull (eraseTerm N)) (eraseHeap H). 
Proof.
  intros. destruct H; simpl. apply rawHeapsEq. eapply raw_eraseHeapCommitWrite; eauto. 
Qed. 

Theorem raw_lookupEraseCommitFull : forall x H ds tid N, 
       raw_heap_lookup x H = Some(sfull COMMIT ds COMMIT tid N) ->
       raw_heap_lookup x (raw_eraseHeap H) = Some (pfull (eraseTerm N)). 
Proof.
  induction H; intros.  
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq. auto. }
   {destruct i0. destruct s. eauto. simpl. rewrite eq. eauto. destruct s. 
    eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupEraseCommitFull : forall x H ds tid N, 
       heap_lookup x H = Some(sfull COMMIT ds COMMIT tid N) ->
       heap_lookup x (eraseHeap H) = Some (pfull (eraseTerm N)). 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseCommitFull; eauto. 
Qed. 

Theorem raw_lookupUnspecSpecFullEmpty : forall x H ds t N,
                                          raw_heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                                          raw_heap_lookup x (raw_unspecHeap H) = Some(sempty COMMIT). 
Proof.
  induction H; intros. 
  {inv H. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H0. simpl. rewrite eq; auto. }
   {destruct i0. destruct s; eauto. simpl. rewrite eq; eauto. 
    destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
  }
Qed. 

Theorem lookupUnspecSpecFullEmpty : forall x H ds t N,
                                          heap_lookup x H = Some(sfull COMMIT ds SPEC t N) ->
                                          heap_lookup x (unspecHeap H) = Some(sempty COMMIT). 
Proof.
  intros. destruct H; simpl. eapply raw_lookupUnspecSpecFullEmpty; eauto. 
Qed. 

 

Theorem raw_eraseHeapCommitNewFull : forall x ds t N H S,
                                   unique ivar_state S H -> 
                                   raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                   raw_eraseHeap (raw_replace x (sfull COMMIT ds SPEC t N) H) =
                                   raw_extend x pempty (raw_eraseHeap H).
Proof.
  intros. apply heapExtensionality. genDeps{S; N; t; ds; x; H}. induction H; intros. 
  {inv H1. } 
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. simpl. destruct (beq_nat x0 x) eqn:eq2; auto. }
   {simpl. destruct (beq_nat x0 x) eqn:eq2; eauto.
    {destruct i0. destruct s. erewrite IHlist. rewrite eq2. auto. 
     auto. inv H0;  eauto. apply beq_nat_true in eq2. subst. simpl. rewrite eq. inv H0.
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. eauto. 
     destruct s. inv H0. eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. 
     eauto. destruct s0. apply beq_nat_true in eq2. subst. simpl. rewrite eq. inv H0. 
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. eauto. 
     simpl. apply beq_nat_true in eq2. subst. rewrite eq. inv H0. 
     eapply IHlist with(x0:=x) in H1; eauto. rewrite <- beq_nat_refl in H1. auto. }
    {destruct i0. destruct s. inv H0. eapply IHlist with(x0:=x0)in H1; eauto. 
     rewrite eq2 in H1. auto. simpl. destruct (beq_nat x0 i)eqn:eq3; auto. 
     inv H0. eapply IHlist with(x0:=x0)in H1. rewrite eq2 in H1. auto. eauto.
     destruct s. inv H0. eapply IHlist with(x0:=x0) in H1. rewrite eq2 in H1. auto. 
     eauto. destruct s0. simpl. destruct (beq_nat x0 i) eqn:eq3; auto. 
     eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. auto. inv H0; eauto. 
     simpl. destruct (beq_nat x0 i); auto. eapply IHlist with(x0:=x0) in H1. 
     rewrite eq2 in H1. auto. inv H0; eauto. }
   }
  }
Qed. 

Theorem eraseHeapCommitNewFull : forall x ds t N H p,
                                   heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                   eraseHeap (replace x (sfull COMMIT ds SPEC t N) H) =
                                   Heap.extend x pempty (eraseHeap H) p.
Proof.
  intros. destruct H. simpl in *. apply rawHeapsEq. eapply raw_eraseHeapCommitNewFull; eauto. 
Qed.

Theorem raw_eraseHeapCommitNewEmpty : forall x S H,
                                   unique ivar_state S H -> 
                                   raw_heap_lookup x H = Some(sempty SPEC) ->
                                   raw_eraseHeap (raw_replace x (sempty COMMIT) H) =
                                   raw_extend x pempty (raw_eraseHeap H).
Proof.
  intros. apply heapExtensionality. genDeps{S; x; H}. induction H; intros. 
  {inv H1. }
  {simpl in H1. simpl. destruct a. destruct (beq_nat x i)eqn:eq. 
   {inv H1. destruct (beq_nat x0 x) eqn:eq2. simpl. rewrite eq2. auto. simpl. rewrite eq2. 
    auto. }
   {simpl. destruct i0. 
    {destruct s. 
     {destruct (beq_nat x0 x) eqn:eq2. 
      {simpl in *. inv H0. eapply IHlist with(x0:=x0) in H1; eauto. rewrite eq2 in H1. 
       auto. }
      {erewrite IHlist. simpl. rewrite eq2. auto. eauto. inv H0; eauto. }
     }
     {simpl. destruct(beq_nat x0 i)eqn:eq2. 
      {apply beq_nat_true in eq2. subst. rewrite beq_nat_sym in eq. rewrite eq. auto. }
      {destruct(beq_nat x0 x) eqn:eq3.
       {eapply IHlist with(x0:=x0) in H1. simpl in *. rewrite eq3 in H1. auto. inv H0; eauto. }
       {erewrite IHlist; eauto. simpl. rewrite eq3. auto. inv H0; eauto. }
      }
     }
    }
    {destruct s. 
     {destruct (beq_nat x0 x)eqn:eq2. 
      {eapply IHlist with(x0:=x0) in H1. simpl in *. rewrite eq2 in H1. auto. inv H0; eauto. }
      {erewrite IHlist; eauto. simpl. rewrite eq2. auto. inv H0; eauto. }
     }
     {destruct s0. 
      {destruct (beq_nat x0 x) eqn:eq2. 
       {simpl. apply beq_nat_true in eq2. subst. rewrite eq.
        eapply IHlist with(x0:=x) in H1; eauto. simpl in *. rewrite <- beq_nat_refl in H1. auto. 
        inv H0; eauto. }
       {simpl. destruct (beq_nat x0 i); auto. erewrite IHlist; eauto. simpl. rewrite eq2. auto. 
        inv H0; eauto. }
      }
      {simpl. destruct (beq_nat x0 i) eqn:eq2. 
       {apply beq_nat_true in eq2. subst. rewrite beq_nat_sym in eq. rewrite eq. auto. }
       {destruct (beq_nat x0 x) eqn:eq3. 
        {simpl in *. eapply IHlist with(x0:=x0) in H1. rewrite eq3 in H1. eauto. inv H0; eauto. }
        {erewrite IHlist; eauto. simpl. rewrite eq3. auto. inv H0; eauto. }
       }
      }
     }
    }
   }
  }
Qed. 

Theorem eraseHeapCommitNewEmpty : forall x H p,
                                   heap_lookup x H = Some(sempty SPEC) ->
                                   eraseHeap (replace x (sempty COMMIT) H) =
                                   Heap.extend x pempty (eraseHeap H) p.
Proof.
  intros. destruct H. simpl in *. apply rawHeapsEq. eapply raw_eraseHeapCommitNewEmpty; eauto. 
Qed.

Theorem uniqueLookupNone : forall (T:Type) x H S, 
                            unique T S H -> Ensembles.In (AST.id) S x ->
                            raw_heap_lookup x H = None. 
Proof.
  induction H; intros. 
  {auto. }
  {inv H0. simpl. assert(x <> m). intros c. subst. contradiction.
   apply beq_nat_false_iff in H0. rewrite H0. eapply IHlist; eauto.
   constructor. auto. }
Qed. 

Theorem raw_lookupNoneBoth : forall x H,
                           raw_heap_lookup x H = None ->
                           raw_heap_lookup x (raw_eraseHeap H) = None. 
Proof.
  induction H; intros; auto. simpl in *. 
  destruct a. destruct (beq_nat x i) eqn:eq. 
  {inv H0. }
  {destruct i0. destruct s; auto. simpl. rewrite eq. auto. destruct s; auto. 
   destruct s0; simpl; rewrite eq; auto. }
Qed. 
 
Theorem raw_lookupEraseSpecNone : forall x H t S N ds,
                                    unique ivar_state S H ->
                                    raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                    raw_heap_lookup x (raw_eraseHeap H) = None. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. inv H0. eapply uniqueLookupNone in H6. Focus 2. 
    apply Ensembles.Union_intror. constructor. apply raw_lookupNoneBoth. 
    apply beq_nat_true in eq. subst. auto. }
   {destruct i0. 
    {destruct s. inv H0. eauto. simpl. rewrite eq. inv H0. eauto. }
    {destruct s; auto. inv H0; eauto. inv H0. destruct s0; simpl; rewrite eq; eauto. }
   }
  }
Qed.

Theorem lookupEraseSpecNone : forall x H t N ds,
                                heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                heap_lookup x (eraseHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseSpecNone; eauto. 
Qed.

Theorem raw_lookupEraseSpecNoneEmpty : forall x H S,
                                    unique ivar_state S H ->
                                    raw_heap_lookup x H = Some(sempty SPEC) ->
                                    raw_heap_lookup x (raw_eraseHeap H) = None. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. inv H0. eapply uniqueLookupNone in H6. Focus 2. 
    apply Ensembles.Union_intror. constructor. apply raw_lookupNoneBoth. 
    apply beq_nat_true in eq. subst. auto. }
   {destruct i0.  
    {destruct s. inv H0; eauto. simpl. rewrite eq. inv H0; eauto. }
    {inv H0. destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
   }
  }
Qed.

Theorem lookupEraseSpecNoneEmpty : forall x H,
                                heap_lookup x H = Some(sempty SPEC) ->
                                heap_lookup x (eraseHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupEraseSpecNoneEmpty; eauto. 
Qed.  

Theorem raw_lookupUnspecNoneBoth : forall x H,
                           raw_heap_lookup x H = None ->
                           raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof.
  induction H; intros; auto. simpl in *. 
  destruct a. destruct (beq_nat x i) eqn:eq. 
  {inv H0. }
  {destruct i0. destruct s; eauto. simpl. rewrite eq; eauto. destruct s. eauto. 
   destruct s0; simpl; rewrite eq; eauto. }
Qed. 

Theorem raw_lookupUnspecSpecNone : forall x H t S N ds,
                                    unique ivar_state S H ->
                                    raw_heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                    raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1.  inv H0. eapply uniqueLookupNone in H6. Focus 2. 
    apply Ensembles.Union_intror. constructor. apply raw_lookupUnspecNoneBoth. 
    apply beq_nat_true in eq. subst. auto. }
   {destruct i0. 
    {inv H0. destruct s; eauto. simpl. rewrite eq. eauto. }
    {inv H0. destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
   }
  }
Qed. 

Theorem lookupUnspecSpecNone : forall x H t N ds,
                                heap_lookup x H = Some(sfull SPEC ds SPEC t N) ->
                                heap_lookup x (unspecHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupUnspecSpecNone; eauto. 
Qed. 

Theorem raw_lookupUnspecSpecEmptyNone : forall x H S,
                                    unique ivar_state S H ->
                                    raw_heap_lookup x H = Some(sempty SPEC) ->
                                    raw_heap_lookup x (raw_unspecHeap H) = None. 
Proof.
  induction H; intros. 
  {inv H0. }
  {simpl in *. destruct a. destruct (beq_nat x i) eqn:eq. 
   {inv H1. inv H0. eapply uniqueLookupNone in H6. Focus 2. 
    apply Ensembles.Union_intror. constructor. apply raw_lookupUnspecNoneBoth. 
    apply beq_nat_true in eq. subst. auto. }
   {destruct i0. 
    {inv H0. destruct s; eauto. simpl. rewrite eq. eauto. }
    {inv H0. destruct s; eauto. destruct s0; simpl; rewrite eq; eauto. }
   }
  }
Qed. 

Theorem lookupUnspecSpecEmptyNone : forall x H,
                                heap_lookup x H = Some(sempty SPEC) ->
                                heap_lookup x (unspecHeap H) = None. 
Proof.
  intros. destruct H. simpl. eapply raw_lookupUnspecSpecEmptyNone; eauto. 
Qed. 
