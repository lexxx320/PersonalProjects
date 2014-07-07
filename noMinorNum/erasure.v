Require Import AST.  
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import SfLib. 
Require Import Heap. 
Require Import sets. 
Require Import hetList.

(*Updates bound variables for erasure of spec return*)
Fixpoint incBV (k:nat) (t:ptrm) : ptrm :=
  match t with
      |pbvar i => if negb(ble_nat i k) then pbvar (S i) else pbvar i
      |ppair e1 e2 => ppair (incBV k e1) (incBV k e2)
      |plambda e => plambda (incBV (S k) e)
      |papp e1 e2 => papp (incBV k e1) (incBV k e2)
      |pret e => pret (incBV k e)
      |pbind e1 e2 => pbind (incBV k e1) (incBV k e2)
      |pfork e => pfork (incBV k e)
      |pput i e => pput (incBV k i) (incBV k e)
      |pget i => pget (incBV k i)
      |praise e => praise (incBV k e)
      |phandle e1 e2 => phandle (incBV k e1) (incBV k e2)
      |pdone e => pdone (incBV k e)
      |pfst e => pfst (incBV k e)
      |psnd e => psnd (incBV k e)
      |_ => t
  end. 

Inductive eraseTerm : trm -> ptrm -> Prop :=
|eraseFVar : forall i, eraseTerm (fvar i) (pfvar i)
|eraseBVar : forall i, eraseTerm (bvar i) (pbvar i)
|eraseUnit : eraseTerm unit punit
|erasePair : forall t1 t1' t2 t2', eraseTerm t1 t1' -> eraseTerm t2 t2' ->
                                     eraseTerm (pair_ t1 t2) (ppair t1' t2')
|eraseLambda : forall e e', eraseTerm e e' -> 
                              eraseTerm (lambda e) (plambda e')
|eraseApp : forall e1 e1' e2 e2', eraseTerm  e1 e1' -> eraseTerm  e2 e2' ->
                                    eraseTerm  (AST.app e1 e2) (papp e1' e2')
|eraseRet : forall e e', eraseTerm e e' -> eraseTerm  (ret e) (pret e')
|eraseBind : forall e1 e1' e2 e2', eraseTerm  e1 e1' -> eraseTerm  e2 e2' ->
                                     eraseTerm  (bind e1 e2) (pbind e1' e2')
|eraseFork : forall e e' , eraseTerm  e  e' -> eraseTerm  (fork e)  (pfork e')
|eraseNew : eraseTerm  new  pnew
|erasePut : forall e e' i  i', eraseTerm  e  e' -> eraseTerm  i  i' ->
                                eraseTerm  (put i e)  (pput i' e')
|eraseGet : forall i i' , eraseTerm  i  i' -> eraseTerm  (get i)  (pget i')
|eraseRaise : forall e e' , eraseTerm  e  e' -> eraseTerm  (raise e)  (praise e')
|eraseHandle : forall e1 e1' e2 e2' , eraseTerm  e1  e1' -> eraseTerm  e2  e2' ->
                                       eraseTerm  (handle e1 e2)  (phandle e1' e2')
|eraseDone : forall e e' , eraseTerm  e  e' -> eraseTerm  (done e)  (pdone e')
|eraseFst : forall e e' , eraseTerm e  e' -> eraseTerm (fst e)  (pfst e')
|eraseSnd : forall e e' , eraseTerm e  e' -> eraseTerm (snd e)  (psnd e')
|eraseSpec : forall e1 e1' e2 e2' , 
               eraseTerm e1  e1' -> eraseTerm  e2  e2' -> 
               eraseTerm (spec e1 e2)  
                         (pbind e1' (plambda (pbind (incBV 1 e2') (plambda (pret (ppair (pbvar 0) (pbvar 1)))))))
|eraseSpecReturn : forall e e' N0 N', 
                     eraseTerm e e' -> eraseTerm N0 N' ->
                     eraseTerm  (specReturn e N0)
                     (pbind e' (plambda (pbind (incBV 1 N')
                        (plambda (pret (ppair (pbvar 0) (pbvar 1)))))))
|eraseSpecJoin : forall e e' M M', (*specJoin e M = M >>= \x. ret(e, x)*)
                     eraseTerm e e' -> eraseTerm M M' -> 
                     eraseTerm  (specJoin e M)
                                (pbind M' (plambda (pret (ppair e' (pbvar 0))))).

Hint Constructors eraseTerm. 

Inductive eraseHeap : sHeap -> pHeap -> Prop :=
|eraseSE : forall (h :sHeap) (h':pHeap) (i:AST.id) hd tl,
             eraseHeap h h' -> eraseHeap ((i, sempty (hd::tl)) :: h) h'
|eraseCE : forall h h' i ,
             eraseHeap h h' -> eraseHeap ((i, sempty nil)::h) ((i, pempty)::h')
|eraseSF : forall h h' i hd tl d s t N,
             eraseHeap h h' -> eraseHeap ((i, sfull (hd::tl) d s t N)::h) h'
|eraseCCSF : forall h h' i d hd tl t M,
               eraseHeap h h' -> 
               eraseHeap ((i, sfull nil d (hd::tl) t M)::h) ((i, pempty)::h')
|eraseCCCF : forall h h' i d t M M',
               eraseHeap h h' -> eraseTerm M M' ->
               eraseHeap ((i, sfull nil d nil t M)::h) ((i, pfull M')::h')
|eraseNil : eraseHeap nil nil.

Hint Constructors eraseHeap. 

Inductive eraseThread : thread -> pPool -> Prop :=
|tEraseCommit : forall tid s2 M M', eraseTerm M M' ->
                                    eraseThread (tid, nil, s2, M) (pSingleton  M')
|tEraseRead : forall tid s1 s1' s2 x M M' M'' E,
               s1 = s1' ++ [rAct x M'] -> eraseTerm M' M'' ->
               decompose M' E (get (fvar x)) -> 
               eraseThread (tid, s1, s2, M) (pSingleton M'')
|tEraseWrite : forall tid M M' M'' x s1 s2 s1' E N,
                s1 = s1' ++ [wAct x M'] -> eraseTerm M' M'' ->
                decompose M' E (put (fvar x) N) -> eraseThread (tid, s1, s2, M) (pSingleton M'')
|tEraseNew : forall tid M M' M'' x s1 s2 s1' E,
              s1 = s1' ++ [cAct x M'] -> eraseTerm M' M'' ->
              decompose M' E new -> eraseThread (tid, s1, s2, M) (pSingleton M'')
|tEraseFork : forall tid M M' M'' s1 s2 s1' E N,
                s1 = s1' ++ [fAct M'] -> eraseTerm M' M'' ->
                decompose M' E (fork N) -> eraseThread (tid, s1, s2, M) (pSingleton M'')
|tEraseSpecRet : forall tid M M' M'' s1 s2 s1' E N N',
                s1 = s1' ++ [specRetAct M'] -> eraseTerm M' M'' ->
                decompose M' E (spec N N') -> eraseThread (tid, s1, s2, M) (pSingleton M'')
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

Theorem erasureTotal : forall t, exists t', eraseTerm t t'. 
Proof.
  induction t; intros; try solve[repeat econstructor]; try solve[
  invertExists; repeat econstructor; eauto]. 
Qed. 

Axiom erasePoolEraseThread : forall T T' t, erasePool T T' -> tIn T t -> 
                                              exists t', eraseThread t t'. 


(*Erasure is idempotent with respect to unspeculate*)
Theorem eraseUnspecHeapIdem : 
  forall H H' H'', unspecHeap H H' -> eraseHeap H' H'' -> eraseHeap H H''. 
Proof. 
  intros.   
  {generalize dependent H''.  
   induction H0; intros; eauto. 
   {inversion H1; subst. apply IHunspecHeap in H4. constructor. assumption. }
   {inversion H1; subst. apply IHunspecHeap in H4. constructor. assumption. }
   {inversion H1; subst. apply IHunspecHeap in H7. constructor. assumption. 
    assumption. }
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
   inversion H4; subst. cleanup. econstructor. econstructor. eassumption.
   reflexivity. Focus 2. eassumption. inversion H5; subst. 
   {assumption. }
   {inversion H1; subst; try invertListNeq. 
    {eapply tEraseRead. auto. decompErase. eauto. }
   }
   {inversion H1; subst; try invertListNeq. eapply tEraseWrite; eauto. }
   {inversion H1; subst; try invertListNeq. eapply tEraseNew; eauto. }
   {inversion H1; subst; try invertListNeq. eapply tEraseFork; eauto. }
   {inversion H1; subst; try invertListNeq. eapply tEraseSpecRet; eauto. }
  }
  {inversion H; subst. inversion H0; subst. cleanup. inversion H1; subst. 
   {econstructor. econstructor. econstructor. eassumption. constructor. 
    auto. eassumption. assumption. }
   {do 2 econstructor; eauto. econstructor. eassumption. eapply unspecRead; eauto.
    decompErase. inversion H2; subst. auto. }
   {do 2 econstructor; eauto. econstructor. eassumption. eapply unspecWrite; eauto.
    decompErase. inversion H2; subst. auto. }
   {do 2 econstructor; eauto. econstructor. eassumption. eapply unspecCreate; eauto.
    decompErase. inversion H2; subst. auto. }
   {do 2 econstructor; eauto. econstructor. eassumption. eapply unSpecFork; eauto. 
    decompErase. inversion H2; subst; auto. }
   {do 2 econstructor; eauto. econstructor. eassumption. eapply unSpecSpecret; eauto.
    inversion H2; subst. auto. }
   {inversion H2. }
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

Theorem lastElementEq : forall (T:Type) s1 s2 (e1 e2 : T), s1 ++ [e1] = s2 ++ [e2] -> e1 = e2. 
Proof.
  intros. generalize dependent s2. induction s1; intros. 
  {destruct s2. inversion H. reflexivity. inversion H. destruct s2; inversion H2. }
  {destruct s2. inversion H. destruct s1; inversion H2. inversion H. 
   apply IHs1 in H2. assumption. } Qed. 

Axiom uniqueThreadPool : forall T tid t t', 
                           thread_lookup T tid t -> thread_lookup T tid t' -> t = t'. 

Theorem termErasureDeterminism : forall M M1 M2,
                                   eraseTerm M M1 -> eraseTerm M M2 -> M1 = M2. 
Proof.
  intros. generalize dependent M2. induction H; intros; try solve[ 
  inversion H0; subst; auto]; try solve[ 
  try(inversion H1);try(inversion H0); subst; repeat 
  match goal with
    |H:forall M, eraseTerm ?t M -> ?t1=M, H':eraseTerm ?t ?t1, 
    H'':eraseTerm ?t ?y |- _ =>
  apply H in H''; clear H
  end; subst; auto]. 
Qed. 

Theorem erasureDeterminism : forall t t1' t2', 
                               eraseThread t t1' -> 
                               eraseThread t t2' -> t1' = t2'.
Proof.
  intros. induction H; inversion H0;subst;
  try(match goal with
               |H:eraseTerm ?M ?x, H':eraseTerm ?M ?y |- _ =>
                eapply termErasureDeterminism in H; eauto; subst; auto
               |H:[] = [] ++ [?x] |- _ => inversion H       
               |H:[] = ?x ++ [?y] |- _ => destruct x; inversion H
               |H:?s1++[?x]=?s2++[?y]|-_ => apply lastElementEq in H; inversion H
             end);
  try(subst; eapply termErasureDeterminism in H12;[rewrite <-H12; reflexivity| auto]); eauto.
  {subst. eapply termErasureDeterminism in H9; eauto; subst; auto. }
  {subst. eapply termErasureDeterminism in H9; eauto; subst; auto. }
  {subst. eapply termErasureDeterminism in H9; eauto; subst; auto. }
  {subst. eapply termErasureDeterminism in H9; eauto; subst; auto. }
  {subst. eapply termErasureDeterminism in H9; eauto; subst; auto. }
Qed. 
  
Theorem eraseHeapDeterminism : forall h h1 h2, 
                                 eraseHeap h h1 -> eraseHeap h h2 ->
                                 h1 = h2. 
Proof.
  intros. generalize dependent h2. induction H; intros. 
  {inversion H0. subst. apply IHeraseHeap in H6. assumption. }
  {inversion H0. subst. apply IHeraseHeap in H4. subst. reflexivity. }
  {inversion H0; subst. apply IHeraseHeap in H10. assumption. }
  {inversion H0. subst. apply IHeraseHeap in H9. subst. reflexivity. }
  {inversion H1. subst. apply IHeraseHeap in H8. subst. 
   eapply termErasureDeterminism in H0. rewrite <-H0. reflexivity. assumption. }
  {inversion H0; subst. reflexivity. }
Qed. 

Inductive eraseContext : ctxt -> pctxt -> Prop :=
|eraseCtxtBind : forall N N' E E', eraseTerm N N' -> eraseContext E E' ->
                                     eraseContext (bindCtxt E N) (pbindCtxt E' N')
|eraseCtxtSpec : forall E E' N0 N0',
                   eraseContext E E' -> eraseTerm N0 N0' -> 
                   eraseContext (specReturnCtxt E N0)
                                (pbindCtxt E' (plambda (pbind (incBV 1 N0') (plambda (pret (ppair (pbvar 0)(pbvar 1)))))))
|eraseCtxtSpecJoin : forall E E' N N', (*specJoin M N = N >>= \x ret(M, x)*)
                       eraseContext E E' -> eraseTerm N N' ->
                       eraseContext (specJoinCtxt E N) 
                             (pbindCtxt E' (plambda (pret (ppair N' (pbvar 0)))))
|eraseCtxtHandle : forall N N' E E',
                     eraseTerm N N' -> eraseContext E E' ->
                     eraseContext (handleCtxt E N) (phandleCtxt E' N')
|eraseCtxtApp : forall N N' E E',
                  eraseTerm N N' -> eraseContext E E' -> 
                  eraseContext (appCtxt E N) (pappCtxt E' N')
|eraseCtxtFst : forall E E', eraseContext E E' -> eraseContext (fstCtxt E) (pfstCtxt E')
|eraseCtxtSnd : forall E E', eraseContext E E' -> eraseContext (sndCtxt E) (psndCtxt E')
|eraseCtxtHole : eraseContext holeCtxt pholeCtxt
.
 
Theorem ctxtErasureDeterminism : forall E E1 E2, eraseContext E E1 -> 
                                                  eraseContext E E2 -> E1 = E2. 
Proof.
  intros. generalize dependent E2. induction H; intros; try solve[ 
  inversion H1; subst; eapply termErasureDeterminism in H; eauto; subst; 
  apply IHeraseContext in H6; subst; auto]. 
  {inversion H1; subst. eapply termErasureDeterminism in H0; eauto; subst. 
   apply IHeraseContext in H4. subst. auto. }
  {inversion H1; subst. eapply termErasureDeterminism in H0; eauto; subst. 
   apply IHeraseContext in H4. subst. auto. }
  {inversion H0; subst. apply IHeraseContext in H2. subst. auto. } 
  {inversion H0; subst. apply IHeraseContext in H2; subst; auto. }
  {inversion H0; subst. auto. }
Qed. 

Ltac invertHyp :=
  match goal with
      |H : exists e : _, ?x |- _ => inversion H; clear H; try subst; try invertHyp
      |H : ?x /\ ?y |- _ => inversion H; clear H; try subst; try invertHyp
      |H : eraseTerm ?M ?T ?t, H' : eraseTerm ?M ?T ?t' |- _ => 
       eapply termErasureDeterminism in H; try eassumption; try subst; try invertHyp
      |H : eraseContext ?E ?T ?E1, H' : eraseContext ?E ?T ?E2 |- _ => 
       eapply ctxtErasureDeterminism in H; try eassumption; try subst; try invertHyp
  end. 

Hint Constructors eraseContext eraseTerm.  

Theorem decomposeErase : forall E e t', 
                           eraseTerm (fill E e)  t' -> 
                           exists E' e', eraseContext E E' /\ eraseTerm e e' /\
                                         t' = pfill E' e'.
 Proof. 
  intros. remember (fill E e). generalize dependent E. generalize dependent e.
  induction H; intros; try solve[destruct E; inversion Heqt; simpl in *; subst; repeat econstructor];
  try solve[destruct E; inversion Heqt; simpl in *; subst; repeat econstructor; auto]; try solve[ 
  destruct E; inversion Heqt; simpl in *; subst; eauto; try solve[ repeat econstructor; eauto];
   match goal with
       |H:forall e E, fill ?E' ?e' = fill E e -> ?x |- _ => assert(EQ:fill E' e' = fill E' e') by auto;
                                                           apply H in EQ; invertHyp
   end; repeat econstructor; eauto].  
Qed. 

Theorem inErasure : forall t t', erasePoolAux t = Singleton ptrm t' ->
                                 Ensembles.In ptrm (erasePoolAux t) t'.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. 
  inversion H. assert(Ensembles.In ptrm (Singleton ptrm t') t') by constructor. 
  apply H1 in H2. assumption. Qed. 

Theorem eTerm : forall pt, exists t, eraseTerm t pt. 
Proof.
  induction pt; eauto; try solve[invertHyp; repeat econstructor; eauto]. 
Qed. 

Theorem eHeap : forall PH, exists H, eraseHeap H PH. 
Proof.
  induction PH; eauto. 
  {destruct a. destruct p. 
   {assert(hd:action). repeat constructor.  assert(tl:specStack). repeat constructor. 
    assert(w:tid). repeat constructor. assert(M:trm). repeat constructor. 
    inversion IHPH. exists((i, sfull nil nil (hd::tl) w M)::x). constructor. 
    assumption. }
   {inversion IHPH. assert(exists t, eraseTerm t p) by apply eTerm.  
    inversion H0. assert(t:tid). repeat constructor. 
    exists ((i, sfull nil nil nil t x0)::x). constructor. assumption. 
    assumption. }
  }
Qed. 

Theorem eCtxt : forall E, exists E', eraseContext E' E. 
Proof.
  induction E; eauto; try solve[assert(EX:exists N, eraseTerm N p) by apply eTerm;
                                 invertHyp; repeat econstructor; eauto].
  invertHyp; repeat econstructor; eauto. invertHyp; repeat econstructor; eauto. 
Qed. 

 
Inductive specPoolAux(T:pPool) : pool :=
|specAux : forall M M', Ensembles.In ptrm T M -> eraseTerm M' M -> 
                        tIn (specPoolAux T) (nil,nil,nil,M'). 

Theorem eraseSpecPool : forall T,erasePoolAux (specPoolAux T)  = T.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. cleanup. inversion H3; subst. 
   inversion H1; try invertListNeq; subst. inversion H2; subst; clear H2. 
   eapply termErasureDeterminism in H9; eauto. subst. auto. }
  {assert(exists M, eraseTerm M x). apply eTerm. invertHyp. 
   apply IncludedSingleton. econstructor. econstructor. econstructor. eassumption. 
   eassumption. reflexivity. auto. econstructor. eassumption. assumption. }
Qed. 

Theorem ePool : forall T, exists T', erasePool T' T. 
Proof.
  intros. exists (specPoolAux T). rewrite <- eraseSpecPool. constructor. Qed. 

Hint Constructors thread_lookup erasePoolAux Singleton eraseThread eraseTerm. 

Theorem termErasePoolErase : forall tid M M' s2,
                               eraseTerm M M' ->
                               erasePoolAux (tSingleton(tid,nil,s2,M)) = 
                               (pSingleton M'). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H0; subst. inversion H1; subst. cleanup. inversion H4; subst.
   clear H4. inversion H2; subst; try invertListNeq. 
   {eapply termErasureDeterminism in H; eauto; subst. assumption. }
  }
  {inversion H0; subst. repeat econstructor; eauto. }
Qed. 

Theorem eraseFill : forall E e E' e', eraseTerm e e' -> eraseContext E E' -> 
                                              eraseTerm (fill E e) (pfill E' e').
Proof.
  induction E; intros; inversion H0; subst; simpl; eauto. Qed. 


Theorem termEraseTotal : forall M, exists M', eraseTerm M M'. 
Proof.
  induction M; eauto; try solve[inv IHM1; inv IHM2; eauto]; try solve[inv IHM; eauto].
Qed. 

Theorem eraseCtxtTotal : forall E, exists E', eraseContext E E'. 
Proof.
  induction E; auto; try solve[ 
  assert(EX:exists t', eraseTerm t t') by apply termEraseTotal; inv IHE; inv EX; eauto]; 
  try solve[inv IHE; eauto]. 
  {eauto. }
Qed. 


Theorem eraseNotVal : forall e e', eraseTerm e e' -> (~val e <-> ~pval e'). 
Proof.
  intros. split; intros. 
  {induction H; try solve[intros C; inversion C]; 
   try solve[intros C; apply H0; constructor]. }
  {induction H; try solve[intros C; inversion C]; try solve[intros C; apply H0; constructor]. }
Qed. 

 

Theorem fillNotVal' : forall E E' e e', pctxtWF e' E' -> eraseContext E E' -> eraseTerm e e' ->
                                        pdecompose e' pholeCtxt e' ->
                                        ~(pval (pfill E' e')) -> ~(val (fill E e)). 
Proof.
  intros. genDeps{E; e}. induction H; intros; try solve[ 
  inv H4; intros C; inversion C]. inversion H0; subst. simpl in *. intros c. 
  apply eraseNotVal in H1. apply H1 in H3. contradiction. Qed. 

Theorem fillNotVal : forall E E' e e', ctxtWF e E -> eraseContext E E' -> eraseTerm e e' ->
                                       pdecompose e' pholeCtxt e' ->
                                       ~(val (fill E e)) -> ~(pval (pfill E' e')). 
Proof.
  intros. genDeps{E'; e'}. induction H; intros; try solve[inv H4; intros C; inv C]. 
  {inversion H0; subst. simpl. simpl in H3. intros c. apply eraseNotVal in H1; auto.
   apply H1 in H3. contradiction. }
Qed. 
 
Theorem eraseCtxtWF : forall E E' e e', eraseContext E E' -> eraseTerm e e' ->
                                        pdecompose e' pholeCtxt e' ->
                                        (ctxtWF e E <-> pctxtWF e' E'). 
Proof.
  intros. split; intros. 
  {genDeps{E'; e'}. induction H2; intros; try solve[ 
   inversion H3; subst; econstructor; eauto; eapply fillNotVal; eauto]. 
   {inversion H. auto. }
  }
  {genDeps{E; e}. induction H2; intros; try solve[ 
   inversion H3; subst; econstructor; eauto; eapply fillNotVal'; eauto]. 
   {inversion H; auto. }
  }
Qed. 



