Require Import AST.  
Require Import NonSpec.  
Require Import Spec. 
Require Import Coq.Sets.Ensembles. 
Require Import SfLib. 
Require Import Heap. 
Require Import sets. 

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

Inductive eraseTerm : trm -> pool -> ptrm -> Prop :=
|eraseFVar : forall i T, eraseTerm (fvar i) T (pfvar i)
|eraseBVar : forall i T, eraseTerm (bvar i) T (pbvar i)
|eraseUnit : forall T, eraseTerm unit T punit
|erasePair : forall t1 t1' t2 t2' T, eraseTerm t1 T t1' -> eraseTerm t2 T t2' ->
                                     eraseTerm (pair_ t1 t2) T (ppair t1' t2')
|eraseLambda : forall e e' T, eraseTerm e T e' -> 
                              eraseTerm (lambda e) T (plambda e')
|eraseApp : forall e1 e1' e2 e2' T, eraseTerm  e1 T e1' -> eraseTerm  e2 T e2' ->
                                    eraseTerm  (AST.app e1 e2) T (papp e1' e2')
|eraseRet : forall e e' T, eraseTerm  e T e' -> eraseTerm  (ret e) T (pret e')
|eraseBind : forall e1 e1' e2 e2' T, eraseTerm  e1 T e1' -> eraseTerm  e2 T e2' ->
                                     eraseTerm  (bind e1 e2) T (pbind e1' e2')
|eraseFork : forall e e' T, eraseTerm  e T e' -> eraseTerm  (fork e) T (pfork e')
|eraseNew : forall T, eraseTerm  new T pnew
|erasePut : forall e e' i T i', eraseTerm  e T e' -> eraseTerm  i T i' ->
                                eraseTerm  (put i e) T (pput i' e')
|eraseGet : forall i i' T, eraseTerm  i T i' -> eraseTerm  (get i) T (pget i')
|eraseRaise : forall e e' T, eraseTerm  e T e' -> eraseTerm  (raise e) T (praise e')
|eraseHandle : forall e1 e1' e2 e2' T, eraseTerm  e1 T e1' -> eraseTerm  e2 T e2' ->
                                       eraseTerm  (handle e1 e2) T (phandle e1' e2')
|eraseDone : forall e e' T, eraseTerm  e T e' -> eraseTerm  (done e) T (pdone e')
|eraseFst : forall e e' T, eraseTerm e T e' -> eraseTerm (fst e) T (pfst e')
|eraseSnd : forall e e' T, eraseTerm e T e' -> eraseTerm (snd e) T (psnd e')
|eraseSpec : forall e1 e1' e2 e2' T, 
               eraseTerm e1 T e1' -> eraseTerm  e2 T e2' -> 
               eraseTerm (spec e1 e2) T 
                         (pbind e1' (plambda (pbind (incBV 1 e2') (plambda (pret (ppair (pbvar 0) (pbvar 1)))))))
|eraseSpecReturn : forall e e' tid maj min min' min'' T M M' M'' s1 s1' s2 , 
                     eraseTerm e T e' -> s1 = s1' ++ [sAct (Tid (maj,min'') tid) M'] ->
                     eraseTerm M' T M'' -> thread_lookup T (Tid(maj,min) tid) (Tid(maj,min')tid, s1, s2, M) ->
                     eraseTerm  (specReturn e (threadId (Tid (maj,min) tid))) T
                     (pbind e' (plambda (pbind (incBV 1 M'') (plambda (pret (ppair (pbvar 0) (pbvar 1)))))))
                                   
. 

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
               eraseHeap h h' -> eraseTerm M (Empty_set thread) M' ->
               eraseHeap ((i, sfull nil d nil t M)::h) ((i, pfull M')::h')
|eraseNil : eraseHeap nil nil.

Hint Constructors eraseHeap. 



Inductive eraseThread : thread -> pool -> pPool -> Prop :=
|tEraseCommit : forall T tid s2 M M', eraseTerm M T M' ->
                                     eraseThread (tid, nil, s2, M) T (pSingleton  M')
|tEraseRead : forall T tid min s1 s1' s2 x M M' M'' E,
               s1 = s1' ++ [rAct x min M'] -> eraseTerm M' T M'' ->
               decompose M' E (get (fvar x)) -> 
               eraseThread (tid, s1, s2, M) T (pSingleton M'')
|tEraseWrite : forall tid min M M' M'' x s1 s2 s1' T E N,
                s1 = s1' ++ [wAct x min M'] -> eraseTerm M' T M'' ->
                decompose M' E (put (fvar x) N) -> eraseThread (tid, s1, s2, M) T (pSingleton M'')
|tEraseNew : forall tid min M M' M'' x s1 s2 s1' T E,
              s1 = s1' ++ [cAct x min M'] -> eraseTerm M' T M'' ->
              decompose M' E new -> eraseThread (tid, s1, s2, M) T (pSingleton M'')
|tEraseSpec : forall tid tid' M M' s1 s2 s1' T,
               s1 = s1' ++ [sAct tid' M'] -> 
               eraseThread (tid, s1, s2, M) T (Empty_set ptrm)
|tEraseFork : forall tid tid' min M M' M'' s1 s2 s1' T E N,
                s1 = s1' ++ [fAct tid' min M'] -> eraseTerm M' T M'' ->
                decompose M' E (fork N) -> eraseThread (tid, s1, s2, M) T (pSingleton M'')
|tEraseSpecRet : forall tid tid' min M M' M'' s1 s2 s1' T E N N',
                s1 = s1' ++ [specRetAct tid' min M'] -> eraseTerm M' T M'' ->
                decompose M' E (spec N N') -> eraseThread (tid, s1, s2, M) T (pSingleton M'')
|tEraseCreatedSpec : forall tid M s1 s1' s2 T,
                       s1 = s1' ++ [specAct] ->  eraseThread (tid, s1, s2, M) T (Empty_set ptrm)
.

Hint Constructors eraseThread. 

Inductive erasePoolAux (T:pool) (LookupPool:pool) : pPool :=
|eraseAux : forall t t' s1 s2 M, 
              thread_lookup T t (t, s1, s2, M) -> Included thread T LookupPool ->
              eraseThread (t, s1, s2, M) LookupPool t' ->
              Included ptrm t' (erasePoolAux T LookupPool). 

Hint Constructors erasePoolAux. 

Inductive erasePool : pool -> pPool -> Prop :=
|eraseP : forall T, erasePool T (erasePoolAux T T).

Hint Constructors erasePool. 

Axiom erasePoolEraseThread : forall T T' t, erasePool T T' -> tIn T t -> 
                                              exists t', eraseThread t T t'. 


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

Theorem eraseTermIff : 
  forall M M' P, eraseTerm M (unspecPoolAux P) M' <-> eraseTerm M P M'.
Proof.
  intros. split; intros.
  {remember (unspecPoolAux P). induction H; eauto.  
   {assert(unspecPool P (unspecPoolAux P)). constructor. 
    eapply LookupSame with(tid := Tid(maj,min) tid) (T := (Tid (maj,min') tid, s1, s2, M)) in H3. 
    inversion H3. inversion H4. inversion H6; subst; try invertListNeq. 
     {destruct s1'; inversion H12. subst. eapply eraseSpecReturn. assert(unspecPoolAux P = unspecPoolAux P).
      reflexivity. apply IHeraseTerm1 in H0. assumption. reflexivity. 
      assert(unspecPoolAux P = unspecPoolAux P). reflexivity. apply IHeraseTerm2 in H0. 
      eassumption. eassumption. destruct s1'; inversion H8. }
     {subst. assumption. }
   }
  }
  {induction H; eauto. eapply eraseSpecReturn with (min':=min'')(min'':=min'')(M':=M')(s1':=nil).
   assumption. simpl. reflexivity. assumption. 
   assert(unspecThread(Tid (maj, min') tid, s1, s2, M)
                      (Some(Tid(maj,min'') tid,[sAct (Tid (maj, min'') tid) M'], s2, M'))).
   econstructor. eassumption. eapply eraseSomeLookup in H3. eassumption. assumption. }
Qed. 

Hint Unfold Included. 
 
Theorem erasePoolAuxEQUnspecAux : forall T, erasePoolAux (unspecPoolAux T) (unspecPoolAux T) = erasePoolAux T T. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H; subst. inversion H0; subst. inversion H5; subst; clear H5. 
   assert(unspecPool T (unspecPoolAux T)). constructor. 
   apply LookupSame with (tid:=(Tid (maj, min') tid))(T:=(Tid (maj, min') tid, s0, s3, M0)) in H5; auto.
   invertExists. inversion H6. inversion H7; subst. 
   {inversion H2; subst; try invertListNeq. 
    econstructor. eassumption. unfold Included; auto. econstructor. rewrite <- eraseTermIff.
    eassumption. eassumption. }
   {inversion H2; subst; try invertListNeq. inversion H5; subst. inversion H16; subst. 
    econstructor. econstructor. eassumption. auto. auto. eapply tEraseRead. 
    auto. apply decomposeEq in H11. subst. rewrite <- eraseTermIff. eassumption. eassumption. assumption. }
   {inversion H2; subst; try invertListNeq. inversion H5; subst. inversion H16; subst. 
    econstructor. econstructor. eassumption. auto. auto. eapply tEraseWrite; eauto. 
    apply decomposeEq in H11. subst. rewrite <- eraseTermIff. eassumption. auto. }
   {inversion H2; subst; try invertListNeq. inversion H5; subst. inversion H16; subst. 
    econstructor; eauto. eapply tEraseNew; eauto. apply decomposeEq in H11. subst. rewrite <- eraseTermIff. 
    eassumption. }
   {inversion H2; subst; try invertListNeq. inversion H5; subst. inversion H15; subst. 
    econstructor; eauto. }
   {inversion H2; subst; try invertListNeq. inversion H5; subst. inversion H16; subst. 
    econstructor; eauto. eapply tEraseFork; eauto. apply decomposeEq in H11. subst; auto. 
   rewrite <- eraseTermIff. eassumption. }
   {inversion H2; subst; try invertListNeq. inversion H5; subst. inversion H16; subst. 
    econstructor; eauto. eapply tEraseSpecRet; eauto. rewrite <- eraseTermIff. auto. }
  }
  {inversion H. inversion H0; subst. inversion H6; subst; clear H6. apply IncludedSingleton. 
   inversion H2; subst. 
   {inversion H3; subst. eapply eraseAux. inversion H0; subst. econstructor. econstructor. 
    eassumption. econstructor. auto. auto. econstructor. rewrite eraseTermIff. auto. }
   {inversion H3; subst. eapply eraseAux. inversion H0; subst. econstructor. econstructor. 
    eassumption. eapply unspecRead. eassumption. auto. auto. auto. constructor. 
    apply decomposeEq in H13. subst. rewrite eraseTermIff. auto. }
   {inversion H3; subst. eapply eraseAux. inversion H0; subst. econstructor. econstructor. 
    eassumption. eapply unspecWrite. eassumption. auto. auto. auto. constructor. 
    apply decomposeEq in H13. subst. rewrite eraseTermIff. auto. }
   {inversion H3; subst. eapply eraseAux. inversion H0; subst. econstructor. econstructor. 
    eassumption. eapply unspecCreate. eassumption. auto. auto. auto. constructor. 
    apply decomposeEq in H13. subst. rewrite eraseTermIff. auto. }
   {inversion H3; subst. }
   {inversion H3; subst. eapply eraseAux. inversion H0; subst. econstructor. econstructor. 
    eassumption. eapply unSpecFork. eassumption. auto. auto. auto. constructor. 
    apply decomposeEq in H13. subst. rewrite eraseTermIff. auto. }
   {inversion H3; subst. eapply eraseAux. inversion H0; subst. econstructor. econstructor. 
    eassumption. eapply unSpecSpecret. eassumption. auto. auto. auto. constructor. 
    apply decomposeEq in H13. subst. rewrite eraseTermIff. auto. }
   {inversion H3. }
  }
Qed.  

Theorem eraseUnspecPoolIdem :
  forall T T' T'', unspecPool T T' -> erasePool T' T'' ->
                        erasePool T T''. 
Proof. 
  intros. inversion H; inversion H0; subst. rewrite erasePoolAuxEQUnspecAux. constructor. Qed. 

Ltac applyHyp :=
  match goal with
      |H : forall a : _, ?X -> ?Y, H' : ?Z |- _ => apply H in H'
  end. 

Theorem lastElementEq : forall (T:Type) s1 s2 (e1 e2 : T), s1 ++ [e1] = s2 ++ [e2] -> e1 = e2. 
Proof.
  intros. generalize dependent s2. induction s1; intros. 
  {destruct s2. inversion H. reflexivity. inversion H. destruct s2; inversion H2. }
  {destruct s2. inversion H. destruct s1; inversion H2. inversion H. apply IHs1 in H2.
   assumption. } Qed. 

Axiom uniqueThreadPool : forall T tid t t', 
                           thread_lookup T tid t -> thread_lookup T tid t' -> t = t'. 

Theorem termErasureDeterminism : forall M T M1 M2,
                                   eraseTerm M T M1 -> eraseTerm M T M2 -> M1 = M2. 
Proof.
  intros. generalize dependent M2. induction H; intros; 
                                   try(inversion H0; reflexivity);
  try(clear H; clear H0; match goal with
                           |H:eraseTerm ?T ?T' ?M |- _ => 
                    inversion H; clear H; applyHyp; applyHyp; subst; reflexivity
                         end); 
  try(clear H; match goal with
                |H : eraseTerm ?T ?T' ?M |- _ =>
                 inversion H; clear H; applyHyp; subst; reflexivity
               end). 
  {inversion H3; subst. apply IHeraseTerm1 in H8. rewrite H8. 
   apply uniqueThreadPool with (t' := (Tid(maj,min') tid, s1' ++ [sAct (Tid(maj,min'')tid) M'], s2, M)) in H13. 
   inversion H13. apply lastElementEq in H5. inversion H5. subst. apply IHeraseTerm2 in H12. 
   subst. reflexivity. assumption. }
Qed. 

Theorem erasureDeterminism : forall t t1' t2' T, 
                               eraseThread t T t1' -> 
                               eraseThread t T t2' -> t1' = t2'.
Proof.
  intros. induction H; inversion H0;
  try(subst; match goal with
               |H:eraseTerm ?M ?T ?x, H':eraseTerm ?M ?T ?y |- _ =>
                eapply termErasureDeterminism in H;[rewrite<-H;reflexivity|auto]
               |H:[] = [] ++ [?x] |- _ => inversion H       
               |H:[] = ?x ++ [?y] |- _ => destruct x; inversion H
               |H:?s1++[?x]=?s2++[?y]|-_ => apply lastElementEq in H; inversion H
             end);
  try(subst; eapply termErasureDeterminism in H12;[rewrite <-H12; reflexivity| auto]); eauto.
  {inversion H9; subst. eapply termErasureDeterminism in H10. rewrite <- H10. reflexivity. auto. }
  {inversion H9; subst. eapply termErasureDeterminism in H10. rewrite <- H10. reflexivity. auto. }
  {inversion H9; subst. eapply termErasureDeterminism in H10. rewrite <- H10. reflexivity. auto. }
  {inversion H9; subst. eapply termErasureDeterminism in H10. rewrite <- H10. reflexivity. auto. }
  {inversion H9; subst. eapply termErasureDeterminism in H10. rewrite <- H10. reflexivity. auto. }
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

Inductive eraseContext : ctxt -> pool -> pctxt -> Prop :=
|eraseCtxtBind : forall T N N' E E', eraseTerm N T N' -> eraseContext E T E' ->
                                     eraseContext (bindCtxt E N) T (pbindCtxt E' N')
|eraseCtxtSpec : forall T M M' M'' E E' t maj min min' min'' s1 s2,
                   eraseContext E T E' -> 
                   thread_lookup T (Tid(maj,min) t) (Tid(maj,min')t, s1 ++ [sAct (Tid(maj,min'')t) M'], s2, M) ->
                   eraseTerm M' T M'' ->
                   eraseContext (specReturnCtxt E (threadId (Tid(maj,min)t))) T 
                        (pbindCtxt E' (plambda (pbind (incBV 1 M'') (plambda (pret (ppair (pbvar 0)(pbvar 1)))))))
|eraseCtxtHandle : forall T N N' E E',
                     eraseTerm N T N' -> eraseContext E T E' ->
                     eraseContext (handleCtxt E N) T (phandleCtxt E' N')
|eraseCtxtApp : forall T N N' E E',
                  eraseTerm N T N' -> eraseContext E T E' -> 
                  eraseContext (appCtxt E N) T (pappCtxt E' N')
|eraseCtxtFst : forall T E E', eraseContext E T E' -> eraseContext (fstCtxt E) T (pfstCtxt E')
|eraseCtxtSnd : forall T E E', eraseContext E T E' -> eraseContext (sndCtxt E) T (psndCtxt E')
|eraseCtxtHole : forall T, eraseContext holeCtxt T pholeCtxt
.
 
Theorem ctxtErasureDeterminism : forall E T E1 E2, eraseContext E T E1 -> eraseContext E T E2 ->
                                                   E1 = E2. 
Proof.
  intros. generalize dependent E2. induction H; intros; try solve[
  inversion H1; subst; 
   match goal with
       H:eraseContext ?E ?T ?E', H':eraseTerm ?N ?T ?N' |- _ =>
       apply IHeraseContext in H; eapply termErasureDeterminism in H'; eauto; subst; auto
   end]. 
  {inversion H2; subst. apply IHeraseContext in H9. subst. 
   apply uniqueThreadPool with (t' := (Tid (maj, min'0) t, s0 ++ [sAct (Tid (maj, min''0) t) M'0], s3, M0)) in H0. 
   inversion H0; subst. apply lastElementEq in H5. inversion H5; subst. 
   eapply termErasureDeterminism in H11. rewrite <- H11. reflexivity. assumption. assumption. }
  {inversion H0; subst. apply IHeraseContext in H2. subst. auto. }
  {inversion H0; subst. apply IHeraseContext in H2. subst. auto. } 
  {inversion H0; subst; auto. }
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
Theorem decomposeErase : forall E e T t', 
                           eraseTerm (fill E e) T t' -> 
                           exists E' e', eraseContext E T E' /\ eraseTerm e T e' /\ t' = pfill E' e'.
 Proof. 
  intros. remember (fill E e). generalize dependent E. generalize dependent e.
  induction H; intros; try solve[destruct E; inversion Heqt; simpl in *; subst; repeat econstructor];
  try solve[destruct E; inversion Heqt; simpl in *; subst; repeat econstructor; auto]; try solve[ 
  destruct E; inversion Heqt; simpl in *; subst; eauto; try solve[ repeat econstructor; eauto];
   match goal with
       |H:forall e E, fill ?E' ?e' = fill E e -> ?x |- _ => assert(EQ:fill E' e' = fill E' e') by auto;
                                                           apply H in EQ; invertHyp
   end; repeat econstructor; eauto]. 
  {destruct E; inversion Heqt; simpl in *. 
   {apply IHeraseTerm1 in H4. invertHyp. econstructor. econstructor. split. econstructor. eassumption. 
    eassumption. eassumption. split. eassumption. simpl. auto. }
   {subst. econstructor. econstructor. eauto. }
  }
Qed. 

Theorem inErasure : forall t t', erasePoolAux t t = Singleton ptrm t' -> Ensembles.In ptrm (erasePoolAux t t) t'.
Proof.
  intros. apply eqImpliesSameSet in H. unfold Same_set in H. unfold Included in H. inversion H. 
  assert(Ensembles.In ptrm (Singleton ptrm t') t') by constructor. apply H1 in H2. assumption. Qed. 

Theorem eTerm : forall pt T, exists t, eraseTerm t T pt. 
Proof.
  induction pt; eauto;
  try intros; repeat( match goal with
               |T:?pool, H:forall T':?pool, ?X |- _ => specialize (H T); try invertHyp
           end); econstructor; eauto. Qed. 

Theorem eHeap : forall PH, exists H, eraseHeap H PH. 
Proof.
  induction PH; eauto. 
  {destruct a. destruct p. 
   {assert(hd:action). repeat constructor.  assert(tl:specStack). repeat constructor. 
    assert(w:tid). repeat constructor. assert(M:trm). repeat constructor. 
    inversion IHPH. exists((i, sfull nil nil (hd::tl) w M)::x). constructor. 
    assumption. }
   {inversion IHPH. assert(exists t, eraseTerm t tEmptySet p) by apply eTerm.  
    inversion H0. assert(t:tid). repeat constructor. 
    exists ((i, sfull nil nil nil t x0)::x). constructor. assumption. 
    assumption. }
  }
Qed. 

Theorem eCtxt : forall E T, exists E', eraseContext E' T E. 
Proof.
  induction E; eauto; intros; specialize(IHE T); inversion IHE; 
  try (assert(EX:exists N, eraseTerm N T p) by apply eTerm; invertHyp); eauto. 
Qed. 

Theorem termEraseDifferentPools : forall T M M1 M2, eraseTerm M tEmptySet M1 -> 
                                            eraseTerm M T M2 -> M1 = M2. 
Proof.
  intros. remember tEmptySet. generalize dependent M2. generalize dependent T. induction H; intros;
  try solve[inversion H0; subst; reflexivity]; 
  try solve[inversion H0; subst; apply IHeraseTerm in H2; subst; reflexivity]; 
  try solve[inversion H1; subst; assert(tEmptySet = tEmptySet) by reflexivity; eapply IHeraseTerm1 in H2;[
   rewrite  H2; assert(tEmptySet = tEmptySet) by reflexivity; eapply IHeraseTerm2 in H3;[ 
   rewrite H3; reflexivity|eassumption]|eassumption]]. 
  {subst. inversion H2. inversion H8. }
Qed. 

Theorem eraseWeakening : forall M M' T, eraseTerm M tEmptySet M' -> eraseTerm M T M'. 
Proof.
  intros. remember(tEmptySet). induction H; try solve[auto]. 
  {subst. inversion H2. inversion H7. }
Qed. 

Inductive specPoolAux(T:pPool) : pool :=
|specAux : forall M M', Ensembles.In ptrm T M -> eraseTerm M' tEmptySet M -> 
                        tIn (specPoolAux T) (Tid(0,0)nil,nil,nil,M'). 

Theorem eraseSpecPool : forall T,erasePoolAux (specPoolAux T)(specPoolAux T)  = T.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inversion H; subst. inversion H0; subst. inversion H4;subst. inversion H5; subst. 
   clear H5. inversion H2; subst; try invertListNeq. 
   {inversion H3. subst. eapply termEraseDifferentPools with(M1:=M1)(M2:=x) in H13. 
    subst. assumption. eassumption. }
  }
  {assert(exists M, eraseTerm M tEmptySet x). apply eTerm. inversion H0.
   apply IncludedSingleton. econstructor. econstructor. econstructor. eassumption. 
   eassumption. reflexivity. auto. econstructor. eapply eraseWeakening. eassumption. auto. }
Qed. 


Theorem ePool : forall T, exists T', erasePool T' T. 
Proof.
  intros. exists (specPoolAux T). rewrite <- eraseSpecPool. constructor. Qed. 

Hint Constructors thread_lookup erasePoolAux Singleton eraseThread eraseTerm. 

Theorem eraseEmpty : forall M T e, eraseTerm M tEmptySet e -> eraseTerm M T e. 
Proof.
  intros. remember tEmptySet. generalize dependent T. induction H; eauto. 
  {subst. inversion H2. inversion H7. }
Qed. 

Theorem termErasePoolErase : forall tid M M' s2,
                               eraseTerm M tEmptySet M' ->
                               erasePoolAux (tSingleton(tid,nil,s2,M))(tSingleton(tid,nil,s2,M)) = (pSingleton M'). 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. split; intros. 
  {inversion H0; subst. inversion H1; subst. inversion H5; subst.
   inversion H3; subst; try invertListNeq. 
   {eapply termEraseDifferentPools with(M:=M0)(M1:=M')(M2:=M'0)in H. subst. assumption. 
    eassumption. }
  }
  {inversion H0; subst. inversion H; subst; try solve[ 
   destruct tid; destruct p; econstructor; [econstructor; econstructor|eauto|auto|auto]]; 
   try solve[destruct tid; destruct p; econstructor; [econstructor; econstructor|eauto|econstructor;
   econstructor; eapply eraseEmpty; eauto|auto]]. 
   {inversion H4. inversion H9. }
  }
Qed. 

Theorem eraseFillHelper : forall E e E' e' T, eraseTerm e T e' -> eraseContext E T E' -> 
                                              eraseTerm (fill E e) T (pfill E' e').
Proof.
  induction E; intros; inversion H0; subst; simpl; eauto. Qed. 


Theorem eraseFill : forall E e E' e' T, eraseContext E T E' -> eraseTerm e T e' ->
                                           eraseTerm (fill E e) T (pfill E' e'). 
Proof. 
  intros. generalize dependent e'. generalize dependent e. induction H; intros;
   try solve[simpl; econstructor; auto].                                 
  {simpl. econstructor. apply IHeraseContext. assumption. auto. eassumption. eassumption. }
  {simpl. assumption. }
Qed. 







