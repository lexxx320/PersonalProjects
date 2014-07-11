Require Import NonSpec.   
Require Import Spec.
Require Import Coq.Sets.Ensembles. 
Require Import erasure. 
Require Import AST. 
Require Import SfLib.  
Require Import unspec. 
Require Import sets. 
Require Import SpecLib. 
Require Import classifiedStep. 
Require Import hetList. 
(*
Theorem ForkInd' : forall h H' t T T' tid s1 s2 s2' E M M' N N' d,
             decompose t E (fork N') -> 
             splitMultistep H' T (tSingleton(tid,s1,s2,t))
                            (OK h T' (tUnion (tSingleton (tid, fAct t E M' d::s1, s2, M))
                                            (tSingleton (1::tid, [specAct], s2', N)))) ->
             multistep H' (tSingleton(tid,s1,s2,t)) T (OK h (tSingleton(tid,s1,s2,t)) T').
Proof.
  intros. dependent induction H0. 
  {auto. }
  {econstructor. auto. apply decomposeEq in H. subst. eapply H1. eauto. }
  {apply SingletonEqUnion in H3. inversion H3. 
   {inv H4. inversion H1; subst; try solve[
    match goal with
      |H:tSingleton ?t = Empty_set ?x |- _ => apply SingletonNeqEmpty in H; inversion H
      |H:tCouple ?t1 ?t2 = Empty_set ?x |- _ => apply CoupleNeqEmpty in H; inversion H
      |H:tAdd ?T ?t = Empty_set ?x |- _ => apply AddNeqEmpty in H; inversion H
    end]. }
   {inv H4. 
    {

Hint Unfold tSingleton tUnion tCouple.

Theorem passThroughAct : forall a M M' T T' tid s1 s2 H H',
                           actionTerm a M' ->
                           splitMultistep H T (unspecPoolAux (tSingleton(tid,a::s1,s2,M)))
                                          (OK H' T' (tSingleton(tid,a::s1,s2,M))) ->
                           exists T'' H'', 
                             splitMultistep H T (unspecPoolAux (tSingleton(tid,a::s1,s2,M)))
                                            (OK H'' T'' (tSingleton(tid,s1,s2,M'))). 
Admitted.  
*)
Theorem spec_multi_trans : forall H H' H'' T T' T'',
                        spec_multistep H T H' T' ->
                        spec_multistep H' T' H'' T'' ->
                        spec_multistep H T H'' T''.  
Proof.
  intros. genDeps {H''; T''}. induction H0; intros.  
  {auto. }
  {apply IHspec_multistep in H1. econstructor. eauto. auto. }
Qed. 

Theorem rollbackWF : forall H H' T TR TR' tid s2 M tidR acts,
                       wellFormed H (tUnion T (tAdd TR (tid, nil, s2, M))) ->
                       rollback tidR acts H TR H' TR' ->
                       wellFormed H' (tUnion T (tAdd TR' (tid, nil, s2, M))). 
Proof.
  intros. induction H1. 
  {auto. }
  {

Theorem specStepSingleton : forall h t h' T t', 
                              spec_step h T t h' T t' -> 
                              exists t'', t = tSingleton t''. 
Proof.
  intros. inv H; eauto. Qed. 

Ltac eqSets H := apply eqImpliesSameSet in H; unfold Same_set in H; unfold Included in H;
                 inv H.

Ltac eqIn H := unfoldTac; 
  match type of H with
      |forall x, Ensembles.In ?X (Union ?X ?T (Singleton ?X ?t)) x -> ?y =>
       assert(Ensembles.In X(Union X T (Singleton X t)) t) by (apply Union_intror; constructor)
  end.

Require Import Coq.Program.Equality. 
Theorem passThroughAct : forall a M M' T T' tid s1 s2 H H',
                           actionTerm a M' ->
                           spec_multistep H (tUnion T (unspecPoolAux (tSingleton(tid,a::s1,s2,M))))
                                          H' (tUnion T' (tSingleton(tid,a::s1,s2,M))) ->
                           exists T'' H'', 
                             spec_multistep H (tUnion T (unspecPoolAux (tSingleton(tid,a::s1,s2,M))))
                                            H'' (tUnion T'' (tSingleton(tid,s1,s2,M'))) /\
                             spec_multistep H'' (tUnion T'' (tSingleton(tid,s1,s2,M')))
                                            H' (tUnion T' (tSingleton(tid,s1,s2,M'))). 
Proof.
  intros. dependent induction H1. 
  {assert(tIn (tUnion T' (tSingleton(tid,a::s1,s2,M)))(tid,a::s1,s2,M)). apply Union_intror. 
   constructor. eqSets x. copy H. apply H2 in H. inv H. 
   {admit. }
   {inv H4. inv H. inv H7. inv H4. inv H5; try solve[inv H6]. }
  }
  {copy H. apply specStepSingleton in H2. invertHyp. eqSets x. eqIn H2. apply H2 in H4. 
   inv H4. 
   {admit. }
   {assert(







