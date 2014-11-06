Require Export semantics_rewind. 

Theorem replayHeapExtension : forall H H' t t',
                                replay H t t' -> replay (H'++H) t t'. 
Proof.
  intros. induction H0. 
  {constructor. }
  {inv H0. 
   {

Theorem OKExtension : forall H H' T1 T2 C,
                            OK H T1 T2 -> 
                            Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                            OK (H'++H) T1 T2.
Proof.
  intros. inv H0. 
  {constructor. }
  {eapply validateHeapExtensionC in H2; eauto. Focus 2. admit. inv H2. 
   {invertHyp. eapply inTXOKValid; eauto. admit. }
   {invertHyp. 





admit. }
  }
  {eapply validateHeapExtensionA in H2; eauto.
   eapply validateHeapExtensionA in H3; eauto.
   inv H2; inv H3; try invertHyp; eapply inTXInvalid; eauto. admit. admit. }
Qed. 