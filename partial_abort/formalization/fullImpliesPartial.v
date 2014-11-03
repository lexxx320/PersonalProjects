Require Export p_stepWF. 

Inductive OK H : thread -> thread -> Prop :=
|noTXOk : forall e, OK H (None,nil,e) (None,nil,e)
|commitCommitOK : forall S L L' S' H' H'' e0 e e',
                    validate S L H S' (commit H') ->
                    validate S L' H S' (commit H'') ->
                    trans_multistep H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                    OK H (Some(S,e0),L,e) (Some(S,e0),L',e')
|commitAbortOK : forall S L L' S' H' e0 e e' L'' e'',
                    validate S L H S' (commit H') ->
                    validate S L' H S' (abort e'' L'') ->
                    OK H (Some(S,e0),L,e) (Some(S,e0),L',e')
|abortAbortOK : forall S L L' S' eAbort eAbort' LAbort LAbort' e0 e e',
                    validate S L H S' (abort eAbort LAbort) ->
                    validate S L' H S' (abort eAbort' LAbort') ->
                    OK H (Some(S,e0),L,e) (Some(S,e0),L',e')   
.

Inductive poolOK H : pool -> pool -> Prop :=
|SingleOK : forall t t', OK H t t' -> poolOK H (Single t) (Single t')
|ParOk : forall T1 T1' T2 T2', poolOK H T1 T1' -> poolOK H T2 T2' ->
                          poolOK H (Par T1 T2) (Par T1' T2'). 

