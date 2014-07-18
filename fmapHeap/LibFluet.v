Require Import Coq.Program.Equality.

(* ********** *)
(* ********** *)

(* "clear_except H" is like "clear - H",
* but clears even in the presence of goals with meta-variables.
*)
Ltac clear_except H :=
 repeat match goal with
          | [ H' : _ |- _ ] =>
            progress (match H' with
                        | H => idtac
                        | _ => clear H'
                      end)
        end.

(* ********** *)

Tactic Notation "dup" hyp(H1) "as" ident(H2) :=
 let P := type of H1 in
 assert P as H2 by exact H1.

Tactic Notation "dup" hyp(H1) :=
 let P := type of H1 in
 assert P by exact H1.

(* ********** *)

Ltac with_hyp P f :=
 match goal with
   | [ H : P |- _ ] => f H
   | [ H : eq _ _ |- _ ] =>
     let TEMP := fresh in
     assert P as TEMP by simple apply H; clear TEMP; f H
 end.

Ltac with_dup_hyp P f :=
 let TEMP := fresh in
 with_hyp P ltac:(fun H => dup H as TEMP; f TEMP).

Ltac derived_tac P :=
 with_hyp P ltac:(fun H => clear_except H ; exact H).

Tactic Notation "derived" constr(P) :=
 derived_tac P.

Tactic Notation "unique" tactic(tac) := (tac ; fail) || (tac ; [idtac]).

Ltac fforward lem :=
 let rec brk z :=
     match type of z with
       | ex _ => let x := fresh in
                 destruct z as [? x]; brk x
       | _ /\ _ => let x := fresh in
                   let y := fresh in
                   destruct z as [x y]; brk x; brk y
(*
       | False => destruct z
*)
       | _ \/ _ => let x := fresh in
                   let y := fresh in
                   destruct z as [x | y]; [brk x | brk y]
       | eq ?x ?y => (is_var x ; subst x) || 
                     (is_var y ; subst y) || 
                     idtac
       | _ => idtac
     end in
 let rec chk :=
     match goal with
       | [ H : _ |- _ ] => eexact H
       | |- ex _ => eexists ; chk
       | |- _ /\ _ => split ; [chk | chk]
       | |- _ \/ _ => (left ; chk) || (right ; chk)
       | |- eq _ _ => reflexivity || (symmetry ; eassumption)
     end in
 let rec go x :=
     let xT := type of x in
     match xT with
       | ?P -> ?Q => match goal with
                       | [ H : ?HT |- _ ] => go (x H)
                       | _ => fail 2
                     end
       | forall _ : ?T , _ => let z := fresh in 
                              evar(z:T);
                              let x' := constr:(x z) in
                              let x'' := (eval unfold z in x') in
                              subst z; go x''
       | _ => (has_evar xT ; fail 1)
       | _ => (assert xT by exact lem ; fail 1)
       | _ => (assert xT by chk ; fail 1)
       | _ => let z := fresh in
              assert xT as z by apply x;
              brk z
     end in
 go lem.

(* ********** *)
(* ********** *)

(* For some reason, can't use "ltac:(fun H => dependent induction H)" notation in with_hyp. *)

Tactic Notation "dependent_induction" hyp(H) :=
 do_depind ltac:(fun hyp => induction hyp) H.

Tactic Notation "dependent_induction" hyp(H) "as" simple_intropattern(I) :=
 do_depind ltac:(fun hyp => induction hyp as I) H.

Tactic Notation "dependent_induction" hyp(H) "using" constr(c) :=
 do_depind ltac:(fun hyp => induction hyp using c) H.

Tactic Notation "dependent_induction" hyp(H) "as" simple_intropattern(I) "using" constr(c) :=
 do_depind ltac:(fun hyp => induction hyp as I using c) H.


Tactic Notation "dependent_destruct" hyp(H) :=
 do_depind ltac:(fun hyp => destruct hyp) H.

Tactic Notation "dependent_destruct" hyp(H) "as" simple_intropattern(I) :=
 do_depind ltac:(fun hyp => destruct hyp as I) H.

Tactic Notation "dependent_destruct" hyp(H) "using" constr(c) :=
 do_depind ltac:(fun hyp => destruct hyp using c) H.

Tactic Notation "dependent_destruct" hyp(H) "as" simple_intropattern(I) "using" constr(c) :=
 do_depind ltac:(fun hyp => destruct hyp as I using c) H.

(* ********** *)
(* ********** *)

Ltac unpack P :=
 let aux H :=
     let HT := type of H in
     (assert HT by (econstructor; eassumption) ; fail 1) ||
     (assert HT by exact H); unique (dependent_destruct H) in
 match goal with
   | [ H : P _ |- _ ] => aux H
   | [ H : P _ _ |- _ ] => aux H
   | [ H : P _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ _ _ _ _ |- _ ] => aux H
 end.

Ltac unpack' P :=
 let aux H :=
     let HT := type of H in
     (assert HT by (econstructor; eassumption) ; fail 1) ||
     (assert HT by exact H); dependent_destruct H in
 match goal with
   | [ H : P _ |- _ ] => aux H
   | [ H : P _ _ |- _ ] => aux H
   | [ H : P _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ _ _ _ |- _ ] => aux H
   | [ H : P _ _ _ _ _ _ _ _ |- _ ] => aux H
 end.

(* ********** *)
(* ********** *)

(*
*** Local Variables:
*** coq-load-path: ("." "./tlc")
*** End:
*)

