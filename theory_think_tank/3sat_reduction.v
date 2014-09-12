(*This is an effort to reproduce the results presented in:
http://dl.acm.org/citation.cfm?id=976579
*)

Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  

Definition bvar := nat. (*boolean variables*)
Definition vvar := nat. (*vertex variables*)
Definition colors := nat. (*colors for graph vertices*) 
Definition edge : Type := prod vvar vvar. (*graph edges*)

(*boolean formula*)
Inductive bformula : Type :=
|pos : bvar -> bformula
|neg : bvar -> bformula
|new : bvar -> bformula -> bformula
|conjForm : bformula -> bformula -> bformula
|disjForm : bformula -> bformula -> bformula. 

(*graph*)
Inductive graph : Type :=
|emptyGraph : graph
|newVertex : vvar -> graph -> graph
|newEdge : edge -> graph -> graph
|unionGraph : graph -> graph -> graph. 

(*environment (eta) mapping either boolean or vertex variables
**to their respective values (true/false or a color)*)
Inductive env {A:Type} : Type :=
|emptyEnv : env  
|consEnv : bvar -> A -> env -> env. 

(*lookup a variable in a given environment*)
Fixpoint lookup {A:Type} (e:@env A) bv :=
  match e with
      |emptyEnv => None
      |consEnv x v e' => if eq_nat_dec bv x
                         then Some v
                         else lookup e' bv
  end. 

(*Specificaion of SAT satisfiability*)
Inductive SAT : @env bool -> bformula -> Prop :=
|satp : forall eta u, lookup eta u = Some true -> SAT eta (pos u)
|satn : forall eta u, lookup eta u = Some false -> SAT eta (neg u)
|satConj : forall eta F1 F2, SAT eta F1 -> SAT eta F2 -> SAT eta (conjForm F1 F2)
|satDisj1 : forall eta F1 F2, SAT eta F1 -> SAT eta (disjForm F1 F2)
|satDij2 : forall eta F1 F2, SAT eta F2 -> SAT eta (disjForm F1 F2)
|satt : forall eta u F, SAT (consEnv u true eta) F -> SAT eta (new u F)
|satf : forall eta u F, SAT (consEnv u false eta) F -> SAT eta (new u F). 

(*specification of graph coloring*)
Inductive coloring : @env colors -> graph -> nat -> Prop :=
|cgempty : forall eta C, coloring eta emptyGraph C 
|cgVertex : forall eta C C' G v, C <= C' -> coloring (consEnv v C' eta) G C ->
                          coloring eta (newVertex v G) C
|cgEdge : forall eta C1 C2 C A B G, C1 <= C2 -> C2 <= C -> C1 <> C2 -> 
                             coloring (consEnv A C1 (consEnv B C2 eta)) G C ->
                             coloring eta (newEdge (A, B) G) C
|cgUnion : forall eta G1 G2 C, coloring eta G1 C -> coloring eta G2 C ->
                        coloring eta (unionGraph G1 G2) C. 
             
Fixpoint newV vs G :=
  match vs with
      |v::vs => newVertex v (newV vs G)
      |nil => G
  end. 

Inductive connectX : list (bvar * vvar * vvar * vvar) -> list bvar ->
                     vvar -> graph -> Prop :=
|connectXNil : forall Gamma X, connectX Gamma nil X emptyGraph
|connectX_vtx : forall Gamma Delta u v v' x' X G, 
                  In (u, v, v', x') Gamma -> connectX Gamma Delta X G -> 
                  connectX Gamma (u::Delta) X (newEdge (X, x') G). 

Inductive connectV : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      vvar -> graph -> Prop :=
|connectV_nil : forall Gamma X, connectV Gamma nil X emptyGraph
|connectV_vtx : forall Gamma Delta u v v' x' X G, 
                  In (u, v, v', x') Gamma -> connectV Gamma Delta X G ->
                  connectV Gamma (u::Delta) X (newEdge (X,v) (newEdge (X, v') G)). 

Inductive vars_to_clique : list (bvar * vvar * vvar * vvar) -> list bvar ->
                           graph -> Prop :=
|vars2cliqueNil : forall Gamma, vars_to_clique Gamma nil emptyGraph
|vars2cliqueVTX : forall Gamma Delta u v v' x G1 G2 G3 G4, 
         In (u,v,v',x) Gamma -> vars_to_clique Gamma Delta G1 ->
         connectX Gamma Delta v G2 -> connectX Gamma Delta v' G3 ->
         connectV Gamma Delta x G4 ->
         vars_to_clique Gamma (x::Delta) (unionGraph G1 (unionGraph G2 (unionGraph G3 G4))). 

Inductive convFormula : list (bvar * vvar * vvar * vvar) -> list bvar ->
                        bformula -> graph -> Prop := 
. 

(*Convert Stack of Continuations (Gamma; Delta |- K => G)*)
Inductive convStack : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      list bformula -> graph -> Prop :=
|conv_base : forall Gamma Delta, convStack Gamma Delta nil emptyGraph
|conv_cons : forall Gamma Delta K F G1 G2, convStack Gamma Delta K G1 -> convFormula Gamma Delta F G2 ->
                              convStack Gamma Delta (F::K) (unionGraph G1 G2)
.

(*Top Level Reduction (Gamma; Delta |- K o F => C C' G)*)
Inductive reduce : list (bvar * vvar * vvar * vvar) -> list bvar ->
                   list bformula -> bformula -> nat -> nat -> graph -> Prop :=
|c_new : forall u v v' x Gamma Delta K F C C' G, 
           reduce ((u,v,v',x)::Gamma) (u::Delta) K F (C+1) C' G -> 
           reduce Gamma Delta K (new u F) C C' (newV [v;v';x] (newEdge (v,v') G))
|convConj : forall Gamma Delta K F F' C C' G, 
              reduce Gamma Delta (F::K) F' C C' G ->
              reduce Gamma Delta K (conjForm F F') C C' G
.

Theorem reductionInvariant : forall K F G C C' Delta Gamma, 
                               reduce Gamma Delta K F C C' G -> C <= C'. 
Proof.
  intros. induction H; omega. 
Qed. 



















