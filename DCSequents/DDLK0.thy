(* I borrow the implementation by 
    [Title:      Sequents/LK0.thy
     Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
     Copyright   1993  University of Cambridge]

But make a modification to adapt to our application. 
*)

header {* Classical First-Order Sequent Calculus *}

theory DDLK0
imports DLK0
begin

datatype dexp = l | Dur fform ("Dur _" 80)
                  | DR real   ("DR _" 80)
                  | DAdd dexp dexp (infixl "[[+]]" 65)


(*dc formulas*)
datatype dform = DTrue | DFalse 
               | DEq dexp dexp        (infixl "[[=]]" 50)
               | DLess dexp dexp       (infixl "[[<]]" 50)
               | DGreat dexp dexp      (infixl "[[>]]" 50)
               | DNot dform           ("[[~]] _" [40] 40)
               | DConj dform dform    (infixr "[[&]]" 35)
               | DDisj dform dform    (infixr "[[|]]" 30)
               | DImp dform dform      (infixr "[[-->]]" 30)
               | DIff dform dform      (infixr "[[<->]]" 25)
               | DAll string dform      ("DALL _ _ " 10)
               | DEx  string dform      ("DEX _ _" 10) 
               | chop dform dform     (infixr "[^]" 38)

definition
dequal_less  (infixl "[[<=]]" 50) where
"x [[<=]] y == (x [[<]] y) [[|]] (x [[=]] y)"
definition
dequal_greater  (infixl "[[>=]]" 50) where
"x [[>=]] y == (x [[>]] y) [[|]] (x [[=]] y)"
definition
almost ("almost _" 60) where
"almost p == ((Dur p) [[=]] l [[&]] l [[>]] DR 0) "

definition
almostz ("almostz _" 60) where
"almostz p == almost p [[|]] l [[=]] DR 0"



 axioms
 (*Propositional rules*)

  dconjR: "[| $H|- $E, P, $F;  $H|- $E, Q, $F |] ==> $H|- $E, P [[&]] Q, $F"
  dconjL: "$H, P, Q, $G |- $E ==> $H, P [[&]] Q, $G |- $E"

  ddisjR: "$H |- $E, P, Q, $F ==> $H |- $E, P [[|]] Q, $F"
  ddisjL: "[| $H, P, $G |- $E;  $H, Q, $G |- $E |] ==> $H, P [[|]] Q, $G |- $E"
 
  dimpR:  "$H, P |- $E, Q, $F ==> $H |- $E, P [[-->]] Q, $F"
  dimpL:  "[| $H,$G |- $E,P;  $H, Q, $G |- $E |] ==> $H, P [[-->]] Q, $G |- $E"

  dnotR:  "$H, P |- $E, $F ==> $H |- $E, [[~]] P, $F"
  dnotL:  "$H, $G |- $E, P ==> $H, [[~]] P, $G |- $E"

  dFalseL: "$H, DFalse, $G |- $E"

  dTrue_def: "DTrue == DFalse [[-->]] DFalse"
  diff_def:  "P [[<->]] Q == (P [[-->]] Q) [[&]] (Q [[-->]] P)"

 axioms
  (*Quantifiers*)

  dallR:  "(!!x.$H |- $E, P(x), $F) ==> $H |- $E, DALL x P(x), $F"
  dallL:  "$H, P(t), $G, DALL x P(x) |- $E ==> $H, DALL x P(x), $G |- $E"

  dexR:   "$H |- $E, P(t), $F, DEX x P(x) ==> $H |- $E, DEX  x P(x), $F"
  dexL:   "(!!x.$H, P(x), $G |- $E) ==> $H, DEX x P(x), $G |- $E"

 axioms
 (*Equality*)

  drefl:  "$H |- $E, a [[=]] a, $F"
  dsubst: "$H(a), $G(a) |- $E(a) ==> $H(b), a [[=]] b, $G(b) |- $E(b)"

  (* Reflection *)

  deq_reflection:  "|- x [[=]] y ==> (x==y)"
  diff_reflection: "|- P [[<->]] Q ==> (P==Q)"


(** Structural Rules on formulas are inherited from DLK0.thy **)


ML {*
(*Cut and thin, replacing the right-side formula*)
fun cutR_tac ctxt s i =
  res_inst_tac ctxt [(("P", 0), s) ] @{thm cut} i  THEN  rtac @{thm thinR} i

(*Cut and thin, replacing the left-side formula*)
fun cutL_tac ctxt s i =
  res_inst_tac ctxt [(("P", 0), s)] @{thm cut} i  THEN  rtac @{thm thinL} (i+1)
*}


(** If-and-only-if rules **)
lemma diffR: 
    "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P [[<->]] Q, $F"
  apply (unfold diff_def)
  apply (assumption | rule dconjR dimpR)+
  done

lemma diffL: 
    "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P [[<->]] Q, $G |- $E"
  apply (unfold diff_def)
  apply (assumption | rule dconjL dimpL basic)+
  done

lemma diff_refl: "$H |- $E, (P [[<->]] P), $F"
  apply (rule diffR basic)+
  done

lemma dTrueR: "$H |- $E, DTrue, $F"
  apply (unfold dTrue_def)
  apply (rule dimpR)
  apply (rule basic)
  done


(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

lemma dallL_thin: "$H, P(x), $G |- $E ==> $H, DALL x P(x), $G |- $E"
  apply (rule dallL)
  apply (erule thinL)
  done

lemma dexR_thin: "$H |- $E, P(x), $F ==> $H |- $E, DEX x P(x), $F"
  apply (rule dexR)
  apply (erule thinR)
  done

(*The rules of LK*)

ML {*
val dprop_pack = empty_pack add_safes
                [@{thm basic}, @{thm drefl}, @{thm dTrueR}, @{thm dFalseL},
                 @{thm dconjL}, @{thm dconjR}, @{thm ddisjL}, @{thm ddisjR}, @{thm dimpL}, @{thm dimpR},
                 @{thm dnotL}, @{thm dnotR}, @{thm diffL}, @{thm diffR}];

val dLK_pack = dprop_pack add_safes   [@{thm dallR}, @{thm dexL}]
                        add_unsafes [@{thm dallL_thin}, @{thm dexR_thin}];

val dLK_dup_pack = dprop_pack add_safes   [@{thm dallR}, @{thm dexL}]
                            add_unsafes [@{thm dallL}, @{thm dexR}];


fun lemma_tac th i =
    rtac (@{thm thinR} RS @{thm cut}) i THEN REPEAT (rtac @{thm thinL} i) THEN rtac th i;
*}

method_setup dfast_prop = {* Scan.succeed (K (SIMPLE_METHOD' (fast_tac dprop_pack))) *}
method_setup dfast = {* Scan.succeed (K (SIMPLE_METHOD' (fast_tac dLK_pack))) *}
method_setup dfast_dup = {* Scan.succeed (K (SIMPLE_METHOD' (fast_tac dLK_dup_pack))) *}
method_setup dbest = {* Scan.succeed (K (SIMPLE_METHOD' (best_tac dLK_pack))) *}
method_setup dbest_dup = {* Scan.succeed (K (SIMPLE_METHOD' (best_tac dLK_dup_pack))) *}


lemma dmp_R:
  assumes dmajor: "$H |- $E, $F, P [[-->]] Q"
    and dminor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule thinRS [THEN cut], rule dmajor)
  apply (tactic "step_tac dLK_pack 1")
  apply (rule thinR, rule dminor)
  done

lemma dmp_L:
  assumes dmajor: "$H, $G |- $E, P [[-->]] Q"
    and dminor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule thinL [THEN cut], rule dmajor)
  apply (tactic "step_tac dLK_pack 1")
  apply (rule thinL, rule dminor)
  done


(** Two rules to generate left- and right- rules from implications **)

lemma dR_of_imp:
  assumes dmajor: "|- P [[-->]] Q"
    and dminor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule dmp_R)
   apply (rule_tac [2] dminor)
  apply (rule thinRS, rule dmajor [THEN thinLS])
  done

lemma dL_of_imp:
  assumes dmajor: "|- P [[-->]] Q"
    and dminor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule dmp_L)
   apply (rule_tac [2] dminor)
  apply (rule thinRS, rule dmajor [THEN thinLS])
  done

(*Can be used to create implications in a subgoal*)
lemma dbackwards_impR:
  assumes prem: "$H, $G |- $E, $F, P [[-->]] Q"
  shows "$H, P, $G |- $E, Q, $F"
  apply (rule dmp_L)
   apply (rule_tac [2] basic)
  apply (rule thinR, rule prem)
  done

lemma dconjunct1: "|-P [[&]] Q ==> |-P"
  apply (erule thinR [THEN cut])
  apply dfast
  done

lemma dconjunct2: "|-P [[&]] Q ==> |-Q"
  apply (erule thinR [THEN cut])
  apply dfast
  done

lemma dspec: "|- (DALL x P(x)) ==> |- P(x)"
  apply (erule thinR [THEN cut])
  apply dfast
  done


(** Equality **)

lemma dsym: "|- a [[=]] b [[-->]] b [[=]] a"
  by (tactic {* safe_tac (dLK_pack add_safes [@{thm dsubst}]) 1 *})

lemma dtrans: "|- a [[=]] b [[-->]] b [[=]] c [[-->]] a [[=]] c"
  by (tactic {* safe_tac (dLK_pack add_safes [@{thm dsubst}]) 1 *})

(* Symmetry of equality in hypotheses *)
lemmas dsymL =dsym [THEN dL_of_imp, standard]

(* Symmetry of equality in hypotheses *)
lemmas dsymR = dsym [THEN dR_of_imp, standard]

lemma dtransR: "[| $H|- $E, $F, a [[=]] b;  $H|- $E, $F, b [[=]] c |] ==> $H|- $E, a [[=]] c, $F"
  by (rule dtrans [THEN dR_of_imp, THEN dmp_R])

(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

lemma ddef_imp_iff: "(A == B) ==> |- A [[<->]] B"
  apply unfold
  apply (rule diff_refl)
  done

lemma dmeta_eq_to_obj_eq: "(A == B) ==> |- A [[=]] B"
  apply (unfold)
  apply (rule drefl)
  done

(*New added axioms for formulas of DC expressions are not specified here, since the expressions form are limited.*)
(*Arith*)

end
