header {*The sequent calculus for interval logic: all the rules are taken from 
        "Duration Calculus: A formal approach to real-time systems", by Zhou Chaochen and Michael R. Hansen*}

theory ILSequent
imports DDLK0
begin


(*the special variable l is always greater or equal than 0*)
axiomatization where
A0 : "DTrue == l[[>=]] DR 0"

section {*Definitions and rules for rigid and chop-free.*}

primrec CF:: "dform => bool" ("CF _")
where
 "CF (DTrue) = True" |
 "CF (DFalse) = True" |
 "CF (s [[=]] t) = True" |
 "CF (s [[>]] t) = True" |
 "CF (s [[<]] t) = True" |
 "CF ([[~]]P) = (CF (P))" |
 "CF (P[[&]]Q) = (CF (P) & CF (Q))"|
 "CF (P[[|]]Q) = (CF (P) & CF (Q))" |
 "CF (P[[-->]]Q) = (CF (P) & CF (Q))" |
 "CF (P[[<->]]Q) = (CF (P) & CF (Q))" |
 "CF (DALL x P) = (CF (P))" |
 "CF (DEX x P) = (CF (P))" |
 "CF (P [^] Q) = False"

(*RIt: a term is rigid*)
primrec RIt :: "dexp => bool"  ("RIt _" 50)
where
"RIt (l) = False" |
"RIt (Dur S) = False" |
"RIt (DR s) = True" |
"RIt (t [[+]] m) = (RIt (t) & RIt (m))"

(*RI: a dc formula is rigid: notice that in quantified formulas, variable x is interval independent*)
primrec RI :: "dform => bool" ("RI _")
where
 "RI (DTrue) = True" |
 "RI (DFalse) = True" |
 "RI (s [[=]] t) = (RIt (s) & RIt(t))" |
 "RI (s [[>]] t) = (RIt (s) & RIt(t))" |
 "RI (s [[<]] t) = (RIt (s) & RIt(t))" |
 "RI ([[~]]P) = (RI (P))" |
 "RI (P[[&]]Q) = (RI (P) & RI (Q))"|
 "RI (P[[|]]Q) = (RI (P) & RI (Q))" |
 "RI (P[[-->]]Q) = (RI (P) & RI (Q))" |
 "RI (P[[<->]]Q) = (RI (P) & RI (Q))" |
 "RI (DALL x P) = (RI (P))" |
 "RI (DEX x P) = (RI (P))" |
 "RI (P [^] Q) = (RI (P) & RI (Q))"

section {*Sequent rules for the other modalities [Zhou and Hansen modified].*}
axiomatization where
LA2:                 "$H, P [^] (Q [^] R) |- $E ==> $H, (P [^] Q) [^] R |- $E" and
RA2:                 "$H |- P [^] (Q [^] R), $E ==> $H |- (P [^] Q) [^] R, $E" and

R1R:                 "[|RI P; $H |- P [^] Q, $E|] ==> $H |- P, $E" and
R2R:                 "[|RI Q; $H |- P [^] Q, $E|] ==> $H |- Q, $E" and

LL1:                  "[| RIt s; $H |- (l [[=]] s) [^] P, $E |] ==> $H, (l [[=]] s) [^] ([[~]]P) |- $E" and
RL1:                  "[| RIt s; $H , (l [[=]] s) [^] P |- $E |] ==> $H |- (l [[=]] s) [^] ([[~]]P), $E" and
LL1a:                "[| RIt s; $H |- P [^] (l [[=]] s) , $E |] ==> $H, ([[~]]P) [^] (l [[=]] s) |- $E" and
RL1a:                "[| RIt s; $H , P [^] (l [[=]] s)  |- $E |] ==> $H |- ([[~]]P) [^] (l [[=]] s), $E" and 


LL2:                "[| RIt s; RIt t; $H, l [[=]] (s [[+]] t) |- $E |] ==> $H, (l [[=]] s) [^] (l [[=]] t) |- $E" and
RL2:                "[| RIt s; RIt t; $H |- l [[=]] (s [[+]] t), $E |] ==> $H |- (l [[=]] s) [^] (l [[=]] t), $E" and

LL3:                " $H |- P, $E ==> $H  |- P [^] (l [[=]] (DR 0)), $E" and
(*RL3:                " $H, P [^] (l [[=]] Real 0) |- $E ==> $H, P |- $E" and *)
LL4:                " $H, P |- $E ==> $H, P [^] (l [[=]] DR 0) |- $E" and
(*RL4:                " $H |- P, $E ==> $H  |- P [^] (l [[=]] (Real 0)), $E" and*)
LL3a:                " $H, P |- $E ==> $H, (l [[=]] (DR 0)) [^] P |- $E" and
RL3a:                " $H |- P, $E ==> $H  |- (l [[=]] (DR 0)) [^] P, $E" and

(*The following 4 rules correspond to IL14 in the book, theorems, should be proved in fact not axiomed.*)
LT1:                  "[| $H, P [^] Q |- $E;  $H, R [^] Q |- $E|] ==> $H, (P [[|]] R) [^] Q |- $E" and
RT1:                  "$H |- P [^] Q, R [^] Q, $E ==> $H |- (P [[|]] R) [^] Q, $E" and
LT1a:                "[| $H, P [^] Q |- $E;  $H, P [^] R |- $E|] ==> $H, P [^] (Q [[|]] R) |- $E" and
RT1a:                "$H |- P [^] Q, P [^] R, $E ==> $H |- P [^] (Q [[|]] R), $E" 


(*The following 4 rules correspond to the E rule in the book.*)
axiomatization where
LB1:                  "(!!x. $H, (P(x) [^] Q) |- $E) ==> $H, ((DEX x P(x)) [^] Q) |- $E" and
RB1:                 "[|RIt s; CF P(x); $H |- P(x) [^] Q, $E|] ==> $H |- (DEX x P(x)) [^] Q, $E" 

axiomatization where
LBr:                  "(!!x. $H, (P [^] Q(x)) |- $E) ==> $H, (P [^] (DEX x Q(x))) |- $E" and
RBr:                 "[|RIt s; CF Q(x); $H |- P [^] Q(x), $E|] ==> $H |- P [^] (DEX x Q(x)), $E" 

axiomatization where
MP:  "[|$H |- P, $E; $H, P |- Q, $E|] ==> $H |- Q, $E" and
G : "$H |- P, $E ==> $H |- DALL x P, $E" and
N1 : "$H |- P, $E ==> $H, ([[~]]P) [^] Q |- $E" and
N2 : "$H |- P, $E ==> $H, Q [^] ([[~]]P)  |- $E" and

M1 : "$H, P |- Q, $E ==> $H, P [^] R |- Q [^] R, $E"and
M2 : "$H, P |- Q, $E ==> $H, R [^] P |- R [^] Q, $E"


end
