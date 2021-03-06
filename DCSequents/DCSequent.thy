header {*The axioms and inference rules for dc, from the book by Zhou Chaochen and Michael Hansen.*}
theory DCSequent
imports ILSequent
begin


type_synonym s = fform


(* Axioms for DC for reasoning about state durations.*)
axiomatization where
DA1              : "|- Dur (WFalse) [[=]] DR 0" and
DA2              : "|- Dur (WTrue) [[=]] l" and
DA3a             : " (l [[=]] DR 0) |- (dur (S) [[=]] DR 0)" and
DA3b             : " (DR 0 [[<=]]  l) |- (DR 0 [[<=]] dur (S)) " and
DA4              : " |- Dur (S1) [[+]] Dur (S2) [[=]] Dur (S1 [|] S2) [[+]] Dur (S1 [&] S2)" and
DA5              : " [|RIt s; RIt t|] ==>
                 (Dur (S) [[=]] s [^]  Dur (S) [[=]] t) |- Dur (S) [[=]] s [[+]] t" and
DA5a              : " [|RIt s; RIt t|] ==>
                 Dur (S) [[=]] s [[+]] t |- (Dur (S) [[=]] s [^]  Dur (S) [[=]] t) " and
DA6              : "|- s1 [<->] s2 ==> |- Dur (s1) [[=]] Dur (s2)"

(*Part of theorems given in [Zhou&Hansen03] for DC*)
axiomatization where
DC11     : "$H, (almost WFalse) |- $H, DFalse" and
DC12    : "$H |- $E, (almost ([~]s)) ==> $H |- $E, (Dur (s) [[=]] (DR 0))" and
DC18     : "$H, s |- t ==> $H, (almost s) |- (almost t)" and
DCR3    : "$H |- (almost S) [^] (almost S), $E ==> $H |- (almost S),$E" and
DCL4    : "$H, (almost S)[^](almost S) |-$E ==> $H,(almost S) |- $E" and
DCM     : "[|$H,(almost Q),$F |- $E; $H, P, $F |- Q|] ==> $H,(almost P),$F |- $E" and
DCAL : "|- p [-->] q ==> |- almost p [[-->]] almost q"


end
