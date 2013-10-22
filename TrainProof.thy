theory TrainProof
imports Train
begin
(*Precondition Pre: three conjuncts VA and Vinv and Ain*)
(*Constraints for v and a*)
definition VA :: "fform" where
"VA == ((v [>] Real (vmax - cmax * T1 - cmax * T2)) [-->] (a [<] Real 0)) [&]
       ((v [<] Real (cmax * T1 + cmax*T2)) [-->] (a [>=] Real 0))"

definition Vinv :: "fform" where
"Vinv == (v [>=] Real 0) [&] (v [<=] Real vmax)"

definition Ainv :: "fform" where
"Ainv == (a [<=] Real cmax) [&] (a [>=] Real -cmax)"

definition Pre :: "fform" where
"Pre == VA [&] Vinv [&] Ainv"

section {*Invariants*}
(*Differential Invariants for the three above continuous in Move1, Move2, and SelfC*)
definition Acc1 :: "fform" where
"Acc1 == (a [<] Real 0 [&] ((v [>=] (Real (cmax * T2) [+] (a [*] t1) [+] Real (cmax * T1)) [&] (v [<=] Real vmax))))"
definition Acc2 :: "fform" where
"Acc2 == (a [>=] Real 0 [&] ((v [<=] ((Real vmax) [+] (a [*] t1)  [+] (Real (-cmax * T2))  [+] Real (-cmax * T1))) [&] (v [>=] Real 0)))"

definition Inv1 :: "fform" where
"Inv1 == ((t1 [>=] (Real 0)) [&] (t1 [<=] (Real T1))) [&]
        (Acc1 [|] Acc2)"

definition Acc3 :: "fform" where
"Acc3 ==  (a [<] Real 0 [&] ((v [>=] (Real (cmax * T2) [+] (a [*] t2)) [&] (v [<=] Real vmax))))"
definition Acc4 :: "fform" where
"Acc4 ==  (a [>=] Real 0 [&] ((v [<=] ((Real vmax) [+] (a [*] t2)  [+] (Real (-cmax * T2)))) [&] (v [>=] Real 0)))"

definition Inv2 :: "fform" where
"Inv2 == ((t2 [>=] (Real 0)) [&] (t2 [<=] (Real T2))) [&]
         (Acc3 [|] Acc4)"

definition Inv3 :: "fform" where
"Inv3 ==  (v [>=] Real 0) [&]  (v [<=] Real vmax)"

section {*Proof*}

(*General Lemmas*)
lemma chopalmostz : "|- almostz S [^] almostz S [[-->]] almostz S"
apply (simp add: almostz_def) apply (rule dimpR)
apply (rule LT1) apply (rule LT1a)
apply (rule ddisjR) apply (rule DCR3) apply dfast
apply (rule ddisjR) apply (rule LL4) apply dfast
apply (rule LT1a) apply (rule ddisjR)
apply (rule LL3a) apply dfast
apply (rule ddisjR) apply (rule LL4) apply dfast
done

lemma Almostfact : " |- p [-->] q ==> |- almostz p [[-->]] almostz q"
apply (cut_tac p = p and q = q in DCAL, auto)
apply (rule dimpR)
apply (simp add:almostz_def)
apply (rule ddisjR)
apply (rule ddisjL)
apply (cut_tac P = "almost p" in dmp_R, auto)
apply (rule thinL)
apply (rule thinR)
apply assumption
apply dfast+
done 

definition mid1 :: "fform" where
"mid1 == ((t1 [<] Real T1 [-->] VA) [|] (t1 [>=] Real T1)) [&] Vinv [&] Ainv"

lemma Midfact : "(mid1 [&] [~] t1 [>=] Real T1) |- Pre"
apply (simp add:mid1_def Pre_def)
apply (rule conjL)+ apply (rule notL) apply (rule conjR)+
apply (rule disjL) apply (rule impL) apply (rule thinR) 
apply (rule exchR) apply (simp add:equal_greater_def)
apply (rule disjR) apply (rule Trans22) apply (simp add:t1_def)
apply arith apply fast+
done

definition mid11 :: "fform" where
"mid11 == (Lex (WEX ''s'' WEX ''v'' WEX ''t1'' Pre [&] t1 [=] Real 0) [&] (t1 [>=] Real T1) [&] close(Inv1) mvar b1)"

definition mid22 :: "fform" where
"mid22 ==  Lex (WEX ''s'' WEX ''v'' WEX ''t1'' Pre [&] t1 [=] Real 0) [&]
                    t1 [<] Real T1 [&] Inv1 mvar b1"

lemma mid11fact : "mid11 |- Ainv [&] (t1 [>] Real T1 [|] t1 [=] Real T1) [&] close(Inv1)"
apply (simp add:mid11_def) apply (rule conjR)
apply (simp add:b1_def Pre_def Ainv_def a_def)
apply fast apply (rule conjR) apply (simp add:b1_def t1_def equal_greater_def)
apply fast apply (simp add:b1_def Inv1_def) apply fast
done 

lemma mid22fact : "mid22 |- Ainv [&] (t1 [<] Real T1) [&] Inv1"
apply (simp add:mid22_def) apply (rule conjR)
apply (simp add:b1_def Pre_def Ainv_def a_def)
apply fast apply (rule conjR) apply (simp add:b1_def t1_def equal_greater_def)
apply fast apply (simp add:b1_def Inv1_def) apply fast
done 

lemma simple1[simp] : "formT(RVar ''a'' [>=] Real - cmax) == rvar(''a'') >=  - cmax"
apply (simp add:equal_greater_def)
apply arith
done 

lemma simple2[simp] : "formT(RVar ''t1'' [>=] Real 0) == rvar(''t1'') >= 0"
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma simple3[simp] : "formT(RVar ''t1'' [<=] Real T1) == rvar(''t1'') <= T1"
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma simple4[simp] : "formT(RVar ''v'' [>=]
                     Real cmax * T2 [+] RVar ''a'' [*] RVar ''t1'' [+] Real cmax * T1) 
                       ==
                      rvar(''v'') >= cmax * T2 + rvar(''a'') * rvar (''t1'') + cmax*T1 
                     "
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma simple5[simp] : "formT(RVar ''v'' [<=] Real vmax) ==  rvar(''v'') <= vmax"
                       
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma simple6[simp] : "formT(RVar ''v'' [>=] Real 0) == rvar(''v'') >= 0"
apply (simp add:equal_greater_def)
apply arith
done

lemma mid11fact21 : "  a [>=] Real - cmax [&]
                       (t1 [>=] Real 0 [&] t1 [<=] Real T1) [&]
                       close(Acc1)
                      |- v [>=] Real 0 [&] v [<=] Real vmax"
apply (rule conjL)+
apply (simp add:Acc1_def a_def v_def t1_def)
apply (rule Trans4, simp)
apply (subgoal_tac "rvar(''a'') * rvar(''t1'') >= -(cmax * T1)")
apply (subgoal_tac "cmax * T2 <= rvar(''v'')")
apply (subgoal_tac "cmax>0 & T2>0")
apply (metis less_trans mult_pos_pos not_le, simp)
apply smt
apply (subgoal_tac "cmax >0 & T1>0")
apply (smt comm_semiring_1_class.normalizing_semiring_rules(7) less_eq_neg_nonpos less_le_trans less_minus_iff linear linorder_neqE_linordered_idom minus_le_iff minus_less_iff minus_mult_commute minus_mult_right mult_left_mono_neg mult_less_cancel_left_disj mult_strict_mono neg_0_less_iff_less neg_equal_0_iff_equal neg_le_iff_le not_le not_less not_less_iff_gr_or_eq)
apply simp
done 

lemma mid22fact21 : " a [>=] Real - cmax [&] (t1 [>=] Real 0 [&] t1 [<=] Real T1) [&] Acc1
                      |- v [>=] Real 0 [&] v [<=] Real vmax"
apply (rule conjL)+
apply (simp add:Acc1_def a_def v_def t1_def)
apply (rule Trans4, simp)
apply (subgoal_tac "rvar(''a'') * rvar(''t1'') >= -(cmax * T1)")
apply (subgoal_tac "cmax * T2 <= rvar(''v'')")
apply (subgoal_tac "cmax>0 & T2>0")
apply (metis less_trans mult_pos_pos not_le, simp)
apply smt
apply (subgoal_tac "cmax >0 & T1>0")
apply (smt comm_semiring_1_class.normalizing_semiring_rules(7) less_eq_neg_nonpos less_le_trans less_minus_iff linear linorder_neqE_linordered_idom minus_le_iff minus_less_iff minus_mult_commute minus_mult_right mult_left_mono_neg mult_less_cancel_left_disj mult_strict_mono neg_0_less_iff_less neg_equal_0_iff_equal neg_le_iff_le not_le not_less not_less_iff_gr_or_eq)
apply simp
done 

lemma simple7[simp] : "formT(RVar ''a'' [<=] Real cmax) == rvar(''a'') <=  cmax"
apply (simp add:equal_less_def)
apply arith
done 

lemma simple8[simp] : "formT(RVar ''a'' [>=] Real 0) == rvar(''a'') >=  0"
apply (simp add:equal_greater_def)
apply arith
done 


lemma simple9[simp] : "formT(RVar ''v'' [<=] Real vmax [+]
               RVar ''a'' [*] RVar ''t1'' [+] Real - (cmax * T2) [+] Real - (cmax * T1)) 
                       ==
                      rvar(''v'') <= vmax + rvar(''a'') * rvar (''t1'') - cmax*T2 -cmax * T1
                     "
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma mid11fact22 : "  a [<=] Real cmax [&]
                       (t1 [>=] Real 0 [&] t1 [<=] Real T1) [&]
                       close(Acc2)
                      |- v [>=] Real 0 [&] v [<=] Real vmax"
apply (rule conjL)+
apply (simp add:Acc2_def a_def v_def t1_def)
apply (rule Trans4, simp)
apply (subgoal_tac "rvar(''a'') * rvar(''t1'') <= (cmax * T1)")
apply (subgoal_tac "rvar(''v'') <= vmax - cmax * T2")
apply (subgoal_tac "cmax>0 & T2>0 & vmax>0")
apply (smt real_minus_mult_self_le real_mult_le_cancel_iff2 real_mult_less_iff1)
apply simp
apply smt
apply (metis mult_mono')
done

lemma mid22fact22 : "a [<=] Real cmax [&] (t1 [>=] Real 0 [&] t1 [<=] Real T1) [&] Acc2
                     |- v [>=] Real 0 [&] v [<=] Real vmax"
apply (rule conjL)+
apply (simp add:Acc2_def a_def v_def t1_def)
apply (rule Trans4, simp)
apply (subgoal_tac "rvar(''a'') * rvar(''t1'') <= (cmax * T1)")
apply (subgoal_tac "rvar(''v'') <= vmax - cmax * T2")
apply (subgoal_tac "cmax>0 & T2>0 & vmax>0")
apply (smt real_minus_mult_self_le real_mult_le_cancel_iff2 real_mult_less_iff1)
apply simp
apply smt
apply (metis mult_mono')
done

lemma mid11fact2 : "Ainv [&] (t1 [>=] Real T1) [&] close(Inv1) |- Vinv"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv1_def)
apply (cut_tac P = "(a [<=] Real cmax [&]
                       (close(t1 [>=] Real 0) [&] close(t1 [<=] Real T1)) [&]
                       close(Acc2)) [|] (a [>=] Real - cmax [&]
                       (close(t1 [>=] Real 0) [&] close(t1 [<=] Real T1)) [&]
                       close(Acc1))" in cut, auto)
apply fast  apply (rule thinL)
apply (rule disjL)  apply (rule mid11fact22)
apply (rule mid11fact21)
done

lemma mid22fact2 : "Ainv [&] (t1 [<] Real T1) [&] Inv1 |- Vinv"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv1_def)
apply (cut_tac P = "(a [<=] Real cmax [&]
                       (t1 [>=] Real 0 [&] t1 [<=] Real T1) [&]
                       Acc2) [|] (a [>=] Real - cmax [&]
                       (t1 [>=] Real 0 [&] t1 [<=] Real T1) [&]
                       Acc1)" in cut, auto)
apply fast  apply (rule thinL)
apply (rule disjL)  apply (rule mid22fact22)
apply (rule mid22fact21)
done

lemma mid22fact3 : "mid22 |- Vinv"
apply (cut_tac P = "Ainv [&] (t1 [<] Real T1) [&] Inv1" in cut, auto)
apply (rule thinR) apply (rule mid22fact) apply (rule thinL)
apply (rule mid22fact2)
done

lemma mid11fact3 : "mid11 |- Vinv"
apply (cut_tac P = "Ainv [&] (t1 [>] Real T1 [|] t1 [=] Real T1) [&] close(Inv1)" in cut, auto)
apply (rule thinR) apply (rule mid11fact) apply (rule thinL)
apply (cut_tac P = "Ainv [&] (t1 [>=] Real T1) [&] close(Inv1)" in cut, auto)
apply (simp add:equal_greater_def)
apply fast apply (rule thinL) apply (rule mid11fact2)
done

lemma mid1fact : " (mid11 [|] Pre) |- mid1 "
apply (rule disjL) apply (simp add:mid1_def)
apply (rule conjR)+  apply (simp add:mid11_def b1_def Pre_def)
apply fast  apply (rule conjR) apply (rule mid11fact3)
apply (simp add:mid11_def Pre_def b1_def)
apply (simp add:Ainv_def uv_def wv_def a_def)
apply fast apply (simp add:Pre_def mid1_def) apply fast
done 


lemma mid2fact2 : "|- almostz mid22 [[-->]] almostz Vinv"
apply (rule Almostfact) apply (rule impR) apply (rule mid22fact3)
done 

lemma mid2fact4: "|- almostz Vinv [^] (l [[=]] DR 0 [[|]] almostz Vinv) [[-->]] almostz Vinv"
apply (rule dimpR) apply (rule LT1a) defer
apply (cut_tac S = "Vinv" in chopalmostz) 
apply (rule dbackwards_impR) apply assumption
apply (rule LL4) apply dfast 
done 

lemma mid2fact5 : "almostz mid22 [^] (l [[=]] DR 0 [[|]] almostz Vinv)   |- almostz Vinv"
apply (cut_tac P = "almostz Vinv [^] (l [[=]] DR 0 [[|]] almostz Vinv)" in cut, auto)
apply (rule thinR) apply (rule M1) apply (rule dbackwards_impR) apply (rule mid2fact2)
apply (rule thinL) apply (rule dbackwards_impR) apply (rule mid2fact4)
done

definition afterb1 :: "fform" where
"afterb1 == Lex (WEX ''s'' WEX ''v'' WEX ''t1'' Pre [&] t1 [=] Real 0) [&] close(Inv1) mvar b1 [&]
                    bAck(b1)"

definition case1B :: "fform" where
"case1B == (BVar uv [=] Bool True [&] BVar wv [=] Bool True)"

definition mid2 :: "fform" where
"mid2 == ((t2 [<] Real T2 [-->] VA) [|] (t2 [>=] Real T2)) [&] Vinv [&] Ainv [&] case1B"
definition mid211 :: "fform" where
"mid211 ==  Lex (WEX ''s'' WEX ''v'' WEX ''t2'' afterb1 [&] case1B [&] t2 [=] Real 0) [&]
            (t2 [>] Real T2 [|] t2 [=] Real T2) [&] close(Inv2) mvar b2"
definition mid212 :: "fform" where
"mid212 == Lex (WEX ''s'' WEX ''v'' WEX ''t2'' afterb1 [&] case1B [&] t2 [=] Real 0) [&]
                t2 [<] Real T2 [&] Inv2 mvar b2"

lemma mid211fact : "mid211 |- Ainv [&] (t2 [>] Real T2 [|] t2 [=] Real T2) [&] close(Inv2)"
apply (rule conjR)
apply (simp add:mid211_def b2_def afterb1_def b1_def Pre_def)
apply fast
apply (simp add:mid211_def b2_def)
apply fast
done

definition BreakPre :: "fform" where
"BreakPre == Lex (WEX ''s'' WEX ''v'' WEX ''t2'' afterb1 [&] case1B [&] t2 [=] Real 0) [&]
         close(Inv2) mvar b2 [&] bAck(b2)"
lemma Break211fact : "BreakPre |- Ainv [&] close(Inv2)"
apply (rule conjR)
apply (simp add:BreakPre_def b2_def afterb1_def b1_def Pre_def)
apply fast
apply (simp add:BreakPre_def b2_def)
apply fast
done

 
lemma simple22[simp] : "formT(RVar ''t2'' [>=] Real 0) == rvar(''t2'') >= 0"
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma simple23[simp] : "formT(RVar ''t2'' [<=] Real T2) == rvar(''t2'') <= T2"
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma simple29[simp] : "formT(RVar ''v'' [<=]
                          Real vmax [+] RVar ''a'' [*] RVar ''t2'' [+] Real - (cmax * T2)) 
                       ==
                      rvar(''v'') <= vmax + rvar(''a'') * rvar (''t2'') - cmax*T2
                     "
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma mid211fact22 : "a [<=] Real cmax [&] (t2 [>=] Real 0 [&] t2 [<=] Real T2) [&] close(Acc4)
    |- v [>=] Real 0 [&] v [<=] Real vmax"
apply (rule conjL)+
apply (simp add:Acc4_def a_def v_def t2_def)
apply (rule Trans4, simp)
apply (subgoal_tac "rvar(''a'') * rvar(''t2'') >= -(cmax * T2)")
apply (subgoal_tac "cmax>0 & T2>0")
apply (smt real_mult_le_cancel_iff2 real_mult_less_iff1 real_two_squares_add_zero_iff)
apply simp
apply (subgoal_tac "cmax >0 & T2>0")
apply (smt comm_semiring_1_class.normalizing_semiring_rules(7) less_eq_neg_nonpos less_le_trans less_minus_iff linear linorder_neqE_linordered_idom minus_le_iff minus_less_iff minus_mult_commute minus_mult_right mult_left_mono_neg mult_less_cancel_left_disj mult_strict_mono neg_0_less_iff_less neg_equal_0_iff_equal neg_le_iff_le not_le not_less not_less_iff_gr_or_eq)
apply simp
done 

lemma mid212fact22 : "a [<=] Real cmax [&] (t2 [>=] Real 0 [&] t2 [<=] Real T2) [&] Acc4
    |- v [>=] Real 0 [&] v [<=] Real vmax"

apply (rule conjL)+
apply (simp add:Acc4_def a_def v_def t2_def)
apply (rule Trans4, simp)
apply (subgoal_tac "rvar(''a'') * rvar(''t2'') >= -(cmax * T2)")
apply (subgoal_tac "cmax>0 & T2>0")
apply (smt real_mult_le_cancel_iff2 real_mult_less_iff1 real_two_squares_add_zero_iff)
apply simp
apply (subgoal_tac "cmax >0 & T2>0")
apply (smt comm_semiring_1_class.normalizing_semiring_rules(7) less_eq_neg_nonpos less_le_trans less_minus_iff linear linorder_neqE_linordered_idom minus_le_iff minus_less_iff minus_mult_commute minus_mult_right mult_left_mono_neg mult_less_cancel_left_disj mult_strict_mono neg_0_less_iff_less neg_equal_0_iff_equal neg_le_iff_le not_le not_less not_less_iff_gr_or_eq)
apply simp
done 


lemma simple24[simp] : "formT(RVar ''v'' [>=] Real cmax * T2 [+] RVar ''a'' [*] RVar ''t2'')
                       ==
                      rvar(''v'') >= cmax * T2 + rvar(''a'') * rvar (''t2'') 
                     "
apply (simp add:equal_greater_def equal_less_def)
apply arith
done

lemma mid211fact21 : "a [>=] Real - cmax [&] (t2 [>=] Real 0 [&] t2 [<=] Real T2) [&] close(Acc3)
    |- v [>=] Real 0 [&] v [<=] Real vmax"
apply (rule conjL)+
apply (simp add:Acc3_def a_def v_def t2_def)
apply (rule Trans4, simp)
apply (subgoal_tac "rvar(''a'') * rvar(''t2'') >= -(cmax * T2)")
apply (subgoal_tac "cmax>0 & T2>0")
apply smt apply simp
apply (subgoal_tac "cmax >0 & T2>0")
apply (smt comm_semiring_1_class.normalizing_semiring_rules(7) less_eq_neg_nonpos less_le_trans less_minus_iff linear linorder_neqE_linordered_idom minus_le_iff minus_less_iff minus_mult_commute minus_mult_right mult_left_mono_neg mult_less_cancel_left_disj mult_strict_mono neg_0_less_iff_less neg_equal_0_iff_equal neg_le_iff_le not_le not_less not_less_iff_gr_or_eq)
apply simp
done 

lemma mid212fact21: "a [>=] Real - cmax [&] (t2 [>=] Real 0 [&] t2 [<=] Real T2) [&] Acc3
    |- v [>=] Real 0 [&] v [<=] Real vmax"
apply (rule conjL)+
apply (simp add:Acc3_def a_def v_def t2_def)
apply (rule Trans4, simp)
apply (subgoal_tac "rvar(''a'') * rvar(''t2'') >= -(cmax * T2)")
apply (subgoal_tac "cmax>0 & T2>0")
apply smt apply simp
apply (subgoal_tac "cmax >0 & T2>0")
apply (smt comm_semiring_1_class.normalizing_semiring_rules(7) less_eq_neg_nonpos less_le_trans less_minus_iff linear linorder_neqE_linordered_idom minus_le_iff minus_less_iff minus_mult_commute minus_mult_right mult_left_mono_neg mult_less_cancel_left_disj mult_strict_mono neg_0_less_iff_less neg_equal_0_iff_equal neg_le_iff_le not_le not_less not_less_iff_gr_or_eq)
apply simp
done 



lemma mid211fact2 : "Ainv [&] t2 [>=] Real T2 [&] close(Inv2) |- Vinv"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv2_def)
apply (cut_tac P = "(a [<=] Real cmax [&]
                       (close(t2 [>=] Real 0) [&] close(t2 [<=] Real T2)) [&]
                       close(Acc4)) [|] (a [>=] Real - cmax [&]
                       (close(t2 [>=] Real 0) [&] close(t2 [<=] Real T2)) [&]
                       close(Acc3))" in cut, auto)
apply fast  apply (rule thinL)
apply (rule disjL)  apply (rule mid211fact22)
apply (rule mid211fact21)
done

lemma Break211fact2 : "Ainv [&] close(Inv2) |- Vinv"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv2_def)
apply (cut_tac P = "(a [<=] Real cmax [&]
                       (close(t2 [>=] Real 0) [&] close(t2 [<=] Real T2)) [&]
                       close(Acc4)) [|] (a [>=] Real - cmax [&]
                       (close(t2 [>=] Real 0) [&] close(t2 [<=] Real T2)) [&]
                       close(Acc3))" in cut, auto)
apply fast  apply (rule thinL)
apply (rule disjL)  apply (rule mid211fact22)
apply (rule mid211fact21)
done

lemma mid211fact3 : "mid211 |- Vinv"
apply (cut_tac P = "Ainv [&] (t2 [>] Real T2 [|] t2 [=] Real T2) [&] close(Inv2)" in cut, auto)
apply (rule thinR) apply (rule mid211fact) apply (rule thinL)
apply (cut_tac P = "Ainv [&] (t2 [>=] Real T2) [&] close(Inv2)" in cut, auto)
apply (simp add:equal_greater_def)
apply fast apply (rule thinL) apply (rule mid211fact2)
done

definition case11B :: "fform" where
"case11B == BVar wa [=] Bool True"

lemma Breakfact11 : "BreakPre |- Vinv"
apply (cut_tac P = "Ainv [&] close(Inv2)" in cut, auto)
apply (rule thinR) apply (rule Break211fact) apply (rule thinL)
apply (cut_tac P = "Ainv [&] close(Inv2)" in cut, auto)
apply fast apply (rule thinL) apply (rule Break211fact2)
done

lemma mid212fact31 : "mid212 |- Ainv [&] t2 [<] Real T2 [&] Inv2"
apply (simp add:mid212_def) apply (rule conjR)
apply (simp add:b2_def afterb1_def Pre_def b1_def)
apply fast apply (rule conjR) apply (simp add:b2_def)
apply fast apply (simp add:b2_def) apply fast
done 

lemma mid212fact32: "Ainv [&] t2 [<] Real T2 [&] Inv2 |- Vinv"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv2_def)
apply (cut_tac P = "(a [<=] Real cmax [&]
                       (t2 [>=] Real 0 [&] t2 [<=] Real T2) [&]
                       Acc4) [|] (a [>=] Real - cmax [&]
                       (t2 [>=] Real 0 [&] t2 [<=] Real T2) [&]
                       Acc3)" in cut, auto)
apply fast  apply (rule thinL)
apply (rule disjL)  apply (rule mid212fact22)
apply (rule mid212fact21)
done

lemma mid212fact3 : "mid212 |- Vinv"
apply (cut_tac P = "Ainv [&] (t2 [<] Real T2) [&] Inv2" in cut, auto)
apply (rule thinR) apply (rule mid212fact31) apply (rule thinL)
apply (rule mid212fact32)
done


lemma mid2fact : " (mid211 [|] (Pre [&] case1B)) |- mid2 "
apply (rule disjL) apply (simp add:mid2_def)
apply (rule conjR)+ apply (rule disjR) apply (rule thinR)
apply (simp add:mid211_def b1_def b2_def equal_greater_def)
apply fast apply (rule conjR) apply (rule mid211fact3)
apply (rule conjR) apply (simp add:mid211_def b2_def afterb1_def b1_def Pre_def)
apply fast apply (simp add:mid211_def b2_def)
apply fast apply (simp add:Pre_def mid2_def) apply fast
done 

lemma mid212fact2 : "|-almostz mid212 [[-->]] almostz Vinv"
apply (rule Almostfact) apply (rule impR) apply (rule mid212fact3)
done 


lemma mid212fact : "almostz mid212 [^] (l [[=]] DR 0 [[|]] almostz Vinv) |- almostz Vinv"
apply (cut_tac P = "almostz Vinv [^] (l [[=]] DR 0 [[|]] almostz Vinv)" in cut, auto)
apply (rule thinR) apply (rule M1) apply (rule dbackwards_impR) apply (rule mid212fact2)
apply (rule thinL) apply (rule dbackwards_impR) apply (rule mid2fact4)
done

lemma VAyfact1 : "{(BreakPre [&] BVar wa [=] Bool True) [&]
     VAy}a := ya{Pre [&] case1B [&] case11B [&] VAy;almostz Vinv}"
apply (rule Assign, auto)
apply (simp add:a_def xa_def Pre_def VA_def Vinv_def Ainv_def equal_greater_def equal_less_def)
apply (simp add:a_def xa_def case1B_def)
apply (simp add:a_def xa_def case11B_def)
apply (simp add:a_def xa_def VAy_def ya_def equal_greater_def equal_less_def)
apply (rule impR) apply (rule conjR)+
apply (simp add:a_def xa_def Pre_def VA_def Vinv_def Ainv_def equal_greater_def equal_less_def v_def)
apply (rule conjR) apply (simp add:VAy_def v_def ya_def equal_greater_def)
apply fast  apply (rule conjR) apply (rule conjL) apply (cut_tac P = "Vinv" in cut, auto) 
apply (rule thinR) apply (rule conjL) apply (rule exchL) apply (rule thinL)
apply (rule exchL) apply (rule thinL) apply (rule Breakfact11)
apply (simp add:Vinv_def equal_greater_def equal_less_def v_def) apply fast
apply (rule conjL) apply (rule thinL) 
apply (simp add:VAy_def)  apply (rule conjL) apply (rule conjL)
apply (simp add:v_def ya_def equal_greater_def equal_less_def) 
apply (rule Trans3, auto) apply (simp add:case1B_def a_def ya_def case11B_def VAy_def equal_greater_def equal_less_def v_def BreakPre_def b2_def exist_def)
apply fast apply (simp add:almostz_def) apply dfast
done 

lemma VAyfact : "{BreakPre [&] BVar wa [=] Bool True}
                     IF VAy a := ya{BreakPre [&] case11B [&] [~] VAy [|]
                              Pre [&] case1B [&] case11B [&] VAy;almostz Vinv}"
apply (cut_tac qx = "Pre [&] case1B [&] case11B [&] VAy" and hx = "almostz Vinv" in IFelse, auto)
defer apply (simp add:case11B_def) apply (rule impR) apply (rule disjR)
apply (rule disjL) apply fast+ apply (simp add:almostz_def) apply dfast
apply (rule VAyfact1)
done

lemma Assignfact1 : "{BreakPre [&]
     case11B}a := (Real - cmax){Vinv [&] case1B [&] case11B;almostz Vinv}"
apply (rule Assign, auto)
apply (simp add:a_def xa_def Pre_def VA_def Vinv_def Ainv_def equal_greater_def equal_less_def)
apply (simp add:a_def xa_def case1B_def)
apply (simp add:a_def xa_def case11B_def)
apply (simp add:a_def xa_def VAy_def ya_def equal_greater_def equal_less_def)
apply (rule impR) apply (rule conjR)+
apply (simp add:a_def xa_def Pre_def VA_def Vinv_def Ainv_def equal_greater_def equal_less_def v_def) apply (rule conjL) apply (rule exchL) apply (rule thinL)
apply (cut_tac P = "Vinv" in cut, auto) 
apply (rule thinR) apply (rule Breakfact11)
apply (simp add:Vinv_def equal_greater_def equal_less_def v_def) apply fast
apply (simp add:case1B_def a_def ya_def case11B_def VAy_def equal_greater_def equal_less_def v_def BreakPre_def b2_def exist_def)
apply fast apply (simp add:almostz_def) apply dfast
done 

lemma Breakfact1 : "{Vinv [&] case1B [&] case11B}[''s'',''v'']:<fselfc&&(v [>] Real 0)> {v [=] Real 0 [&] case1B [&] case11B;almostz Vinv}"
apply (cut_tac FunInv = "Inv3" in Continuous, auto)
apply (rule impR) apply (rule conjR) defer apply fast
apply (cut_tac p = "(WEX ''s'' WEX ''v'' Vinv [&] case1B [&] case11B) [&]
                v [>] Real 0 [&] Inv3" and q = "Vinv" in Almostfact)
apply (simp add:Vinv_def Inv3_def equal_greater_def equal_less_def)
apply fast apply assumption
apply (simp add:Inv3_def Vinv_def)
apply (rule conjL) apply (rule thinL)
apply (simp add:v_def equal_greater_def equal_less_def) apply (rule Trans1, auto)
done  

lemma Subsfact : "|- v [=] Real 0 [-->] substF([(a, Real 0)], Pre)"
apply (simp add:Pre_def VA_def Vinv_def Ainv_def v_def a_def)
apply (rule impR) apply (rule conjR)+  apply (rule impR)
apply (rule Trans2, auto) prefer 2
apply (simp add:equal_greater_def) apply fast prefer 2
apply (rule conjR)+ apply (simp add:equal_greater_def)
apply fast apply (simp add:equal_less_def) prefer 2
apply (simp add: equal_greater_def equal_less_def)
apply (rule conjR) apply (rule Trans1, auto)+
apply (subgoal_tac "vmax > 2*cmax*T1 + 2*cmax*T2 & cmax>0 & T1>0 & T2>0")
apply (smt real_mult_less_iff1)
apply simp
done  

lemma SelfCfact2 : "{BreakPre [&] case11B}SelfC{Pre [&] case1B [&] case11B;almostz Vinv}"
apply (simp add:SelfC_def)
apply (cut_tac qx = "Vinv [&] case1B [&] case11B" and hx = "almostz Vinv" and qy = "Pre [&] case1B [&] case11B" and hy = "almostz Vinv" in Sequential, auto)
apply (rule Assignfact1)
apply (cut_tac qx = "v [=] Real 0 [&] case1B [&] case11B" and hx = "almostz Vinv" and qy = "Pre [&] case1B [&] case11B" and hy = "almostz Vinv" in Sequential, auto)
apply (rule Breakfact1)
apply (rule Assign, auto)
apply (simp add:a_def Pre_def VA_def Vinv_def Ainv_def v_def equal_greater_def equal_less_def)
apply (simp add:case1B_def a_def)
apply (simp add:case11B_def a_def)
apply (rule impR) apply (rule conjR) apply (rule conjL) apply (rule exchL) apply (rule thinL)
apply (rule backwards_impR)
apply (rule Subsfact)
apply (simp add:case1B_def case11B_def a_def)
apply fast
apply (simp add:almostz_def)
apply dfast
apply fast
apply (rule chopalmostz)
apply fast
apply (rule chopalmostz)
done 

lemma NVAyfact : "{BreakPre [&] case11B [&] [~] VAy [|] Pre [&] case1B [&]
     case11B [&] VAy}IF ([~] VAy) SelfC{Pre [&] case1B [&] case11B;almostz Vinv}"
apply (cut_tac qx = "Pre [&] case1B [&] case11B" and hx = "almostz Vinv" in IFelse, auto)
defer apply fast apply (simp add:almostz_def) apply dfast
apply (cut_tac ax = "BreakPre [&] case11B" and qx = "Pre [&] case1B [&] case11B" and Hx = "almostz Vinv" in Consequence, auto)
apply (rule SelfCfact2) apply fast apply fast apply dfast
done

lemma uvwvwafact : "{BreakPre}uvwvwa{BreakPre [&] [~] case11B [|]
                     Pre [&] case1B [&] case11B;almostz Vinv}"
apply (simp add:uvwvwa_def)
apply (cut_tac qx = "Pre [&] case1B [&] case11B" and hx = "almostz Vinv" in IFelse, auto)
apply (cut_tac qx = "(BreakPre [&] case11B [&] [~]VAy) [|] (Pre [&] case1B [&] case11B [&] VAy)" and hx = "almostz Vinv" and qy = "Pre [&] case1B [&] case11B" and hy = "almostz Vinv" in Sequential, auto)
defer defer apply fast apply (rule chopalmostz) apply (simp add:case11B_def) apply fast
apply (simp add:almostz_def) apply dfast
apply (rule VAyfact) apply (rule NVAyfact)
done

definition case12B :: "fform" where
"case12B == (BVar wa [=] Bool False) [&] (BVar ua [=] Bool True)"
definition case13B :: "fform" where
"case13B == (BVar wa [=] Bool False) [&] (BVar ua [=] Bool False)"

(*Important: We define the following facts for processes uvwvua and uvwvnon as axioms rather than proving them as we did to process uvwvwa. The reason is that they have very similar structure with uvwvwa, and the proofs are slightly different.*)
axiomatization where
uvwvuafact : "{(BreakPre [&] [~] case11B) [|] (Pre [&] case1B [&] case11B)}uvwvua
   {(BreakPre [&] [~] case11B [&] [~] case12B) [|] (Pre [&] case1B [&] (case11B [|] case12B));almostz Vinv}" and
uvwvnonfact: "{(BreakPre [&] [~] case11B [&] [~] case12B) [|] (Pre [&] case1B [&] (case11B [|] case12B))}uvwvnon
  {(BreakPre [&] [~] case11B [&] [~] case12B [&] [~] case13B) [|] (Pre [&] case1B [&] (case11B [|] case12B [|] case13B));almostz Vinv}"

lemma uanonfact : "{(BreakPre [&] [~] case11B) [|] (Pre [&] case1B [&] case11B)}uvwvua; uvwvnon{Pre [&] case1B;almostz Vinv}"
apply (cut_tac qx = "(BreakPre [&] [~] case11B [&] [~] case12B) [|] (Pre [&] case1B [&] (case11B [|] case12B))" and hx = "almostz(Vinv)" and qy = "Pre [&] case1B" and hy = "almostz(Vinv)" in Sequential, auto)
apply (rule uvwvuafact)
apply (cut_tac ax = "(BreakPre [&] [~] case11B [&] [~] case12B) [|] (Pre [&] case1B [&] (case11B [|] case12B))" and qx ="(BreakPre [&] [~] case11B [&] [~] case12B [&] [~] case13B) [|] (Pre [&] case1B [&] (case11B [|] case12B [|] case13B))" and Hx = "almostz Vinv" in Consequence, auto)
apply (rule uvwvnonfact)
apply fast defer apply dfast apply fast apply (rule chopalmostz)
apply(rule impR) apply (rule conjR) apply (rule disjL)
apply (rule conjL) apply (rule conjL) apply (rule conjL) 
apply (rule notL) apply (rule notL) apply (rule notL) 
apply (rule thinR)  apply (rule thinL) apply (simp add:case11B_def case12B_def case13B_def) 
apply (rule Transr3, auto) apply fast 
apply (rule disjL)
apply (rule conjL) apply (rule conjL) apply (rule conjL) 
apply (rule notL) apply (rule notL) apply (rule notL) 
apply (rule thinR)  apply (rule thinL) apply (simp add:case11B_def case12B_def case13B_def) 
apply (rule Transr3, auto) apply fast 
done 

lemma Break1body : "{Lex (WEX ''s'' WEX ''v'' WEX ''t2'' afterb1 [&] case1B [&] t2 [=] Real 0) [&]
         close(Inv2) mvar b2 [&] bAck(b2)}uvwvwa; uvwvua; uvwvnon{Pre [&] case1B;almostz Vinv}"
apply (cut_tac qx = "(BreakPre [&] [~] case11B) [|] (Pre [&] case1B [&] case11B)" and hx = "almostz Vinv" and qy = "Pre [&] case1B" and hy = "almostz Vinv" in Sequential, auto)
defer defer apply fast apply (rule chopalmostz)
apply (cut_tac ax = "BreakPre" and qx = "BreakPre [&] [~] case11B [|]
                     Pre [&] case1B [&] case11B" and Hx = "almostz Vinv" in Consequence, auto)
apply (rule uvwvwafact)  apply (simp add:BreakPre_def) apply fast+ apply dfast 
apply (rule uanonfact)
done

lemma Break1 : "{afterb1 [&] case1B [&] t2 [=] Real 0}[''s'', ''v'', ''t2'']:<fmove2&&(t2 [<] Real T2)>[[b2 (uvwvwa; uvwvua; uvwvnon){mid2;almostz Vinv}"
apply (cut_tac FunInv = "Inv2" and qx = "Pre [&] case1B" and hx = "almostz Vinv" in Interrupt, auto)
defer apply (rule impR)
apply (cut_tac P = "mid211 [|] ((Pre [&] case1B))" in cut, auto)
apply (simp add:mid211_def equal_greater_def) apply fast
apply (rule thinL) apply (rule mid2fact) apply (rule dimpR)
apply (cut_tac P = "almostz mid212 [^] (l [[=]] DR 0 [[|]] almostz Vinv)" in cut, auto)
apply (rule thinR)  apply (simp add:mid212_def) apply dfast 
apply (rule thinL) apply (rule mid212fact) apply (rule Break1body)
done

lemma Assignfact12 : "{mid2}a := (Real - cmax){Vinv [&] case1B;almostz Vinv}"
apply (simp add:mid2_def Vinv_def case1B_def)
apply (simp add:a_def v_def equal_greater_def equal_less_def almostz_def)
apply (rule Assign, auto) apply fast apply dfast
done 

lemma Breakfact12 : " {Vinv [&]case1B}[''s'', ''v'']:<fselfc&&(v [>]
                              Real 0)> {v [=] Real 0 [&] case1B;almostz Vinv}"
apply (cut_tac FunInv = "Inv3" in Continuous, auto)
apply (simp add:Vinv_def case1B_def Inv3_def equal_greater_def equal_less_def)
apply (rule impR) apply (rule conjL)+
apply (rule conjR) apply (rule thinL) apply (rule Trans3, auto)
apply (case_tac "expTrans(v)", auto)+ apply fast
apply (cut_tac p = "(WEX ''s'' WEX ''v'' Vinv[&] case1B) [&] v [>] Real 0 [&] Inv3" and q = "Vinv" in Almostfact, auto)
apply (simp add:Inv3_def Vinv_def) apply fast
done 


lemma SelfCfact1 : "{mid2}SelfC{Pre [&] case1B;almostz Vinv}"
apply (simp add:SelfC_def)
apply (cut_tac qx = "Vinv [&] case1B" and hx = "almostz Vinv" and qy = "Pre [&] case1B" and hy = "almostz Vinv" in Sequential, auto)
apply (rule Assignfact12)
apply (cut_tac qx = "v [=] Real 0 [&] case1B" and hx = "almostz Vinv" and qy = "Pre [&] case1B" and hy = "almostz Vinv" in Sequential, auto)
apply (rule Breakfact12)
apply (rule Assign, auto)
apply (simp add:a_def Pre_def VA_def Vinv_def Ainv_def v_def equal_greater_def equal_less_def)
apply (simp add:case1B_def a_def)
apply (rule impR) apply (rule conjR) apply (rule conjL)+  apply (rule exchL) apply (rule thinL)
apply (rule backwards_impR) 
apply (rule Subsfact)
apply (simp add:case1B_def a_def) apply fast
apply (simp add:almostz_def) apply dfast apply fast
apply (rule chopalmostz) apply fast apply (rule chopalmostz)
done 

lemma Midfact1 : "mid2 [&] [~] t2 [>=] Real T2 |- Pre [&] case1B"
apply (simp add:mid2_def Pre_def case1B_def)
apply (rule conjR)+ defer apply fast+
apply (rule conjL)+ apply (rule notL)
apply (rule exchL)  apply (rule thinL)
apply (rule exchL)  apply (rule thinL)
apply (rule exchL)  apply (rule thinL)
apply (rule exchL)  apply (rule thinL) apply (simp add:equal_greater_def)
apply (rule disjR) apply (rule disjL)+
defer apply fast apply (rule impL) defer  apply fast apply (simp add:t2_def)
apply (rule Transr4, auto)
done 

lemma FailSelfC1 : "{mid2}IF (t2 [>=] Real T2) SelfC{Pre [&] case1B;almostz Vinv}"
apply (cut_tac qx = "Pre [&] case1B" and hx = "almostz Vinv" in IFelse, auto)
apply (cut_tac ax = "mid2" and qx ="Pre [&] case1B" and Hx = "almostz Vinv" in Consequence, auto)
apply (rule SelfCfact1) apply fast+
apply dfast apply (rule impR) apply (rule disjL) apply (rule Midfact1)
apply fast apply (simp add:almostz_def) apply dfast
done 


lemma FailSkip1 : "{Pre [&] case1B}SkipV{Pre [&] case1B;almostz Vinv}"
apply (simp add:SkipV_def)
apply (cut_tac qx = "Pre [&] case1B" and hx = "almostz Vinv" in IFelse, auto)
apply (rule Skip) apply fast apply (simp add:almostz_def)
apply dfast apply fast apply (simp add:almostz_def) apply dfast
done

lemma Fail1 : "{mid2}P2{Pre [&] case1B;almostz Vinv}"
apply (simp add:P2_def)
apply (cut_tac qx = "Pre [&] case1B" and hx = "almostz(Vinv)" and qy = "Pre [&] case1B" and hy = "almostz(Vinv)" in Sequential, auto)
apply (rule FailSelfC1)
apply (rule FailSkip1)
apply fast apply (rule chopalmostz)
done


lemma Control1 : "{afterb1 [&]case1B [&] t2 [=] Real 0}([''s'', ''v'', ''t2'']:<fmove2&&(t2 [<] Real T2)>[[b2 (uvwvwa; uvwvua; uvwvnon)); P2{Pre [&]case1B;almostz Vinv}"
apply (cut_tac qx = "mid2" and hx = "almostz(Vinv)" and qy = "Pre [&]case1B" and hy = "almostz(Vinv)" in Sequential, auto)
defer defer apply fast apply (rule chopalmostz)
apply (rule Break1) apply (rule Fail1)
done 



lemma Case1fact : "{afterb1}case1{(Pre [&] case1B) [|] (afterb1 [&] ([~] case1B)); almostz Vinv}"
apply (simp add:case1_def move2_def Quvwv_def)
apply (cut_tac qx = "Pre [&] case1B" and hx = "almostz Vinv" in IFelse, auto)
defer apply (simp add:case1B_def) apply fast apply (simp add:almostz_def)
apply dfast 
apply (cut_tac qx = "afterb1 [&] case1B [&] t2 [=] (Real 0)" and hx = "almostz(Vinv)" 
           and qy = "Pre [&] case1B" and hy = "almostz(Vinv)" in Sequential, auto)
apply (rule Assign, auto)
apply (simp add:afterb1_def b1_def t2_def uv_def wv_def Pre_def VA_def equal_greater_def Vinv_def Ainv_def equal_less_def Inv1_def Acc1_def Acc2_def exist_def)
apply (simp add:t2_def case1B_def) apply (rule impR) apply (rule conjR)+
apply (rule conjL) apply (rule exchL) apply (rule thinL)
apply (simp add:t2_def afterb1_def b1_def uv_def wv_def t1_def Inv1_def Acc1_def Acc2_def) 
apply (simp add:equal_greater_def equal_less_def exist_def a_def v_def)
apply (simp add:Pre_def VA_def equal_greater_def Vinv_def Ainv_def a_def v_def equal_less_def)
apply fast
apply (simp add:t2_def case1B_def) apply fast apply (simp add:almostz_def) apply dfast
defer apply fast apply (rule chopalmostz)
apply (rule Control1)
done 


definition case2B:: "fform" where
"case2B == (BVar uv [=] Bool True) [&] (BVar wv [=] Bool False)"
definition case3B :: "fform" where
"case3B == ((BVar uv [=] Bool False) [&] (BVar wv [=] Bool True))"
definition case4B :: "fform" where
"case4B == ((BVar uv [=] Bool False) [&] (BVar wv [=] Bool False))"

(*Important: we present the facts for case2, case3, and case4 as axioms rather than proving them
as what we did to case1. The reason is that they have very similar structure, and the proofs of them are almost the same as case1.*)
axiomatization where
Case2fact : "{(Pre [&] case1B) [|] (afterb1 [&] ([~] case1B))}case2
{(Pre [&] (case2B [|] case1B)) [|] (afterb1 [&] ([~] case2B) [&] ([~] case1B)); almostz Vinv}"
and
Case3fact : "{(Pre [&] (case2B [|] case1B)) [|] (afterb1 [&] ([~] case2B) [&] ([~] case1B))}case3
             {(Pre [&] (case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ([~] case3B)[&] ([~] case2B) [&] ([~] case1B)); almostz Vinv}"
and
Case4fact : "{(Pre [&] (case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ([~] case3B)[&] ([~] case2B) [&] ([~] case1B))}case4
                   {(Pre [&] (case4B [|] case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ([~]case4B) [&] ([~] case3B)[&] ([~] case2B) [&] ([~] case1B)); almostz Vinv}"


lemma AllCases : "{afterb1}case1; case2; case3; case4{Pre;almostz Vinv}"
apply (cut_tac qx = "(Pre [&] case1B) [|] (afterb1 [&] ([~] case1B))" and hx = "almostz(Vinv)" and qy = "Pre" and hy = "almostz(Vinv)" in Sequential, auto)
apply (rule Case1fact)
apply (cut_tac qx = "(Pre [&] (case2B [|] case1B)) [|] (afterb1 [&] ([~] case2B) [&] ([~] case1B))" and hx = "almostz(Vinv)" and qy = "Pre" and hy = "almostz(Vinv)" in Sequential, auto)
apply (rule Case2fact)
apply (cut_tac qx = "(Pre [&] (case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ([~] case3B)[&] ([~] case2B) [&] ([~] case1B))" and hx = "almostz(Vinv)" and qy = "Pre" and hy = "almostz(Vinv)" in Sequential, auto)
apply (rule Case3fact)
apply (cut_tac ax = "(Pre [&] (case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ([~] case3B)[&] ([~] case2B) [&] ([~] case1B))" and qx ="(Pre [&] (case4B [|] case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ([~]case4B) [&] ([~] case3B)[&] ([~] case2B) [&] ([~] case1B))" and Hx = "almostz Vinv" in Consequence, auto)
apply (rule Case4fact)
apply (fast) defer apply dfast apply fast
apply (rule chopalmostz) apply fast
apply (rule chopalmostz) apply fast
apply (rule chopalmostz) 
apply (simp add:case1B_def case2B_def case3B_def case4B_def)
apply (rule impR) apply (rule disjL) apply fast apply (rule conjL)
apply (rule thinL) apply (rule conjL) apply (rule conjL) apply (rule conjL) 
apply (rule notL) apply (rule notL) apply (rule notL) apply (rule notL)
apply (rule thinR) apply (rule Transr4, auto)
done 

lemma Bodyfact : "{Pre [&] t1 [=] Real 0} body {mid1; almostz Vinv}"
apply (simp add:body_def)
apply (cut_tac FunInv = "Inv1" and qx = "Pre" and hx = "almostz Vinv" in Interrupt, auto)
defer apply (rule impR)
apply (cut_tac P = "mid11 [|] Pre" in cut, auto)
apply (simp add:mid11_def equal_greater_def) apply fast
apply (rule thinL) apply (rule mid1fact) apply (rule dimpR)
apply (cut_tac P = "almostz mid22 [^] (l [[=]] DR 0 [[|]] almostz Vinv)" in cut, auto)
apply (rule thinR)  apply (simp add:mid22_def) apply dfast 
apply (rule thinL) apply (rule mid2fact5)
apply (cut_tac ax = "afterb1" and qx = "Pre" and Hx = "almostz Vinv" in Consequence, auto)
apply (rule AllCases)
apply (simp add:afterb1_def) apply fast apply fast  apply dfast
done


lemma Assignfact : "{mid1} a := (Real - cmax) {Vinv; almostz Vinv}"
apply (simp add:mid1_def Vinv_def)
apply (simp add:a_def v_def equal_greater_def equal_less_def almostz_def)
apply (rule Assign, auto)
apply fast
apply dfast
done 


lemma Breakfact : "{Vinv} [''s'', ''v'']:<fmove3&&(v [>] Real 0)> {v [=] Real 0; almostz Vinv}"
apply (cut_tac FunInv = "Inv3" in Continuous, auto)
apply (simp add:Vinv_def Inv3_def equal_greater_def equal_less_def)
apply (rule impR)
apply (rule conjL)+
apply (rule thinL)
apply (rule Trans3, auto)
apply (case_tac "expTrans(v)", auto)+
apply (cut_tac p = "(WEX ''s'' WEX ''v'' Vinv) [&] v [>] Real 0 [&] Inv3" and q = "Vinv" in Almostfact, auto)
apply (simp add:Inv3_def Vinv_def)
apply fast
done 


lemma SelfCfact : "{mid1} SelfC {Pre; almostz Vinv}"
apply (simp add:SelfC_def)
apply (cut_tac qx = "Vinv" and hx = "almostz Vinv" and qy = "Pre" and hy = "almostz Vinv" in Sequential, auto)
apply (rule Assignfact)
apply (cut_tac qx = "v [=] Real 0" and hx = "almostz Vinv" and qy = "Pre" and hy = "almostz Vinv" in Sequential, auto)
apply (rule Breakfact)
apply (rule Assign, auto)
apply (simp add:a_def Pre_def VA_def Vinv_def Ainv_def v_def equal_greater_def equal_less_def)
apply (rule Subsfact)
apply (simp add:almostz_def)
apply dfast
apply fast
apply (rule chopalmostz)
apply fast
apply (rule chopalmostz)
done 

lemma FailSelfC : "{mid1}IF (t1 [>=] Real T1) SelfC {Pre; almostz Vinv}"
apply (cut_tac qx = "Pre" and hx = "almostz Vinv" in IFelse, auto)
apply (cut_tac ax = "mid1" and qx ="Pre" and Hx = "almostz Vinv" in Consequence, auto)
apply (rule SelfCfact)
apply fast+
apply dfast
apply (rule impR)
apply (rule disjL)
apply (rule Midfact)
apply fast
apply (rule dimpR)
apply (rule ddisjL)
apply (simp add:almostz_def)
apply dfast+
done 

lemma FailSkip : " {Pre} SkipV {Pre; almostz Vinv}"
apply (simp add:SkipV_def)
apply (cut_tac qx = "Pre" and hx = "almostz Vinv" in IFelse, auto)
apply (rule Skip)
apply fast
apply (simp add:almostz_def)
apply dfast
apply fast
apply (simp add:almostz_def)
apply dfast
done

lemma Fail : "{mid1} P1 {Pre; almostz Vinv}"
apply (simp add:P1_def)
apply (cut_tac qx = "Pre" and hx = "almostz(Vinv)" and qy = "Pre" and hy = "almostz(Vinv)" in Sequential, auto)
apply (rule FailSelfC)
apply (rule FailSkip)
apply fast
apply (rule chopalmostz)
done

lemma Control : "{Pre [&] t1 [=] Real 0} body; P1 {Pre; almostz Vinv}"
apply (cut_tac qx = "mid1" and hx = "almostz(Vinv)" and qy = "Pre" and hy = "almostz(Vinv)" in Sequential, auto)
apply (rule Bodyfact)
apply (rule Fail)
apply fast
apply (rule chopalmostz)
done 


(*This is the final theorem stating the safety of the train, as defined in the paper.*)
theorem Train : "{Pre} train {Pre; almostz(Vinv)}"
apply (simp add:train_def)
apply (cut_tac qx = "Pre [&] t1 [=] (Real 0)" and hx = "almostz(Vinv)" 
           and qy = "Pre" and hy = "almostz(Vinv)" in Sequential, auto)
apply (simp add:Pre_def VA_def Vinv_def Ainv_def t1_def a_def v_def equal_greater_def equal_less_def almostz_def)
apply (rule Assign, auto)
apply fast
apply dfast
apply (rule Control)
apply fast
apply (rule chopalmostz)
done 


end