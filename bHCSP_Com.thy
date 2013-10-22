
header {* Abstract syntax for the extension of Hybrid CSP with binder. *}

theory bHCSP_Com 
  imports  Main
"DCSequents/DCSequent"

begin


type_synonym bexp = fform
type_synonym Inv = fform


(*Only ch?RVar x{u} is allowed for simplicity, but not an essential restriction.*)
type_synonym qualityp = "fform \<Rightarrow> fform \<Rightarrow> fform"
datatype bindp 
=  Send "string" "exp" "string"        ("_!!_{_}" [110,108,108] 100)      
  | Receive "string" "string"  "string"  ("_??_{_}" [110,108,108] 100) 
  | Binder "qualityp" "bindp" "bindp" ("& _ [_, _]" [110,108,108] 10)

(*May-modified variables of binders*)
primrec mvar :: "bindp \<Rightarrow> string list" ("mvar _")
where 
"mvar (ch??x{u}) = [x, u]" |
"mvar (ch!!e{u}) = [u]" |
"mvar (&q [a, b]) = mvar (a) @ mvar (b)"

(*Existential quantifiers extension to a list of variables*)
primrec Lex :: "fform => string list => fform"  ("Lex _ _")
where
"Lex p [] = p" |
"Lex p (x # xs) = (WEX x (Lex p xs))"


datatype typeid = Ri | Si | Bi

consts der :: "string => string"
type_synonym diffeq = "string list => exp"
type_synonym eqlist = "diffeq list"

definition test :: "diffeq" where
"test  ==  % a. (if (a = [''s'']) then ((RVar ''s'') [+] RVar (der (''s''))) else (Real 0))"

datatype bproc
= "Skip"
| Ass "exp" "exp"          ("_ := _" [99, 95] 94)  
(*binder from quality calculus*) 
| Qb "bindp"                ("Qb _" 94)
| Con "string list" "eqlist" "bexp"                 ("_:<_&&_> " [94,95,96]94)
| Inr "string list" "eqlist" "bexp" "bindp" "bproc" ("_:<_&&_>[[_ _"[95,94,95,94]94)
| Par  "bproc" "bproc"                  ("_||_" [90,90]89)
| Seq "bproc" "bproc"                   ("_; _"        [91,90] 90)
| Cond "bexp" "bproc"                 ("IF _ _"   [95,94]93)
| Rep    "bproc"                               ("_*"[91] 90)
| Nondeter "typeid" "string" "bexp" "bproc"                 ("NON _ _ : _ _"   [95,95,94,94]93)


type_synonym pair = "exp * exp"


primrec map :: "pair list => exp => exp" where
"map ([]) (a) = a" |
"map (x#xs) (a) = (if (fst (x) = a) then (snd (x)) else (map (xs) (a)))"


lemma "map ([(RVar ''x'', Real 2), (RVar ''y'', RVar z)],  RVar ''x'') = (Real 2)"
apply (induct, auto)
done

lemma fact1 : "map ([(RVar ''x'', Real 2), (RVar ''y'', RVar z)]) (RVar ''z'') = RVar ''z''"
apply (induct, auto)
done

(*Expression substitution: "map" records the substitution mapping.*)
primrec substE :: "pair list => exp => exp" where
"substE (mp, (RVar x)) = map (mp, (RVar x))"  |
"substE (mp, (SVar x)) = map (mp, (SVar x))"  |
"substE (mp, (BVar x)) = map (mp, (BVar x))"  |
"substE (mp, (Real m)) = map (mp, (Real m))"  |
"substE (mp, (Bool b)) = map (mp, (Bool b))"  |
"substE (mp, (String s)) = map (mp, (String s))"  |
"substE (mp, (e1 [+] e2)) = substE (mp, e1) [+] substE (mp, e2)"  |
"substE (mp, (e1 [-] e2)) = substE (mp, e1) [-] substE (mp, e2)"|
"substE (mp, (e1 [*] e2)) = substE (mp, e1) [*] substE (mp, e2)"

lemma "(% x. x [+] x = RVar ''z'' [+] RVar ''z'') (RVar ''z'')"
apply auto
done

lemma "substE ([(RVar ''x'', Real 1), (RVar ''y'', RVar ''z'')], (RVar ''y'' [+] RVar ''z'')) 
        = RVar ''z'' [+] RVar ''z''"
apply (induct, auto)
done 


(*Tip: for theory built on Pure, application is written by f(x) rather than f x as usual. *)

primrec lVarE :: "pair list => string => pair list" where
"lVarE ([],s) = []" |
"lVarE (x#xs,s) = (if (fst (x) = (RVar s)) then xs else x#lVarE(xs, s))"

primrec inExp :: "string => exp => bool" where
"inExp (s, (RVar x)) = (s=x)"  |
"inExp (s, (SVar x)) = (s=x)"  |
"inExp (s, (BVar x)) = (s=x)"  |
"inExp (s, (Real m)) = (False)"  |
"inExp (s, (Bool b)) = (False)"  |
"inExp (s, (String r)) = (False)"  |
"inExp (s, (e1 [+] e2)) = (inExp (s, e1) | inExp (s, e2))"  |
"inExp (s, (e1 [-] e2)) = (inExp (s, e1) | inExp (s, e2))"|
"inExp (s, (e1 [*] e2)) = (inExp (s, e1) | inExp (s, e2))"

primrec inPairL :: "pair list => string => bool" where
"inPairL ([],s) = False" |
"inPairL (x#xs,s) = (if (inExp (s, fst (x))) then True else inPairL(xs, s))"

primrec inPairR :: "pair list => string => bool" where
"inPairR ([],s) = False" |
"inPairR (x#xs,s) = (if (inExp (s, snd (x))) then True else inPairR(xs, s))"

(*Check if the quantifiers of a formula occur in mp*)
primrec inPairForm :: "pair list => fform => bool" where
 "inPairForm (mp) (WTrue) = False" |
 "inPairForm (mp) (WFalse) = False" |
 "inPairForm (mp) (e1 [=] e2) =False" |
 "inPairForm (mp) (e1 [<] e2) = False" |
 "inPairForm (mp) (e1 [>] e2) =False" |
 "inPairForm (mp) ([~]p) = (inPairForm (mp) (p))" |
 "inPairForm (mp) (p [&] q) = ((inPairForm (mp) (p)) | (inPairForm (mp) (q)))" |
 "inPairForm (mp) (p [|] q) = ((inPairForm (mp) (p)) | (inPairForm (mp) (q)))" |
 "inPairForm (mp) (p [-->] q) = ((inPairForm (mp) (p)) | (inPairForm (mp) (q)))" |
 "inPairForm (mp) (p [<->] q) = ((inPairForm (mp) (p)) | (inPairForm (mp) (q)))" |
 "inPairForm (mp) (WALL i p) = (inPairL (mp, i) | inPairR (mp, i) | inPairForm (mp)(p))" |
 "inPairForm (mp) (WEX i p) = (inPairL (mp, i) | inPairR (mp, i) | inPairForm (mp)(p))"

(*Formula sustitution.*)
primrec substF :: "pair list => fform => fform" where
 "substF (mp) (WTrue) = WTrue" |
 "substF (mp) (WFalse) = WFalse" |
 "substF (mp) (e1 [=] e2) = ((substE (mp, e1)) [=] (substE (mp, e2)))" |
 "substF (mp) (e1 [<] e2) = ((substE (mp, e1)) [<] (substE (mp, e2)))" |
 "substF (mp) (e1 [>] e2) = (substE (mp, e1) [>] substE (mp, e2))" |
 "substF (mp) ([~]p) = ([~](substF (mp) (p)))" |
 "substF (mp) (p [&] q) = ((substF (mp) (p)) [&] (substF (mp) (q)))" |
 "substF (mp) (p [|] q) = ((substF (mp) (p)) [|] (substF (mp) (q)))" |
 "substF (mp) (p [-->] q) = ((substF (mp) (p)) [-->] (substF (mp) (q)))" |
 "substF (mp) (p [<->] q) = ((substF (mp) (p)) [<->] (substF (mp) (q)))" |
 "substF (mp) (WALL i p) = (if ((~inPairL (mp, i)) & (~inPairR (mp, i))) then (WALL i (substF (mp)(p))) 
                           else WFalse)" |
 "substF (mp) (WEX i p) = (if ((~inPairL (mp, i)) & (~inPairR (mp, i))) then (WEX i (substF (mp)(p))) 
                           else WFalse)"

lemma allEX : "substF([(RVar ''x'', RVar ''m''), (RVar ''y'', RVar ''z'')], 
                 ((RVar ''x'')[=]Real 2) [&] (WALL ''w'' ((RVar ''w'') [>] (RVar ''z''))))
             = (((RVar ''m'')[=]Real 2) [&] (WALL ''w'' ((RVar ''w'') [>] (RVar ''z''))))"
apply auto
done


lemma test : "substF ([(RVar ''x'', Real 2), (RVar ''y'', RVar ''z'')]) (RVar ''x'' [>] Real 1) = (Real 2 [>] Real 1)"
apply (induct, auto)
done


end




