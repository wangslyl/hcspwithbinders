header {*The Inference System for HCSP with Binders*}

theory Inference
  imports bHCSP_Com
begin

consts 
spec :: "fform => bproc => fform => dform => prop"   ("{_}_{_;_}" 80)

section {*Acknowledgement judgement for binders*}

(*The following considers the special cases when binder number is 2*)
primrec bAck :: "bindp => fform" 
where
"bAck(ch??x{u}) = ((BVar u) [=] Bool True)" |
"bAck(ch!!e{u}) = ((BVar u) [=] Bool True)"|
"bAck(&q [b, d]) = (q (bAck(b)) (bAck(d)))"

(*Consequence rule*)
axiomatization where 
Consequence : "[|{ax} P  {qx; Hx}; |-a [-->] ax; |- qx [-->] q; |- Hx [[-->]] H|]
              ==> {a} P  {q; H}"
(*Skip rule*)
axiomatization where
Skip : "[||- p [-->] q; |- l [[=]] DR 0 [[-->]] h|] ==> {p} Skip {q; h}"

(*Assignment rule*)
axiomatization where
Assign  :"[|~inPairForm ([(e, f)], q); |- p [-->] substF ([(e, f)]) (q); |- (l [[=]] DR 0) [[-->]] h|]
          ==> {p} e:=f {q; h}"


axiomatization where
Input : "[||-(WEX x (WEX u p)) [&]((BVar u) [=] Bool True) [-->] q; |- almostz p [[-->]] h  |] ==>
         {p} Qb ch??x{u} {q; h}"

axiomatization where
Output : "[||- (WEX u p) [&]((BVar u) [=] Bool True) [-->] q; |- almostz p [[-->]] h |] ==>
          {p} Qb ch!!e{u} {q; h}"

axiomatization where
Binder : "[||-((Lex p mvar(&r [a, b])) [&] bAck(&r [b, d])) [-->] q;
            |- almostz(Lex p mvar(&r [a, b])) [[-->]] h|] ==>
          {p} Qb (&r [b, d]) {q; h}"

axiomatization where
Continuous : "[||- ((Lex p v) [&] (close ([~]E)) [&] (close (FunInv))) [-->] q;
                |- almostz((Lex p v) [&] E [&] FunInv) [[-->]] h |] ==>
              {p} v:<Fun&&E> {q; h}"
axiomatization where
RefContinuous: "[||- p [-->] close(E); |- ((Lex p v) [&] ((close ([~]E)) [&] (close(E))) [&] (close (FunInv))) [-->] q;
                |- almostz((Lex p v) [&] E [&] FunInv) [[-->]] h |] ==>
              {p} v:<Fun&&E> {q; h}"

axiomatization where
Interrupt : "[|{Lex ((Lex p v) [&] (close (FunInv))) (mvar b) [&] bAck (b)} Q {qx; hx};
              |- (Lex ((Lex p v) [&] (close ([~]E)) [&] (close (FunInv))) (mvar b) [|] qx) [-->] q;
              |- (almostz(Lex ((Lex p v) [&] E [&] FunInv) (mvar b)) [^] (l [[=]] DR 0 [[|]]hx)) [[-->]] h|]
==> {p} v:<Fun&&E>[[b Q {q; h}"

axiomatization where
Parallel : "[|{px} P {qx; hx}; {py} Q {qy; hy}; |- (qx [&] qy) [-->] q; 
             |- ((hx [^] DTrue) [[&]](hy [^] DTrue)) [[-->]] h |]
           ==> {px [&] py} P || Q {q; h}"

axiomatization where
Sequential : "[|{px} P {qx; hx}; {qx} Q {qy; hy}; |- qy [-->] q; |-(hx [^] hy) [[-->]] h|]
           ==> {px} P; Q {q; h}"

axiomatization where
IFelse : "[|{p [&] B} P {qx; hx}; |- ((p [&] [~] B) [|] qx) [-->] q; 
           |- (l [[=]] DR 0 [[|]] hx) [[-->]] h|] ==>
         {p} IF B P {q; h}"

axiomatization where
Repetition : "[|{p} P {p; hx}; |- hx [^] hx [[-->]] hx; |- p [-->] q; 
                 |- (hx [[|]] l [[=]] DR 0) [[-->]] h |] ==>
              {p} P* {q; h}"

axiomatization where
Choice : "{p [&] B} P {q; h}==>
          {p} NON tpid s : B P {q; h}"

end