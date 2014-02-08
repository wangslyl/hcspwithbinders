hcspwithbinders
===============

The source files for implementation of the prover, plus one application on verifying a train example.

1. Introduction:

  The folder DCSequents includes the files for implementing the two assertion languages, first-order logic and duration 
calculus. We list the information in more detail below.

  LSyntax.thy: the syntax of expressions and first-order formulas

  DSequents.thy: the sequent calculus style deductive system for any type of formulas

  DLK0.thy: the sequent calculus based deductive system for first-order formulas
  
  DDLK0.thy: the sequent calclus based deductive system for first-order constructs of interval logic

  ILSequent.thy: the sequent calculus based deductive system for interval logic, from which duration calculus is defined

  DCSequent.thy: the sequent calculus based deductive system for duration calculus

  In the root folder, 

  bHCSP_Com.thy: the syntax for the modeling language HCSP with binders

  Inference.thy: the inference system for reasoning about HCSP with binders

  Train.thy: the train model written in the syntax defined in bHCSP_Com.thy

  TrainProof.thy: the proofs of the train model. Especially, the last theorem states the specification of the train

2. How to Use the Prover:

  You can always build your model, e.g, with name "usermodel", as follows:

  theory usermodel

   imports Inference
  
  begin
  
        here you can list the definitions of your model, the properties to be proved, and also proofs. 
  
  end




