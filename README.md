hcspwithbinders
===============

The source files for implementation of the prover, plus an application on a train example.

1. Introduction:

The folder DCSequents include the files for implementing the two assertion languages, first-order logic and duration 
calculus. We list the information in more detail below.

  LSyntax.thy: the syntax of expressions and first-order formulas

  DSequents.thy: the sequent calculus style deductive system for any type of formulas

  DLK0.thy: the sequent calculus based deductive system for first-order formulas

  ILSequent.thy: the sequent calculus based deductive system for interval logic, from which duration calculus is defined

  DCSequent.thy: the sequent calculus based deductive system for duration calculus

In the root folder, 

  bHCSP_Com.thy: the syntax for the HCSP with binders

  Inference.thy: the inference system for HCSP with binders

  Train.thy: the train model written in the syntax defined in bHCSP_Com.thy

  TrainProof.thy: the safety proof of the train model

2. How to Use it:

You can always build your model, e.g, with name "usermodel", as follows:

  theory usermodel

    imports Inference
  
  begin
  
     %here you can list the definitions of your model, the properties to be proved, and also proofs. 
  
  end




