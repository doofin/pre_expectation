# pre_expectation

impl and demo for A Pre-Expectation Calculus for Probabilistic Sensitivity

# requirements

setup z3:
1.with binary:put the *.so files (under lib/) under envirment variable LD_LIBRARY_PATH (in Linux) so that z3 can be loaded:


2.compile z3-4.8 from source : https://github.com/mario-bucev/ScalaZ3/tree/z3-4.8.12 or https://github.com/Z3Prover/z3

# run

`sbt test`

# files

rpeSMT : the expressions for sgd example in the paper

InfRealTuple : lifting for Number into Number with infinity

dslAST : eDSL syntax and interpreter for simple sgd program

# ide
vscode + metals plugin