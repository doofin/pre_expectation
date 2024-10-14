# pre_expectation

An embedded Domain Specific Language (eDSL) in Scala for
probabilistic programs, supporting assertions,assumption and loop
invariants for paper "A Pre-Expectation Calculus for Probabilistic Sensitivity"

Example eDsl program : https://github.com/doofin/pre_expectation/blob/master/src/main/scala/precondition/syntax/dslTest.scala

# requirements

setup z3:
1.with binary:put the *.so files (under lib/) under envirment variable LD_LIBRARY_PATH (in Linux) so that z3 can be loaded:


2.compile z3-4.8 from source : https://github.com/mario-bucev/ScalaZ3/tree/z3-4.8.12 or https://github.com/Z3Prover/z3

# run

`sbt test`

# files

rpeSMT : the expressions for sgd example in the paper

InfRealTuple : lifting for Number into Number with infinity

syntax/dslAST : eDSL syntax and interpreter for simple sgd program

# ide
vscode + metals plugin

intellij
