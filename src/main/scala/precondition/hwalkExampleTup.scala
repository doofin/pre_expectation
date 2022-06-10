package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}

import InfRealTuple.TupNum
import rpeFunctionTup._
import issuesAndTests._

import lemmas._
import hwalkLemmas._
// sgd with tuple number
object hwalkExampleTup {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  /**
   * generate smt terms for while loop body for hwalk at p17
   */
  def genSMTterms() = {
    import InfRealTuple._
    import ImplicitConv._

    val N: IntExpr = mkIntConst("N")

    val t0 = mkInt(0)
    val (w1, w2) = (newVecReal("w1"), newVecReal("w2"))
    val (g1, g2) = (newVecReal("g1"), newVecReal("g2"))
    val k1 :: k2 :: Nil = (1 to 2).map(x => mkIntConst(s"t$x")).toList
    val K1 = mkIntConst("K1")
    val K2 = mkIntConst("K2")

    val i1 :: i2 :: Nil = mkSymList(2, "i", mkIntConst)

    val (f_bij, f_bij_prop) = lemmas.f_bijection_int()
    val rpeF_inst = rpeF(f_bij) _

    val (pos1, pos2, dh, invar, invarProps, exp) = hwalkInvariantUni(N, k1, k2, K1, K2)

    // e(i)
    val (ei1, ei1p) = ei_uni(i1)
    val (ei2, ei2p) = ei_uni(i2)

    // xor ⊕
    val (xor_r1, xor1P) = xor_uni(pos1, ei1)
    val (xor_r2, xor2P) = xor_uni(pos2, ei2)

    // val premises: Seq[BoolExpr] =
    //   Seq(ei1p) //  ei1p is bad

    // val premises: Seq[BoolExpr] =
    //   Seq(f_bij_prop, invarProps)

    // Seq(f_bij_prop, invarProps, ei1p) //  ei1p is bad
    val premises: Seq[BoolExpr] =
      Seq(N >= 0, f_bij_prop, invarProps, ei1p, ei2p, xor1P, xor2P)

    val while_bd = WhileSmtTup(
      invar,
      (k1 < K1, k2 < K2), // cond doesn't matter
      StmtSmtList(
        List(
          AssigRandInt(i1, i2, N),
          If_Tup((i1 !== 0, i1 !== 0), Assig(pos1, xor_r1, pos2, xor_r2), SkipSmt),
          Assig(k1, k1 + mkInt(1), k2, k2 + mkInt(1))
        )
      )
    )

    val hwalkProgram =
      StmtSmtList(
        List(
          NewVars(k1, t0, k2, t0),
          while_bd
        )
      )

    // by TH.7.should be auto derived from I_gen

    // p13. rpe(sgd,|w1-w2|) <= 2L/n sum
    val (goalLhs, sideConds) = rpeF_inst(
      while_bd,
      dh,
      List() // initial side conditions is empty
    )

    val sideCond = if (sideConds.nonEmpty) sideConds.reduce(_ && _) else mkTrue()

    // rhs of p13. rpe(sgd,|w1-w2|) <= 2L/n sum, sum 0 T - 1 a_j

    // val finalGoal = (premise ==> sideCond) // unsat,unk after changes of infty*0
    val finalGoal = sideCond.neg // unsat,unk after changes of infty*0

    val goal0 = N < 0
    val goal1 = (exp >= 0).neg //unknow
    // (premises, finalGoal.neg) //finalGoal.neg

    z3CheckApi.checkBoolExpr(
      ctx,
      premises = premises,
      formulas = Seq(goal1),
      List(Status.UNSATISFIABLE), // Status.UNKNOWN
      "rpe (while k < K do bd, d H) <= I" // "unsat (sat(I_lhs <= I) ~= unsat(not I_lhs <= I))",
      // printSmtStr = true,
      // printSATmodel = true
    )
  }

  def test = {
    genSMTterms()

  }

  /*
  result: UNKNOWN , goal: List(UNSATISFIABLE)  , description : rpe (while k < K do bd, d H) <= I
checking premise (sat or unknown) :  premise is bad
   */
}
