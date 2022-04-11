package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}

import lemmas._
import rpeFunctionTup._
import InfRealTuple.TupNum
import issuesAndTests._
// sgd with tuple number
object hwalkExampleTup {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  /**
   * generate smt terms for while loop body for sgd example at p.12
   */
  def genSMTterms() = {
    import InfRealTuple._
    import ImplicitConv._

    // N ⊖ n denotes max(N −n, 0)

    // example test set
    val s_distrib: Set[Expr[IntSort]] =
      (2 to 6).map(x => mkIntConst(s"s$x")).toSet

    val t0 = mkInt(0)
    val (w1, w2) = (newVecReal("w1"), newVecReal("w2"))

    val (g1, g2) = (newVecReal("g1"), newVecReal("g2"))
    val k1 :: k2 :: Nil = (1 to 2).map(x => mkIntConst(s"t$x")).toList
    val K1 = mkIntConst("K1")
    val K2 = mkIntConst("K2")

    val i1 :: i2 :: Nil = mkSymList(2, "s", mkIntConst)

    val (f_bij, f_bij_prop) = lemmas.f_bijection_int()
    val rpeF_inst = rpeF(f_bij) _

    val (pos1, pos2, dh, invar, invarProps) = lemmas.hwalkInvariant(k1, k2, K1, K2)
    val (ei1, ei1p) = ei_arr(i1)
    val (ei2, ei2p) = ei_arr(i2)
    val (xor_r1, xor1P) = xor_arr(pos1, ei1)
    val (xor_r2, xor2P) = xor_arr(pos2, ei2)

    val premises: Seq[BoolExpr] =
      Seq(f_bij_prop, invarProps, ei1p, ei2p, xor1P, xor2P)

    val while_bd = WhileSmtTup(
      invar,
      (k1 < K1, k2 < K2),
      StmtSmtList(
        List(
          AssigRand(i1, i2, s_distrib),
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
    import ImplicitConv._

    // by TH.7.should be auto derived from I_gen

    val premise = premises.reduce(_ && _)

    // p13. rpe(sgd,|w1-w2|) <= 2L/n sum
    val (goalLhs, sideConds) = rpeF_inst(
      while_bd,
      dh,
      List() // initial side conditions is empty
    )

    val sideCond = if (sideConds.nonEmpty) sideConds.reduce(_ && _) else mkTrue()

    // rhs of p13. rpe(sgd,|w1-w2|) <= 2L/n sum, sum 0 T - 1 a_j

    val finalGoal = (premise ==> sideCond) // unsat,unk after changes of infty*0

    (premises, finalGoal.neg)
  }

  def test = {
    val (prem, propWithPrem) = genSMTterms()

    val allPrem = prem.reduce(_ && _)

    z3CheckApi.checkBoolExpr(
      ctx,
      Seq(propWithPrem),
      List(Status.UNSATISFIABLE), // Status.UNKNOWN
      "rpe (while k < K do bd, d H) <= I", // "unsat (sat(I_lhs <= I) ~= unsat(not I_lhs <= I))",
      premise = prem,
      printSmtStr = false
    )
  }

  /*
  result: UNKNOWN , goal: List(UNSATISFIABLE)  , description : rpe (while k < K do bd, d H) <= I
checking premise (sat or unknown) :  premise is bad
   */
}
