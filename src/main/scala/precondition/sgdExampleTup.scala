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
object sgdExampleTup {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  /**
   * generate smt terms for while loop body for sgd example at p.12
   */
  def genSMTterms() = {
    import InfRealTuple._
    import ImplicitConv._

    // example test set
    val s_distrib: Set[Expr[IntSort]] =
      (2 to 6).map(x => mkIntConst(s"s$x")).toSet

//    vars for loop invariant in p.13
//   previous simplification : dim w = 1,use R instead of R^n
    val w0 = newVecReal("w0")
    // val t0 = mkIntConst("t0")
    val t0 = mkInt(0)
    // val t0prop = t0 === mkInt(0)
    val (w1, w2) = (newVecReal("w1"), newVecReal("w2"))

    val (g1, g2) = (newVecReal("g1"), newVecReal("g2"))
    val t1 :: t2 :: Nil = (1 to 2).map(x => mkIntConst(s"t$x")).toList
    val s1 :: s2 :: Nil = mkSymList(2, "s", mkIntConst)

    val T: IntExpr = mkIntConst("T")
    val T_prem = T >= 1

    val e1 :: e2 :: Nil = List(t1 > 0, t2 > 0)

    // a_t for sgd at p13
    val a_t = mkRealConst("a_t")
    val atPrpo = a_t > mkReal(0)

    val varProps = atPrpo //&& t0prop
    // delta L function with Lipschitz property
    val (deltaL, lipschez_premise) = vec_deltaL(1)

    val (f_bij, f_bij_prop) = lemmas.f_bijection_int()
    val rpeF_inst = rpeF(f_bij) _

    // sum of a_j :  sumAjF=sum i j a_j
    val (sumAjF, sumProps) =
      sumAjGen()

    // original invariant_annonotation in while stmt and also rhs of p13(1)
    // val invariant_annon =
    //   invariantRhsTup(List(t1, t2), List(w1, w2), T, sumAjF)

    // testing invariant_annonotation in while stmt and also rhs of p13(1)
    val invariant_annon =
      invariantRhsTup(List(t1, t2), List(w1, w2), T, sumAjF)

    val whileBd_relational = StmtSmtList(
      List(
        AssigRandSet(s1, s2, s_distrib),
        Assig(g1, deltaL(s1, w1), g2, deltaL(s2, w2)),
        Assig(w1, w1 - g1.mulByScalar(a_t), w2, w2 - g2.mulByScalar(a_t)),
        Assig(t1, t1 + mkInt(1), t2, t2 + mkInt(1))
      )
    )

    val sgdProgram =
      StmtSmtList(
        List(
          NewVars(w1, w0, w2, w0),
          NewVars(t1, t0, t2, t0),
          WhileSmtTup(
            invariant_annon,
            (e1, e2),
            whileBd_relational
          )
        )
      )

    val sgdProgram1 =
      StmtSmtList(
        List(
          // NewVars(w1, w0, w2, w0),
          // NewVars(t1, t0, t2, t0),
          WhileSmtTup(
            invariant_annon,
            (e1, e2),
            whileBd_relational
          )
        )
      )
    import ImplicitConv._

    // by TH.7.should be auto derived from I_gen

    val premises: Seq[BoolExpr] =
      Seq(lipschez_premise, lemmas.vecPremise, varProps, T_prem) ++ sumProps

    // p13. rpe(sgd,|w1-w2|) <= 2L/n sum
    val (goalLhs, sideConds) = rpeF_inst(
      sgdProgram,
      (w1 - w2)
        .norm(),
      List() // initial side conditions is empty
    )

    val sideCond = if (sideConds.nonEmpty) sideConds.reduce(_ && _) else mkTrue()

    // rhs of p13. rpe(sgd,|w1-w2|) <= 2L/n sum, sum 0 T - 1 a_j
    val goalRhs = sumAjF(0, T - 1)

    // val finalGoal =
    //   (premise ==> (goalLhs <= goalRhs)) && (premise ==> sideCond) // unknown for sgd,ok for sgd1

    val finalGoal = sideCond // unsat,unk after changes of infty*0

    (premises, finalGoal)
  }

  def test = {
    val (prem, props) = genSMTterms()

    z3CheckApi.checkBoolExpr(
      ctx,
      premises = prem,
      Seq(props.neg),
      List(Status.UNSATISFIABLE), // Status.UNKNOWN
      "rpe(sgd,|w1-w2|) <= 2L/n sum", // "unsat (sat(I_lhs <= I) ~= unsat(not I_lhs <= I))",
      printSmtlib = true
    )
  }

}

// previouse goal of p13 (1)
// val I_lhs: TupNum = invar_lhs_gen(
//   e1,
//   e2,
//   rpeF_inst(
//     whileBd_relational,
//     invariant,
//     List()
//   )._1,
//   (w1 - w2)
//     .norm()
// )

// val goalOld = premise ==> (I_lhs <= invariant)
