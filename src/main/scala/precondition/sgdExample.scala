package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}

import lemmas._
import rpeFunction._
// import InfRealTuple.TupNum

object sgdExample {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  /**
   * generate smt terms for while loop body for sgd example at p.12
   */
  def genSMTterms() = {
    // import InfRealTuple._
    import ImplicitConv._

    // example test set
    val s_distrib: Set[Expr[IntSort]] =
      (2 to 6).map(x => mkIntConst(s"s$x")).toSet

//    vars for loop invariant in p.13
//   previous simplification : dim w = 1,use R instead of R^n
    val w0 = newVec("w0")
    // val t0 = mkIntConst("t0")
    val t0 = mkInt(0)
    // val t0prop = t0 === mkInt(0)
    val (w1, w2) = (newVec("w1"), newVec("w2"))

    val (g1, g2) = (newVec("g1"), newVec("g2"))
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

    //  relational statements for while loop body
    //  generate relational I ,also return sumF_Aj=sum i j a_j for convenience
    val (invariant) = invariant_rhs(List(t1, t2), List(w1, w2), T, sumAjF)

    val whileBd_relational = StmtSmtList(
      List(
        AssigRand(s1, s2, s_distrib),
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
          WhileSmt(
            invariant,
            (e1, e2),
            whileBd_relational
          )
        )
      )

    // by TH.7.should be auto derived from I_gen
    val premises: Seq[BoolExpr] =
      Seq(lipschez_premise, lemmas.vecPremise, varProps, T_prem) ++ sumProps

    val premise = premises.reduce(_ && _)
    // p13. rpe(sgd,|w1-w2|) <= 2L/n sum
    val (goalLhs, sideConds) = rpeF_inst(
      sgdProgram,
      (w1 - w2)
        .norm(),
      List() // initial side conditions
    )

    val sideCond = if (sideConds.nonEmpty) sideConds.reduce(_ && _) else mkTrue()

    // sum 0 T - 1 a_j
    val goalRhs = sumAjF(0, T - 1)
    // val goalRhs = sumF_Aj(0, T) //

    // println("sideCond :", sideCond.toString())
    // println("goal2lhs <= goal2rhs")
    // println(goal2lhs <= goal2rhs)

    // val finalGoal = (premise ==> ((w1 - w1).norm() === 0)) && (premise ==> sideCond) // ok
    // val finalGoal = (premise ==> (goalRhs <= goalRhs)) && (premise ==> sideCond) // ok
    // val finalGoal = (premise ==> ((w1 === w2))) && (premise ==> sideCond) // unknown
    val finalGoal =
      (premise ==> (goalLhs <= goalRhs)) && (premise ==> sideCond) // unknown for sgd,ok for sgd1
    // val finalGoal = (premise ==> sideCond) // unsat,unk after changes of infty*0
    // placeholder goal
    // val finalGoal = (premise ==> (mkReal(0) <= goalRhs)) && (premise ==> sideCond) // unknown

//    println("I_lhs : ", I_lhs.toString)

    // (premises, goalOld.neg)
    (premises, finalGoal.neg)
  }

  /**
   * loop invariant I at p13 to be put as annotation of while loop
   * @param t
   * @param w
   * @return
   */
  def invariant_rhs(
      t: List[IntExpr],
      w: List[Expr[VecType]],
      T: IntExpr,
      sumAjF: (Expr[IntSort], Expr[IntSort]) => RealExpr
  ) = {
    import z3Utils._
    import ImplicitConv.int2mkint
    // sum for a_j from t to T . ctx.mkInt2Real()
    val `2L/n*SumAj`: RealExpr =
      sumAjF(t(0), T)

//    terms I in p.13
    val num: ArithExpr[RealSort] = iverB(t(0) !== t(1)) * infty_+ + (iverB(t(0) === t(1)) *
      ((w(0) - w(1)).norm() + `2L/n*SumAj`))

    num
  }

  def test = {
    val (prem, propWithPrem) = genSMTterms()

    val allPrem = prem.reduce(_ && _)

    z3CheckApi.checkBoolExpr(
      ctx,
      Seq(propWithPrem),
      List(Status.UNSATISFIABLE), // Status.UNKNOWN
      "rpe(sgd,|w1-w2|) <= 2L/n sum", // "unsat (sat(I_lhs <= I) ~= unsat(not I_lhs <= I))",
      premise = prem,
      printSmtStr = false
    )
  }

}
