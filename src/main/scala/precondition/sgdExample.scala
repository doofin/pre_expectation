package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}

import lemmas._
import rpeFunction._
import InfRealTuple.TupNum

object sgdExample {
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
    val w0 = newVec("w0")
    val t0 = mkIntConst("t0")
    val t0prop = t0 === mkInt(0)
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

    val varProps = atPrpo && t0prop
    // delta L function with Lipschitz property
    val (deltaL, lipschez_premise) = vec_deltaL(1)

    val (f_bij, f_bij_prop) = lemmas.f_bijection_int()
    val rpeF_inst = rpeF(f_bij) _
    //  relational statements for while loop body
    //  generate relational I ,also return sumF_Aj=sum i j a_j for convenience
    val (invariant, sumF_Aj, i_prem) = invariant_gen(List(t1, t2), List(w1, w2), T)

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

    import ImplicitConv._

    // by TH.7.should be auto derived from I_gen

    val premises: Seq[BoolExpr] =
      Seq(lipschez_premise, lemmas.vecPremise, varProps, T_prem) ++ i_prem

    val premise = premises.reduce(_ && _)
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

    // val goal = I_lhs <= invariant
    // val goalWithAxiom = premise ==> goal

    // p13. rpe(sgd,|w1-w2|) <= 2L/n sum
    val (goalLhs, sideConds) = rpeF_inst(
      sgdProgram,
      (w1 - w2)
        .norm(),
      List() // initial side conditions
    )

    val sideCond = sideConds.reduce(_ && _)

    // sum 0 T - 1 a_j
    // val goalRhs = sumF_Aj(0, T - 1)
    val goalRhs = sumF_Aj(0, T) //

    // println("sideCond :", sideCond.toString())
    // println("goal2lhs <= goal2rhs")
    // println(goal2lhs <= goal2rhs)

    // val finalGoal = (premise ==> (goalLhs <= goalRhs)) && (premise ==> sideCond) // unknown
    val finalGoal = (premise ==> (mkReal(0) <= goalRhs)) && (premise ==> sideCond) // unknown
    // val finalGoal = (premise ==> sideCond) // unsat

//    println("I_lhs : ", I_lhs.toString)
    // (premises, goalWithAxiom.neg)

    (premises, finalGoal.neg)
  }

  /**
   * loop invariant I at p13 to be put as annotation of while loop
   * @param t
   * @param w
   * @return
   */
  def invariant_gen(t: List[IntExpr], w: List[Expr[VecType]], T: IntExpr) = {

    import z3Utils._
    import ImplicitConv.int2mkint
//    sum terms in I in p.13
    val (beta, n, l_L) =
      (mkRealConst("beta"), mkIntConst("n"), mkRealConst("L"))

    val numProp = (beta > 0) && (n > 0) && (l_L >= 0)
    val (a_j, aj_prop) = aj_func(B = beta)

    val (sumFuncInst, sumFunc_prop) = sum_func_ord(a_j)

    val sumTermAjF = { (startIdx: Expr[IntSort], endIdx: Expr[IntSort]) =>
      (mkReal(2) * l_L / mkInt2Real(n) * sumFuncInst(
        startIdx,
        endIdx
      )).asInstanceOf[RealExpr]
    }

    // sum for a_j from t to T . ctx.mkInt2Real()
    val `2L/n*SumAj`: RealExpr =
      sumTermAjF(t(0), T)

    import ImplicitConv._
    import InfRealTuple._
//    terms I in p.13
    val tup = TupNum(iverB(t(0) !== t(1)) -- false) * infty_+ + (TupNum(
      iverB(t(0) === t(1)) -- false
    ) *
      ((w(0) - w(1)).norm() + `2L/n*SumAj`))

    (tup, sumTermAjF, Seq(numProp) ++ aj_prop ++ Seq(sumFunc_prop))
  }

  // delta loss function for vector W
  def vec_deltaL(B: Long) = {

    val typesOfParam: Array[Sort] =
      Array(mkIntSort(), vecSort)
    val l = mkFuncDecl("delta_lossF", typesOfParam, vecSort)
    val z1 = mkIntConst("z1")
    val (w1, w2) = (newVec("w11"), newVec("w12"))
//    B-Lipschitz as p.12
    val L = mkReal(B)

//    L-Lipschitz property
    val prop = (l(z1, w1) - l(z1, w2))
      .norm() <= (L * (w1 - w2).norm())

    val qtf: Quantifier =
      forall_z3(Array(z1, w1, w2).asInstanceOf[Array[Expr[Sort]]], prop)
    (l, qtf)

  }

  /**
   * L-Lipschitz property and Uninterpreted function
   */
  def deltaL_B_Lipschitz(B: Long) = {

    val typesOfParam: Array[Sort] =
      Array(mkIntSort(), mkRealSort())
    val l = mkFuncDecl("lossF_Lipschitz", typesOfParam, mkRealSort())
    val z1 = mkIntConst("z1")
    val (w1, w2) = (mkRealConst("w11"), mkRealConst("w12"))
//    B-Lipschitz as p.12
    val L = mkReal(B)

//    L-Lipschitz property
    val prop = (l(z1, w1) - l(z1, w2))
      .normW() <= (L * (w1 - w2).normW())

    val qtf: Quantifier =
      forall_z3(Array(z1, w1, w2).asInstanceOf[Array[Expr[Sort]]], prop)
    (l, qtf)
  }

  // summation in p13  T: Int
  // smt check: unknown,take 15min
  def aj_func(B: RealExpr) = {

    val aj: FuncDecl[RealSort] = mkFuncDecl(
      "aj",
      Array(mkIntSort()): Array[Sort],
      mkRealSort()
    )
    val t: Expr[IntSort] = mkIntConst("t")
    // properties for array a_j :  0<=a_t<=2/B,p12
    val aj_prop = (mkReal(0) <= aj(t)) && (aj(t) <= (mkReal(2) / B))
    // 2 th premise,take long time.fixed
    val qtf = forall_z3(Array(t), aj_prop)
    (aj, Seq(qtf))
  }

  def test = {
    val (prem, propWithPrem) = genSMTterms()

    val allPrem = prem.reduce(_ && _)

    z3CheckApi.checkBoolExpr(
      ctx,
      Seq(propWithPrem),
      List(Status.UNSATISFIABLE, Status.UNKNOWN),
      "rpe(sgd,|w1-w2|) <= 2L/n sum", // "unsat (sat(I_lhs <= I) ~= unsat(not I_lhs <= I))",
      premise = prem,
      printSmtStr = false
    )
  }

}
