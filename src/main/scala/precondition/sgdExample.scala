package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}
import cats.kernel.instances.TupleMonoidInstances

import lemmas._
import rpeFunction.rpeF
object sgdExample {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  type Rd = RealExpr // n dim reals,let R^d=R for now

  /**
   * generate smt terms for while loop body for sgd example at p.12
   */
  def genSMTterms() = {
    import InfRealTuple._

    // delta L function with Lipschitz property
    val (l_lip, lip_premise) = vec_deltaL(1)

    // example test set
    val s_distrib: Set[Expr[IntSort]] =
      (2 to 6).map(x => mkIntConst(s"s$x")).toSet

//    vars for loop invariant in p.13
//   prev simplification:dim w = R instead of R^n
    val w0 = newVec("w0")
    val t0 = mkIntConst("t0")
    val t0prop = t0 === mkInt(0)
    val (w1, w2) = (newVec("w1"), newVec("w2"))

    val (g1, g2) = (newVec("g1"), newVec("g2"))
    val t1 :: t2 :: Nil = (1 to 2).map(x => mkIntConst(s"t$x")).toList
    val s1 :: s2 :: Nil = mkSymList(2, "s", mkIntConst)

    val e1 :: e2 :: Nil = mkSymList(2, "e", mkBoolConst)

    // a_t for sgd
    val at = mkRealConst("a_t")
    val atPrpo = at > mkReal(0)

    val varProps = atPrpo && t0prop
    val (f_bij, f_bij_prop) = lemmas.f_bijection_int()
    val rpeF_inst = rpeF(f_bij) _
    //  relational statements for while loop body
    //  generate relational I
    val (invariant, i_prem) = I_gen(List(t1, t2), List(w1, w2))

    val whileBd_relational = StmtSmtList(
      List(
        AssigRand(s1, s2, s_distrib),
        Assig(g1, l_lip(s1, w1), g2, l_lip(s2, w2)),
        Assig(w1, w1 - g1.mulByScalar(at), w2, w2 - g2.mulByScalar(at)),
        Assig(t1, t1 + mkInt(1), t2, t2 + mkInt(1))
      )
    )
    
    // todo: sgd is not used
    // interp seq is revesed,how to put params for invariant?
    val sgd =
      StmtSmtList(
        List(
          NewVars(w1, w0, w2, w0),
          NewVars(t1, t0, t2, t0),
          WhileSmt(
            I_gen(List(t1, t2), List(w1, w2))._1.tup,
            whileBd_relational
          )
        )
      )

    // println("whileBd_relational")
    // pp(whileBd_relational)

    // test on sgd whole
    println("rpeF_inst(sgd, invariant)")
    rpeF_inst(sgd, invariant)

    import ImplicitConv._

    // by TH.7.should be auto derived from I_gen

    val I_lhs: TupNum =
      TupNum(iverB(e1 && e2) -- false) * rpeF_inst(
        whileBd_relational,
        invariant
      ) +
        TupNum(iverB(e1.neg && e2.neg) -- false) * (w1 - w2)
          .norm() +
        iverB(e1 !== e2)

    val goal = I_lhs <= invariant
    val premise: Seq[BoolExpr] =
      Seq(lip_premise, lemmas.vecPremise, varProps) ++ i_prem
    val goalWithAxiom = premise.reduce(_ && _) ==> goal

//    println("I_lhs : ", I_lhs.toString)
    (premise, goalWithAxiom.neg)
  }

  /**
   * generate relational loop invariant I from unrelational loop invariant I
   * @param t
   * @param w
   * @return
   */
  def I_gen(t: List[IntExpr], w: List[Expr[VecType]]) = {

    import z3Utils._
    import ImplicitConv.int2mkint
//    sum terms in I in p.13
    // val `2L/n*SumAj` = mkReal(1)
    val (beta, n, l_L) =
      (mkRealConst("beta"), mkIntConst("n"), mkRealConst("L"))

    val numProp = (beta > 0) && (n > 0) && (l_L >= 0)
    val (a_j, aj_prop) = aj_func(B = beta)

    val (sumTerm, sumTerm_prop) = sum_func(a_j)

    val T = mkIntConst("T")

    // sum for a_j from t to T
    // ctx.mkInt2Real()
    val `2L/n*SumAj`: RealExpr =
      (mkReal(2) * l_L / mkInt2Real(n) * sumTerm(
        t(0),
        T
      )).asInstanceOf[RealExpr]

    import ImplicitConv._
    import InfRealTuple._
//    terms I in p.13
    val tup = TupNum(iverB(t(0) !== t(1)) -- false) * infty_+ + (TupNum(
      iverB(t(0) === t(1)) -- false
    ) *
      ((w(0) - w(1)).norm() + `2L/n*SumAj`))

    (tup, Seq(numProp) ++ aj_prop ++ Seq(sumTerm_prop))
  }

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
  // smt unknown,take 15min
  def aj_func(B: RealExpr) = {

    val aj: FuncDecl[RealSort] = mkFuncDecl(
      "aj",
      Array(mkIntSort()): Array[Sort],
      mkRealSort()
    )
    val t: Expr[IntSort] = mkIntConst("t")
    // val bt = mkRealConst("beta")
    // val btq = bt > mkReal(0)
    // properties for array a_j :  0<=a_t<=2/B,p12
    val aj_prop = (mkReal(0) < aj(t)) && (aj(t) < (mkReal(2) / B))
    // 2 th premise,take long time.fixed
    val qtf = forall_z3(Array(t), aj_prop)
    (aj, Seq(qtf))
  }

//  sum function in p.13
// sum_aj : int^2=>real,sum over a_j from i to j
// (smt result:,UNKNOWN)
  def sum_func(aj: FuncDecl[RealSort]) = {
    /* val sum_f_params: Array[Sort] = Array(mkIntSort(), mkIntSort(),
     * mkIntSort()) */
//    sum from i to n.need to change 3rd param to array?
    val sum_f = mkFuncDecl(
      "sum",
      Array(mkIntSort(), mkIntSort()): Array[Sort],
      mkRealSort()
    )
    val i: Expr[IntSort] = mkIntConst("i")
    val n: Expr[IntSort] = mkIntConst("n")

    import ImplicitConv.int2mkint
    val numProp = i >= 0 && (n >= 0)
//    use implicits for mkInt
    import ImplicitConv.int2mkint
    //  sum i j x(i) = (sum i+1 j x(i+1)) + x(i)
    // val prop = sum_f(i, n, aj(i)) === (sum_f(i + 1, n, aj(i + 1)) + aj(i))
    // trick: encode a_j inside sum
    //  sum i j = (sum i+1 j) + x(i)
    val prop1 = i <= n ==> (sum_f(i, n) === (sum_f(i + 1, n) + aj(i)))
    val prop2 = i > n ==> (sum_f(i, n) === 0)

    val qtf = forall_z3(Array(i, n), prop1 && prop2)
    (sum_f, numProp && qtf)
  }

  def test = {
    val (prem, propWithPrem) = genSMTterms()

    val allPrem = prem.reduce(_ && _)

    z3CheckApi.checkBoolExpr(
      ctx,
      Seq(propWithPrem),
      Status.UNSATISFIABLE,
      "unsat (sat(I_lhs <= I) ~= unsat(not I_lhs <= I))",
      premise = prem,
      printSmtStr = false
    )
  }

}
