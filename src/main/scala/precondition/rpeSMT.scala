package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}

object rpeSMT {
  import precondition.z3api.z3Utils._ //scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  type Rd = RealExpr // n dim reals,let R^d=R for now

  def test = {
    z3CheckApi.checkBoolCtx(
      ctx,
      Seq(genSMTterms()),
      "goal : unsat (sat(I_lhs <= I) ~= unsat(not I_lhs <= I))"
    )
  }

  /** generate smt terms from program statements and initial smt terms
    * @param stmt
    *   program statements
    * @param E
    *   : loop invariant
    * @return
    *   substituted E
    */
  def rpeF[a <: Sort](stmt: StmtSmt, E: Expr[a]): Expr[a] = stmt match {
    case SkipSmt     => E
    case Assig(x, e) => E.substitute(x, e)
    case AssigRand(x, d) =>
      val sum = d.reduce(mkAdd(_, _))
      val r = mkDiv(sum, mkInt(d.size))
      E.substitute(x, r)

    case StmtSmtList(xs) =>
      xs match {
        case i :: Nil => rpeF(i, E)
        case head :: tl =>
          rpeF(head, rpeF(StmtSmtList(tl), E))
      }
    case WhileSmt(annotation, xs) => rpeF(xs, E)
  }

  /** generate relational loop invariant I from unrelational loop invariant I
    * @param t
    * @param w
    * @return
    */
  def I_gen(t: List[IntExpr], w: List[RealExpr]) = {
    import InfRealTuple._
    import ImplicitConv._

//    sum terms in I in p.13
    // val `2L/n*SumAj` = mkReal(1)
    val B_Lipschitz = mkReal(1)
    val (a_j, aj_prop) = aj_func(B = B_Lipschitz)

    val (sumTerm, sumTerm_prop) = sum_func(B = B_Lipschitz, a_j)

    val T = mkInt(10)

    // sum for a_j from t to T
    val `2L/n*SumAj` = sumTerm(t(0), T)
//    terms I in p.13
    TupNum(iverB(t(0) !== t(1)) -- false) * infty_+ + (TupNum(
      iverB(t(0) === t(1)) -- false
    ) *
      ((w(0) - w(1)).normW() + `2L/n*SumAj`))

  }

  /** L-Lipschitz property and Uninterpreted function
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
  def aj_func(B: RealExpr) = {

    val aj: FuncDecl[RealSort] = mkFuncDecl(
      "aj",
      Array(mkIntSort()): Array[Sort],
      mkRealSort()
    )
    val t: Expr[IntSort] = mkIntConst("t")
    val aj_prop = (t < aj(t)) && (aj(t) < (mkReal(2) / B))
    // properties for array a_j :  0<=a_t<=2/B,p12
    val qtf = forall_z3(Array(t), aj_prop)
    (aj, qtf)
  }

//  sum function in p.13
// todo : sum over all indexes of array
// sum_aj : int^2=>real,sum over a_j from i to j
  def sum_func(B: RealExpr, aj: FuncDecl[RealSort]) = {
    val sum_f_params: Array[Sort] = Array(mkIntSort(), mkIntSort())
    // val sum_f_params: Array[Sort] = Array(mkIntSort(), mkIntSort(), mkIntSort())
//    sum from i to n.need to change 3rd param to array?
    val sum_f = mkFuncDecl("sum", sum_f_params, mkRealSort())
    val i: Expr[IntSort] = mkIntConst("i")
    val n: Expr[IntSort] = mkIntConst("n")

//    use implicits for mkInt
    import ImplicitConv.int2mkint
    //  sum i j x(i) = (sum i+1 j x(i+1)) + x(i)
    // val prop = sum_f(i, n, aj(i)) === (sum_f(i + 1, n, aj(i + 1)) + aj(i))
    //trick: encode a_j inside sum
    //  sum i j = (sum i+1 j) + x(i)
    val prop = sum_f(i, n) === (sum_f(i + 1, n) + aj(i))
    val qtf = forall_z3(Array(i, n), prop)
    (sum_f, qtf)
  }

  /** generate smt terms for while loop body for sgd example at p.12
    */
  def genSMTterms() = {
    import InfRealTuple._

    val (l_lip: z3.FuncDecl[RealSort], qtfL) = deltaL_B_Lipschitz(1)

    // example test set
    val s_distrib: Set[Expr[IntSort]] =
      (2 to 6).map(x => mkIntConst(s"s$x")).toSet

//    generator for "while" body
    def whileBd_gen(s1: IntExpr, g1: RealExpr, w1: RealExpr, t1: IntExpr) =
      List(
        AssigRand(s1, s_distrib),
        Assig(g1, l_lip(s1, w1)),
        Assig(w1, w1 - g1),
        Assig(t1, mkAdd(t1, mkInt(1)))
      )

//    vars for loop invariant in p.13
//    simplification:dim w = R instead of R^n
    val w1 :: w2 :: g1 :: g2 :: Nil =
      "w1::w2::g1::g2".split("::").toList.map(x => mkRealConst(x))
    val t1 :: t2 :: Nil = (1 to 2).map(x => mkIntConst(s"t$x")).toList
    val s1 :: s2 :: Nil = mkSymList(2, "s", mkIntConst)

    val e1 :: e2 :: Nil = mkSymList(2, "e", mkBoolConst)

//  relational statements for while loop body
    val whileBd_relational = StmtSmtList(
      List(whileBd_gen(s1, g1, w1, t1), whileBd_gen(s2, g2, w2, t2)).flatten
    )

    val I = I_gen(List(t1, t2), List(w1, w2))

    import ImplicitConv._

    // by TH.7.should be auto derived from I_gen
    val I_lhs: TupNum =
      TupNum(iverB(e1 && e2) -- false) * rpeF(whileBd_relational, I.tup) +
        TupNum(iverB(e1.neg && e2.neg) -- false) * (w1 - w2)
          .normW() +
        iverB(e1 !== e2)

    val goal = I_lhs <= I
    val goalWithAxiom = qtfL ==> goal

//    println("I_lhs : ", I_lhs.toString)
    goalWithAxiom.neg
  }

}
//    pp("I before rpe:")
//    pp(I.tup.toString)
//    val deltaL = ""
