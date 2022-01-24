package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._

import precondition.syntax.smtAST._

object rpeSMT {
  import z3Utils._
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  type Rd = RealExpr // n dim reals,let R^d=R for now

  def test = {
    z3CheckApi.checkBoolCtx(ctx, Seq(genSMTterms()))
  }

  /** generate smt terms from program statements and initial smt terms
    * @param stmt program statements
    * @param E : loop invariant
    * @return substituted E
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

  /** generate relational loop invariant I from unrelational loop invariant  I
    * @param t
    * @param w
    * @return
    */
  def I_gen(t: List[IntExpr], w: List[RealExpr]) = {
    import InfRealTuple._
    import ImplicitConv._

//    sum terms in I in p.13
    val `2L/n*SumAj` = mkReal(1)

//    terms I in p.13
    TupNum(iverB(t(0) !== t(1)) -- false) * infty_+ + (TupNum(
      iverB(t(0) === t(1)) -- false
    ) *
      (TupNum(w(0) - w(1) -- false).normW() + `2L/n*SumAj`))

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

  //todo summation in p13  T: Int
  def `2L/n`(L: Int, n: Int, j: IntExpr, a_j: Seq[Float]) = {
//    import InfRealTuple.ctx._
    val Aj_type = mkArraySort(mkIntSort(), mkRealSort())
    val aj = mkConst("aj", Aj_type)
    val r = mkSelect(aj, mkInt(1))
    // can't get indexes t1:IntSort to T:Int or IntSort
    ((2 * L / n) * a_j.reduce(_ + _)).toInt
  }

//  sum function in p.13
  def sum_func() = {
    val sum_f_params: Array[Sort] = Array(mkIntSort(), mkIntSort(), mkIntSort())
//    sum from i to n
    val sum_f = mkFuncDecl("sum", sum_f_params, mkRealSort())
    val i: Expr[IntSort] = mkIntConst("i")
    val n: Expr[IntSort] = mkIntConst("n")
//    array const
    val ajc = mkConst("aj", mkArraySort(mkIntSort(), mkRealSort()))
//    use mkStore() to store values in array
//    the array a_j
    val aj = (x: Expr[IntSort]) => mkSelect(ajc, x)

//    use implicits for mkInt
    import ImplicitConv._
    //  sum i j x(i) = (sum i+1 j x(i+1)) + x(i)
    val prop = sum_f(i, n, aj(i)) === (sum_f(i + 1, n, aj(i + 1)) + aj(i))
    val qtf = forall_z3(Array(i, n), prop)
    (sum_f, qtf)
  }

  /** generate smt terms for while loop body for sgd p.12
    * @return
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
        TupNum(iverB(e1.neg && e2.neg) -- false) * TupNum(w1 - w2 -- false)
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
