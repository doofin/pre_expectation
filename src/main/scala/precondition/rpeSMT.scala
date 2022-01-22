package precondition

import com.microsoft.z3.{
  ArithSort,
  Expr,
  IntExpr,
  IntSort,
  Pattern,
  Quantifier,
  RealExpr,
  RealSort,
  Sort,
  StringSymbol,
  TupleSort,
  UninterpretedSort
}
import precondition.dslAST._
import cats.data._
import cats.implicits._
import cats.free.Free._
import cats.free.Free
import cats.{Id, ~>}

import scala.collection.mutable
import com.doofin.stdScala._
import com.microsoft.z3
import precondition.InfRealTuple.{TupNum, tupTp_InfReal}

object rpeSMT {
  import z3Utils._
  private lazy val ctx = newZ3ctx()
  import ctx._

  sealed trait StmtSmt
  case object SkipSmt extends StmtSmt
  case class Assig[a <: Sort](x: Expr[a], e: Expr[a]) extends StmtSmt
  case class AssigRand[a <: ArithSort](x: Expr[a], d: Set[Expr[a]])
      extends StmtSmt
  case class StmtSmtList(xs: List[StmtSmt]) extends StmtSmt {
    def append(x: StmtSmt) = StmtSmtList(xs :+ x)
  }
  case class WhileSmt(annotation: Option[String], xs: StmtSmtList)
      extends StmtSmt

  type Rd = RealExpr // set Rd=R for now
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
//  val sortS = ctx.mkUninterpretedSort("s")
//  val s1: Expr[UninterpretedSort] = ctx.mkConst("s1", sortS)
//  val s1: IntExpr = ctx.mkIntConst("s1")

  /** l:int,tupReal->tupReal z:int ~= type of samples w:real simplifed from R^d
    * tuple num or normal num?
    */
  def deltaL_B_Lipschitz(B: Long) = {
    // import InfRealTuple._
    val typesOfParam: Array[Sort] =
      Array(mkIntSort(), mkRealSort())
    val l = mkFuncDecl("l_Lip", typesOfParam, mkRealSort())
    val z1 = mkIntConst("z1")
    // val w1 = mkConst("w1", InfRealTuple.tupTp_InfReal)
    // val w2 = mkConst("w2", InfRealTuple.tupTp_InfReal)
    val (w1, w2) = (mkRealConst("w1"), mkRealConst("w2"))
    // val L = TupNum(mkReal(B) -- false)
    val L = mkReal(B)

    val prop = (l(z1, w1) - l(z1, w2))
      .normW() <= (L * (w1 - w2).normW())

    val qtf: Quantifier =
      forall_z3(Array(z1, w1, w2).asInstanceOf[Array[Expr[Sort]]], prop)
    (l, qtf)
  }

  def f_bijection() = {
    val params: Array[Sort] = Array(mkIntSort())
    val f = mkFuncDecl("f_bij", params, mkIntSort())
    val f_inv = mkFuncDecl("f_bij_inv", params, mkIntSort())
    val z1: Expr[IntSort] = mkIntConst("z1")
    val prop = (f(f_inv(z1)) === z1) && (f_inv(f(z1)) === z1)

    val qtf = forall_z3(Array(z1), prop)
    (f, qtf)
  }
//  T: Int
  def `2L/n`(L: Int, n: Int, a_j: Seq[Float]) = {
//    import InfRealTuple.ctx._
    ((2 * L / n) * a_j.reduce(_ + _)).toInt
  }

  def rpeSMT() = {
    import InfRealTuple._

    println("rpeSMT newvar start")
    val (l_lip, qtfL) = deltaL_B_Lipschitz(1)
    val (f_bij, qtfF) = f_bijection()

    val s_distrib: Set[Expr[IntSort]] =
      (2 to 6).map(x => mkIntConst(s"s$x")).toSet

    def whileBd_gen(s1: IntExpr, g1: RealExpr, w1: RealExpr, t1: IntExpr) =
      List(
        AssigRand(s1, s_distrib),
        Assig(g1, l_lip(s1, w1)),
        Assig(w1, w1 - g1),
        Assig(t1, mkAdd(t1, mkInt(1)))
      )

    val w1 :: w2 :: g1 :: g2 :: Nil =
      "w1::w2::g1::g2".split("::").toList.map(x => mkRealConst(x))
    val t1 :: t2 :: Nil = (1 to 2).map(x => mkIntConst(s"t$x")).toList
    val s1 :: s2 :: Nil = (1 to 2).map(x => mkIntConst(s"s$x")).toList

    val e1 :: e2 :: Nil = "e1::e2".split("::").toList.map(x => mkBoolConst(x))
    val `2L/n*SumAj` = mkReal(1)

    // import shapeless._
    // import syntax.std.tuple._

    val whileBd = StmtSmtList(
      List(
        AssigRand(s1, s_distrib),
        Assig(g1, l_lip(s1, w1)),
        Assig(w1, w1 - g1),
        Assig(t1, mkAdd(t1, mkInt(1)))
      )
    )

    val whileBd_rel = StmtSmtList(
      List(whileBd_gen(s1, g1, w1, t1), whileBd_gen(s2, g2, w2, t2)).flatten
    )

    import implicits_tup.tup2inj

    def I_gen(t: List[IntExpr], w: List[RealExpr]) = {
      TupNum(iverB(t(0) !== t(1)) -- false) * infty_+ + (TupNum(
        iverB(t(0) === t(1)) -- false
      ) *
        (TupNum(w(0) - w(1) -- false).normW() + TupNum(`2L/n*SumAj`, false)))

    }
    val I = I_gen(List(t1, t2), List(w1, w2))
    val rpe_bd_I = rpeF(whileBd_rel, I.tup) // `I''`
//    println("I after rpe:")
//    pp(rpe_bd_I.toString)

    import implicits_tup.finite2tup

    val I_lhs: TupNum = TupNum(iverB(e1 && e2) -- false) * TupNum(rpe_bd_I) +
      TupNum(iverB(e1.neg && e2.neg) -- false) * TupNum(w1 - w2 -- false)
        .normW() +
      iverB(e1 !== e2)

    val goal = I_lhs <= I
    val goal_ax = (qtfF && qtfL) ==> goal

//    println("I_lhs : ", I_lhs.toString)
//    println("goal", goal.toString)
    z3CheckApi.checkBoolCtx(ctx, Seq(goal_ax.neg))
  }

  def test = {
    import InfRealTuple._
    rpeSMT()
  }

  /** natural transformation between type containers. need two lang,dsl->ast,
    * can also translate into tree
    */
  def compile2SmtStmt =
    new (DslStoreA ~> Id) {
      val kvs = mutable.Map.empty[Int, String]
      //      tr : current node to insert
      var currCtx: Option[String] = None
      var ln: Int = 0
      var stmtSmtListInserter = { x: StmtSmt =>
        StmtSmtList(List() :+ x)
      }

      var isAccum: Boolean = false
      var stmtSmtListAccu = StmtSmtList(List())
      var stmtSmtListGlob = StmtSmtList(List())

      override def apply[A](fa: DslStoreA[A]): Id[A] = {
        ln += 1
        println(s"fa : ${fa}")

        currCtx match {
          case Some(value) => kvs.put(ln, s"($value)  ${fa.toString}")
          case None        => kvs.put(ln, fa.toString)
        }

        fa match {
          case UpdateVar(v, value) =>
            println("isAccum", isAccum, stmtSmtListAccu)
            if (isAccum) {
              stmtSmtListAccu = stmtSmtListAccu.append(Assig(null, null))
            } else stmtSmtListGlob = stmtSmtListGlob.append(Assig(null, null))

            ()
          case NewVar(name) => Var(name)
          case While(cond, annotation, bd) =>
            println("While start")

            currCtx = Some(annotation)

            isAccum = true
            val r = bd.foldMap(this)
            isAccum = false
            stmtSmtListGlob = stmtSmtListGlob.append(
              WhileSmt(Some(annotation), stmtSmtListAccu)
            )
            println("While end")
            //            While(cond, annotation, bd.step)
            currCtx = None
            r
          case True => true
          case Skip => ()

        }
      }
    }

}

//    val expr = TupNum((ctx.mkReal(1), true)) <= TupNum((ctx.mkReal(1), true))
//    println(expr.toString)
//    z3java.checkBoolCtx(ctx, Seq(expr))

//    val P = TupNum(`2L/n*SumAj`, false) + (TupNum(w1, false) - TupNum(w2, false))
//    val I_f = (x: TupNum) =>
//      TupNum(iverB(t1 !== t2) -- false) * infty_+ + (TupNum(iverB(t1 === t2) -- false) * x)
//    val `I'`  = I_f(P)
//    val `I''` = I_f(P) //I''

//    pp("I before rpe:")
//    pp(I.tup.toString)
//    val deltaL = ""
