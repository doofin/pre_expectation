package precondition

import com.microsoft.z3.{Expr, Pattern, Quantifier, RealExpr, RealSort, Sort, StringSymbol, TupleSort, UninterpretedSort}
import precondition.dslAST._
import cats.data._
import cats.implicits._
import cats.free.Free._
import cats.free.Free
import cats.{Id, ~>}

import scala.collection.mutable
import com.doofin.stdScala._
import com.microsoft.z3
import precondition.InfRealTuple.numOps

//import scala.jdk.CollectionConverters._

object rpeSMT {

  sealed trait StmtSmt
  case object SkipSmt                          extends StmtSmt
  case class Assig(x: Expr[_], e: Expr[_])     extends StmtSmt
  case class AssigRand(x: Expr[_], d: Expr[_]) extends StmtSmt
  case class StmtSmtList(xs: List[StmtSmt]) extends StmtSmt {
    def append(x: StmtSmt) = StmtSmtList(xs :+ x)
  }
  case class WhileSmt(annotation: Option[String], xs: StmtSmtList) extends StmtSmt

  type Rd = RealExpr
  def rpeF[a <: Sort](stmt: StmtSmt, E: Expr[a]): Expr[a] = stmt match {
    case SkipSmt         => E
    case Assig(x, e)     => E.substitute(x, e)
    case AssigRand(x, d) => E
    case StmtSmtList(xs) =>
      xs match {
        case i :: Nil     => rpeF(i, E)
        case ::(head, tl) => rpeF(head, rpeF(StmtSmtList(tl), E))
      }
    case WhileSmt(annotation, xs) => rpeF(xs, E)
  }
  import InfRealTuple.ctx
  val sortS                       = ctx.mkUninterpretedSort("s")
  val s1: Expr[UninterpretedSort] = ctx.mkConst("s1", sortS)

  def DeltaL_B_Lipschitz(z_s: Expr[UninterpretedSort])(w: Rd) = {
    import InfRealTuple.ctx._
    val sortsParam         = Array(sortS, mkRealSort())
    val l                  = mkFuncDecl("l", sortsParam, mkRealSort())
    val fr: Expr[RealSort] = l(z_s, w)
    val types              = Array(sortS, mkRealSort())
    val qVars: Array[z3.Symbol] = Array(mkSymbol(""))
    val qtf: Quantifier    = mkForall(types, qVars, fr < fr, 1, Array(mkPattern(fr)), null, null, null)

  }

//  T: Int
  def `2L/n`(L: Int, n: Int, a_j: Seq[Float]) = {
//    import InfRealTuple.ctx._
    ((2 * L / n) * a_j.reduce(_ + _)).toInt
  }

  def rpeSMT() = {
    import InfRealTuple._
    import InfRealTuple.ctx._

    println("rpeSMT newvar start")
    val t1 :: t2 :: w1 :: w2 :: Nil = "t1::t2::w1::w2".split("::").toList.map(x => mkRealConst(x))
    val e1 :: e2 :: Nil             = "e1::e2".split("::").toList.map(x => mkBoolConst(x))
    val `2L/n*SumAj`                = mkReal(1)
    val I = TupNum(iverB(t1 !== t2) -- false) * infty_+ + (TupNum(iverB(t1 === t2) -- false) *
      (TupNum(w1 - w2 -- false).normW() + TupNum(`2L/n*SumAj`, false)))

//    val P = TupNum(`2L/n*SumAj`, false) + (TupNum(w1, false) - TupNum(w2, false))
//    val I_f = (x: TupNum) =>
//      TupNum(iverB(t1 !== t2) -- false) * infty_+ + (TupNum(iverB(t1 === t2) -- false) * x)
//    val `I'`  = I_f(P)
//    val `I''` = I_f(P) //I''

//    pp("I before rpe:")
//    pp(I.tup.toString)
//    val deltaL = ""

    val whileBd  = StmtSmtList(List(Assig(w1, w1 + mkReal(1)), Assig(t1, t1 + mkReal(1))))
    val rpe_bd_I = rpeF(whileBd, I.tup) // `I''`
//    println("I after rpe:")
//    pp(rpe_bd_I.toString)

    val I_lhs = TupNum(iverB(e1 && e2) -- false) * TupNum(rpe_bd_I) +
      TupNum(iverB(e1.neg && e2.neg) -- false) * TupNum(w1 - w2 -- false).normW() +
      TupNum(iverB(e1 !== e2) -- false)

    val goal = I_lhs <= I

//    println("I_lhs : ", I_lhs.toString)
//    println("goal", goal.toString)
    z3java.checkBoolCtx(ctx, Seq(goal))
  }

  def test = {
    import InfRealTuple._
//    val expr = TupNum((ctx.mkReal(1), true)) <= TupNum((ctx.mkReal(1), true))
//    println(expr.toString)
//    z3java.checkBoolCtx(ctx, Seq(expr))
    rpeSMT()
  }

  /**
    * natural transformation between type containers.
    *need two lang,dsl->ast, can also translate into tree*/
  def compile2SmtStmt =
    new (DslStoreA ~> Id) {
      val kvs = mutable.Map.empty[Int, String]
      //      tr : current node to insert
      var currCtx: Option[String] = None
      var ln: Int                 = 0
      var stmtSmtListInserter = { x: StmtSmt =>
        StmtSmtList(List() :+ x)
      }

      var isAccum: Boolean = false
      var stmtSmtListAccu  = StmtSmtList(List())
      var stmtSmtListGlob  = StmtSmtList(List())

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
            stmtSmtListGlob = stmtSmtListGlob.append(WhileSmt(Some(annotation), stmtSmtListAccu))
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
