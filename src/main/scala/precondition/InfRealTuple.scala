package precondition

import com.microsoft.z3._
import com.doofin.stdScala._

import com.microsoft.z3.enumerations.Z3_ast_print_mode

import z3Utils._
import scala.collection.JavaConverters._

import scala.language.existentials

object InfRealTuple {
  lazy val ctx: Context = new Context(Map[String, String]("model" -> "true").asJava)
  ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT)

  val infty_+ = TupNum(ctx.mkReal(1) -- true)
// intsort,bool

  lazy val proj @ (tupTp, inj, prjArr) = {
    import ctx._
    val r =
      mkTupleSort(
        mkSymbol("mk_tuple1"),
        Array(mkSymbol("fst"), mkSymbol("snd")),
        Array(mkRealSort(), mkBoolSort())
      )
    (r, r.mkDecl(), r.getFieldDecls)
  }

  lazy val projReal :: projBool :: Nil = prjArr.toList

  implicit def tup2inj(v_tup: (Expr[RealSort], Boolean)): Expr[TupleSort] =
    inj(v_tup._1, ctx.mkBool(v_tup._2))

  case class TupNum(tup: Expr[TupleSort]) {

    import ctx._

    val (real1: RealExpr, bool1: Expr[BoolSort]) = (projReal(tup), projBool(tup))
    val isInf: BoolExpr                          = bool1.isTrueB
//    private val tup_inf = inj(mkReal(1, 1), mkTrue())

    def mkBinaryOp(op: (RealExpr, RealExpr) => Expr[RealSort])(oth: TupNum) = {
      val (real2: RealExpr, bool2: BoolExpr) = (projReal(oth.tup), projBool(oth.tup))
      val notInf                             = inj(op.apply(real1, real2), mkFalse())
      val r                                  = mkITE(isInf, tup, mkITE(oth.isInf, oth.tup, notInf))
      TupNum(r)
    }

    def + = mkBinaryOp(_ + _) _

    def - = mkBinaryOp(_ - _) _

    def * = mkBinaryOp(_ * _) _

    /**
      * if oth are pos inf,then true
      * if both are not inf,compare real part*/
    def <=(oth: TupNum) = {
      val (real2: RealExpr, bool2: BoolExpr) = (projReal(oth.tup), projBool(oth.tup))

      val isNotInf       = bool1.isFalseB || bool2.isFalseB
      val real1_lt_real2 = real1 <= real2

      val oth_isPosInf = oth.isInf && real2.isPos
      oth_isPosInf || (isNotInf && real1_lt_real2)
    }

    def normW() = {
      TupNum(mkITE(isInf, tup, TupNum(real1.normW() -- false).tup))
    }

  }

  import ctx._

  def iverB(x: Expr[BoolSort]) = {
    mkITE(x, mkReal(1), mkReal(0))
  }

  implicit class exprOps[a <: Sort](x: Expr[a]) {

    def ===(that: Expr[a]) = ctx.mkEq(x, that)
    def !==(y: Expr[a])    = ctx.mkEq(x, y).neg
  }

  implicit class numOps(x: Expr[RealSort]) {
    def <=(y: Expr[RealSort]) = mkLe(x, y)
    def <(y: Expr[RealSort])  = mkLt(x, y)
    def >=(y: Expr[RealSort]) = mkGe(x, y)
    def >(y: Expr[RealSort])  = mkGt(x, y)
    def -(y: Expr[RealSort])  = mkSub(x, y)
    def +(y: Expr[RealSort])  = mkAdd(x, y)
    def *(y: Expr[RealSort])  = mkMul(x, y)

    def isPos   = x > mkReal(0, 1)
    def normW() = mkITE(x.isPos, x, mkSub(mkReal(0), x))
  }

  implicit class boolOps(x: Expr[BoolSort]) {
    def ||(other: Expr[BoolSort]) = mkOr(x, other)
    def isTrueB                   = x === mkTrue()
    def isFalseB                  = x === mkFalse()
    def &&(other: Expr[BoolSort]) = mkAnd(x, other)
    def neg                       = mkNot(x)
  }

}
