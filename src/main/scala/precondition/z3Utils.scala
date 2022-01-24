package precondition

import com.microsoft.z3
import com.microsoft.z3.enumerations.Z3_ast_print_mode
import com.microsoft.z3._

import scala.collection.JavaConverters._
import com.doofin.stdScala._

object z3Utils {

  /** make a list of constants,etc
    *
    * @param i
    *   : num of
    * @param sym
    *   : symbol name
    * @param maker
    *   : mkInt,etc
    * @return
    */
  def mkSymList[a](i: Int, sym: String, maker: String => a) = {
    (1 to i).map(x => maker(s"$sym$x")).toList
  }
  def newZ3ctx1() = new Context(Map[String, String]("model" -> "true").asJava) {
    setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT)
  }

//  some hack to make import work
  private lazy val ctx: Context = newZ3ctx1()

  def newZ3ctx() = ctx

  import ctx._

  def iverB(x: Expr[BoolSort]) = {
    mkITE(x, mkReal(1), mkReal(0))
  }

  implicit class exprOps[a <: Sort](x: Expr[a]) {

    def ===(that: Expr[a]) = ctx.mkEq(x, that)
    def !==(y: Expr[a]) = ctx.mkEq(x, y).neg
  }

  // a <: ArithSort
  implicit class realOps(
      x: Expr[RealSort]
  ) {
    def <=(y: Expr[RealSort]) = mkLe(x, y)
    def <(y: Expr[RealSort]) = mkLt(x, y)
    def >=(y: Expr[RealSort]) = mkGe(x, y)
    def >(y: Expr[RealSort]) = mkGt(x, y)
    def -(y: Expr[RealSort]) = mkSub(x, y)
    def +(y: Expr[RealSort]) = mkAdd(x, y)
    def *(y: Expr[RealSort]) = mkMul(x, y)

    def isPos = mkGt(x, mkReal(0, 1))
    def normW() = mkITE(x.isPos, x, mkSub(mkReal(0), x))
  }

  // a <: ArithSort
  implicit class intOps(
      x: Expr[IntSort]
  ) {
    def +(y: Expr[IntSort]) = mkAdd(x, y)
    def *(y: Expr[IntSort]) = mkMul(x, y)

  }

  implicit class arr[D <: Sort, R <: Sort](ar: Expr[ArraySort[D, R]]) {
    def update(var2: Expr[D], var3: Expr[R]) = mkStore[D, R](ar, var2, var3)
  }

  // a <: ArithSort

  /*
  implicit class numOps(
      x: ArithExpr[_ <: ArithSort]
  ) {
    def <=(y: Expr[RealSort]) = mkLe(x, y)
    def <(y: Expr[RealSort]) = mkLt(x, y)
    def >=(y: Expr[RealSort]) = mkGe(x, y)
    def >(y: Expr[RealSort]) = mkGt(x, y)
    def -(y: Expr[RealSort]) = mkSub(x, y)
    def +(y: Expr[RealSort]) = mkAdd(x, y)
    def *(y: Expr[RealSort]) = mkMul(x, y)

    def isPos = mkGt(x, mkReal(0, 1))
    def normW() = mkITE(x.isPos, x, mkSub(mkReal(0), x))
  }
   */

  implicit class boolOps(x: Expr[BoolSort]) {
    def ||(other: Expr[BoolSort]) = mkOr(x, other)
    def isTrueB = x === mkTrue()
    def isFalseB = x === mkFalse()
    def &&(other: Expr[BoolSort]) = mkAnd(x, other)
    def neg = mkNot(x)
    def ==>(other: Expr[BoolSort]) = mkImplies(x, other)
  }

  def forall_z3[a <: Sort](exprs: Array[Expr[a]], boolExpr: BoolExpr) = {
    ctx.mkForall(
      exprs.asInstanceOf[Array[Expr[_]]],
      boolExpr,
      1,
      null,
      null,
      null,
      null
    )
  }
}
