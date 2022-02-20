package precondition.z3api

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

  

  implicit class exprOps(x: Expr[_]) {

    def ===(that: Expr[_]) = ctx.mkEq(x, that)

    def !==(y: Expr[_]) = ctx.mkEq(x, y).neg
  }

  // a <: ArithSort
  implicit class allOps[r <: ArithSort](
      x: Expr[_ <: r]
  ) {

    def -(y: Expr[_ <: r]) = mkSub(x, y)

    def +(y: Expr[_ <: r]) = mkAdd(x, y)

    def *(y: Expr[_ <: r]) = mkMul(x, y)

    def /(y: Expr[_ <: r]) = mkDiv(x, y)

    // def isPos = mkGt(x, mkReal(0, 1))

  }

  implicit class compareOps(
      x: Expr[_ <: ArithSort]
  ) {
    def <=(y: Expr[_ <: ArithSort]) = mkLe(x, y)

    def <(y: Expr[_ <: ArithSort]) = mkLt(x, y)

    def >=(y: Expr[_ <: ArithSort]) = mkGe(x, y)

    def >(y: Expr[_ <: ArithSort]) = mkGt(x, y)

    def isPos = mkGt(x, mkReal(0, 1))

  }
  // a <: ArithSort

  implicit class realOps(
      x: Expr[RealSort]
  ) {
    def normW() = mkITE(x.isPos, x, mkSub(mkReal(0), x))
  }

  implicit class arr[D <: Sort, R <: Sort](ar: Expr[ArraySort[D, R]]) {
    def update(var2: Expr[D], var3: Expr[R]) = mkStore[D, R](ar, var2, var3)
  }

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
