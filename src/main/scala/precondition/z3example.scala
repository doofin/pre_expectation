package precondition

import com.microsoft.z3
import com.microsoft.z3.{Context, Expr, IntExpr, Sort}

object z3example {
  import z3Utils._
  def quantifierExample1(ctx: Context): Unit = {
    System.out.println("QuantifierExample")
    //    Log.append("QuantifierExample")
    val types = new Array[Sort](3)
    val xs    = new Array[IntExpr](3)
    val names = new Array[z3.Symbol](3)
    val vars  = new Array[IntExpr](3)
    for (j <- 0 until 3) {
      types(j) = ctx.getIntSort
      names(j) = ctx.mkSymbol("x_" + Integer.toString(j))
      xs(j) = ctx.mkConst(names(j), types(j)).asInstanceOf[IntExpr]

      // <-- vars reversed!
      vars(j) = ctx.mkBound(2 - j, types(j)).asInstanceOf[IntExpr]

    }
    val body_vars = ctx.mkAnd(
      ctx.mkEq(ctx.mkAdd(vars(0), ctx.mkInt(1)), ctx.mkInt(2)),
      ctx.mkEq(ctx.mkAdd(vars(1), ctx.mkInt(2)), ctx.mkAdd(vars(2), ctx.mkInt(3)))
    )
    val body_const = ctx.mkAnd(
      ctx.mkEq(ctx.mkAdd(xs(0), ctx.mkInt(1)), ctx.mkInt(2)),
      ctx.mkEq(ctx.mkAdd(xs(1), ctx.mkInt(2)), ctx.mkAdd(xs(2), ctx.mkInt(3)))
    )
    val x = ctx.mkForall(
      types,
      names,
      body_vars,
      1,
      null,
      null,
      ctx.mkSymbol("Q1"),
      ctx.mkSymbol("skid1")
    )
    //    System.out.println("Quantifier X: " + x.toString)
    import ctx._
    val a    = mkIntConst("a")
    val b    = mkIntConst("b")

    val boolExpr = a === b ==> (a === b)

    val intExprs: Array[Expr[_]] = Array(a, b)
    val zz = ctx.mkForall(
      intExprs,
      boolExpr,
      1,
      null,
      null,
      null,
      null
    )

    z3CheckApi.checkBoolCtx(ctx, Seq(zz))

    val y = ctx.mkForall(
      xs.asInstanceOf[Array[Expr[_]]],
      body_const,
      1,
      null,
      null,
      ctx.mkSymbol("Q2"),
      ctx.mkSymbol("skid2")
    )
//    z3CheckApi.checkBoolCtx(ctx, Seq(y))
//    System.out.println("Quantifier Y: " + y.toString)
  }

}
