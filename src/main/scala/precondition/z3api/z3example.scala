package precondition.z3api

import com.microsoft.z3
import com.microsoft.z3.{Context, Expr, IntExpr, IntSort, Sort}
import precondition.InfRealTuple
import precondition.z3api.z3CheckApi

object z3example {

  import precondition.z3api.z3Utils._

  def parserExample1(): Unit = {
    z3CheckApi.checkSmtlibStr(
      Seq(
        "(declare-const x Int) (declare-const y Int) (assert (and (> x y) (> x 0)))",
        "(assert (> 0.0001 0.0))"
        //        "(assert (and (= (snd (mk_tuple1 1.0 true)) true) (> (fst (mk_tuple1 1.0 true)) 0.0)))"
      )
    )
  }

  def quantifierExample1(ctx: Context): Unit = {
    System.out.println("QuantifierExample")
    //    Log.append("QuantifierExample")
    val types = new Array[Sort](3)
    val xs = new Array[IntExpr](3)
    val names = new Array[z3.Symbol](3)
    val vars = new Array[IntExpr](3)
    for (j <- 0 until 3) {
      types(j) = ctx.getIntSort
      names(j) = ctx.mkSymbol("x_" + Integer.toString(j))
      xs(j) = ctx.mkConst(names(j), types(j)).asInstanceOf[IntExpr]

      // <-- vars reversed!
      vars(j) = ctx.mkBound(2 - j, types(j)).asInstanceOf[IntExpr]

    }
    val body_vars = ctx.mkAnd(
      ctx.mkEq(ctx.mkAdd(vars(0), ctx.mkInt(1)), ctx.mkInt(2)),
      ctx.mkEq(
        ctx.mkAdd(vars(1), ctx.mkInt(2)),
        ctx.mkAdd(vars(2), ctx.mkInt(3))
      )
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
    val a = mkIntConst("a")
    val b = mkIntConst("b")

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

    z3CheckApi.checkBoolExpr(ctx, Seq(zz))

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

  import precondition.InfRealTuple.thisCtx._

  //recursion doesn't work
  def rectest(j: Expr[IntSort], i: IntExpr): Expr[IntSort] = {
    // import z3Utils._
    mkITE(j === i, i, rectest(mkAdd(j, mkInt(1)), i))
  }

  // test ok for  sum_{i=0}^n i == n * (n-1)/2
  //  sum i j x(i) = (sum i+1 j x(i+1)) + x(i)
  def sumAsForall() = {
    val ctx = InfRealTuple.thisCtx
    val params: Array[Sort] = Array(mkIntSort(), mkIntSort(), mkIntSort())

    val sum_f = mkFuncDecl("sum", params, mkIntSort())
    val i: Expr[IntSort] = mkIntConst("i")
    val n: Expr[IntSort] = mkIntConst("n")
    val prop = sum_f(mkInt(0), n, i) === mkDiv(
      mkMul(n, (mkSub(n, mkInt(1)))),
      mkInt(
        2
      )
    )
    val qtf = forall_z3(Array(i, n), prop)
    //    (sum_f, qtf)
    z3CheckApi.checkBoolExpr(ctx, Seq(qtf))
  }

  def array_aj(B: z3.RealExpr) = {

    val ajc = mkConst("aj", mkArraySort(mkIntSort(), mkRealSort()))
//    use mkStore() to store values in array.need index from i to n ?
//    the array a_j
    val aj = (x: Expr[IntSort]) => mkSelect(ajc, x)
    val t: Expr[IntSort] = mkIntConst("t")
    val aj_prop = (t < aj(t)) && (aj(t) < (mkReal(2) / B))
    // properties for array a_j :  0<=a_t<=2/B,p12
    val qtf = forall_z3(Array(t), aj_prop)
    (qtf, aj)
  }

  def `2L/n`(L: Int, n: Int, j: IntExpr, a_j: Seq[Float]) = {
//    import InfRealTuple.ctx._
    val Aj_type = mkArraySort(mkIntSort(), mkRealSort())
    val aj = mkConst("aj", Aj_type)
    val r = mkSelect(aj, mkInt(1))
    // can't get indexes t1:IntSort to T:Int or IntSort
    ((2 * L / n) * a_j.reduce(_ + _)).toInt
  }
}
