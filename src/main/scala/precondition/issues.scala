package precondition

import sgdExample._
import lemmas._
import z3api.z3Utils._
import InfRealTuple._
import com.microsoft.z3.Status
// minimal example to reproduce bugs
object issues {
  import InfRealTuple.thisCtx._
  def sumIsUnknown() = {
    val T = mkIntConst("T")
    val T_prem = T >= mkInt(1)

    val (a_j, aj_prop) = aj_func(B = mkRealConst("beta"))

    // use widening technique : (a i >=0,sum i j >0 ==> sum i+1 j >0)
    val (sumFuncInst, sumFunc_prop) = sum_func_ord2(a_j)
    // use decreasing : (sum i j = (sum i j-1) + x(j))
    // val (sumFuncInst, sumFunc_prop) = sum_func_dec(a_j)

    val res = sumFuncInst(mkInt(0), T)
    val qtf = (aj_prop && sumFunc_prop) ==> (mkReal(0) <= res)
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      Seq(qtf.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  // ok, unsat
  def zeroMulInf() = {
    import ImplicitConv._
    val qtf = TupNum(mkReal(0)) * InfRealTuple.infty_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      Seq(qtf.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  // ok, unsat
  def zeroMulInf2() = {
    import ImplicitConv._

    val t0 = mkInt(0)

    // if cond true then 1 else 0. cond is false,so iverB is 0
    val q2 = TupNum(iverB(t0 !== t0)) * infty_+ === TupNum(mkReal(0))

    // val qtf = TupNum(mkReal(0)) * InfRealTuple.infty_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      Seq(q2.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }
}
