package precondition

import sgdExampleTup._
import lemmas._
import z3api.z3Utils._
import InfRealTuple._
import com.microsoft.z3._
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
  // 0 * inf=0
  def zeroMulInf() = {
    import ImplicitConv._
    val qtf = TupNum(mkReal(0)) * InfRealTuple.inftyTup_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      Seq(qtf.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  // ok, unsat
  // iverB() * inf=0 when iverB = 0
  def zeroMulInf2() = {
    import ImplicitConv._

    val t0 = mkInt(0)

    // if cond true then 1 else 0. cond is false,so iverB is 0
    val q2 = TupNum(iverB(t0 !== t0)) * inftyTup_+ === TupNum(mkReal(0))
    val q3 = inftyTup_+ * TupNum(iverB(t0 !== t0)) === TupNum(mkReal(0))

    // val qtf = TupNum(mkReal(0)) * InfRealTuple.infty_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      Seq(q2.neg, q3.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  def iverB1() = {
    import ImplicitConv._

    val t0 = mkIntConst("t0")
    val t1 = mkIntConst("t1")
    val t2 = mkRealConst("t2")

    // if cond true then 1 else 0. cond is false,so iverB is 0
    val q2 = TupNum(iverB(t0 + 1 !== t1 + 1)) * t2 <= TupNum(iverB(t0 !== t1)) * inftyTup_+

    // val qtf = TupNum(mkReal(0)) * InfRealTuple.infty_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      Seq(q2.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  def iverB2() = {
    import ImplicitConv._

    val t0 = mkIntConst("t0")
    val t1 = mkIntConst("t1")
    val t2 = mkRealConst("t2")
    val T = mkIntConst("T")
    val e1 = t0 < T
    val e2 = t1 < T
    // if cond true then 1 else 0. cond is false,so iverB is 0
    val q2 = TupNum(iverB(e1 && e2)) * (TupNum(iverB(t0 + 1 !== t1 + 1)) * inftyTup_+) + TupNum(
      iverB(e1 !== e2)
    ) * inftyTup_+ <= TupNum(
      iverB(t0 !== t1)
    ) * inftyTup_+

    // val qtf = TupNum(mkReal(0)) * InfRealTuple.infty_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      Seq(q2.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  // simplified case for p13.1 rhs
  def invariantRhsTup_i1(
      t: List[IntExpr],
      w: List[Expr[VecType]],
      T: IntExpr,
      sumAjF: (Expr[IntSort], Expr[IntSort]) => RealExpr
  ): TupNum = {
    import ImplicitConv._
    import InfRealTuple._

    // sum for a_j from t to T . ctx.mkInt2Real()
    val sum0toT = sumAjF(t(0), T)

//    terms I in p.13
// TupNum(iverB(t(0) !== t(1))) * inftyTup_+ +

// unsat,ok
    val tup: TupNum = TupNum(iverB(t(0) !== t(1))) * inftyTup_+ + (TupNum(
      iverB(t(0) === t(1))
    ) *
      ((w(0) - w(1)).norm() + sum0toT))

    // unsat,ok
    // val tup: TupNum = ((w(0) - w(1)).norm() + sum0toT)

    // TupNum(mkReal(100)) //unk
    tup // unsat,ok
  }

  // simplified case for p13.1 lhs
  def invariantTup_lhs_i1(e1: BoolExpr, e2: BoolExpr, rpe_bd_I: TupNum, E: TupNum) = {
    import ImplicitConv._
    import InfRealTuple._

    /* val I_lhs: TupNum =
      TupNum(iverB(e1 && e2)) * rpeApplied +
        (TupNum(iverB(e1.neg && e2.neg)) * E) + (iverB(e1 !== e2) * inftyTup_+) */

    // ukn,original
    val I_lhs1: TupNum =
      iverB(e1 && e2) * rpe_bd_I +
        (iverB(e1.neg && e2.neg) * E)

    // ukn,rm iverB(e1 && e2)
    val I_lhs4: TupNum =
      rpe_bd_I +
        (TupNum(iverB(e1.neg && e2.neg)) * E)

    // ukn,rm rpe_bd_I
    val I_lhs3: TupNum =
      iverB(e1 && e2) +
        (TupNum(iverB(e1.neg && e2.neg)) * E)

    // unsat,ok,rm TupNum(iverB(e1 && e2)) * rpe_bd_I
    val I_lhs2: TupNum =
      (TupNum(iverB(e1.neg && e2.neg)) * E)

    // I_lhs2
    I_lhs1
  }

  def testAll = {
    sumIsUnknown()
    zeroMulInf()
    zeroMulInf2()
  }
}
