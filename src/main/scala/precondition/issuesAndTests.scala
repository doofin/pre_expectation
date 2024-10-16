package precondition

import sgdExampleTup._
import lemmas._
import z3api.z3Utils._
import InfRealTuple._
import com.microsoft.z3._
// minimal example to reproduce bugs
object issuesAndTests {
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
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      premises = Seq(aj_prop, sumFunc_prop),
      formulas = Seq((mkReal(0) <= res).neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  // ok, unsat
  // 0 * inf=0
  def zeroMulInf() = {
    import ImplicitConv._
    val qtf = TupNum(mkReal(0)) * InfRealTuple.posInf === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      formulas = Seq(qtf.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  // ok, unsat
  // iverB() * inf=0 when iverB = 0
  def zeroMulInf2() = {
    import ImplicitConv._

    val t0 = mkInt(0)

    // if cond true then 1 else 0. cond is false,so iverB is 0
    val q2 = TupNum(iverB(t0 !== t0)) * posInf === TupNum(mkReal(0))
    val q3 = posInf * TupNum(iverB(t0 !== t0)) === TupNum(mkReal(0))

    // val qtf = TupNum(mkReal(0)) * InfRealTuple.infty_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      formulas = Seq(q2.neg, q3.neg),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  def iverB1() = {
    import ImplicitConv._

    val t0 = mkIntConst("t0")
    val t1 = mkIntConst("t1")
    val t2 = mkRealConst("t2")

    // if cond true then 1 else 0. cond is false,so iverB is 0
    val q2 = TupNum(iverB(t0 + 1 !== t1 + 1)) * t2 <= TupNum(iverB(t0 !== t1)) * posInf

    // val qtf = TupNum(mkReal(0)) * InfRealTuple.infty_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      formulas = Seq(q2.neg),
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
    val q2 = TupNum(iverB(e1 && e2)) * (TupNum(iverB(t0 + 1 !== t1 + 1)) * posInf) + TupNum(
      iverB(e1 !== e2)
    ) * posInf <= TupNum(
      iverB(t0 !== t1)
    ) * posInf

    // val qtf = TupNum(mkReal(0)) * InfRealTuple.infty_+ === TupNum(mkReal(0))
    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      formulas = Seq(q2.neg),
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

// the original
// unsat,ok for some lhs
    val tup: TupNum = iverB(t(0) !== t(1)) * posInf + (iverB(t(0) === t(1)) *
      ((w(0) - w(1)).norm() + sum0toT))

    // unsat,ok
    // val tup: TupNum = ((w(0) - w(1)).norm() + sum0toT)

    // TupNum(mkReal(100)) //unk
    tup
  }

  // simplified case for th.7 and p13.1 lhs
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

    // unsat,ok,rm TupNum(iverB(e1 && e2)) * rpe_bd_I
    val I_lhs2: TupNum =
      (iverB(e1.neg && e2.neg) * E)
    // ukn,rm rpe_bd_I
    val I_lhs3: TupNum =
      iverB(e1 && e2) +
        (TupNum(iverB(e1.neg && e2.neg)) * E)
    // ukn,rm iverB(e1 && e2)
    val I_lhs4: TupNum =
      rpe_bd_I +
        (iverB(e1.neg && e2.neg) * E)

    // unk
    val I_lhs5: TupNum = iverB(e1 && e2)

    val I_lhs6: TupNum =
      iverB(e1 && e2) * rpe_bd_I

    // [verifies] [e1 != e2] * inf <= I
    val I_lhs7: TupNum =
      iverB(e1 !== e2) * posInf

    // rpe_bd_I // ukn
    I_lhs5
  }

  // axiom with infinite array works
  def testarr() = {
    val n = mkIntConst("N2")
    val e = mkArrayVec("vec_e")

    // e(i) = true if n = i else e(i) = false
    val qtf: Quantifier =
      forall_z3(Array(n).asInstanceOf[Array[Expr[Sort]]], mkSelect(e, n) === mkTrue())
    val qr = mkSelect(e, mkInt(1)) === mkTrue()

    z3api.z3CheckApi.checkBoolExpr(
      InfRealTuple.thisCtx,
      premises = Seq(qtf),
      formulas = Seq(qr),
      goals = List(Status.UNSATISFIABLE)
    )
  }

  def testAll = {
    sumIsUnknown()
    zeroMulInf()
    zeroMulInf2()
  }
}
