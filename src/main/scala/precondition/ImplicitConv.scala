package precondition

import InfRealTuple._
import com.microsoft.z3._

import scala.language.implicitConversions

object ImplicitConv {
  implicit def real2tup(num: Expr[RealSort]): InfRealTuple.TupNum =
    TupNum(inj_real2tup(num, thisCtx.mkBool(false)))

  implicit def tup2tupNum(num: Expr[TupleSort]): InfRealTuple.TupNum =
    TupNum(num)

  implicit def tup2inj(v_tup: (Expr[RealSort], Boolean)): Expr[TupleSort] =
    inj_real2tup(v_tup._1, thisCtx.mkBool(v_tup._2))

  implicit def tup2inj2(v_tup: (Expr[RealSort], BoolExpr)): Expr[TupleSort] =
    inj_real2tup(v_tup._1, v_tup._2)
  implicit def real2inj(v_tup: Expr[RealSort]): Expr[TupleSort] =
    inj_real2tup(v_tup, thisCtx.mkBool(false))
  implicit def int2mkint(i: Int): IntNum = thisCtx.mkInt(i)
}
