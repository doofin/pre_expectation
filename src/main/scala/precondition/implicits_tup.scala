package precondition

import InfRealTuple._
import com.microsoft.z3._

object implicits_tup {
  implicit def finite2tup(num: Expr[RealSort]): InfRealTuple.TupNum =
    TupNum(inj_InfReal(num, thisCtx.mkBool(false)))

  implicit def tup2inj(v_tup: (Expr[RealSort], Boolean)): Expr[TupleSort] =
    inj_InfReal(v_tup._1, thisCtx.mkBool(v_tup._2))

}
