package precondition

import com.microsoft.z3._
import com.doofin.stdScala._

import com.microsoft.z3.enumerations.Z3_ast_print_mode

import scala.language.existentials

object InfRealTuple {
  import precondition.z3api.z3Utils._
  lazy val thisCtx = newZ3ctx()
  // intsort,bool
  import ImplicitConv.tup2inj

  val infty_+ = TupNum(thisCtx.mkReal(1) -- true)

  lazy val proj @ (tupTp_InfReal, inj_InfReal, prjArr_InfReal) = {
    import thisCtx._
    val r =
      mkTupleSort(
        mkSymbol("mk_tuple1"),
        Array(mkSymbol("fst"), mkSymbol("snd")),
        Array(mkRealSort(), mkBoolSort())
      )
    (r, r.mkDecl(), r.getFieldDecls)
  }

  lazy val projReal :: projBool :: Nil = prjArr_InfReal.toList

  case class TupNum(thisTup: Expr[TupleSort]) {
    import thisCtx._
//    import z3Utils._
//    import ctx._
    val (real1: RealExpr, bool1: Expr[BoolSort]) =
      (projReal(thisTup), projBool(thisTup))
    val isInf: BoolExpr = bool1.isTrueB
//    private val tup_inf = inj(mkReal(1, 1), mkTrue())

    def mkBinaryOp(
        op: (RealExpr, RealExpr) => Expr[RealSort],
        dominateCond: RealExpr => BoolExpr = { x => mkFalse() }
    )(
        oth: TupNum
    ) = {
      val (real2: RealExpr, bool2: BoolExpr) =
        (projReal(oth.thisTup), projBool(oth.thisTup))
      val notInf = inj_InfReal(op.apply(real1, real2), mkFalse())
      val rInf = mkITE(isInf, thisTup, mkITE(oth.isInf, oth.thisTup, notInf))
      //  make inf * 0 = 0
      import ImplicitConv._

      val r =
        mkITE(
          dominateCond(real1),
          TupNum(real1).thisTup,
          mkITE(dominateCond(real2), TupNum(real2).thisTup, rInf)
        )
      // TupNum(rInf) // the old one ,sidecond ok
      TupNum(r) // this breaks sidecond!
    }

    def + = mkBinaryOp(_ + _) _

    def - = mkBinaryOp(_ - _) _

    def * = mkBinaryOp(_ * _, (x => x === mkReal(0))) _ // this makes sideCond unk

    // def * = mkBinaryOp(_ * _) _

    def / = mkBinaryOp(_ / _) _
    def ===(oth: TupNum) = { thisTup === oth.thisTup }

    /** if oth are pos inf,then true if both are not inf,compare real part
      */
    def <=(oth: TupNum) = {
      val (real2: RealExpr, bool2: BoolExpr) =
        (projReal(oth.thisTup), projBool(oth.thisTup))

      val isNotInf = bool1.isFalseB || bool2.isFalseB
      val real1_lt_real2 = real1 <= real2

      val oth_isPosInf = oth.isInf && real2.isPos
      oth_isPosInf || (isNotInf && real1_lt_real2)
    }

    def normW() = {
      TupNum(mkITE(isInf, thisTup, TupNum(real1.normW() -- false).thisTup))
    }

  }

}
