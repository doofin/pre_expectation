package precondition

import com.microsoft.z3._
import com.doofin.stdScala._

import scala.language.existentials

object InfRealTuple {
  import precondition.z3api.z3Utils._
  import ImplicitConv.tup2inj

  lazy val thisCtx = newZ3ctx()

  val inftyTup_+ = TupNum(thisCtx.mkReal(1) -- true)

  val zeroTup = TupNum(thisCtx.mkReal(0) -- false)

  lazy val proj @ (_, inj_real2tup, prj_realBool) = { //tupTp_InfReal
    import thisCtx._
    val r =
      mkTupleSort(
        mkSymbol("mk_tuple1"),
        Array(mkSymbol("fst"), mkSymbol("snd")),
        Array(mkRealSort(), mkBoolSort())
      )
    (r, r.mkDecl(), r.getFieldDecls)
  }

  lazy val projReal :: projBool :: Nil = prj_realBool.toList

  def projTup(tup: Expr[TupleSort]): (RealExpr, BoolExpr) = {
    (projReal(tup), projBool(tup)).asInstanceOf[(RealExpr, BoolExpr)]
  }

  case class TupNum(thisTup: Expr[TupleSort]) {
    import thisCtx._
    val (real1, bool1) = projTup(thisTup)

    def mkBinaryOp(
        op: (RealExpr, RealExpr) => Expr[RealSort],
        zeroCond: RealExpr => BoolExpr = { x => mkFalse() }
    )(
        oth: TupNum
    ) = {
      import ImplicitConv._
      val (real2, bool2) = projTup(oth.thisTup)
      // if finite
      val finiteRes = inj_real2tup(op(real1, real2), mkFalse())
      val finiteRes1 = op(real1, real2)

      // only deal with non zero cases
      // +,- : (r1,b1) op (r2,b2) =(r1 op r2, b1 | b2) . don't work with inf_+ + inf_-
      // *,/ : (r1,b1) op (r2,b2) =(r1 op r2, b1 | b2) if r1,r2 !=0

      val rNonzero = TupNum(op(real1, real2), bool1 || bool2)

      // only deal with inf * 0 = 0
      // check if real num will dominate inf (0 * inf=0)
      // * : if r1 or r2 =0, then 0
      val r =
        mkITE(
          zeroCond(real1) || zeroCond(real2),
          zeroTup.thisTup, // 0
          rNonzero.thisTup
        )
      // TupNum(rInf) // the old one ,sidecond ok,but not correct
      TupNum(r) // this breaks sidecond!
    }

    def + = mkBinaryOp(_ + _) _

    def - = mkBinaryOp(_ - _) _

    def * = mkBinaryOp(_ * _, (x => x === mkReal(0))) _ // this makes sideCond unk

    // def * = mkBinaryOp(_ * _) _

    def / = mkBinaryOp(_ / _) _
    def ===(oth: TupNum) = { thisTup === oth.thisTup }

    /**
     (r1,b1) (r2,b2) , true if  (b2 and r2 >0) | (b1 and r1 <0) | (not b1) and ( not b2 ) and r1<r2
     if b2 are pos inf then true, if both are not inf,compare real part
      */
    def <=(oth: TupNum) = {
      val (real2: RealExpr, bool2: BoolExpr) =
        projTup(oth.thisTup)

      val bothNotInf = bool1.neg && bool2.neg

      // if num2 is neg inf,or num1 is pos inf,or if both are finite then compare real part
      (bool2 && real2.isPos) || (bool1 && real1.isNeg) || (bothNotInf && (real1 <= real2))
    }

    // not used
    def <(oth: TupNum) = {
      val (real2: RealExpr, bool2: BoolExpr) =
        projTup(oth.thisTup)

      val bothNotInf = bool1.neg && bool2.neg

      (bool1 && real1.isNeg) || (bool2 && real2.isPos) || (bothNotInf && (real1 < real2))
    }

  }

}

/*     def normW() = {
      TupNum(mkITE(bool1, thisTup, TupNum(real1.normW() -- false).thisTup))
    } */
//  inf*inf=(r1*r2,true) ,  inf+inf =undef if signs differ
// val rInf1 = mkITE(bool1, TupNum(finiteRes1), mkITE(bool2, TupNum(finiteRes1)))
// val rInf = mkITE(bool1, thisTup, mkITE(oth.bool1, oth.thisTup, finiteRes))
