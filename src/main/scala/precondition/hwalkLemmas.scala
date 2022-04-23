package precondition
import com.microsoft.z3
import com.microsoft.z3._
import precondition.InfRealTuple
import precondition.z3api.z3CheckApi

import com.doofin.stdScala._
import InfRealTuple.TupNum
import z3api._
import lemmas._

// lemmas for hwalk at p14
object hwalkLemmas {
  import precondition.z3api.z3Utils._
  import precondition.InfRealTuple.thisCtx._

  val vec_nth_bool = vecSelect("vec_nth_b", mkBoolSort())

  def vec_nth_update() = {
    // update: vec,ith,item => vec

    val n = mkIntConst("N2") // index of array
    val e = newVecBool("vec_e")
    val b = mkBoolConst("b")

    val upd_f = mkFuncDecl(
      "upd_f",
      Array(vecSort, mkIntSort(), mkBoolSort()): Array[Sort],
      vecSort
    )

    val qtf = vec_nth_bool(upd_f(e, n, b), n) === b
    val qa = forall_z3(Array(e, n, b).asInstanceOf[Array[Expr[Sort]]], qtf)
    (upd_f, qa)
  }
  // sum for dH at p17 as uninterpreted type
  def sum_func_dh_uni(pos1: Expr[VecType], pos2: Expr[VecType]) = {
    val sum_f = mkFuncDecl(
      "sum",
      Array(mkIntSort(), mkIntSort()): Array[Sort],
      mkRealSort()
    )
    val i: Expr[IntSort] = mkIntConst("i")
    val j: Expr[IntSort] = mkIntConst("j")

    import ImplicitConv.int2mkint
    val numProp = i >= 0 && (j >= 0)
//    use implicits for mkInt
    import ImplicitConv.int2mkint

    // widening: make the result weaker: a i >=0,sum i j >0 -> sum i+1 j >0
    // need a way to update upper bound
    val prop =
      (i <= j) ==> ((sum_f(i, j) >= 0) && (sum_f(i, j) === sum_f(i + 1, j) + iverB(
        vec_nth_bool(pos1, i) !== vec_nth_bool(pos2, i)
      )))

    val prop2 = i > j ==> (sum_f(i, j) === 0)

    val qtfDec = forall_z3(Array(i, j), prop && prop2)
    (sum_f, numProp && qtfDec)
  }

  // req: len dH = N
  // pos:list of bool encode as vec or array/native bitvector

  def hwalkInvariantUni(N: IntExpr, k1: IntExpr, k2: IntExpr, K1: IntExpr, K2: IntExpr) = {

    val pos1 = newVecBool("vec_pos1")
    val pos2 = newVecBool("vec_pos2")
    val (dHF, dHprop) = sum_func_dh_uni(pos1, pos1)

    import ImplicitConv._
    val dH: TupNum = dHF(1, N)
    val exp =
      mkPower(
        mkDiv(
          mkInt2Real(
            N - 1
          ),
          mkInt2Real(
            N + 1
          )
        ),
        mkInt(1) //mkITE((K1 - k1) >= 0, K1 - k1, mkInt(0))
      ).asInstanceOf[RealExpr]

    // original
    val invariant: TupNum =
      iverB(k1 !== k2) * InfRealTuple.posInf + (iverB(k1 === k2) * dH * exp)

    (pos1, pos2, dH, invariant, dHprop, exp)
  }

  // ⊕ for xor
  def xor_uni(a: Expr[VecType], b: Expr[VecType]) = {
    val i = mkIntConst("idx_xor")
    val xorRes = newVecBool("vec_xor")

    // e(i) = true if n = i else e(i) = false

    // won't work with all index?
    // mkStore(e, i, mkXor(mkSelect(a, i), mkSelect(b, i)))

    val qtf: Quantifier =
      forall_z3(
        Array(i).asInstanceOf[Array[Expr[Sort]]],
        vec_nth_bool(xorRes, i) === (mkXor(vec_nth_bool(a, i), vec_nth_bool(a, i)))
      )
    (xorRes, qtf)
  }

  /**
    * UninterpretedSort
    * @param i : ith is one 
    * @return`  
    */
  def ei_uni(i: IntExpr) = {
    val n = mkIntConst("N2") // index of array
    val e = newVecBool("vec_e")

    val (upd_f, upd_f_qtf) = vec_nth_update()

    //also vec_nth_bool(upd_f(e, n, n === i), n) === (n === i) is unknown
    val qtf2: Quantifier =
      forall_z3(
        Array(n).asInstanceOf[Array[Expr[IntSort]]],
        e === upd_f(e, n, n === i) //
      )

    // forall n, if n = i then e(i) = true else e(i) = false
    /*     val qtf: Quantifier =
      forall_z3(
        Array(n).asInstanceOf[Array[Expr[IntSort]]],
        (
          ((n === i) ==> vec_nth_bool(e, n) === mkTrue()) && ((n !== i) ==> vec_nth_bool(
            e,
            n
          ) === mkFalse())
        )
      )

    val m1 = mkIntConst("m1") // index of array
    val m2 = mkIntConst("m2") // index of array
    val q2 = vec_nth_bool(e, m1) !== vec_nth_bool(e, m2)
     */
    // len(e) ==
    // (e, q2 ==> qtf)
    (e, qtf2 && upd_f_qtf)
  }
}
