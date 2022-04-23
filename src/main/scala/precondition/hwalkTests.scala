package precondition
import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}

import InfRealTuple.TupNum
import rpeFunctionTup._
import issuesAndTests._

import lemmas._
import hwalkLemmas._

object hwalkTests {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._
  import InfRealTuple._
  import ImplicitConv._

  val N: IntExpr = mkIntConst("N")

  val t0 = mkInt(0)
  val (w1, w2) = (newVecReal("w1"), newVecReal("w2"))
  val (g1, g2) = (newVecReal("g1"), newVecReal("g2"))
  val k1 :: k2 :: Nil = (1 to 2).map(x => mkIntConst(s"t$x")).toList
  val K1 = mkIntConst("K1")
  val K2 = mkIntConst("K2")

  val i1 :: i2 :: Nil = mkSymList(2, "i", mkIntConst)

  val (f_bij, f_bij_prop) = lemmas.f_bijection_int()
  // val rpeF_inst = rpeF(f_bij) _

  // val (pos1, pos2, dh, invar, invarProps, exp) = hwalkInvariantUni(N, k1, k2, K1, K2)

  val pos1 = newVecBool("vec_pos1")
  val pos2 = newVecBool("vec_pos2")
  val (dHF, dHprop) = sum_func_dh_uni(pos1, pos1)

  val dH: TupNum = dHF(1, N)

  // e(i)
  val (ei1, ei1p) = ei_uni(i1)
  val (ei2, ei2p) = ei_uni(i2)

  // xor ⊕
  val (xor_r1, xor1P) = xor_uni(pos1, ei1)
  val (xor_r2, xor2P) = xor_uni(pos2, ei2)

  // test nums
  val posReal = mkRealConst("exppos")
  val posInt = mkIntConst("expposint")
  val test_premises = Seq(posReal >= 0, posInt >= 0)

  val premises: Seq[BoolExpr] =
    Seq(N >= 0, dHprop, f_bij_prop, ei1p, ei2p, xor1P, xor2P) ++ test_premises

  def runtest() = {
    //  exp>0 ok
    val exp1Gt0 =
      mkPower(
        mkReal(1),
        mkITE((K1 - k1) >= 0, K1 - k1, mkInt(0)) // ok for mkInt(1)
      ).asInstanceOf[RealExpr]

    //   N ⊖ n denotes max(N −n, 0)

    val exp1 =
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

    val invs = Seq(
      ("0<=iverB(k1 !== k2) *inf", mkReal(0) <= (iverB(k1 !== k2) * InfRealTuple.posInf)), // ok
      ("0<=iverB(k1 === k2) * dH", mkReal(0) <= iverB(k1 === k2) * dH), // ok
      ("0<= dH", mkReal(0) <= dH), // ok
      (
        "0<=iverB(k1 !== k2) * inf + (iverB(k1 === k2) * dH)",
        mkReal(0) <= iverB(k1 !== k2) * InfRealTuple.posInf + (iverB(k1 === k2) * dH) // ok
      ),
      (
        "0<=iverB(k1 !== k2) * InfRealTuple.posInf + (iverB(k1 === k2) * dH * exppos",
        mkReal(0) <= iverB(k1 !== k2) * InfRealTuple.posInf + (iverB(k1 === k2) * dH * posReal)
      ), //ok
      ("0<=1^max(K1 - k1, 0)", exp1Gt0 >= 0), // ok
      (
        "0<=2^max(K1 - k1, 0)",
        mkPower(
          mkReal(2),
          mkITE((K1 - k1) >= 0, K1 - k1, mkInt(0))
        ) >= 0
      ),
      (
        "mkITE((K1 - k1) >= 0, K1 - k1, mkInt(0)) >= 0",
        mkInt2Real(mkITE((K1 - k1) >= 0, K1 - k1, mkInt(0))) >= 0
      ),
      (
        "0<=2r^posReal",
        mkPower(
          mkReal(2),
          posReal
        ) >= 0
      ),
      (
        "0<=2r^posInt",
        mkPower(
          mkReal(2),
          posInt
        ) >= 0
      ),
      (
        "0<=2i^posInt",
        mkPower(
          mkInt(2),
          posInt
        ) >= 0
      )
    ) //ok

    // val r = expGt0()
    invs.drop(6) foreach { case (desc, fml) =>
      z3CheckApi.checkBoolExpr(
        thisCtx,
        premises = premises,
        formulas = Seq(fml.neg), // x.neg is unsat => forall .x
        goals = List(Status.UNSATISFIABLE),
        desc = desc
      )
    }

  }
}
