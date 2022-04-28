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

object sgdTests {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._
  import InfRealTuple._
  import ImplicitConv._

  // example test set
  val s_distrib: Set[Expr[IntSort]] =
    (2 to 6).map(x => mkIntConst(s"s$x")).toSet

//    vars for loop invariant in p.13
//   previous simplification : dim w = 1,use R instead of R^n
  val w0 = newVecReal("w0")
  // val t0 = mkIntConst("t0")
  val t0 = mkInt(0)
  // val t0prop = t0 === mkInt(0)
  val (w1, w2) = (newVecReal("w1"), newVecReal("w2"))

  val (g1, g2) = (newVecReal("g1"), newVecReal("g2"))
  val t1 :: t2 :: Nil = (1 to 2).map(x => mkIntConst(s"t$x")).toList
  val s1 :: s2 :: Nil = mkSymList(2, "s", mkIntConst)

  val T: IntExpr = mkIntConst("T")

  val e1 :: e2 :: Nil = List(t1 > 0, t2 > 0)

  // a_t for sgd at p13
  val a_t = mkRealConst("a_t")
  val atPrpo = a_t > mkReal(0)

  val varProps = atPrpo //&& t0prop
  // delta L function with Lipschitz property
  val (deltaL, lipschez_premise) = vec_deltaL(1)

  val (f_bij, f_bij_prop) = lemmas.f_bijection_int()
  val rpeF_inst = rpeF(f_bij) _

  // sum of a_j :  sumAjF=sum i j a_j
  val (sumAjF, sumProps) =
    sumAjGen()

  // original invariant_annonotation in while stmt and also rhs of p13(1)
  // val invariant_annon =
  //   invariantRhsTup(List(t1, t2), List(w1, w2), T, sumAjF)

  // testing invariant_annonotation in while stmt and also rhs of p13(1)
  val invariant_annon =
    invariantRhsTup_i1(List(t1, t2), List(w1, w2), T, sumAjF)

  val sum0toT = sumAjF(t1, T)

  //    terms I in p.13 the original
  val I: TupNum = iverB(t0 !== t1) * posInf + (iverB(t0 === t1) *
    ((w0 - w1).norm() + sum0toT))

  //
  /* val I_lhs: TupNum =
    TupNum(iverB(e1 && e2)) * rpeApplied +
      (TupNum(iverB(e1.neg && e2.neg)) * E) + (iverB(e1 !== e2) * posInf) */
// 3rd term of lhs of I
  val I_lhs2: TupNum =
    (iverB(e1.neg && e2.neg)) * (w0 - w1).norm()

  // 3rd term of lhs of I
  val I_lhs3: TupNum =
    (iverB(e1 !== e2) * posInf)

  val premises: Seq[BoolExpr] =
    Seq(lipschez_premise, lemmas.vecPremise, varProps, T >= 1) ++ sumProps

  def test = {
    val invs = Seq(
      (
        "0 <= iverB(t0 !== t1) * posInf + (iverB(t0 === t1)*((w0 - w1).norm() + sum0toT))",
        mkReal(0) <= I
      ), // ok sometimes
      ("(w1 - w1).norm === mkReal(0)", (w1 - w1).norm === mkReal(0)), // ok aw
      ("(iverB(e1 !== e2) * posInf) <= I", I_lhs3 <= I), //unk
      ("(iverB(e1.neg && e2.neg)) * (w0 - w1).norm() <= I", I_lhs2 <= I) //unk
    )

    1 to 1 foreach { epch => // to test cache and non determinism
      invs.take(1) foreach { case (desc, fml) =>
        z3CheckApi.checkBoolExpr(
          thisCtx,
          premises = premises,
          formulas = Seq(fml.neg), // x.neg is unsat => forall .x
          goals = List(Status.UNSATISFIABLE),
          desc = desc,
          printSmtlib = false
        )
      }
    }

    // try parsing
    z3CheckApi.parseSmtlib2Str(
      """(declare-sort vec 0)
                                |(declare-fun k!36 () Bool)
                                |(declare-fun inftypos () Real)
                                |(declare-fun anyNum () Real)
                                |(declare-fun k!37 () Bool)
                                |(declare-fun a_t () Real)
                                |(declare-fun k!38 () Bool)
                                |(declare-fun T () Int)
                                |(declare-fun k!39 () Bool)
                                |(declare-fun n () Int)
                                |(declare-fun k!40 () Bool)
                                |(declare-fun L () Real)
                                |(declare-fun k!41 () Bool)
                                |(declare-fun j () Int)
                                |(declare-fun k!42 () Bool)
                                |(declare-fun k!43 () Bool)
                                |(declare-fun k!44 () Bool)
                                |(declare-fun k!45 () Bool)
                                |(declare-fun k!46 () Bool)
                                |(declare-fun norm_vec (vec) Real)
                                |(declare-fun vec_binOp_- (vec vec) vec)
                                |(declare-fun delta_lossF (Int vec) vec)
                                |(declare-fun vec_nth_real (Int vec) Real)
                                |(declare-fun vec_binOp_vecadd (vec vec) vec)
                                |(declare-fun i () Int)
                                |(declare-fun zero () vec)
                                |(declare-fun w () vec)
                                |(declare-fun a () Real)
                                |(declare-fun scalaMul (Real vec) vec)
                                |(declare-fun beta () Real)
                                |(declare-fun aj (Int) Real)
                                |(declare-fun sum (Int Int) Real)
                                |(assert (forall ((z1 Int) (w11 vec) (w12 vec))
                                |  (<= (norm_vec (vec_binOp_- (delta_lossF z1 w11) (delta_lossF z1 w12)))
                                |      (norm_vec (vec_binOp_- w11 w12)))))
                                |(assert (forall ((a vec) (b vec))
                                |  (= (+ (vec_nth_real i a) (vec_nth_real i b))
                                |     (vec_nth_real i (vec_binOp_vecadd a b)))))
                                |(assert (forall ((a vec) (b vec))
                                |  (let ((a!1 (= (+ (vec_nth_real i a) (* (- 1.0) (vec_nth_real i b)))
                                |                (vec_nth_real i (vec_binOp_- a b)))))
                                |    (and a!1 (= (= a b) (= (vec_binOp_- a b) zero))))))
                                |(assert (forall ((v vec)) (>= (norm_vec v) 0.0)))
                                |(assert (forall ((v1 vec))
                                |  (<= (norm_vec (vec_binOp_vecadd v1 w)) (+ (norm_vec v1) (norm_vec w)))))
                                |(assert (forall ((v vec))
                                |  (= (norm_vec (scalaMul a v))
                                |     (* (norm_vec v) (ite (<= a 0.0) (* (- 1.0) a) a)))))
                                |(assert (forall ((v7 vec)) (= (= (norm_vec v7) 0.0) (= v7 zero))))
                                |(assert (= (norm_vec zero) 0.0))
                                |(assert (forall ((i Int) (a Real) (v vec))
                                |  (= (vec_nth_real i (scalaMul a v)) (* (vec_nth_real i v) a))))
                                |(assert k!46)
                                |(assert k!43)
                                |(assert k!38)
                                |(assert (not (<= beta 0.0)))
                                |(assert k!44)
                                |(assert k!40)
                                |(assert (forall ((t Int)) (and (<= 0.0 (aj t)) (<= (aj t) (/ 2.0 beta)))))
                                |(assert (>= i 0))
                                |(assert k!41)
                                |(assert (forall ((i Int) (j Int))
                                |  (let ((a!1 (= (sum i j) (+ (sum (+ 1 i) j) (aj i)))))
                                |  (let ((a!2 (or (not (<= i j)) (and (>= (sum i j) 0.0) a!1))))
                                |    (and a!2 (or (<= i j) (= (sum i j) 0.0)))))))
                                |(model-del k!36)
                                |(model-add inftypos () Real (ite k!36 anyNum (+ anyNum (- 1.0))))
                                |(model-del k!37)
                                |(model-add a_t () Real (ite k!37 0.0 (+ 0.0 1.0)))
                                |(model-del k!38)
                                |(model-add T () Int (ite k!38 1 (+ 1 (- 1))))
                                |(model-del k!39)
                                |(model-add n () Int (ite k!39 0 (+ 0 1)))
                                |(model-del k!40)
                                |(model-add L () Real (ite k!40 0.0 (+ 0.0 (- 1.0))))
                                |(model-del k!41)
                                |(model-add j () Int (ite k!41 0 (+ 0 (- 1))))
                                |(model-del k!42)
                                |(model-add anyNum () Real (ite k!42 0.0 (+ 0.0 (- 1.0))))
                                |(model-del k!43)
                                |(model-add k!37 () Bool (not k!43))
                                |(model-del k!44)
                                |(model-add k!39 () Bool (not k!44))
                                |(model-del k!45)
                                |(model-add k!42 () Bool (not k!45))
                                |(model-del k!46)
                                |(model-add k!45 () Bool k!46)
                                |(model-add k!36 () Bool false)
                                |""".stripMargin,
      ctx
    )
  }

}
