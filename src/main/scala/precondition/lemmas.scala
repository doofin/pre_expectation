package precondition
import com.microsoft.z3
import com.microsoft.z3._
import precondition.InfRealTuple
import precondition.z3api.z3CheckApi

import com.doofin.stdScala._
import InfRealTuple.TupNum
import z3api._
// lemmas like bijective function,L lipschez,etc
object lemmas {
  import precondition.z3api.z3Utils._
  import precondition.InfRealTuple.thisCtx._

  type VecType = UninterpretedSort
  type binOpType[a] = (a, a) => a
  type PairType[a] = (a, a)
  val vecSort: VecType = mkUninterpretedSort("vec")
  val infty_+ = mkRealConst("inftypos")
  val anyNum = mkRealConst("anyNum")
  // val inftyP =
  //   forall_z3(
  //     Array(anyNum).asInstanceOf[Array[Expr[Sort]]],
  //     (anyNum >= mkReal(0)) ==> (infty_+ >= anyNum)
  //   )
  val inftyP = (anyNum >= mkReal(0)) ==> (infty_+ >= anyNum)
  // nth component of vector,but n is not specified. v->real
  // val vec_nth: FuncDecl[RealSort] =
  // mkFuncDecl("vec_nth", Array(vecSort): Array[Sort], mkRealSort())

  val vec_nth: FuncDecl[RealSort] =
    mkFuncDecl(
      "vec_nth",
      Array(mkIntSort(), vecSort): Array[Sort],
      mkRealSort()
    )

  val (vec_add, vec_addP) = vec_binOp(_ + _, "+")
  val (vec_scalaMul, vec_scalaMulP) = scala_mul_vec()

  // norm for vec
  val (vec_norm: FuncDecl[RealSort], zeroVec, vec_normP) = norm_vec_gen(vec_add, vec_scalaMul)
  // norm of 0 is 0
  // val zeroVec = newVec("zero")
  // val zeroVecP = vec_norm(zeroVec) === mkReal(0)

  /*
to make ( w1 - w1).norm() === 0 work :

   vec_axioms = And(
  vec_norm(vec_zero()) == 0,
  ForAll(v, (vec_norm(v) == 0) == (v == vec_zero()) ),
  ForAll([v,w], (v == w) == (vec_minus(v,w) == vec_zero()))
  )
   */
  val (vec_minus, vec_minusP) =
    vec_binOp(
      _ - _,
      "-",
      { case (a, b, minus) => (a === b) === (minus(a, b) === zeroVec) }
    )

  // val vec_minusP2 = 1
  implicit class vecOps(v: Expr[VecType]) {
    def +(v2: Expr[VecType]) = vec_add(v, v2)
    def -(v2: Expr[VecType]) = vec_minus(v, v2)
    def mulByScalar(a: Expr[RealSort]) = vec_scalaMul(a, v)
    def norm(): Expr[RealSort] = vec_norm(v)
  }

  val vecPremise = vec_addP && vec_minusP && vec_normP && vec_scalaMulP && inftyP

  def newVec(name: String = "x"): Expr[VecType] = mkConst(name, vecSort)

  /**
   * generate norm operator for vec. return: normF : vec -> real
   */
  def norm_vec_gen(binOp: FuncDecl[VecType], scalaMul: FuncDecl[VecType]) = {

    // val len: Int = 3
    val normF: FuncDecl[RealSort] =
      mkFuncDecl(
        "norm_vec",
        Array(vecSort): Array[Sort],
        mkRealSort()
      )
    /* axioms for norm:
     * 1:|v|>=0
     * 2:|v+w|<=|v|+|w|
     * 3:|av|=|a||v| */
    val p1 = {
      val v = newVec("v")
      val prop = normF(v) >= mkReal(0)
      forall_z3(Array(v), prop)
    }
    val p2 = {
      val v = newVec("v1")
      val w = newVec("w")
      val prop = normF(binOp(v, w)) <= normF(v) + normF(w)
      forall_z3(Array(v), prop)
    }

    val p3 = {
      val v = newVec("v")
      val a = mkRealConst("a")
      val prop = normF(scalaMul(a, v)) === (a.normW() * normF(v))
      forall_z3(Array(v), prop)
    }

    // val p4 = {
    //   val v = newVec("v1")
    //   val w = newVec("w")
    //   // val prop = (v === w) ==> (normF(binOp(v, w)) === mkInt(0))
    //   val prop = (v === w) ==> (binOp(v, w) === zeroVec)
    //   val prop2 = (binOp(v, w) === zeroVec) ==> (v === w)
    //   forall_z3(Array(v, w), prop && prop2)
    // }

    // val pFinDim = {
    //   val v = newVec("v")
    //   val f = mkFuncDecl("findim", Array(vecSort): Array[Sort], mkIntSort())
    //   val prop = f(v) === mkInt(len)
    //   forall_z3(Array(v), prop)
    // }
    val zeroVec = newVec("zero")
    val zeroVecP = normF(zeroVec) === mkReal(0)

    val p7 = {
      val v = newVec("v7")
      val prop = (normF(v) === mkReal(0)) === (v === zeroVec)
      forall_z3(Array(v), prop)
    }
    // && pFinDim && p4
    (normF, zeroVec, p1 && p2 && p3 && p7 && zeroVecP)
  }

  /* scala multiply vector */
  def scala_mul_vec() = {
    val scalaMul: FuncDecl[VecType] =
      mkFuncDecl(
        "scalaMul",
        Array(mkRealSort(), vecSort): Array[Sort],
        vecSort
      )

    val a = mkRealConst("a")
    val i = mkIntConst("i")
    val v = mkConst("v", vecSort)
    // (a*v)[i]=a*v[i]
    val prop =
      vec_nth(i, scalaMul(a, v)) === a * vec_nth(i, v)
    val qtf = forall_z3(Array(i, a, v).asInstanceOf[Array[Expr[Sort]]], prop)

    (scalaMul, qtf)
  }

  /**
   * lift operation on real to vector axiom : distributive. for example,minus: a[i]-b[i]=(a-b)[i]?
   */
  def vec_binOp(
      binOpReal: binOpType[Expr[RealSort]],
      name: String,
      binOpProp: (Expr[VecType], Expr[VecType], FuncDecl[VecType]) => BoolExpr = { case x =>
        mkTrue()
      }
  ) = {
    val a = mkConst("a", vecSort)
    val b = mkConst("b", vecSort)
    val i = mkIntConst("i")
    val binOp: FuncDecl[VecType] =
      mkFuncDecl("vec_binOp_" + name, Array(vecSort, vecSort): Array[Sort], vecSort)
    // a[i]-b[i]=(a-b)[i]
    val prop =
      binOpReal(vec_nth(i, a), vec_nth(i, b)) === vec_nth(i, binOp(a, b))
    val qtf = forall_z3(Array(a, b), prop && binOpProp(a, b, binOp))
    (binOp, qtf)
  }

  def f_bijection_int(): (z3.FuncDecl[IntSort], z3.Quantifier) = {
    val params: Array[Sort] = Array(mkIntSort())
    val f = mkFuncDecl("f_bij", params, mkIntSort())
    val f_inv = mkFuncDecl("f_bij_inv", params, mkIntSort())
    val z1: Expr[IntSort] = mkIntConst("z1")
    val prop = (f(f_inv(z1)) === z1) && (f_inv(f(z1)) === z1)

    val qtf = forall_z3(Array(z1), prop)
    (f, qtf)
  }

  def iverB(x: Expr[BoolSort]) = {
    mkITE(x, mkReal(1), mkReal(0))
  }

  // gen lhs of  p13.1 regarding loop rule.E is |w1-w2|
  def invariantTup_lhs(e1: BoolExpr, e2: BoolExpr, rpeApplied: TupNum, E: TupNum) = {
    import ImplicitConv._
    import InfRealTuple._

    val I_lhs: TupNum =
      TupNum(iverB(e1 && e2)) * rpeApplied +
        (TupNum(iverB(e1.neg && e2.neg)) * E) + (iverB(e1 !== e2) * inftyTup_+)

    /*     val I_lhs: TupNum =
      TupNum(iverB(e1.neg && e2.neg)) * E
     */
    I_lhs
  }

  /**
   * loop invariant I at p13 rhs,also as annotation of while 
   * @param t
   * @param w
   * @return
   */
  def invariantRhsTup(
      t: List[IntExpr],
      w: List[Expr[VecType]],
      T: IntExpr,
      sumAjF: (Expr[IntSort], Expr[IntSort]) => RealExpr
  ) = {
    import ImplicitConv._
    import InfRealTuple._

    // sum for a_j from t to T . ctx.mkInt2Real()
    val sum0toT = sumAjF(t(0), T)

//    terms I in p.13
// TupNum(iverB(t(0) !== t(1))) * inftyTup_+ +
    val tup: TupNum = TupNum(iverB(t(0) !== t(1))) * inftyTup_+ + (TupNum(
      iverB(t(0) === t(1))
    ) *
      ((w(0) - w(1)).norm() + sum0toT))

    tup
  }

  def invariant_lhs(e1: BoolExpr, e2: BoolExpr, rpeApplied: Expr[RealSort], E: Expr[RealSort]) = {

    val I_lhs: Expr[RealSort] =
      iverB(e1 && e2) * rpeApplied +
        (iverB(e1.neg && e2.neg) * E) +
        (iverB(e1 !== e2) * infty_+)

    I_lhs
  }

  //  sum function in p.13
  // deal with unknown SMT result for sum, problem:unwrapping might be infinite
  // 1:sum = sum i-1 ,2:sum : make it weaker 3.limited function
// sum_aj : int^2=>real,sum over a_j from i to j
// (smt result:,UNKNOWN)
// decreasing:  sum i j = (sum i j-1) + x(j) = x 0 ... x j-2 x j-1 x j
  def sum_func_dec(aj: FuncDecl[RealSort]) = {
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
    //  sum i j x(i) = (sum i+1 j x(i+1)) + x(i)

    // 1:sum = sum i-1 ,2:sum : make it weaker 3.limited function
    // increasing:  sum i j = (sum i+1 j) + x(i)
    // i <= j ==> (sum_f(i, j) === (sum_f(i, j - 1) + aj(j)))

    /* val prop1 = i <= j ==> ((sum_f(i, j) === (sum_f(i + 1, j) + aj(i)) && (sum_f(i + 1, j) >=
     * 0))) */
    // val prop2 = i > j ==> (sum_f(i, j) === 0)
    // val qtf = forall_z3(Array(i, j), prop1 && prop2)

    // (sum_f, numProp && qtf)

    // decreasing:  sum i j = (sum i j-1) + x(j) = x 0 ... x j-2 x j-1 x j
    val propDec1 =
      i <= j ==> (sum_f(i, j) === (sum_f(i, j - 1) + aj(j)))
    val propDec2 = i > j ==> (sum_f(i, j) === 0)

    val qtfDec = forall_z3(Array(i, j), propDec1 && propDec2)
    // (sum_f, numProp && qtf)
    (sum_f, numProp && qtfDec)

  }

  // only ordering property
  def sum_func_ord(aj: FuncDecl[RealSort]) = {
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
    val prop = (i <= j && aj(j) >= 0 && (sum_f(i, j - 1) >= 0)) ==> sum_f(i, j) >= sum_f(i, j - 1)

    val prop2 = i > j ==> (sum_f(i, j) === 0)

    val qtfDec = forall_z3(Array(i, j), prop && prop2)
    // (sum_f, numProp && qtf)
    (sum_f, numProp && qtfDec)

  }

  def sum_func_ord2(aj: FuncDecl[RealSort]) = {
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
    val prop = (i <= j) ==> ((sum_f(i, j) >= 0) && (sum_f(i, j) === sum_f(i + 1, j) + aj(i)))

    val prop2 = i > j ==> (sum_f(i, j) === 0)

    val qtfDec = forall_z3(Array(i, j), prop && prop2)
    // (sum_f, numProp && qtf)
    (sum_f, numProp && qtfDec)

  }

  // generate sumation func from i to j for a_j
  def sumAjGen() = {
    import z3Utils._
    import ImplicitConv.int2mkint
//    sum terms in I in p.13
    val (beta, n, l_L) =
      (mkRealConst("beta"), mkIntConst("n"), mkRealConst("L"))

    val numProp = (beta > 0) && (n > 0) && (l_L >= 0)
    val (a_j, aj_prop) = aj_func(B = beta)

    val (sumFuncInst, sumFunc_prop) = sum_func_ord2(a_j)

    val sumAjF = { (startIdx: Expr[IntSort], endIdx: Expr[IntSort]) =>
      (mkReal(2) * l_L / mkInt2Real(n) * sumFuncInst(
        startIdx,
        endIdx
      )).asInstanceOf[RealExpr]
    }
    (sumAjF, Seq(numProp, aj_prop, sumFunc_prop))
  }

  // summation in p13  T: Int
  // smt check: unknown,take 15min
  def aj_func(B: RealExpr) = {

    val aj: FuncDecl[RealSort] = mkFuncDecl(
      "aj",
      Array(mkIntSort()): Array[Sort],
      mkRealSort()
    )
    val t: Expr[IntSort] = mkIntConst("t")
    // properties for array a_j :  0<=a_t<=2/B,p12
    val aj_prop = (mkReal(0) <= aj(t)) && (aj(t) <= (mkReal(2) / B))
    // 2 th premise,take long time.fixed
    val qtf = forall_z3(Array(t), aj_prop)
    (aj, qtf)
  }

  /**
   * L-Lipschitz property and Uninterpreted function
   */
  def deltaL_B_Lipschitz(B: Long) = {

    val typesOfParam: Array[Sort] =
      Array(mkIntSort(), mkRealSort())
    val l = mkFuncDecl("lossF_Lipschitz", typesOfParam, mkRealSort())
    val z1 = mkIntConst("z1")
    val (w1, w2) = (mkRealConst("w11"), mkRealConst("w12"))
//    B-Lipschitz as p.12
    val L = mkReal(B)

//    L-Lipschitz property
    val prop = (l(z1, w1) - l(z1, w2))
      .normW() <= (L * (w1 - w2).normW())

    val qtf: Quantifier =
      forall_z3(Array(z1, w1, w2).asInstanceOf[Array[Expr[Sort]]], prop)
    (l, qtf)
  }

  // delta loss function for vector W
  def vec_deltaL(B: Long) = {

    val typesOfParam: Array[Sort] =
      Array(mkIntSort(), vecSort)
    val l = mkFuncDecl("delta_lossF", typesOfParam, vecSort)
    val z1 = mkIntConst("z1")
    val (w1, w2) = (newVec("w11"), newVec("w12"))
//    B-Lipschitz as p.12
    val L = mkReal(B)

//    L-Lipschitz property
    val prop = (l(z1, w1) - l(z1, w2))
      .norm() <= (L * (w1 - w2).norm())

    val qtf: Quantifier =
      forall_z3(Array(z1, w1, w2).asInstanceOf[Array[Expr[Sort]]], prop)
    (l, qtf)

  }
}
