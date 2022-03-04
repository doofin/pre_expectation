package precondition
import com.microsoft.z3
import com.microsoft.z3._
import precondition.InfRealTuple
import precondition.z3api.z3CheckApi

import com.doofin.stdScala._
import InfRealTuple.TupNum
// lemmas like bijective function,L lipschez,etc
object lemmas {
  import precondition.z3api.z3Utils._
  import precondition.InfRealTuple.thisCtx._

  type VecType = UninterpretedSort
  type binOpType[a] = (a, a) => a
  val vecSort: VecType = mkUninterpretedSort("vec")

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
  val (vec_minus, vec_minusP) = vec_binOp(_ - _, "-")
  val (vec_scalaMul, vec_scalaMulP) = scala_mul_vec()
  val (vec_norm, vec_normP) = norm_vec_gen(vec_add, vec_scalaMul)

  val vecPremise = vec_addP && vec_minusP && vec_normP && vec_scalaMulP

  implicit class vecOps(v: Expr[VecType]) {
    def +(v2: Expr[VecType]) = vec_add(v, v2)
    def -(v2: Expr[VecType]) = vec_minus(v, v2)
    def mulByScalar(a: Expr[RealSort]) = vec_scalaMul(a, v)
    def norm(): Expr[RealSort] = vec_norm(v)
  }

  def newVec(name: String = "x"): Expr[VecType] = mkConst(name, vecSort)

  /**
   * generate norm operator for vec. return: normF : vec -> real
   */
  def norm_vec_gen(vec_add: FuncDecl[VecType], scalaMul: FuncDecl[VecType]) = {
    val normF =
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
      val prop = normF(vec_add(v, w)) <= normF(v) + normF(w)
      forall_z3(Array(v), prop)
    }

    val p3 = {
      val v = newVec("v")
      val a = mkRealConst("a")
      val prop = normF(scalaMul(a, v)) === (a.normW() * normF(v))
      forall_z3(Array(v), prop)
    }

    (normF, p1 && p2 && p3)
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
      binReal: binOpType[Expr[RealSort]],
      name: String
  ) = {
    val a = mkConst("a", vecSort)
    val b = mkConst("b", vecSort)
    val i = mkIntConst("i")
    val binOp: FuncDecl[VecType] =
      mkFuncDecl("binOp_" + name, Array(vecSort, vecSort): Array[Sort], vecSort)
    // a[i]-b[i]=(a-b)[i]
    val prop =
      binReal(vec_nth(i, a), vec_nth(i, b)) === vec_nth(i, binOp(a, b))
    val qtf = forall_z3(Array(a, b), prop)
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

  // gen lhs of  p13.1 regarding loop rule
  def invar_lhs_gen(e1: BoolExpr, e2: BoolExpr, rpeApplied: TupNum, E: TupNum) = {
    import ImplicitConv._
    import InfRealTuple._

    val I_lhs: TupNum =
      TupNum(iverB(e1 && e2)) * rpeApplied +
        (TupNum(iverB(e1.neg && e2.neg)) * E) +
        (iverB(e1 !== e2) * infty_+)

    I_lhs
  }

  //  sum function in p.13
// sum_aj : int^2=>real,sum over a_j from i to j
// (smt result:,UNKNOWN)
// problem:unwrapping might be infinite
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
    val prop1 = i <= j ==> ((sum_f(i, j) === (sum_f(i + 1, j) + aj(i)) && (sum_f(i + 1, j) >= 0)))
    val prop2 = i > j ==> (sum_f(i, j) === 0)

    val qtf = forall_z3(Array(i, j), prop1 && prop2)
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

    // 1:sum = sum i-1 ,2:sum : make it weaker 3.limited function
    // make it weaker: a i >=0,sum i j >0 -> sum i+1 j >0
    // need a way to update upper bound
    val prop = (i <= j && aj(j) >= 0 && (sum_f(i, j - 1) >= 0)) ==> sum_f(i, j) >= sum_f(i, j - 1)

    val prop2 = i > j ==> (sum_f(i, j) === 0)

    val qtfDec = forall_z3(Array(i, j), prop && prop2)
    // (sum_f, numProp && qtf)
    (sum_f, numProp && qtfDec)

  }
}
