package precondition
import com.microsoft.z3
import com.microsoft.z3.{Context, Expr, IntExpr, IntSort, Sort}
import precondition.InfRealTuple
import precondition.z3api.z3CheckApi

// lemmas like bijective function,L lipschez,etc
object lemmas {
  import precondition.z3api.z3Utils._
  import precondition.InfRealTuple.thisCtx._

  def f_bijection_int(): (z3.FuncDecl[IntSort], z3.Quantifier) = {
    val params: Array[Sort] = Array(mkIntSort())
    val f = mkFuncDecl("f_bij", params, mkIntSort())
    val f_inv = mkFuncDecl("f_bij_inv", params, mkIntSort())
    val z1: Expr[IntSort] = mkIntConst("z1")
    val prop = (f(f_inv(z1)) === z1) && (f_inv(f(z1)) === z1)

    val qtf = forall_z3(Array(z1), prop)
    (f, qtf)
  }
}
