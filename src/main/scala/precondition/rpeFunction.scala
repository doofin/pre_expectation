package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}
import cats.kernel.instances.TupleMonoidInstances

import lemmas._

object rpeFunction {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  import InfRealTuple.TupNum

  /**
   * generate smt terms from program statements and initial smt terms
   * @param stmt:
   *   program statements
   * @param E
   *   : the initial map E,or loop invariant
   * @return
   *   substituted E
   */
  def rpeF(f_bij: z3.FuncDecl[IntSort])(stmt: StmtSmt, E: TupNum): TupNum =
    stmt match {
      case NewVars(x1, e1, x2, e2) =>
        println("NewVars(x1, e1, x2, e2)")
        println(e1, e2)
        E.copy(tup = E.tup.substitute(x1, e1).substitute(x2, e2))
      case SkipSmt => E
      // case Assig(x, e)     => E.substitute(x, e)
      case Assig(x1, e1, x2, e2) =>
        E.copy(tup = E.tup.substitute(x1, e1).substitute(x2, e2))

      case AssigRand(x1, x2, d) =>
        /* use the trick from bottom of p.10,which only works if rpe is in left
         * hand side, due to the inequality */
        /* make a sum of E ,substitute x1 for f(v) where f:isomorphism of S -> S
         * and v is in distribution D */
        // (p.10 Proposition 6)
        val sum1 = d
          .map(v =>
            E.copy(tup = E.tup.substitute(x1, v).substitute(x2, f_bij(v))) // .substitute(x2, r)
          )
          .reduce(_ + _)
        import ImplicitConv._
        sum1 / mkReal(d.size)

      // eval of stmt is done reversely!
      case StmtSmtList(xs) =>
        xs match {
          case Nil      => E
          case i :: Nil => rpeF(f_bij)(i, E)
          case head :: tl =>
            rpeF(f_bij)(head, rpeF(f_bij)(StmtSmtList(tl), E))
        }
      case WhileSmt(annotation, xs) =>
        // need to find t,w in xs,feed to anno
        // just E && annotation ?
        // E.tup.getArgs()
        println("WhileSmt(annotation, xs)")
        println(E.tup)
        // assert(false)
        //
        rpeF(f_bij)(xs, E)
    }
}
