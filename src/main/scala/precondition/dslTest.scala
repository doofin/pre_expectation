package precondition

import com.doofin.stdScala.pp
import precondition.syntax.dslAST._
import cats.data._
import cats.implicits._
import cats.free.Free._
import cats.free.Free
import cats.{Id, ~>}
import precondition.compilers.{compileSyntax2Smt, impureCompilerId}
import precondition.syntax.dslAST

//import cuttingedge.progAnalysis.ast.Expr.Var
//import cuttingedge.progAnalysis.ast._
object dslTest {
  type vals = Int
//  type St   = Map[Expr, vals]
//  type Epi  = (St, St) => Float

  def testDsl = {
    val compilerId = impureCompilerId
    val rImpure = program.foldMap(compilerId)
//    println(rImpure)
    pp(compilerId.kvs.toList.sortBy(_._1))

    val smtStmtCp = compileSyntax2Smt
    program.foldMap(smtStmtCp)
    pp(smtStmtCp.stmtSmtListGlob)
//    val rSt = program.foldMap(pureCompilerSt)
//    println(rSt.run(Map("" -> "")).value)
  }

  val annos = "[t<1>!=t<2>]*inf +...+ 2L/n (sum(j:0 to T-1) a(j))"

  def program: DslStore[dslAST.Var] = {
    for {
      w <- newVar("w")
      _ <- updateVar(w, 2)
      t <- newVar("t")
      _ <- while__(true__, annos) {
        for {
          s <- newVar("s")
          _ <- updateVar(s, 2)
          _ <- updateVar(w, w)
        } yield s
      }
      _ <- skip
    } yield { t }
  }

  /*
  def rpe(stmt: Stmt, epis: Epi): Epi = {
    stmt match {
      case Stmt.While_anno(b, ln, s, annotation) =>
        //anno contains loop invariant I,
        // return this I as lfp
        // finally, eval this at w0 and t0 to get a constant mapping st ?
        annotation2Epi(annotation, s)
      case Stmt.`:=`(nm, ln, expr) =>
        val newEp: Epi = { (s1, s2) =>
//          value of expr in s1 and s2.maybe eval expr first?
//          we abuse the notation s(e) to denote the natural lifting of s to a map from expressions to values
          epis(s1.updated(nm, s1(expr)), s2.updated(nm, s2(expr)))
        }

        newEp
      case Stmt.Stmts(x :: xs) => rpe(x, rpe(Stmt.Stmts(xs), epis))

      case _ => ???
    }
  }
   */

  /*
  def annotation2Epi(annotation: String, innerStmt: Stmt): Epi = {
    ???
  }
   */
}
