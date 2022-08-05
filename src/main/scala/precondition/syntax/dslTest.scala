package precondition.syntax

import precondition._
import com.doofin.stdScala.pp
import precondition.syntax.dslAST._
import cats.data._
import cats.implicits._
import cats.free.Free._
import cats.free.Free
import cats.{Id, ~>}
import compilers._
import precondition.syntax.dslAST

//import cuttingedge.progAnalysis.ast.Expr.Var
//import cuttingedge.progAnalysis.ast._
object dslTest {
  type vals = Int
//  type St   = Map[Expr, vals]
//  type Epi  = (St, St) => Float

  def testDsl = {
    // val compilerId = compilerToStr
    val compilerId = compilerToHvl
    val r_notused = sgdProgram.foldMap(compilerId)
//    println(rImpure)
    pp(compilerId.kvs.toList.sortBy(_._1))

    // val smtCompiler = compileToSmt
    // program.foldMap(smtCompiler)
    // pp(smtCompiler.stmtSmtListGlob)

//    val rSt = program.foldMap(pureCompilerSt)
//    println(rSt.run(Map("" -> "")).value)
  }

  def hwalkProgram = {
    val invar = ""
    val k = Var("k")
    val i = Var("i")
    val pos = Var("pos")
    val ei = Var("e(i)")
    for {
      _ <- varAssign(k, LitNum(1))
      _ <- while__(true__, invar) {
        for {
          _ <- if_(
            BinOpBool(i, "!=", LitNum(0)),
            for {
              _ <- varAssign(pos, BinOpVal(pos, "+", ei))
            } yield (),
            skip
          )
          _ <- varAssign(k, BinOpVal(k, "+", LitNum(1)))
        } yield ()
      }
      _ <- skip
    } yield {}
  }
  val annos = "[t<1>!=t<2>]*inf +...+ 2L/n (sum(j:0 to T-1) a(j))"

  def sgdProgram: DslStore[dslAST.Var] = {
    for {
      w <- newVar("w")
      _ <- varAssign(w, LitNum(1))
      t <- newVar("t")
      _ <- while__(true__, annos) {
        for {
          s <- newVar("s")
          _ <- varAssign(s, LitNum(1))
          _ <- varAssign(w, w)
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
