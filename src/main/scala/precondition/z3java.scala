package precondition
import com.microsoft.z3._
import com.microsoft.z3.Status
import org.scalatest.exceptions.TestFailedException
import com.doofin.stdScala._
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Log
import com.microsoft.z3.Status
import org.scalatest.exceptions.TestFailedException
import scala.collection.JavaConverters._

import scala.collection.mutable

object z3java {

  /**
    * https://smtlib.cs.uiowa.edu/examples.shtml*/
  def checkSmtlibStr(xs: Seq[String]) = {
    val ctx = new Context(Map[String, String]("model" -> "true").asJava)

    xs foreach { s =>
      check(ctx, parseSmtlibStr(s, ctx))
    }

//    ctx.mkRealConst("t1")
  }

  /**
    * https://smtlib.cs.uiowa.edu/examples.shtml*/
  def checkBool(xs: Seq[BoolExpr]) = {
    val ctx = new Context(Map[String, String]("model" -> "true").asJava)
    import ctx._

    xs foreach { s =>
      check(ctx, s)
    }
  }

  /**
    * https://smtlib.cs.uiowa.edu/examples.shtml*/
  def checkBoolCtx(ctx: Context, xs: Seq[BoolExpr]) = {
    println("checkBoolCtx")
    xs foreach { s =>
      check(ctx, s)
    }
  }

  private def check(ctx: Context, f: BoolExpr) = {
    val s = ctx.mkSolver
    s.add(f)

    val r = s.check() match {
      case Status.UNSATISFIABLE => "UNSATISFIABLE"
      case Status.UNKNOWN       => "UNKNOWN"
      case Status.SATISFIABLE   => "SATISFIABLE"
    }

    println("--------smt-lib2 start -----------")
    println(s.toString)
    println("smt result:", r)
    println("--------smt-lib2 end-----------")

//    println(s"$r : for formula  ${f} ")

  }

  def parserExample1(): Unit = {
    checkSmtlibStr(
      Seq(
        "(declare-const x Int) (declare-const y Int) (assert (and (> x y) (> x 0)))",
        "(assert (> 0.0001 0.0))"
//        "(assert (and (= (snd (mk_tuple1 1.0 true)) true) (> (fst (mk_tuple1 1.0 true)) 0.0)))"
      )
    )
  }

  private def parseSmtlibStr(s: String, ctx: Context) = {
    val fs = ctx.parseSMTLIB2String(
      s,
      null,
      null,
      null,
      null
    )
//    println(fs.toList map (x => x.toString))
    fs(0)
  }
}
