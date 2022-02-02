package precondition.z3api

import com.microsoft.z3._

import scala.collection.JavaConverters._
import scala.util.Try
import scala.util.Failure
import scala.util.Success

object z3CheckApi {

  /** https://smtlib.cs.uiowa.edu/examples.shtml
    */
  def checkSmtlibStr(xs: Seq[String]) = {
    val ctx = new Context(Map[String, String]("model" -> "true").asJava)

    xs foreach { s =>
      check(ctx, parseSmtlibStr(s, ctx))
    }

    //    ctx.mkRealConst("t1")
  }

  /** https://smtlib.cs.uiowa.edu/examples.shtml
    */
  def checkBool(xs: Seq[BoolExpr]) = {
    val ctx = new Context(Map[String, String]("model" -> "true").asJava)

    xs foreach { s =>
      check(ctx, s)
    }
  }

  /** https://smtlib.cs.uiowa.edu/examples.shtml
    */
  def checkBoolCtx(
      ctx: Context,
      xs: Seq[BoolExpr],
      goal: Status = Status.SATISFIABLE,
      goalStr: String = ""
  ) = {
    println("checkBoolCtx")
    xs foreach { s =>
      val r = check(ctx, s)
      println(goalStr)
      val msg = if (goal == r) "goal achieved" else "goal not  achieved"
      println(msg)
    }

  }

  def getProofVals(ctx: Context, f: BoolExpr) = {
    // https://stackoverflow.com/questions/29577754/getting-proof-from-z3py
    val s = ctx.mkSolver
    s.add(f)
    // s.setpa
    s.getProof()
  }

  private def check(ctx: Context, f: BoolExpr) = {
    val s = ctx.mkSolver
    s.add(f)
    // s.getProof()
    // s.
    val statusR = s.check()
    val checkRes = statusR match {
      case Status.UNSATISFIABLE =>
        val ur = Try(s.getUnsatCore()) match {
          case Failure(exception) => "no getUnsatCore"
          case Success(value)     => "UnsatCore : " + value.toList.toString()
        }
        "UNSATISFIABLE : " + ur

      case Status.UNKNOWN     => "UNKNOWN"
      case Status.SATISFIABLE => "SATISFIABLE"
      case x                  => "unknown : " + x.toString()
    }

    val pf = Try(s.getProof()) match {
      case Failure(exception) => "no proof"
      case Success(value)     => value.toString()
    }

    println("--------smt-lib2 start -----------")
    println(s.toString)
    println("smt result:", checkRes)
    println("proof : ", pf)
    println("--------smt-lib2 end-----------")

    //    println(s"$r : for formula  ${f} ")
    statusR
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
