package precondition.z3api

import com.microsoft.z3._

import scala.collection.JavaConverters._
import scala.util.Try
import scala.util.Failure
import scala.util.Success

import com.doofin.stdScala._

object z3CheckApi {

  /** https://smtlib.cs.uiowa.edu/examples.shtml
    */
  def checkSmtlibStr(xs: Seq[String]) = {
    val ctx = new Context(Map[String, String]("model" -> "true").asJava)

    xs foreach { s =>
      check(ctx, Seq(parseSmtlibStr(s, ctx)))
    }

    //    ctx.mkRealConst("t1")
  }

  /** https://smtlib.cs.uiowa.edu/examples.shtml
    */
  /*   def checkBool(xs: Seq[BoolExpr]) = {
    val ctx = new Context(Map[String, String]("model" -> "true").asJava)

    check(ctx, xs)

    xs foreach { s =>
      check(ctx, s)
    }
  } */

  /** https://smtlib.cs.uiowa.edu/examples.shtml
    *
    * if premise is not unsat (premise is sat or unknown) ,it's fine
    */
  def checkBoolExpr(
      ctx: Context,
      xs: Seq[BoolExpr],
      goal: Status = Status.SATISFIABLE,
      goalStr: String = "",
      printSAT: Boolean = false,
      premise: Seq[BoolExpr] = Seq()
  ) = {
    // println("checkBoolCtx")
    val r = check(ctx, xs, printSAT)
    println("goal:" + goalStr)
    val msg = if (goal == r) "goal achieved" else "goal not  achieved"
    println(msg)

    if (premise.nonEmpty) {
      println("doing sanity check on premise")
      val r = check(ctx, premise, printSAT)
      println("goal: premise is sat or unknown")
      val msg =
        if (r != Status.UNSATISFIABLE) " premise is consistent"
        else " premise is bad"
      println(msg)
    } else {
      println("skip sanity check on premise")
    }
  }

  @deprecated
  def getProofVals(ctx: Context, f: BoolExpr) = {
    // https://stackoverflow.com/questions/29577754/getting-proof-from-z3py
    val s = ctx.mkSolver
    s.add(f)
    // s.setpa
    s.getProof()
  }

  private def check(
      ctx: Context,
      fs: Seq[BoolExpr],
      printSAT: Boolean = false
  ) = {
    val s = ctx.mkSolver
    fs foreach (f => s.add(f))

    val statusR = s.check()
    val checkRes = statusR match {
      case Status.UNSATISFIABLE =>
        val ur = Try(s.getUnsatCore()) match {
          case Failure(exception) => "no getUnsatCore"
          case Success(value)     => "UnsatCore : " + value.toList.toString()
        }
        "UNSATISFIABLE : " + ur

      case Status.UNKNOWN => "UNKNOWN"
      case Status.SATISFIABLE =>
        if (!printSAT) encloseDebug("model str:") {
          println(s.getModel().toString())
        }
        "SATISFIABLE"
      case x => "unknown : " + x.toString()
    }

    /* val pf = Try(s.getProof()) match {
      case Failure(exception) => "no proof"
      case Success(value)     => value.toString()
    } */

    encloseDebug("smt-lib2 str", true) {
      println(s.toString)
      println("smt result:", checkRes)
    }

    statusR
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
