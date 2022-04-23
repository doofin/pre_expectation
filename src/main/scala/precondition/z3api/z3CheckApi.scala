package precondition.z3api

import com.microsoft.z3._

import scala.collection.JavaConverters._
import scala.util.Try
import scala.util.Failure
import scala.util.Success

import com.doofin.stdScala._

object z3CheckApi {

  /**
   * https://smtlib.cs.uiowa.edu/examples.shtml
   */
  def checkSmtlibStr(xs: Seq[String]) = {
    val ctx = new Context(Map[String, String]("model" -> "true").asJava)

    xs foreach { s =>
      check(ctx, Seq(parseSmtlibStr(s, ctx)))
    }

    //    ctx.mkRealConst("t1")
  }

  /**
   * https://smtlib.cs.uiowa.edu/examples.shtml
   */
  /* def checkBool(xs: Seq[BoolExpr]) = { val ctx = new Context(Map[String, String]("model" ->
   * "true").asJava)
   *
   * check(ctx, xs)
   *
   * xs foreach { s => check(ctx, s) } } */

  def checkBoolExpr(
      ctx: Context,
      premises: Seq[BoolExpr] = Seq(),
      formulas: Seq[BoolExpr],
      goals: List[Status],
      desc: String = "",
      printSATmodel: Boolean = false,
      printSmtStr: Boolean = false,
      timeout: Int = 5
  ) = {
    // println("checkBoolCtx")
    val r = check(
      ctx,
      premises ++ formulas,
      printSATmodel,
      printSmtStr = printSmtStr,
      timeout = timeout * 1000
    )
    val resMsg =
      if (goals contains r)
        s"ok ! result: ${r} , goal: ${goals}"
      else s"failed ! result: ${r} , goal: ${goals}"

    println(resMsg + (if (desc.nonEmpty) ",description: " + desc else ""))
    // val msg = if (goals contains r) "goal achieved !" else s"goal failed ! result ${r} != ${goals}"
    // println(msg)

    // check premise. if premise is not unsat (premise is sat or unknown) ,it's fine
    if (premises.nonEmpty) {
      val r = check(ctx, premises, true, printSmtStr = printSmtStr, timeout = 5000)
      /* val rn =
        check(
          ctx,
          premise.map(x => ctx.mkNot(x)),
          true,
          printSmtStr = printSmtStr,
          timeout = 5000
        ) */

      // println("neg of premise : ", rn)

      // println("premise model : ", r)
      val premOk = r != Status.UNSATISFIABLE
      if (!premOk) println(" premise is bad")

    } else {
      println("skip sanity check on premise")
    }
  }

  private def check(
      ctx: Context,
      formulas: Seq[BoolExpr],
      printSATmodel: Boolean = false,
      printSmtStr: Boolean = false,
      timeout: Int = 2500000
  ) = {
    val s = ctx.mkSolver
    val p = ctx.mkParams()
    p.add("timeout", timeout)
    s.setParameters(p)
    formulas foreach (f => s.add(f))

    val statusR = s.check()
    val checkRes = statusR match {
      case Status.UNSATISFIABLE =>
        val ur = Try(s.getUnsatCore()) match {
          case Failure(exception) => "no getUnsatCore"
          case Success(value)     => "UnsatCore : " + value.toList.toString()
        }
        "UNSATISFIABLE : " + ur

      case Status.UNKNOWN =>
        // println(("UNKNOWN after checking for " + "timeout " + timeout))
        "UNKNOWN"
      case Status.SATISFIABLE =>
        if (printSATmodel) encloseDebug("model str:") {
          println(s.getModel().toString())
        }
        "SATISFIABLE"
      case x => "unknown : " + x.toString()
    }

    if (printSmtStr)
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
    println(fs.toList map (x => x.toString))
    // println("parseSmtlibStr: ", fs)
    assert(fs.length > 0, "parse smtlib failed!")
    fs(0)
  }
}

/*   @deprecated
  def getProofVals(ctx: Context, f: BoolExpr) = {
    // https://stackoverflow.com/questions/29577754/getting-proof-from-z3py
    val s = ctx.mkSolver
    s.add(f)
    // s.setpa
    s.getProof()
  }
 */
