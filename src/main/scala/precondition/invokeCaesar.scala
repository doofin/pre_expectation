package precondition
import com.doofin.stdScala._
import sys.process._
import java.io.File

import java.io.PrintWriter;

object invokeCaesar {
  def run = {
    // cd /home/dg/mwork/caesar/pgcl/pgcl2heyvl/pgcl2heyvl &&
    val axiomsDef = scala.io.Source.fromFile(new File("./caesar/hwalkrpeax.heyvl")).mkString
    val hvl = Process(
      s"python cmd.py   ${getHomeDir}/work/pre_expectation/caesar/hwalkrpe.pgcl",
      new File("/home/dg/mwork/caesar/pgcl/pgcl2heyvl/pgcl2heyvl")
    ).lazyLines.toList.mkString("\n")

    val hvlAll = axiomsDef ++ "\n\n" ++ hvl
    encloseDebug("before") {

      println(hvlAll)
    }

    val dh = "1 / n * sum(1, n, pos1, pos2)"
    val invar1 = s"[not(k1=k2)]*infty + [k1=k2]*${dh}*exp((n-1)/(n+1),ite(kk>k1,kk,k1))"

    val replacelist =
      Seq(
        "[k1 == k2] * infty" -- invar1,
        "var pos1: UInt;" -- "var pos1: Vec;",
        "var pos2: UInt;" -- "var pos2: Vec;",
        "pos1 = 1;" -- "pos1 = dsum(pos1,ei(i)) \n        pos2 = dsum(pos2,ei(i))",
        "i = 1;" -- "i = unif(1,2);"
      )

    val replacedHvl = replacelist.foldLeft(hvlAll) { (str, rep) => str.replace(rep._1, rep._2) }
    encloseDebug("after") {
      println(replacedHvl)

      // hvl foreach (p => println(p))
    }
    val fn = "compiledHvl.heyvl"
    val fdir = s"./caesar/$fn"
    writeToFile(fdir, replacedHvl)
    import scala.util.Try
    Try(s"caesar --raw $fdir".lazyLines foreach (println)) // needs raw!

  }
  /* ~/mwork/caesar/pgcl/pgcl2heyvl/pgcl2heyvl
 python cmd.py   ~/work/pre_expectation/caesar/hwalkrpe.pgcl
   */

//    replace [k1 == k2] * infty with invar
  def writeToFile(url: String, s: String) = {
    val pw = new PrintWriter(new File(url))
    pw.println(s)
    pw.close()
  }
}
