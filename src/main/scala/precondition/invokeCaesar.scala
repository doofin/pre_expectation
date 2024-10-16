package precondition
// import com.doofin.stdScala._
import com.doofin.stdScalaJvm._
import sys.process._
import java.io.File
import scala.util.Try
import java.io.PrintWriter;

object invokeCaesar {
  def run = {
    //axiom like vec,exp
    val axiomsDef = scala.io.Source.fromFile(new File("./caesar/hwalkrpeax.heyvl")).mkString

    // raw fmt generated by pgcl2heyvl
    val hvl_raw = Process(
      s"python cmd.py   $getCurrDir/caesar/hwalkrpe.pgcl",
      new File("/home/dg/mwork/caesar/pgcl/pgcl2heyvl/pgcl2heyvl")
    ).lazyLines.toList.mkString("\n")

    //convert raw to non-raw
    val hvlWrapped = s"""proc name()->()
    down requires ?(true)
    down ensures ?(true)
  {
   $hvl_raw
  }"""

    val hvlNoInvar = axiomsDef ++ "\n\n" ++ hvlWrapped

    // add invariants and while body
    val dh = " n * sum(1, n, pos1, pos2)" // 1 / n ,divide not impl?
    val invar1 =
      s"[not(k1==k2)]*∞ + [k1==k2] * ($dh) * exp((n-1)*(n+1),ite(kk>k1,kk,k1))" //(n-1)/(n+1)

    val replacelist =
      Seq(
        "[k1 == k2] * ∞" -- invar1,
        "var pos1: UInt;" -- "var pos1: Vec;",
        "var pos2: UInt;" -- "var pos2: Vec;",
        "pos1 = 1;" -- "pos1 = dsum(pos1,ei(i)); \n        pos2 = dsum(pos2,ei(i));",
        "i = 1;" -- "i = unif(1,2);"
      )

    val hvl_all = replacelist.foldLeft(hvlNoInvar) { (str, rep) => str.replace(rep._1, rep._2) }
    encloseDebug("hvl_all") {
      println(hvl_all)
    }

    val fn = "compiledHvl.heyvl"
    val fdir = s"./caesar/$fn"
    writeToFile(fdir, hvl_all)

    Try(s"caesar $fdir".lazyLines foreach (println)) // --raw

  }

}

/*
encloseDebug("before") {
      println(hvlAll)
    }

~/mwork/caesar/pgcl/pgcl2heyvl/pgcl2heyvl
 python cmd.py   ~/work/pre_expectation/caesar/hwalkrpe.pgcl
 */

//    replace [k1 == k2] * infty with invar
