package precondition

import cats.{Id, ~>}
import precondition.dslAST._
import precondition.rpeSMT._

import scala.collection.mutable

object compilers {

  /** natural transformation between type containers. need two lang,dsl->ast,
    * can also translate into tree
    */
  def compileSyntax2Smt =
    new (DslStoreA ~> Id) {
      val kvs = mutable.Map.empty[Int, String]
      //      tr : current node to insert
      var currCtx: Option[String] = None
      var ln: Int = 0
      var stmtSmtListInserter = { x: StmtSmt =>
        StmtSmtList(List() :+ x)
      }

      var isAccum: Boolean = false
      var stmtSmtListAccu = StmtSmtList(List())
      var stmtSmtListGlob = StmtSmtList(List())

      override def apply[A](fa: DslStoreA[A]): Id[A] = {
        ln += 1
        println(s"fa : ${fa}")

        currCtx match {
          case Some(value) => kvs.put(ln, s"($value)  ${fa.toString}")
          case None        => kvs.put(ln, fa.toString)
        }

        fa match {
          case UpdateVar(v, value) =>
            println("isAccum", isAccum, stmtSmtListAccu)
            if (isAccum) {
              stmtSmtListAccu = stmtSmtListAccu.append(Assig(null, null))
            } else stmtSmtListGlob = stmtSmtListGlob.append(Assig(null, null))

            ()
          case NewVar(name) => Var(name)
          case While(cond, annotation, bd) =>
            println("While start")

            currCtx = Some(annotation)

            isAccum = true
            val r = bd.foldMap(this)
            isAccum = false
            stmtSmtListGlob = stmtSmtListGlob.append(
              WhileSmt(Some(annotation), stmtSmtListAccu)
            )
            println("While end")
            //            While(cond, annotation, bd.step)
            currCtx = None
            r
          case True => true
          case Skip => ()

        }
      }
    }

}
