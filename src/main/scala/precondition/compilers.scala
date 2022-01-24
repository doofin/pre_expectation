package precondition

import cats.{Id, ~>}
import precondition.syntax.dslAST._
import precondition.rpeSMT._

import scala.collection.mutable

import precondition.syntax.smtAST._

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

  /**
   * natural transformation between type containers.
   *need two lang,dsl->ast, can also translate into tree*/
  def impureCompilerId =
    new (DslStoreA ~> Id) {
      //      val kvs                     = mutable.Map.empty[String, Any]
      val kvs = mutable.Map.empty[Int, String]
      //      tr : current node to insert
      var currCtx: Option[String] = None
      var ln: Int                 = 0
      override def apply[A](fa: DslStoreA[A]): Id[A] = {

        println(s"fa : ${fa}")
        currCtx match {
          case Some(value) => kvs.put(ln, s"($value)  ${fa.toString}")
          case None        => kvs.put(ln, fa.toString)
        }

        ln += 1
        fa match {
          case UpdateVar(v, value) =>
            ()
          case NewVar(name) => Var(name)
          case While(cond, annotation, body) =>
            println("While start")
            currCtx = Some(annotation)
            //            use some state there
            val r = body.foldMap(this)
            println("While end")
            //            While(cond, annotation, bd.step)
            currCtx = None
            r
          case True => true
          case Skip => ()

        }
      }
    }

  import cats.data.State
  type StState[A] = State[Map[String, Any], A]
  val pureCompilerSt: DslStoreA ~> StState = new (DslStoreA ~> StState) {
    override def apply[A](fa: DslStoreA[A]): StState[A] = {
      fa match {
        case UpdateVar(v, value) =>
          val r: StState[Unit] = State.modify(_.updated("", v))
          r
        case NewVar(name) =>
          val r: StState[Var] = State.inspect(_.getOrElse("", Var()).asInstanceOf[Var])
          r
        case While(cond, annotation, dslStoreA) =>
          val r = dslStoreA.foldMap(this)
          r
        case True =>
          val r: StState[Boolean] = State.inspect(_.getOrElse("", true).asInstanceOf[Boolean])
          r
      }
    }
  }

}

// println("t1 : ", t1.getId())
// println("t1 : ", mkInt(1).getInt())
// import shapeless._
// import syntax.std.tuple._