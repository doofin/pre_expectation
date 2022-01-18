package precondition

import cats.data._
import cats.implicits._
import cats.free.Free._
import cats.free.Free
import cats.{Id, ~>}
import scala.collection.mutable
import com.doofin.stdScala._

object dslAST {

  sealed trait DslStoreA[A]
  sealed trait Expr1
  case class Var(nm: String = "")           extends Expr1
  case class UpdateVar[T](v: Var, value: T) extends DslStoreA[Unit]
  case class NewVar(name: String = "")      extends DslStoreA[Var] //DslStoreA[Var]
  case class While(cond: DslStore[Boolean], annotation: String, body: DslStore[Unit])
      extends DslStoreA[Unit]
  case object True extends DslStoreA[Boolean]
  case object Skip extends DslStoreA[Unit]

  type DslStore[A] = Free[DslStoreA, A]

  def whileM_[A](cond: DslStore[Boolean], prog: DslStore[A]): DslStore[Unit] =
    cond.flatMap {
      case false => ().pure[DslStore]
      case true  => prog >> whileM_(cond, prog)
    }

  def updateVar[T](v: Var, value: T): DslStore[Unit] =
    liftF[DslStoreA, Unit](UpdateVar[T](v, value))

  def newVar(name: String = ""): Free[DslStoreA, Var] = liftF(NewVar(name))

  def skip: Free[DslStoreA, Unit] = liftF(Skip)

  /**
    * https://github.com/rtitle/free-control/blob/master/src/main/scala/control/free/ControlFlowInterpreter.scala*/
  def while__[t](cond: DslStore[Boolean], annotation: String)(dslStoreA: DslStore[Unit]) =
    liftF[DslStoreA, Unit](While(cond, annotation, dslStoreA))

  def true__ = liftF[DslStoreA, Boolean](True)

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

/*  def p1 =
    newVar("")
      .flatMap { v: Var =>
        updateVar(v, 2)
      }
      .flatMap(_ => newVar(""))

//  limitation of scala for notation?
//  https://github.com/scala/bug/issues/1760
 */
