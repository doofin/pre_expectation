package precondition.syntax

import cats.implicits._
import cats.free.Free._
import cats.free.Free

object dslAST {

  sealed trait DslStoreA[A]

  sealed trait Expr1

  case class Var(nm: String = "") extends Expr1

  case class UpdateVar[T](v: Var, value: T) extends DslStoreA[Unit]

  case class NewVar(name: String = "") extends DslStoreA[Var] //DslStoreA[Var]

  case class While(
      cond: DslStore[Boolean],
      annotation: String,
      body: DslStore[Unit]
  ) extends DslStoreA[Unit]

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
    * https://github.com/rtitle/free-control/blob/master/src/main/scala/control/free/ControlFlowInterpreter.scala */
  def while__[t](cond: DslStore[Boolean], annotation: String)(
      dslStoreA: DslStore[Unit]
  ) =
    liftF[DslStoreA, Unit](While(cond, annotation, dslStoreA))

  def true__ = liftF[DslStoreA, Boolean](True)

}
