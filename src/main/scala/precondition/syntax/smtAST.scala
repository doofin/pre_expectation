package precondition.syntax

import com.microsoft.z3._

object smtAST {
  sealed trait StmtSmt

  case object SkipSmt extends StmtSmt

  case class Assig[_ <: Sort](x: Expr[_], e: Expr[_]) extends StmtSmt

  case class AssigRand[a <: ArithSort](x: Expr[a], d: Set[Expr[a]])
    extends StmtSmt

  case class StmtSmtList(xs: List[StmtSmt]) extends StmtSmt {
    def append(x: StmtSmt) = StmtSmtList(xs :+ x)
  }

  case class WhileSmt(annotation: Option[String], xs: StmtSmtList)
    extends StmtSmt

}
