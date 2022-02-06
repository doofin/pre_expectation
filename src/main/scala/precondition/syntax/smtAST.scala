package precondition.syntax

import com.microsoft.z3._

object smtAST {
  sealed trait StmtSmt

  case object SkipSmt extends StmtSmt

  case class Assig[_ <: Sort](varname: Expr[_], expr: Expr[_]) extends StmtSmt

  case class AssigRand[a <: ArithSort](varname: Expr[a], dist: Set[Expr[a]])
      extends StmtSmt

  case class StmtSmtList(xs: List[StmtSmt]) extends StmtSmt {
    def append(x: StmtSmt) = StmtSmtList(xs :+ x)
  }

  case class WhileSmt(annotation: Option[String], xs: StmtSmtList)
      extends StmtSmt

}
