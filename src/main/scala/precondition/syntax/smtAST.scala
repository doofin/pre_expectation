package precondition.syntax

import com.microsoft.z3._
import precondition.lemmas.VecType
import precondition.InfRealTuple

object smtAST {
  sealed trait StmtSmt

  case object SkipSmt extends StmtSmt

  // make it relational : x1<-e1,x2<-e2
  case class Assig[_ <: Sort](
      x1: Expr[_],
      e1: Expr[_],
      x2: Expr[_],
      e2: Expr[_]
  ) extends StmtSmt

  case class NewVars[_ <: Sort](
      x1: Expr[_],
      e1: Expr[_],
      x2: Expr[_],
      e2: Expr[_]
  ) extends StmtSmt

  // make it relational : x1,x2<-D
  case class AssigRand[a <: ArithSort](
      x1: Expr[a],
      x2: Expr[a],
      dist: Set[Expr[a]]
  ) extends StmtSmt

  case class StmtSmtList(xs: List[StmtSmt]) extends StmtSmt {
    def append(x: StmtSmt) = StmtSmtList(xs :+ x)
  }

  case class WhileSmt(
      annotation: InfRealTuple.TupNum,
      cond: (BoolExpr, BoolExpr),
      xs: StmtSmtList
  ) extends StmtSmt

}
