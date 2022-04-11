package precondition

import com.doofin.stdScala._
import com.microsoft.z3
import com.microsoft.z3._
import precondition.syntax.smtAST._
import precondition.z3api.{z3CheckApi, z3Utils}

import lemmas._
import issuesAndTests.invariantTup_lhs_i1

object rpeFunctionTup {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  import InfRealTuple.TupNum

  /**
   * generate smt terms from program statements and initial smt terms
   * @param stmt:
   *   program statements
   * @param E
   *   : the initial map E,or loop invariant
   * @param sideCond
   *   : side conditions during compile
   * @return
   *   substituted E
   */
  def rpeF(
      f_bij: z3.FuncDecl[IntSort]
  )(stmt: StmtSmt, E: TupNum, sideCond: List[BoolExpr]): (TupNum, List[BoolExpr]) = {
    // println("StmtSmt: ")
    // pp(stmt)
    stmt match {
      case NewVars(x1, e1, x2, e2) =>
        // println("NewVars(x1, e1, x2, e2)")
        // println(e1, e2)
        (E.copy(thisTup = E.thisTup.substitute(x1, e1).substitute(x2, e2)), sideCond)
      case SkipSmt => (E, sideCond)
      // case Assig(x, e)     => E.substitute(x, e)
      case Assig(x1, e1, x2, e2) =>
        (E.copy(thisTup = E.thisTup.substitute(x1, e1).substitute(x2, e2)), sideCond)

      case AssigRand(x1, x2, d) =>
        /* use the trick from bottom of p.10,which only works if rpe is in left hand side, due to
         * the inequality */
        /* make a sum of E ,substitute x1 for f(v) where f:isomorphism of S -> S and v is in
         * distribution D */
        // (p.10 Proposition 6)
        val sum1 = d
          .map(v =>
            E.copy(thisTup =
              E.thisTup.substitute(x1, v).substitute(x2, f_bij(v))
            ) // .substitute(x2, r)
          )
          .reduce(_ + _)
        import ImplicitConv._
        (sum1 / mkReal(d.size), sideCond)

      // eval of stmt is done reversely!
      case StmtSmtList(xs) =>
        xs match {
          case Nil      => (E, sideCond)
          case i :: Nil => rpeF(f_bij)(i, E, sideCond)
          case head :: tl =>
            val (tlR, tlRsideC) = rpeF(f_bij)(StmtSmtList(tl), E, sideCond)
            rpeF(f_bij)(head, tlR, tlRsideC)
        }
      case If_Tup((e1, e2), s1, s2) =>
        import ImplicitConv._
        val (t1, sc1) = rpeF(f_bij)(s1, E, sideCond)
        val (t2, sc2) = rpeF(f_bij)(s2, E, sideCond)
        val res: TupNum =
          iverB(e1 && e2) * t1 + (iverB(e1.neg && e2.neg) * t2) + (iverB(
            e1 !== e2
          ) * InfRealTuple.inftyTup_+)
        (res, sc1 ++ sc2)
      case WhileSmtTup(invariantRhs, (e1, e2), whileBd) =>
        // put I and cond as some side condition,apply rpe for stmt inside while
        // the rpe(bd,I) in p13.(1),  rpe(bd,I)=rpe(s<-U(S),I')
        val (rpe_bd_I, rpe_bd_I_sideCond) = rpeF(f_bij)(whileBd, invariantRhs, sideCond)

        import ImplicitConv._
        // test cases:
        // val sideCondNew: BoolExpr = TupNum(mkReal(0)) <= invariantRhs // unsat,ok
        // val sideCondNew: BoolExpr =
        //   invariantTup_lhs(e1, e2, rpe_bd_I, E) <= InfRealTuple.inftyTup_+ // unsat,ok

        // p13.(1)
        val sideCondNew: BoolExpr = theorem7p11_lhs(e1, e2, rpe_bd_I, E) <= invariantRhs

        // val sideCondNew: BoolExpr = invariantTup_lhs_i1(e1, e2, rpe_bd_I, E) <= invariantRhs
        // val sideCondNew: BoolExpr = InfRealTuple.inftyTup_+ <= InfRealTuple.inftyTup_+ // unsat,ok
        // val sideCondNew: BoolExpr = InfRealTuple.inftyTup_+ <= invariantRhs // ukn
        // val sideCondNew: BoolExpr = invariantTup_lhs(e1, e2, rpe_bd_I, E) <= InfRealTuple.inftyTup_+
        // just return invariant due to TH.7 at p.11 because we have proven the side condition
        rpeF(f_bij)(whileBd, invariantRhs, (sideCond :+ sideCondNew) ++ rpe_bd_I_sideCond)
    }
  }
}
