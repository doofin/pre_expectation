package precondition.syntax

import cats.{Id, ~>}
import cats.data.State

import precondition.syntax.dslAST._
import precondition.sgdExampleTup._

import scala.collection.mutable

import precondition.syntax.smtAST._

object compilers {

  /**
   * natural transformation between type containers. need two lang,dsl->ast, can
   * also translate into tree
   */
  def compileToSmt =
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
          case VarAssign(v, value) =>
            println("isAccum", isAccum, stmtSmtListAccu)
            if (isAccum) {
              stmtSmtListAccu = stmtSmtListAccu.append(Assig(null, null, null, null))
            } else
              stmtSmtListGlob = stmtSmtListGlob.append(Assig(null, null, null, null))

            ()
          case NewVar(name) => Var(name)
          case While(cond, annotation, bd) =>
            println("While start")

            currCtx = Some(annotation)

            isAccum = true
            val r = bd.foldMap(this)
            isAccum = false
            stmtSmtListGlob = stmtSmtListGlob.append(
              WhileSmtTup(???, ???, stmtSmtListAccu)
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

  /** read values after invoke
   * natural transformation between type containers. need two lang,dsl->ast, can
   * also translate into tree
   */
  def compilerToStr =
    new (DslStoreA ~> Id) {
      //      val kvs                     = mutable.Map.empty[String, Any]
      val kvs = mutable.Map.empty[Int, String]
      //      tr : current node to insert
      var currCtx: Option[String] = None
      var ln: Int = 0
      override def apply[A](fa: DslStoreA[A]): Id[A] = {

        println(s"fa : ${fa}")
        currCtx match {
          case Some(str) => kvs.put(ln, s"($str)  ${fa.toString}")
          case None      => kvs.put(ln, fa.toString)
        }

        ln += 1
        fa match {
          case VarAssign(v, value) =>
            ()
          case NewVar(name) => Var(name)
          case While(cond, annotation, body) =>
            println("While start")
            currCtx = Some(annotation)
            //            use some state there
            val r = body.foldMap(this)
            println("While end")
            currCtx = None
            r
          case True => true
          case Skip => ()

        }
      }
    }

  def dsl2hvl[A](dStmt: DslStoreA[A]) = {
    dStmt match {
      case VarAssign(v, value) => s"${v.nm}1=$value;${v.nm}2=$value"
      // case If(cond, s1, s2)              =>
      // case NewVar(name)                  =>
      // case True                          =>
      // case While(cond, annotation, body) =>
      // case Skip                          =>
      case _ => ""
    }
  }

  def compilerToHvl =
    new (DslStoreA ~> Id) {
      //      val kvs                     = mutable.Map.empty[String, Any]
      val kvs = mutable.Map.empty[Int, String]
      //      tr : current node to insert
      var currCtx: Option[String] = None
      var lineNum: Int = 0
      override def apply[A](fa: DslStoreA[A]): Id[A] = {
        lineNum += 1
        val dslStmt = fa

        val dslStr = dsl2hvl(dslStmt)
        currCtx match {
          case Some(str) => kvs.put(lineNum, s"($str)  ${dslStr}")
          case None      => kvs.put(lineNum, dslStr)
        }

        dslStmt match {
          case VarAssign(v, value) =>
            ()
          case NewVar(name)                  => Var(name)
          case While(cond, annotation, body) =>
            // println("While start")
            currCtx = Some(annotation)
            //            use some state there
            val r = body.foldMap(this)
            // println("While end")
            //            While(cond, annotation, bd.step)
            currCtx = None
            r
          case True             => true
          case Skip             => ()
          case If(cond, s1, s2) =>
        }
      }
    }

  type StState[A] = State[Map[String, Any], A]
  val pureCompilerSt: DslStoreA ~> StState = new (DslStoreA ~> StState) {
    override def apply[A](fa: DslStoreA[A]): StState[A] = {
      fa match {
        case VarAssign(v, value) =>
          val r: StState[Unit] = State.modify(_.updated("", v))
          r
        case NewVar(name) =>
          val r: StState[Var] =
            State.inspect(_.getOrElse("", Var()).asInstanceOf[Var])
          r
        case While(cond, annotation, dslStoreA) =>
          val r = dslStoreA.foldMap(this)
          r
        case True =>
          val r: StState[Boolean] =
            State.inspect(_.getOrElse("", true).asInstanceOf[Boolean])
          r
      }
    }
  }

}

// println("t1 : ", t1.getId())
// println("t1 : ", mkInt(1).getInt())
// import shapeless._
// import syntax.std.tuple._
