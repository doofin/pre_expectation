package precondition

import precondition._
import org.scalatest.funsuite._
import precondition.z3api.z3Utils

class testSmt extends AnyFunSuite {
  test("smt_z3") {
//    smt_z3.run
    rpeSMT.test
//    z3java.parserExample1()
    val ctx = z3Utils.newZ3ctx()
    // z3example.quantifierExample1(ctx)
  }
}
