package precondition

import precondition._
import org.scalatest.funsuite._
import precondition.z3api.z3Utils

class testIssue extends AnyFunSuite {
  test("smt_z3") {
//    smt_z3.run
    // issues.sumIsUnknown() // ok
    issues.zeroMulInf2()
  }
}
