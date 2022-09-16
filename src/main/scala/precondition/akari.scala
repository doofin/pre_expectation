package precondition
import z3api.z3Utils
// import com.doofin.stdScala._
object akari {
  import precondition.z3api.z3Utils._ // scala bug? can't move this outside
  private lazy val ctx = z3Utils.newZ3ctx()
  import ctx._

  val GRID_B = """[
  [8,9,9,9,8,9,9,8],
  [9,9,9,2,9,3,9,9],
  [9,8,9,9,9,9,9,9],
  [3,9,9,9,9,9,8,9],
  [9,8,9,9,9,9,9,8],
  [9,9,9,9,9,9,4,9],
  [9,9,8,9,8,9,9,9],
  [0,9,9,2,9,9,9,8],
]"""
  val gridArr =
    str2mat(GRID_B).zipWithIndex.map(x => x._1.zipWithIndex.map(y => (y._1, y._2, x._2)))
//for all empty tile,exists bulb in same row/col that
// no wall between tile and lamp: for t in tile ,or(not (wall map (lamp map (l=> l.x<w.x<t.x))))
  val varsz = 10
  val lampL = for {
    i <- 0 to varsz
    j <- 0 to varsz
  } yield (mkInt("x_" + i), mkInt("y_" + j))

  val tilesEpt = Array(1 -> 1)
  val walls = Array(1 -> 1)
  val req1 = for {
    t <- tilesEpt
    w <- walls
    // l <- lampL
  } yield (lampL.map(l => l._1 < mkInt(w._1)).reduce(_ || _))

  def str2arr(s: String) = { //"[4, 0, 1, -2, 3]"
    s.replace("[", "").replace("]", "").split(",").map(_.trim().toInt)
  }

  def str2mat(s: String) = {
    /* [[1, 1, 1],
          [1, 0, 1],
          [1, 0, 1]] */
    s.split("],").map(str2arr)
    // Array[Array[Int]]
  }
}

/**
  SOLN_B = [
  [0,0,1,0,0,1,0,0],
  [0,1,0,0,1,0,1,0],
  [1,0,0,1,0,0,0,0],
  [0,1,0,0,0,0,0,1],
  [1,0,0,0,0,0,1,0],
  [0,0,0,0,0,1,0,1],
  [0,1,0,0,0,0,1,0],
  [0,0,1,0,1,0,0,0],
]

  */
