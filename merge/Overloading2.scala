// S   T
//  \ /
//   U

trait S {}

trait T {}

case class U() extends S with T {}

case class C() {
  def m(x: S) = 1
  def m(x: T) = true
  def m(x: U) = 1.0
}

object Overloading2 {
  def main(args: Array[String]) {
    val c = C()
    val u = U()
    println(c.m(u))
  }
}
