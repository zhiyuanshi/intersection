// S   T
//  \ /
//   U

trait S {}

trait T {}

case class U() extends S with T {}

case class C() {
  def m(x: S): Short = 1
  def m(x: T): Short = 1
  def m(x: U): Int   = 1
}

object Overloading2 {
  def main(args: Array[String]) {
    val c = C()
    val u = U()
    println(c.m(u))
  }
}
