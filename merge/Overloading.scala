// S   T
//  \ /
//   U

trait S {}

trait T {}

case class U() extends S with T {}

case class C() {
  def m(x: S) = 1
  def m(x: T) = true
}

object Main {
  val c = C()
  val u = U()
  c.m(u)
}
