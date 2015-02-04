trait Lifter[A,B] {
  def lift(x : A, y : B ) : A with B
}

//trait Exp[A] {
//  def accept(f: ExpAlg[A]): A
//}
//
//trait SubExp[A] extends Exp[A] {
//  override def accept(f: SubExpAlg[A]): A
//}

trait Exp {
  def eval: Int
}

trait Lit extends Exp {
  val x: Int
  def eval = x
}

trait Add extends Exp {
  val e1, e2: Exp
  def eval = e1.eval + e2.eval
}

def main(args: Array[String]): Unit = {
  println("Hello")
}
