object Visitor {
  trait ExpAlg[E]
  trait SubExpAlg[E]

  trait Exp {
    def accept[E](v: ExpAlg[E]): E
  }

  trait ExpVisitor[E] {
    def lit(x: Int): E
    def add(e1: E, e2: E): E
  }

  trait SubExp extends Exp {
    def accept[E](v: SubExpAlg[E]): E
  }
}
