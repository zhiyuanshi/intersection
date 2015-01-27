object Decorator {
  // Library
  type Open[-S,-A,+B] = (=> S) => A => B
  type Base[-S,+A] = (=> S) => A

  def compose[S,A,B,C](f : Open[S,B,C], g : Open[S,A,B]) : Open[S,A,C] =
    self => parent => f(self)(g(self)(parent))

  def fix[S <: A,A](f : Open[S,A,S], s : Base[S,A]) : S = {lazy val r : S = f(r)(s(r)); r}

  // Client code
  // An initial Object & Interface
  trait O {
    def fact(x : Int) : Int
  }

  val base : Base[O,O] = s => new O {
    def fact(x : Int) = if (x == 0) 1 else x * s.fact(x-1)
  }

  // One Decorator & Interface
  trait Log extends O {
    def log(x : String) : Unit
  }

  val logI : Open[Log,O,Log] = s => p => new Log {
    def fact(x : Int) = {log("Entering fact!"); p.fact(x)}
    def log(x : String) = System.out.println(x)
  }

  // An instantiation of the object with the decorator
  val test : Log = fix(logI,base)

  // A 2nd decorator & interface
  trait Log2 extends O {
    def log2(x : String) : Unit // = System.out.println(x)
  }

  val logII : Open[Log2,O,Log2] = s => p => new Log2 {
    def fact(x : Int) = { val r = p.fact(x); log2("Exiting fact!"); r}
    def log2(x : String) = System.out.println(x)
  }

  // An object with the right interface: merged interfaces
  def lift(o : Open[Log with Log2, O, Log]) : Open[Log with Log2,O,Log with Log2] =
    s => p => new Log with Log2 {
      def fact(x : Int) = o(s)(p).fact(x)
      def log(x : String) = o(s)(p).log(x)
      def log2(x : String) = logII(s)(p).log2(x)
    }

  // A composed object with 2 decorators
  val test2 : Log with Log2 = fix(lift(compose(logI,logII)),base)
}
