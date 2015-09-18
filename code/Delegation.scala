object DelegationMixins {
  import scala.collection.mutable.HashMap

  /* type of open components: that is components which can be advised with additional behaviour
   * Note: The self/proceed argument (=> A) needs to be lazily evaluated. That's what the annotation "=>" before
   * the A indicates. */
  type Open[A] = (=> A) => A

  /* Weaving/Closing open components -- this is a fixpoint combinator */
  def weave[A](c : Open[A]) : A = {lazy val r : A = c(r); r}

  def weave2[A](c : Open[A]) : A = {
    var r : A = null.asInstanceOf[A];
    r = c(r)
    r
  }

  /* advising open components -- this is just function composition */
  def compose[A](f : Open[A], g : Open[A]) : Open[A] = x => f(g(x))

  /* Fibonacci */
  def fib : Open[Int => Int] = fib /*This is the self/proceed argument, like "this" in an OO language */  => {
    case 0 => 0
    case 1 => 1
    case n => fib.apply(n-1) + fib.apply(n-2) /* Scala protests if I write: fib(n-1) + fib (n-2), though this should work */
  }

  /* Some advice */

  /* Tracing */
  def trace[A] : Open[A => A] = proceed => x => {
    println("Entering function with argument " + x)
    proceed.apply(x)
  }

  /* Memoization */
  class Memo(proceed : Int => Int) extends (Int => Int) {
    val cache : HashMap[Int,Int] = new HashMap[Int,Int]

    def apply(n : Int) : Int =
      cache.get(n) match {
        case Some(v) => v
        case None => {val r = proceed(n); cache.put(n,r); r}
      }
  }

  def memo : Open[Int => Int] = proceed => new Memo(proceed)

  /* Memoization */

  /* This is the good old recursive definition of fib */
  def slowFib = weave(fib)

  /* This is a traced version of fib */
  def traceFib = weave[Int => Int](compose(trace,fib))

  /* This is a memoized version of fib */
  def fastFib = weave[Int => Int](compose(memo,fib))

  /* Two variations of traced/memoized versions of fib */
  def tmfib = weave[Int => Int](compose(trace,compose(memo,fib)))
  def mtfib = weave[Int => Int](compose(memo,compose(trace,fib)))

  /* Using Mixins on interfaces/classes instead of just functions */
  trait EvenOdd {
    def even(n : Int) : Boolean
    def odd(n : Int) : Boolean
  }

  class EvenOddImpl(proceed : => EvenOdd) extends EvenOdd {
    def even(n : Int) : Boolean = if (n==0) true else proceed.odd(n-1)
    def odd(n : Int) : Boolean = if (n==0) false else proceed.even(n-1)
  }

  class TraceEvenOdd(proceed : => EvenOdd) extends EvenOdd {
    def even(n : Int) : Boolean = {println("Entering even with arg " + n); proceed.even(n)}
    def odd(n : Int) : Boolean = {println("Entering odd with arg " + n); proceed.odd(n)}
  }

  def evenOdd : Open[EvenOdd] = proceed => new EvenOddImpl(proceed)
  def traceEvenOdd : Open[EvenOdd] = proceed => new TraceEvenOdd(proceed)

  def tracedEO = weave[EvenOdd](compose(traceEvenOdd,evenOdd))
  def tracedEO2 = weave2[EvenOdd](compose(traceEvenOdd,evenOdd))

  def main(args: Array[String]) {
    println("**** Slow Fib ****")
    println(slowFib(10))
    println("**** Traced Fib ****")
    println(traceFib(10))
    println("**** Fast Fib ****")
    println(fastFib(10))
    println("**** Traced Memoized Fib ****")
    println(tmfib(10))
    println("**** Memoized Traced Fib ****")
    println(mtfib(10))

    println("**** Advising classes ****")
    println("**** Even 10? ****")
    println(tracedEO.even(10))
    println("**** Odd 10? ****")
    println(tracedEO.odd(10))

    println("**** Mutable Even 10? ****")
    println(tracedEO2.even(2))
  }
}