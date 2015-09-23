object EvenOdd {
  trait Even { self: Even with Odd =>
    def even(n: Int): Boolean = if (n == 0) true else self.odd(n - 1)
  }

  trait Odd { self: Even with Odd =>
    def odd(n: Int): Boolean = if (n == 0) false else self.even(n - 1)
  }

  def main(args: Array[String]) {
    val eo = new Even with Odd
    println(eo.odd(42))
    println(eo.odd(7))
  }
}
