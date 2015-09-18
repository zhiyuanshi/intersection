object Mixins {
  // Example that shows mixin composition without conflicts
  // Encode the traits with records
  trait A {
    def m1() : Int
  }

  trait B {
    def m2() : Int
    def m3() : Int
  }

  // Simulating the merge: In our language merge should do this automatically
  def merge(x : (=> A) => A, y : (=> B) => B) : (=> A with B) => A with B = s => new A with B {
    def m1() : Int = x(s).m1()
    def m2() : Int = y(s).m2()
    def m3() : Int = y(s).m3()
  }

// trait anA : A = {m1 = 1}
  val anA : (=> A) => A = s => new A {
    def m1() = 1
  }

// trait anB : B = {m2 = 0, m3 = this.m2}
// trait x : T = e --> let x : (() -> T) -> T = e [this |-> this()]
  val anB : (=> B with A) => B = s => new B {
    //def m2() = 0
    def m3() = s.m1() //this()
  }

  val composedTrait : (=> B with A) => B with A = s => merge(anA,anB)(s)

  def test : A with B = merge(anA,anB)(test) // wiring the self references
  // let test = anA(test) ,, anB(test)
  // let test = new (anA,,andB) -- possible syntax!
}
