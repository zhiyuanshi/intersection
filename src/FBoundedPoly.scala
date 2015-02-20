def getName[A <: { def name: String }](v: A) = v.name

case class Person(name: String)

getName[Person](Person("Ek"))

