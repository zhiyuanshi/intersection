say the example above:

(Int & Char) ((1 ,, 'c') : Int & Char)

without the cast, you could either get:
1,,'c'
or
1
depending on what rules you use

but I think with your change, you can only get the first

(which is what we want)

right?

let me see how we can get `1` before the change

(Int & Char) (1 : Int) ~> 1
----------------------------------------------
(Int & Char) ((1 ,, 'c') : Int & Char) ~> 1

i think that’s it

with the change, we need `Int <: Int & Char` to hold in order to get the line before the `—`, which is false

so it can be shown that `(Int & Char) ((1 ,, 'c') : Int & Char) ~> 1` is not derivable
