fix = (f) ->
  x = () ->
    f x
  x()

compose = (trait1, trait2) ->
  (self) ->
    Object.assign({}, trait1(self), trait2(self))

Counter = (val) ->
  (self) ->
    { val: () ->
     		val
      incr: () ->
        fix(Counter(val + 1))
    }

Reset = () ->
  (self) ->
    { reset: () ->
        fix(compose(Counter(0), Reset()))
    }

c1 = fix(Counter(0))
c2 = fix(compose(Counter(0), Reset()))
