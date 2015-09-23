fix = (f) ->
  x = ->
    f x
  x()

compose = (trait1, trait2) ->
  (self) ->
    Object.assign {}, trait1(self), trait2(self)

Even = ->
  (self) ->
    even: (n) ->
      if n is 0
        true
      else
        self.odd n - 1

Odd = ->
  (self) ->
    odd: (n) ->
      if n is 0
        false
      else
        self.even n - 1

res = fix(compose(Even(), Odd()))
