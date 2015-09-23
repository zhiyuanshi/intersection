fix = (f) ->
  x = () ->
    f(x)
  x()

compose = (trait1, trait2) ->
  (self) ->
    Object.assign({}, trait1(self), trait2(self))

Point = (x, y) ->
  (self) ->
    { x: () ->
        x
      y: () ->
        y
    }

EuclideanNorm = () ->
  (self) ->
    { norm: () ->
        Math.sqrt(self.x() * self.x() + self.y() * self.y())
    }

res = fix(compose(Point(3,4), EuclideanNorm())).norm()
