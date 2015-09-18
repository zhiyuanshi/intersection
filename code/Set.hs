module Set where

data Set = Set {
  isEmpty  :: Bool,
  contains :: Int -> Bool,
  insert   :: Int -> Set,
  union    :: Set -> Set
}

empty :: Set
empty = Set {
  isEmpty  = True,
  contains = \_ -> False,
  insert   = \i -> ,
  union    = undefined
}
