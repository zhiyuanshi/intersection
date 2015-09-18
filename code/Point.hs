module Store where

infixl #
o # m = m o

type Trait a = a -> a

new :: Trait a -> a
new f = let x = f x in x

data Store key value = Store {
  get :: key -> value,
  set :: key -> value -> Store key value
}

storeTrait :: Trait (Store String Int)
storeTrait self = Store {
  get = \_ -> 0,
  set = \k v -> self
}

main :: IO ()
main = do
  putStrLn "Hello"
