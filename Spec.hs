module Spec where

import Test.Hspec

import Syntax
import Pretty

int = Typ PInt
int2int = Fun int int
intnint = And int int

var = Typ . Var
forall = Typ . Forall
(.->.) o1 o2 = Typ (Fun o1 o2)
(.&&.) = And

main :: IO ()
main = hspec $ do
    describe "tvar" $ do
        it "n = 0"  $ uident 0 `shouldBe` "A"
        it "n = 1"  $ uident 1 `shouldBe` "B"
        it "n = 25" $ uident 25 `shouldBe` "Z"
        it "n = 26" $ uident 26 `shouldBe` "A1"

    describe "var" $ do
        it "n = 0"  $ lident 0 `shouldBe` "a"
        it "n = 1"  $ lident 1 `shouldBe` "b"
        it "n = 25" $ lident 25 `shouldBe` "z"
        it "n = 26" $ lident 26 `shouldBe` "a1"

    describe "pretty print types" $ do
        it "Int -> Int" $ prettyPrintPSigma (Typ int2int) `shouldBe` "Int -> Int"
        it "forall A. A" $ prettyPrintPSigma (forall (\a -> var a)) `shouldBe` "forall A. A"

        it "forall A. forall B. A -> B -> A" $
            prettyPrintPSigma (forall (\a -> forall (\b -> var a .->. (var b .->. var a))))
            `shouldBe` "forall A. forall B. A -> B -> A"

        it "forall A. forall B. (A -> B) -> A" $
            prettyPrintPSigma (forall (\a -> forall (\b -> (var a .->. var b) .->. var a)))
            `shouldBe` "forall A. forall B. (A -> B) -> A"

    describe "Right associativity of ->" $ do
        it "Int -> Int -> Int"   $ prettyPrintPSigma (int .->. Typ int2int) `shouldBe` "Int -> Int -> Int"
        it "(Int -> Int) -> Int" $ prettyPrintPSigma (Typ int2int .->. int) `shouldBe` "(Int -> Int) -> Int"

    describe "Left associativity of &" $ do
        it "Int & Int & Int"   $ prettyPrintPSigma (intnint .&&. int) `shouldBe` "Int & Int & Int"
        it "Int & (Int & Int)" $ prettyPrintPSigma (int .&&. intnint) `shouldBe` "Int & (Int & Int)"

    describe "-> has higher precedence than &" $ do
        it "Int & Int -> Int"   $ prettyPrintPSigma (int .&&. (Typ int2int)) `shouldBe` "Int & Int -> Int"
        it "(Int & Int) -> Int" $ prettyPrintPSigma (intnint .->. int) `shouldBe` "(Int & Int) -> Int" 
        it "Int -> (Int & Int)" $ prettyPrintPSigma (int .->. intnint) `shouldBe` "Int -> (Int & Int)"
        it "Int -> Int & Int"   $ prettyPrintPSigma (Typ int2int .&&. int) `shouldBe` "Int -> Int & Int"

        it "Int -> Int & Int -> Int" $ 
            prettyPrintPSigma (Typ int2int .&&. Typ int2int) `shouldBe` "Int -> Int & Int -> Int"

        it "(Int & Int) -> (Int & Int)" $ 
            prettyPrintPSigma (intnint .->. intnint) `shouldBe` "(Int & Int) -> (Int & Int)"

    describe "Subtyping" $ do
        it "Int <: Int" $ sub int int
        it "Int <: Int & Int" $ sub int intnint
        it "Int & Int <: Int" $ sub intnint int
        it "Int & Int <: Int & Int" $ sub intnint intnint
        it "Int -> Int <: Int -> Int" $ sub (Typ int2int) (Typ int2int)
        it "Int </: Int -> Int" $ not $ sub int (Typ int2int)
        it "Int -> Int </: Int" $ not $ sub (Typ int2int) int 
        it "forall A. Int & Int <: forall A. Int & Int" $ sub (forall (\_ -> intnint)) (forall (\_ -> intnint))
        it "forall A. A <: forall A. A" $ sub (forall (\a -> var a)) (forall (\a -> var a))
        it "forall A. Int </: forall A. A" $ not $ sub (forall (\_ -> int)) (forall (\a -> var a))
        it "forall A. A </: forall A. Int" $ not $ sub (forall (\a -> var a)) (forall (\_ -> int))

        it "forall A. Int & A <: forall A. A & Int" $ 
            sub (forall (\a -> int .&&. var a)) (forall (\a -> var a .&&. int))

        it "forall A. forall B. A & B <: forall A. forall B. B & A" $ 
            sub (forall (\a -> forall (\b -> var a .&&. var b))) (forall (\a -> forall (\b -> var b .&&. var a)))

        it "forall A. forall B. A & B <: forall A. forall B. A" $ 
            sub (forall (\a -> forall (\b -> var a .&&. var b))) (forall (\a -> forall (\_ -> var a)))

        it "forall A. forall B. A </: forall A. forall B. A & B" $ 
            not $ sub (forall (\a -> forall (\_ -> var a))) (forall (\a -> forall (\b -> var a .&&. var b)))
