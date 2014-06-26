module Spec where

import Test.Hspec

import Syntax
import Pretty

int = Typ PInt

int2int = Fun int int

intnint = And int int

main :: IO ()
main = hspec $ do
    describe "tvar" $ do
        it "n = 0"  $ tvar 0 `shouldBe` "A"
        it "n = 1"  $ tvar 1 `shouldBe` "B"
        it "n = 25" $ tvar 25 `shouldBe` "Z"
        it "n = 26" $ tvar 26 `shouldBe` "A1"

    describe "var" $ do
        it "n = 0"  $ var 0 `shouldBe` "a"
        it "n = 1"  $ var 1 `shouldBe` "b"
        it "n = 25" $ var 25 `shouldBe` "z"
        it "n = 26" $ var 26 `shouldBe` "a1"

    describe "pretty print types" $ do
        it "Int -> Int" $ prettyPrintPSigma (Typ int2int) `shouldBe` "Int -> Int"

        it "forall A. A" $ prettyPrintPSigma (Typ (Forall (\a -> Typ (Var a)))) `shouldBe` "forall A. A"

        it "forall A. forall B. A -> B -> A" $
            prettyPrintPSigma (Typ (Forall (\a -> Typ (Forall (\b -> 
                                Typ (Fun (Typ (Var a)) (Typ (Fun (Typ (Var b)) (Typ (Var a))))))))))
            `shouldBe` "forall A. forall B. A -> B -> A"

        it "forall A. forall B. (A -> B) -> A" $
            prettyPrintPSigma (Typ (Forall (\a -> Typ (Forall (\b -> 
                                Typ (Fun (Typ (Fun (Typ (Var a)) (Typ (Var b)))) (Typ (Var a))))))))
            `shouldBe` "forall A. forall B. (A -> B) -> A"

    describe "Right associativity of ->" $ do
        it "Int -> Int -> Int"   $ 
            prettyPrintPSigma (Typ (Fun int (Typ int2int))) 
            `shouldBe` "Int -> Int -> Int"

        it "(Int -> Int) -> Int" $ 
            prettyPrintPSigma (Typ (Fun (Typ int2int) int)) 
            `shouldBe` "(Int -> Int) -> Int"

    describe "Left associativity of &" $ do
        it "Int & Int & Int"   $ 
            prettyPrintPSigma (And intnint int) `shouldBe` "Int & Int & Int"

        it "Int & (Int & Int)" $ 
            prettyPrintPSigma (And int intnint) `shouldBe` "Int & (Int & Int)"

    describe "-> has higher precedence than &" $ do
        it "Int & Int -> Int"   $ prettyPrintPSigma (And int (Typ int2int)) `shouldBe` "Int & Int -> Int"

        it "(Int & Int) -> Int" $ prettyPrintPSigma (Typ (Fun intnint int)) `shouldBe` "(Int & Int) -> Int" 

        it "Int -> (Int & Int)" $ prettyPrintPSigma (Typ (Fun int intnint)) `shouldBe` "Int -> (Int & Int)"

        it "Int -> Int & Int"   $ prettyPrintPSigma (And (Typ int2int) int) `shouldBe` "Int -> Int & Int"

        it "Int -> Int & Int -> Int" $ 
            prettyPrintPSigma (And (Typ int2int) (Typ int2int)) `shouldBe` "Int -> Int & Int -> Int"

        it "(Int & Int) -> (Int & Int)" $ 
            prettyPrintPSigma (Typ (Fun intnint intnint)) `shouldBe` "(Int & Int) -> (Int & Int)"
