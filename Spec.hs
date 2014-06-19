module Spec where

import Test.Hspec

import Syntax
import Pretty

-- Int & Int
t1 = And (Typ PInt) (Typ PInt)

-- Int
t2 = Typ PInt

-- Int & (Int -> Int)
t3 = And (Typ PInt) t4

-- Int -> Int
t4 = Typ (Fun (Typ PInt) (Typ PInt))

-- forall a . a -> a 
t5 = Typ (Forall (\a -> Typ (Fun (Typ (Var a)) (Typ (Var a)))))

-- forall a . Int & a -> a
t6 = Typ (Forall (\a -> Typ (Fun (And (Typ PInt) (Typ (Var a))) (Typ (Var a)))))

-- (Int -> Int) & Int
t7 = And t4 (Typ PInt)

main :: IO ()
main = hspec $ do
    describe "alpha" $ do
        it "n = 0" $
            alpha 0 `shouldBe` "a"
        it "n = 1" $
            alpha 1 `shouldBe` "b"
        it "n = 25" $
            alpha 25 `shouldBe` "z"
        it "n = 26" $
            alpha 26 `shouldBe` "a0"
    
    describe "pretty print types" $ do
        it "forall a. a" $
            prettyPrintPSigma (Typ (Forall (\a -> Typ (Var a)))) `shouldBe` "forall a. a"
        it "forall a. forall b. a -> b -> a" $
            prettyPrintPSigma (Typ (Forall (\a -> Typ (Forall (\b -> 
                                Typ (Fun (Typ (Var a)) (Typ (Fun (Typ (Var b)) (Typ (Var a))))))))))
                `shouldBe` "forall a. forall b. a -> b -> a"
        it "forall a. forall b. (a -> b) -> a" $
            prettyPrintPSigma (Typ (Forall (\a -> Typ (Forall (\b -> 
                                Typ (Fun (Typ (Fun (Typ (Var a)) (Typ (Var b)))) (Typ (Var a))))))))
                `shouldBe` "forall a. forall b. (a -> b) -> a"
        it "Int" $
            prettyPrintPSigma (Typ PInt) `shouldBe` "Int"

        it "Int & Int" $
            prettyPrintPSigma t1 `shouldBe` "Int & Int"

        it "Int" $
            prettyPrintPSigma t2 `shouldBe` "Int"

        it "Int & (Int -> Int)" $
            prettyPrintPSigma t3 `shouldBe` "Int & (Int -> Int)"

        it "Int -> Int" $
            prettyPrintPSigma t4 `shouldBe` "Int -> Int"

        it "(Int -> Int) & Int" $
            prettyPrintPSigma t7 `shouldBe` "(Int -> Int) & Int"

        it "Int & Int & Int" $
            prettyPrintPSigma (And (And (Typ PInt) (Typ PInt)) (Typ PInt)) `shouldBe` "Int & Int & Int"

        it "Int & (Int & Int)" $
            prettyPrintPSigma (And (Typ PInt) (And (Typ PInt) (Typ PInt))) `shouldBe` "Int & (Int & Int)"
