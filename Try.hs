{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module Try where

import Data.Maybe

import Language.Inter.Syntax
import Language.Inter.TypeCheck
import Language.Inter.Reduction
import Language.Inter.Parser    (readExpr)
import Language.Inter.Pretty

t = infer_exn

t_int_to_int = Int `Fun` Int

-- \(x : Int). x
-- Int -> Int
idInt = Lam Int (\x -> Var x)

{- equality -}

-- 1 ,, ((\x : Int). x)
lit_and_id = Lit 1 `Merge` idInt

-- ((\x : Int). x) ,, 2
id_and_lit = idInt `Merge` Lit 2

{- subtype -}

-- lit_to_and <: and_to_lit

-- \(x : Int). (x ,, (\(x : Int). x))
lit_to_and = Lam Int (\x -> Var x `Merge` idInt)

-- \(f : (Int -> Int) & Int). 1
and_to_lit = Lam (t_int_to_int `And` Int) (\x -> Lit 1)

{- not related -}

-- (Int & (Int -> Int)) -> ((Int -> Int) & Int)
and_to_and = Lam (Int `And` t_int_to_int) (\x -> id_and_lit)

int_to_int = idInt

-- (\(x : Int). x) ((\(x : Int). x) ,, 2)
app = idInt `App` id_and_lit

-- 3 ,, 4
intPair = Lit 3 `Merge` Lit 4
