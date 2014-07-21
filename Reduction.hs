{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Reduction where

import Syntax

eval :: PExp Int (PSigma Int) -> Int -> Maybe (PExp Int (PSigma Int))
eval (EApp e1@(ELam s f) e2) i =
    do s1 <- tcheck e1 i
       s2 <- tcheck e2 i
       case s1 of
         Typ (Fun s3 _s4) | subSigma s2 s3 i -> Just $ substExp i e2 (f s)
         _                                   -> Nothing
eval (ETApp e1@(ETLam _f) _s) i =
    do s1 <- tcheck e1 i
       case s1 of
         Typ (Forall _g) -> Just e1   -- TODO
         _               -> Nothing
eval e _i = Just e
