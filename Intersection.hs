{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module Intersection where

import Syntax
import Pretty

e1 = ELam (Typ PInt) (\x -> EVar x)
e2 = EAnd e1 e1
