{
module Inter.TypeParser (readType) where

import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

import Inter.Syntax
import Inter.Lexer    (lexExpr, Token(..))
}

%name parseType
%tokentype { Token }
%monad     { P }
%error     { parseError }

%token

  "("      { Toparen }
  ")"      { Tcparen }
  "forall" { Tforall }
  "->"     { Tarrow }
  "."      { Tdot }
  "Int"    { Tinttype }
  UPPERID  { Tupperid $$ }

%%

typ
    : "forall" tvar "." typ  { \tmap -> Forall (\a -> $4 (Map.insert $2 a tmap)) }
    | atyp "->" typ          { \tmap -> Fun ($1 tmap) ($3 tmap) }
    | atyp                   { $1 }

atyp
    : tvar         { \tmap -> TVar $ fromMaybe (error $ "Unbound variable: `" ++ $1 ++ "'") (Map.lookup $1 tmap) }
    | "Int"        { \tmap -> Int }
    | "(" typ ")"  { $2 }

tvar :: { String }
    : UPPERID  { $1 }

{
data P a = POk a | PError String

instance Monad P where
    POk x      >>= f = f x
    PError msg >>= f = PError msg
    return x         = POk x

parseError :: [Token] -> P a
parseError tokens = PError ("Parse error before tokens:\n\t" ++ show tokens)

readType :: String -> Type t
readType src =
  case (parseType . lexExpr) src of
    POk typ    -> typ (Map.empty)
    PError msg -> error msg
}
