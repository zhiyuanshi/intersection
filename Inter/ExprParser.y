{
module Inter.ExprParser (readExpr) where

import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

import Inter.Syntax
import Inter.Lexer    (lexExpr, Token(..))
}

%name parseExpr
%tokentype { Token }
%monad     { P }
%error     { parseError }

%token

  "("      { Toparen }
  ")"      { Tcparen }
  "/\\"    { Ttlam }
  "\\"     { Tlam }
  ":"      { Tcolon }
  "forall" { Tforall }
  "->"     { Tarrow }
  "."      { Tdot }
  "Int"    { Tinttype }
  ",,"     { Tmerge }
  UPPERID  { Tupperid $$ }
  LOWERID  { Tlowerid $$ }
  INTEGER  { Tinteger $$ }

%%

expr
    : "/\\" tvar "." expr         { \(tmap, emap) -> TLam (\a -> $4 (Map.insert $2 a tmap, emap)) }
    | "\\" var_with_typ "." expr  { \(tmap, emap) -> Lam ((snd $2) tmap) (\x -> $4 (tmap, Map.insert (fst $2) x emap)) }
    | fexp                        { $1 }

fexp
    : fexp aexp         { \m -> App ($1 m) ($2 m) }
    | fexp ",," aexp    { \m -> Merge ($1 m) ($3 m) }
    | fexp typ          { \m@(tmap, emap) -> TApp ($1 m) ($2 tmap) }
    | aexp              { $1 }

aexp
    : var           { \(tmap, emap) -> Var $ fromMaybe (error $ "Unbound variable: `" ++ $1 ++ "'") (Map.lookup $1 emap) }
    | INTEGER       { \(tmap, emap) -> Lit $1 }
    | "(" expr ")"  { $2 }

typ
    : "forall" tvar "." typ  { \tmap -> Forall (\a -> $4 (Map.insert $2 a tmap)) }
    | atyp "->" typ          { \tmap -> Fun ($1 tmap) ($3 tmap) }
    | atyp                   { $1 }

atyp
    : tvar         { \tmap -> TVar $ fromMaybe (error $ "Unbound variable: `" ++ $1 ++ "'") (Map.lookup $1 tmap) }
    | "Int"        { \tmap -> Int }
    | "(" typ ")"  { $2 }

var_with_typ
    : "(" var ":" typ ")"  { ($2, $4) }

var :: { String }
    : LOWERID  { $1 }

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

readExpr :: String -> Expr t e
readExpr src =
  case (parseExpr . lexExpr) src of
    POk expr   -> expr (Map.empty, Map.empty)
    PError msg -> error msg
}
