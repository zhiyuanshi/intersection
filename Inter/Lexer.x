{
{-# OPTIONS_GHC
      -fno-warn-missing-signatures
      -fno-warn-unused-matches
      -fno-warn-unused-binds
      -fno-warn-name-shadowing
      #-}
module Inter.Lexer
  ( lexExpr
    , Token(..)
  ) where
}

%wrapper "posn"

$alpha = [A-Za-z]
$digit = [0-9]

tokens :-

  $white+     ;
  "#".*       ;
  "--".*      ;
  "//".*      ;

  \(          { \_ _ -> Toparen }
  \)          { \_ _ -> Tcparen }
  \/\\        { \_ _ -> Ttlam }
  \\          { \_ _ -> Tlam }
  \:          { \_ _ -> Tcolon }
  forall      { \_ _ -> Tforall }
  \-\>        { \_ _ -> Tarrow }
  \.          { \_ _ -> Tdot }
  Int         { \_ _ -> Tinttype }
  \,\,        { \_ _ -> Tmerge }

  [A-Z] [$alpha $digit \_ \']*  { \_ s -> Tupperid s }
  [a-z] [$alpha $digit \_ \']*  { \_ s -> Tlowerid s }
  \-? $digit+                   { \_ s -> Tinteger (read s) }

{
data Token = Toparen | Tcparen
           | Ttlam | Tlam | Tcolon | Tforall | Tarrow | Tdot
           | Tinttype
           | Tmerge
           | Tupperid String | Tlowerid String
           | Tinteger Integer
           deriving (Eq, Show)

lexExpr :: String -> [Token]
lexExpr = alexScanTokens
}
