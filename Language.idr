module Language

import Box
import Parser

mutual
  data Expr : Type where
    EEmb : Term -> Expr
    Add : Expr -> Term -> Expr
    Sub : Expr -> Term -> Expr
  
  data Term : Type where
    TEmb : Factor -> Term
    Mul : Term -> Factor -> Term
    Div : Term -> Factor -> Term

  data Factor : Type where
    FEmb : Expr -> Factor
    Lit : Nat -> Factor

record Language (n : Nat) where
  constructor MkLanguage
  LExpr : Parser Expr n
  LTerm : Parser Term n
  LFactor : Parser Factor  n

language : Language i
language = fix Language $ \ rec =>
  let
    aop = Add <$ char '+'
    aos = Sub <$ char '-'
    addop =  aop <|> aos
    mom = Mul <$ char '*'
    mod = Div <$ char '/'
    mulop = mom <|> mod
    -- flit = Lit `Parser.map` decimal
    femb = FEmb `Parser.map` parens (map LExpr rec)
    -- factor = femb <|> flit
    -- term = hchainl (TEmb <$> factor) (box mulop) (box factor)
    -- expr = hchainl (EEmb <$> term) (box addop) (box term)
  in ?hole --MkLanguage expr term factor
