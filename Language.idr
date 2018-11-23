module Language

import TypeOperators
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

parens : All (Box (Parser a) :-> Parser a)
parens pa = char '(' &> pa <& box (char ')')

language : All (Language)
language = fix Language $ \ rec =>
    let
      aop = Add <$ char '+'
      aos = Sub <$ char '-'
      addop = aop <|> aos
      mom = Mul <$ char '*'
      mod = Div <$ char '/'
      mulop = mom <|> mod
      parexpr = parens (pexpr rec)
      flit = Lit <$> decimal
      femb = map FEmb parexpr
      factor = femb <|> flit
      term = hchainl (TEmb <$> factor) (box mulop) (box factor)
      expr = hchainl (EEmb <$> term) (box addop) (box term)
    in MkLanguage expr term factor
  where
    pexpr : All(Box (Language) :-> Box (Parser Expr))
    pexpr bl = MkBox (\lt => LExpr $ call bl lt)
 
