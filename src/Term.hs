module Term (Term(..)) where

data Term
  = Var Int
  | Type Int
  | Pi Term Term
  | Lam Term Term
  | App Term Term
  deriving (Show)