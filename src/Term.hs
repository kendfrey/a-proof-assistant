module Term (Term(..)) where

data Term
  = Var String Int
  | Type Int
  | Pi String Term Term
  | Lam String Term
  | App Term Term

instance Show Term where
  show (Var s _) = s
  show (Type n) = "Type" ++ show n
  show (Pi s a b) = "(" ++ s ++ " : " ++ show a ++ ") -> " ++ show b
  show (Lam s x) = "(\\" ++ s ++ ", " ++ show x ++ ")"
  show (App f x) = "(" ++ show f ++ " " ++ show x ++ ")"