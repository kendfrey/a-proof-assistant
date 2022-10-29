module Syntax (
  Preterm(..),
  Term(..),
  Env,
  Closure,
  RTerm(..),
  Irreducible(..),
  RTypeTerm(..),
  Def(..),
  Ctx(..),
  (|-),
  env,
  getLevel,
  getPi,
  getType,
  getVar,
  newVar,
  pushVar
  ) where

import Data.List (intercalate)

data Preterm
  = Var String Int
  | Hole
  | Type Int
  | Pi String Preterm Preterm
  | Lam String Preterm
  | App Preterm Preterm

instance Show Preterm where
  show (Var s _) = s
  show Hole = "?"
  show (Type n) = "Type" ++ show n
  show (Pi s a b) = "(" ++ s ++ " : " ++ show a ++ ") -> " ++ show b
  show (Lam s x) = "(\\" ++ s ++ ", " ++ show x ++ ")"
  show (App f x) = "(" ++ show f ++ " " ++ show x ++ ")"

data Term
  = TVar String Int
  | THole Int RTypeTerm
  | TType Int
  | TPi String Term Term
  | TLam String Term
  | TApp Term Term

instance Show Term where
  show (TVar s _) = s
  show (THole n _) = "?" ++ show n
  show (TType n) = "Type" ++ show n
  show (TPi s a b) = "(" ++ s ++ " : " ++ show a ++ ") -> " ++ show b
  show (TLam s x) = "(\\" ++ s ++ ", " ++ show x ++ ")"
  show (TApp f x) = "(" ++ show f ++ " " ++ show x ++ ")"

type Env = [RTerm]

type Closure = (String, Term, Env)

data RTerm
  = RIrreducible Irreducible RTypeTerm
  | RType Int
  | RPi RTypeTerm Closure
  | RLam Closure

instance Show RTerm where
  show (RIrreducible x _) = show x
  show (RType n) = "Type" ++ show n
  show (RPi a (s, b, _)) = "(" ++ s ++ " : " ++ show a ++ ") -> " ++ show b
  show (RLam (s, x, _)) = "(\\" ++ s ++ ", " ++ show x ++ ")"

data Irreducible
  = IVar String Int
  | IMVar Int
  | IApp Irreducible RTerm RTypeTerm

instance Show Irreducible where
  show (IVar s _) = s
  show (IMVar n) = "?" ++ show n
  show (IApp f x _) = "(" ++ show f ++ " " ++ show x ++ ")"

newtype RTypeTerm = Tp RTerm

instance Show RTypeTerm where
  show (Tp x) = show x

getLevel :: MonadFail m => RTypeTerm -> m Int
getLevel (Tp (RType n)) = return n
getLevel _ = fail "Type expected"

getPi :: MonadFail m => RTypeTerm -> m (RTypeTerm, Closure)
getPi (Tp (RPi a b)) = return (a, b)
getPi _ = fail "Function expected"

data Def = Def { defName :: String, defType :: RTypeTerm, defVal :: RTerm, defBound :: Bool }

newtype Ctx = Ctx { defs :: [Def] }

instance Show Ctx where
  show c = intercalate "\n" . map showDef . reverse $ defs c
    where
    showDef :: Def -> String
    showDef d = defName d ++ " : " ++ show (defType d) ++ " := " ++ show (defVal d)

(|-) :: Ctx -> Def -> Ctx
(Ctx ds) |- x = Ctx (x : ds)

env :: Ctx -> Env
env c = map defVal $ defs c

getVar :: MonadFail m => [a] -> Int -> m a
getVar [] _ = fail "Variable index out of range"
getVar (x : _) 0 = return x
getVar (_ : c) n | n > 0 = getVar c (n - 1)
                 | otherwise = fail "Negative variable index"

getType :: MonadFail m => Ctx -> Int -> m RTypeTerm
getType c n = defType <$> getVar (defs c) n

newVar :: String -> RTypeTerm -> Ctx -> RTerm
newVar s a c = RIrreducible (IVar s (length (defs c))) a

pushVar :: String -> RTypeTerm -> Ctx -> Ctx
pushVar s a c = c |- Def s a (newVar s a c) True