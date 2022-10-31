module Syntax (
  Preterm(..),
  Quotable(..),
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
  getVar,
  lookupVar,
  newVar,
  pushVar
  ) where

import Data.List (intercalate)

data Preterm
  = Var String
  | Hole
  | Type Int
  | Pi String Preterm Preterm
  | Lam String Preterm
  | App Preterm Preterm

data Precedence
  = PZero
  | PApp
  | PPi
  | PLam
  deriving (Eq, Ord, Bounded, Enum)

instance Show Preterm where
  show = showPreterm maxBound
    where
    showPreterm :: Precedence -> Preterm -> String
    showPreterm _ (Var s) = s
    showPreterm _ Hole = "?"
    showPreterm _ (Type n) = "Type" ++ show n
    showPreterm p (Pi "_" a b) = parens p PPi $ showPreterm (pred PPi) a ++ " -> " ++ showPreterm PPi b
    showPreterm p (Pi s a b) = parens p PPi $ "(" ++ s ++ " : " ++ showPreterm maxBound a ++ ") -> " ++ showPreterm PPi b
    showPreterm p (Lam s x) = parens p PLam $ s ++ " => " ++ showPreterm PLam x
    showPreterm p (App f x) = parens p PApp $ showPreterm PApp f ++ " " ++ showPreterm (pred PApp) x
    parens :: Precedence -> Precedence -> String -> String
    parens p pmin s | p >= pmin = s
                    | otherwise = "(" ++ s ++ ")"

class Quotable a where
  quote :: a -> Preterm

data Term
  = TVar String Int
  | THole Int RTypeTerm
  | TType Int
  | TPi String Term Term
  | TLam String Term
  | TApp Term Term

instance Quotable Term where
  quote (TVar s _) = Var s
  quote (THole _ _) = Hole
  quote (TType n) = Type n
  quote (TPi s a b) = Pi s (quote a) (quote b)
  quote (TLam s x) = Lam s (quote x)
  quote (TApp f x) = App (quote f) (quote x)

type Env = [RTerm]

type Closure = (String, Term, Env)

data RTerm
  = RIrreducible Irreducible RTypeTerm
  | RType Int
  | RPi RTypeTerm Closure
  | RLam Closure

instance Quotable RTerm where
  quote (RIrreducible x _) = quote x
  quote (RType n) = Type n
  quote (RPi (Tp a) (s, b, _)) = Pi s (quote a) (quote b)
  quote (RLam (s, x, _)) = Lam s (quote x)

data Irreducible
  = IVar String Int
  | IMVar Int
  | IApp Irreducible RTerm RTypeTerm

instance Quotable Irreducible where
  quote (IVar s _) = Var s
  quote (IMVar _) = Hole
  quote (IApp f x _) = App (quote f) (quote x)

newtype RTypeTerm = Tp RTerm

instance Quotable RTypeTerm where
  quote (Tp x) = quote x

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
    showDef d = defName d ++ " : " ++ show (quote (defType d)) ++ " := " ++ show (quote (defVal d))

(|-) :: Ctx -> Def -> Ctx
(Ctx ds) |- x = Ctx (x : ds)

env :: Ctx -> Env
env c = map defVal $ defs c

getVar :: MonadFail m => [a] -> Int -> m a
getVar [] _ = fail "Variable index out of range"
getVar (x : _) 0 = return x
getVar (_ : c) n | n > 0 = getVar c (n - 1)
                 | otherwise = fail "Negative variable index"

lookupVar :: MonadFail m => Ctx -> String -> m (Def, Int)
lookupVar c s = lookupVar' (defs c) 0
  where
  lookupVar' :: MonadFail m => [Def] -> Int -> m (Def, Int)
  lookupVar' [] _ = fail ("Variable " ++ s ++ " is not defined")
  lookupVar' (d : ds) n | defName d == s = return (d, n)
                        | otherwise = lookupVar' ds (n + 1)

newVar :: String -> RTypeTerm -> Ctx -> RTerm
newVar s a c = RIrreducible (IVar s (length (defs c))) a

pushVar :: String -> RTypeTerm -> Ctx -> Ctx
pushVar s a c = c |- Def s a (newVar s a c) True