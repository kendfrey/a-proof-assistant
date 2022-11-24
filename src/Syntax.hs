module Syntax (
  module Level,
  module VarNames,
  Preterm(..),
  var,
  fun,
  lam,
  Quotable(..),
  Term(..),
  Env,
  Closure,
  RTerm(..),
  Irreducible(..),
  RTypeTerm(..),
  TopLevelDef(..),
  Def(..),
  Ctx(..),
  (|-),
  env,
  getLevel,
  getPi,
  getVar,
  lookupVar,
  newVar,
  pushVar,
  substLevels
  ) where

import Data.List (intercalate)
import Data.Map (empty, foldrWithKey)
import Level
import VarNames

data Preterm
  = Var String [Level]
  | Hole
  | Pi String Preterm Preterm
  | Lam String Preterm
  | App Preterm Preterm

var :: String -> Preterm
var s = Var s []

fun :: Preterm -> Preterm -> Preterm
fun a b = Pi "_" a b

lam :: Preterm -> Preterm
lam x = Lam "_" x

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
    showPreterm _ (Var s []) = s
    showPreterm _ (Var s u) = s ++ "[" ++ intercalate ", " (map show u) ++ "]"
    showPreterm _ Hole = "?"
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
  = TVar String [RLevel] Int
  | THole Int RTypeTerm
  | TType RLevel
  | TPi String Term Term
  | TLam String Term
  | TApp Term Term
  | TEq RLevel Term Term Term
  | TRefl RLevel Term Term
  | TEqElim RLevel RLevel Term Term Term Term Term Term
  | TEmpty
  | TEmptyElim RLevel Term Term
  | TUnit
  | TStar
  | TBool
  | TTrue
  | TFalse
  | TBoolElim RLevel Term Term Term Term

instance Quotable Term where
  quote (TVar s u _) = Var s (map quoteLevel u)
  quote (THole _ _) = Hole
  quote (TType n) = Var vType [quoteLevel n]
  quote (TPi s a b) = Pi s (quote a) (quote b)
  quote (TLam s x) = Lam s (quote x)
  quote (TApp f x) = App (quote f) (quote x)
  quote (TEq u a x y) = App (App (App (Var vEq [quoteLevel u]) (quote a)) (quote x)) (quote y)
  quote (TRefl u a x) = App (App (Var vRefl [quoteLevel u]) (quote a)) (quote x)
  quote (TEqElim u v a p r x y h) = App (App (App (App (App (App (Var vEqElim [quoteLevel u, quoteLevel v]) (quote a)) (quote p)) (quote r)) (quote x)) (quote y)) (quote h)
  quote TEmpty = var vEmpty
  quote (TEmptyElim u a x) = App (App (Var vEmptyElim [quoteLevel u]) (quote a)) (quote x)
  quote TUnit = var vUnit
  quote TStar = var vStar
  quote TBool = var vBool
  quote TTrue = var vTrue
  quote TFalse = var vFalse
  quote (TBoolElim u a t f x) = App (App (App (App (Var vBoolElim [quoteLevel u]) (quote a)) (quote t)) (quote f)) (quote x)

type Env = [(RTerm, Maybe Int)]

type Closure = (String, Term, Env)

data RTerm
  = RIrreducible Irreducible RTypeTerm
  | RType RLevel
  | RPi RTypeTerm Closure
  | RLam Closure
  | REq RLevel RTypeTerm RTerm RTerm
  | RRefl RLevel RTypeTerm RTerm
  | REmpty
  | RUnit
  | RStar
  | RBool
  | RTrue
  | RFalse

instance Quotable RTerm where
  quote (RIrreducible x _) = quote x
  quote (RType n) = Var vType [quoteLevel n]
  quote (RPi (Tp a) (s, b, _)) = Pi s (quote a) (quote b)
  quote (RLam (s, x, _)) = Lam s (quote x)
  quote (REq u a x y) = App (App (App (Var vEq [quoteLevel u]) (quote a)) (quote x)) (quote y)
  quote (RRefl u a x) = App (App (Var vRefl [quoteLevel u]) (quote a)) (quote x)
  quote REmpty = var vEmpty
  quote RUnit = var vUnit
  quote RStar = var vStar
  quote RBool = var vBool
  quote RTrue = var vTrue
  quote RFalse = var vFalse

data Irreducible
  = IVar String [RLevel] Int
  | IMVar Int
  | IApp Irreducible RTerm RTypeTerm
  | IEqElim RLevel RLevel RTypeTerm RTerm RTerm RTerm RTerm Irreducible
  | IEmptyElim RLevel RTerm Irreducible
  | IBoolElim RLevel RTerm RTerm RTerm Irreducible

instance Quotable Irreducible where
  quote (IVar s u _) = Var s (map quoteLevel u)
  quote (IMVar _) = Hole
  quote (IApp f x _) = App (quote f) (quote x)
  quote (IEqElim u v a p r x y h) = App (App (App (App (App (App (Var vEqElim [quoteLevel u, quoteLevel v]) (quote a)) (quote p)) (quote r)) (quote x)) (quote y)) (quote h)
  quote (IEmptyElim u a x) = App (App (Var vEmptyElim [quoteLevel u]) (quote a)) (quote x)
  quote (IBoolElim u a t f x) = App (App (App (App (Var vBoolElim [quoteLevel u]) (quote a)) (quote t)) (quote f)) (quote x)

newtype RTypeTerm = Tp { tpTerm :: RTerm }

instance Quotable RTypeTerm where
  quote (Tp x) = quote x

getLevel :: MonadFail m => RTypeTerm -> m RLevel
getLevel (Tp (RType n)) = return n
getLevel _ = fail "Type expected"

getPi :: MonadFail m => RTypeTerm -> m (RTypeTerm, Closure)
getPi (Tp (RPi a b)) = return (a, b)
getPi _ = fail "Function expected"

data TopLevelDef = TLDef { universeVars :: Int, isPrimitive :: Bool }

data Def = Def { defName :: String, defType :: RTypeTerm, defVal :: RTerm, defTopLevel :: Maybe TopLevelDef }

newtype Ctx = Ctx { defs :: [Def] }

instance Show Ctx where
  show c = intercalate "\n" . map showDef . filter (any (not . isPrimitive) . defTopLevel) . reverse $ defs c
    where
    showDef :: Def -> String
    showDef d = defName d ++ " : " ++ show (quote (defType d)) ++ " := " ++ show (quote (defVal d))

(|-) :: Ctx -> Def -> Ctx
(Ctx ds) |- x = Ctx (x : ds)

env :: Ctx -> Env
env c = map envVar $ defs c
  where
  envVar :: Def -> (RTerm, Maybe Int)
  envVar d = (defVal d, universeVars <$> defTopLevel d)

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
newVar s a c = RIrreducible (IVar s [] (length (defs c))) a

pushVar :: String -> RTypeTerm -> Ctx -> Ctx
pushVar s a c = c |- Def s a (newVar s a c) Nothing

substLevels :: MonadFail m => [RLevel] -> RTerm -> Int -> m RTerm
substLevels [] x 0 = return x
substLevels u _x _n | length u == _n = return $ substLevelsRT _x
                    | otherwise = fail "Wrong number of levels"
  where
  substLevelsRT :: RTerm -> RTerm
  substLevelsRT (RIrreducible x (Tp a)) = RIrreducible (substLevelsIrr x) (Tp (substLevelsRT a))
  substLevelsRT (RType n) = RType (subst n)
  substLevelsRT (RPi (Tp a) (s, b, e)) = RPi (Tp (substLevelsRT a)) (s, substLevelsT b, map substLevelsEnv e)
  substLevelsRT (RLam (s, x, e)) = RLam (s, substLevelsT x, map substLevelsEnv e)
  substLevelsRT (REq v (Tp a) x y) = REq (subst v) (Tp (substLevelsRT a)) (substLevelsRT x) (substLevelsRT y)
  substLevelsRT (RRefl v (Tp a) x) = RRefl (subst v) (Tp (substLevelsRT a)) (substLevelsRT x)
  substLevelsRT REmpty = REmpty
  substLevelsRT RUnit = RUnit
  substLevelsRT RStar = RStar
  substLevelsRT RBool = RBool
  substLevelsRT RTrue = RTrue
  substLevelsRT RFalse = RFalse
  substLevelsIrr :: Irreducible -> Irreducible
  substLevelsIrr (IVar s v n) = IVar s (map subst v) n
  substLevelsIrr (IMVar n) = IMVar n
  substLevelsIrr (IApp f x (Tp a)) = IApp (substLevelsIrr f) (substLevelsRT x) (Tp (substLevelsRT a))
  substLevelsIrr (IEqElim v w (Tp a) p r x y h) = IEqElim (subst v) (subst w) (Tp (substLevelsRT a)) (substLevelsRT p) (substLevelsRT r) (substLevelsRT x) (substLevelsRT y) (substLevelsIrr h)
  substLevelsIrr (IEmptyElim v a x) = IEmptyElim (subst v) (substLevelsRT a) (substLevelsIrr x)
  substLevelsIrr (IBoolElim v a t f x) = IBoolElim (subst v) (substLevelsRT t) (substLevelsRT f) (substLevelsRT a) (substLevelsIrr x)
  substLevelsT :: Term -> Term
  substLevelsT (TVar s v n) = TVar s (map subst v) n
  substLevelsT (THole n (Tp a)) = THole n (Tp (substLevelsRT a))
  substLevelsT (TType n) = TType (subst n)
  substLevelsT (TPi s a b) = TPi s (substLevelsT a) (substLevelsT b)
  substLevelsT (TLam s x) = TLam s (substLevelsT x)
  substLevelsT (TApp f x) = TApp (substLevelsT f) (substLevelsT x)
  substLevelsT (TEq v a x y) = TEq (subst v) (substLevelsT a) (substLevelsT x) (substLevelsT y)
  substLevelsT (TRefl v a x) = TRefl (subst v) (substLevelsT a) (substLevelsT x)
  substLevelsT (TEqElim v w a p r x y h) = TEqElim (subst v) (subst w) (substLevelsT a) (substLevelsT p) (substLevelsT r) (substLevelsT x) (substLevelsT y) (substLevelsT h)
  substLevelsT TEmpty = TEmpty
  substLevelsT (TEmptyElim v a x) = TEmptyElim (subst v) (substLevelsT a) (substLevelsT x)
  substLevelsT TUnit = TUnit
  substLevelsT TStar = TStar
  substLevelsT TBool = TBool
  substLevelsT TTrue = TTrue
  substLevelsT TFalse = TFalse
  substLevelsT (TBoolElim v a t f x) = TBoolElim (subst v) (substLevelsT a) (substLevelsT t) (substLevelsT f) (substLevelsT x)
  substLevelsEnv :: (RTerm, Maybe Int) -> (RTerm, Maybe Int)
  substLevelsEnv (x, Nothing) = (substLevelsRT x, Nothing)
  substLevelsEnv x = x
  subst :: RLevel -> RLevel
  subst (RLevel n m) = foldrWithKey (\n' (m', _) l -> rlMax (rlPlus (u !! n') m') l) (RLevel n empty) m