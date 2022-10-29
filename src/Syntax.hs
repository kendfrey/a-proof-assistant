module Syntax (Preterm(..), Term(..), RTerm(..), Irreducible(..), Ctx(..), Goal, addDef) where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Accum
import Control.Monad.Trans.State
import Data.List (intercalate)
import Error

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

data Goal = Goal Int Ctx RTypeTerm

instance Show Goal where
  show (Goal n c a) = "?" ++ show n ++ "\n" ++ showGoalCtx ++ "\n|- " ++ show a
    where
    showGoalCtx :: String
    showGoalCtx = intercalate "\n" . map showDef . reverse . filter defBound $ defs c
    showDef :: Def -> String
    showDef d = defName d ++ " : " ++ show (defType d)

addDef :: String -> Preterm -> Preterm -> StateT Ctx (AccumT [Goal] Error) ()
addDef s a x = mapStateT (mapAccumT (trace ("\nAdding a definition with type " ++ show a ++ " and value " ++ show x))) $ do
  c <- get
  d <- lift $ checkDef c
  put (c |- d)
  where
    checkDef :: Ctx -> AccumT [Goal] Error Def
    checkDef c = do
      (a', _) <- elaborateType c a
      a'' <- lift $ Tp <$> reduce (env c) a'
      x' <- elaborate c a'' x
      x'' <- lift $ reduce (env c) x'
      return $ Def s a'' x'' False

elaborate :: MonadTrace m => Ctx -> RTypeTerm -> Preterm -> AccumT [Goal] m Term
elaborate _c _a _x = mapAccumT (trace ("\nElaborating " ++ show _x ++ " as " ++ show _a)) $ elaborate' _c _a _x
  where
  elaborate' :: MonadTrace m => Ctx -> RTypeTerm -> Preterm -> AccumT [Goal] m Term
  elaborate' c a (Var s n) = do
    a' <- getType c n
    unifyType c a a'
    return $ TVar s n
  elaborate' c a Hole = do
    n <- looks length
    add [Goal n c a]
    return $ THole n a
  elaborate' c a (App f x) = do
    (f', a'') <- infer c f
    (a', (_, b, e)) <- getPi a''
    x' <- elaborate c a' x
    x'' <- reduce (env c) x'
    b' <- Tp <$> reduce (x'' : e) b
    unifyType c a b'
    return $ TApp f' x'
  elaborate' c (Tp (RType n)) x = do
    (x', m) <- elaborateType c x
    if m == n then
      return x'
    else
      fail "Wrong universe level"
  elaborate' c (Tp (RPi a (s, b, e))) x = elaboratePi c a s b e x
  elaborate' _ (Tp (RIrreducible _ _)) _ = fail "Cannot elaborate as an irreducible type"
  elaborate' _ _ _ = fail "Cannot elaborate"

elaborateType :: MonadTrace m => Ctx -> Preterm -> AccumT [Goal] m (Term, Int)
elaborateType _c _a = trace ("\nElaborating " ++ show _a ++ " as a type") $ elaborateType' _c _a
  where
  elaborateType' :: MonadTrace m => Ctx -> Preterm -> AccumT [Goal] m (Term, Int)
  elaborateType' c (Var s n) = do
    a <- getType c n
    m <- getLevel a
    return (TVar s n, m)
  elaborateType' _ (Type n) = return (TType n, n + 1)
  elaborateType' c (Pi s a b) = do
    (a', n) <- elaborateType c a
    a'' <- Tp <$> reduce (env c) a'
    (b', m) <- elaborateType (pushVar s a'' c) b
    return (TPi s a' b', max n m)
  elaborateType' c (App f x) = do
    (f', a') <- infer c f
    (a, (_, b, e)) <- getPi a'
    x' <- elaborate c a x
    x'' <- reduce (env c) x'
    b' <- Tp <$> reduce (x'' : e) b
    n <- getLevel b'
    return (TApp f' x', n)
  elaborateType' _ _ = fail "Type expected"

elaboratePi :: MonadTrace m => Ctx -> RTypeTerm -> String -> Term -> Env -> Preterm -> AccumT [Goal] m Term
elaboratePi c a s b e (Lam s' x) = do
  b' <- Tp <$> reduce (newVar s a c : e) b
  x' <- elaborate (pushVar s' a c) b' x
  return $ TLam s' x'
elaboratePi _ _ _ _ _ (App _ _) = fail "Unreachable code"
elaboratePi _ _ _ _ _ _ = fail "Function expected"

infer :: MonadTrace m => Ctx -> Preterm -> AccumT [Goal] m (Term, RTypeTerm)
infer c (Var s n) = do
  a <- getType c n
  return (TVar s n, a)
infer _ Hole = fail "Cannot infer the type of a hole"
infer _ (Type n) = return (TType n, Tp (RType (n + 1)))
infer c (Pi s a b) = do
  (a', a'') <- infer c a
  n <- getLevel a''
  (b', b'') <- infer (pushVar s a'' c) b
  m <- getLevel b''
  return (TPi s a' b', Tp (RType (max n m)))
infer _ (Lam _ _) = fail "Cannot infer the type of a lambda"
infer c (App f x) = do
  (f', a') <- infer c f
  (a, (_, b, e)) <- getPi a'
  x' <- elaborate c a x
  x'' <- reduce (env c) x'
  b' <- reduce (x'' : e) b
  return (TApp f' x', Tp b')

reduce :: MonadTrace m => Env -> Term -> m RTerm
reduce e (TVar _ n) = getVar e n
reduce _ (THole n a) = return $ RIrreducible (IMVar n) a
reduce _ (TType n) = return $ RType n
reduce e (TPi s a b) = do
  a' <- Tp <$> reduce e a
  return $ RPi a' (s, b, e)
reduce e (TLam s x) = do
  return $ RLam (s, x, e)
reduce e (TApp f x) = do
  f' <- reduce e f
  x' <- reduce e x
  reduceApp f' x'

reduceApp :: MonadTrace m => RTerm -> RTerm -> m RTerm
reduceApp (RIrreducible f (Tp (RPi a (_, b, e)))) x = do
  b' <- Tp <$> reduce (x : e) b
  return $ RIrreducible (IApp f x a) b'
reduceApp (RLam (_, f, e)) x = reduce (x : e) f
reduceApp _ _ = fail "Function expected"

unify :: MonadTrace m => Ctx -> RTypeTerm -> RTerm -> RTerm -> m ()
unify _c _a _x _y = trace ("\nUnifying " ++ show _x ++ " and " ++ show _y) $ unify' _c _a _x _y
  where
  unify' c (Tp (RType _)) a b = unifyType c (Tp a) (Tp b)
  unify' c (Tp (RPi a (s, b, e))) f g = do
    let v = newVar s a c
    x <- reduceApp f v
    y <- reduceApp g v
    b' <- Tp <$> reduce (v : e) b
    unify (c |- Def s a v True) b' x y
  unify' c _ (RIrreducible x _) (RIrreducible y _) = unifyIrreducible c x y
  unify' _ _ _ _ = fail "Cannot unify"

unifyType :: MonadTrace m => Ctx -> RTypeTerm -> RTypeTerm -> m ()
unifyType _c _a _b = trace ("\nUnifying " ++ show _a ++ " and " ++ show _b) $ unifyType' _c _a _b
  where
  unifyType' c (Tp (RIrreducible x _)) (Tp (RIrreducible y _)) = unifyIrreducible c x y
  unifyType' _ (Tp (RType n)) (Tp (RType m)) | n == m = return ()
                                            | otherwise = fail "Wrong universe level"
  unifyType' c (Tp (RPi a (s, b, e))) (Tp (RPi a' (s', b', e'))) = do
    unifyType c a a'
    b'' <- Tp <$> reduce (newVar s a c : e) b
    b''' <- Tp <$> reduce (newVar s' a c : e') b'
    unifyType c b'' b'''
  unifyType' _ _ _ = fail "Cannot unify types"

unifyIrreducible :: MonadTrace m => Ctx -> Irreducible -> Irreducible -> m ()
unifyIrreducible _ (IVar _ x) (IVar _ y) | x == y = return ()
                                         | otherwise = fail "Variables are not equal"
unifyIrreducible _ (IMVar x) (IMVar y) | x == y = return ()
                                       | otherwise = fail "Metavariables are not equal"
unifyIrreducible c (IApp f x a) (IApp g y b) = do
  unifyIrreducible c f g
  unifyType c a b
  unify c a x y
unifyIrreducible _ _ _ = fail "Cannot unify irreducibles"