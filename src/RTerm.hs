module RTerm (RTerm(..), Irreducible(..), Ctx(..), addDef) where

import Control.Monad.State
import Error
import Term

data RTerm
  = RIrreducible Irreducible RTypeTerm
  | RType Int
  | RPi RTypeTerm Closure
  | RLam Closure

data Irreducible
  = IVar String Int
  | IApp Irreducible RTerm RTypeTerm

newtype RTypeTerm = Tp RTerm

type Closure = (String, Term, Env)

data Ctx
  = EmptyCtx
  | Ctx :- (RTypeTerm, RTerm)

type Env = [RTerm]

instance Show RTerm where
  show (RIrreducible x _) = show x
  show (RType n) = "Type" ++ show n
  show (RPi a (s, b, _)) = "(" ++ s ++ " : " ++ show a ++ ") -> " ++ show b
  show (RLam (s, x, _)) = "(\\" ++ s ++ ", " ++ show x ++ ")"

instance Show Irreducible where
  show (IVar s _) = s
  show (IApp f x _) = "(" ++ show f ++ " " ++ show x ++ ")"

instance Show RTypeTerm where
  show (Tp x) = show x

instance Show Ctx where
  show EmptyCtx = ""
  show (c :- (a, x)) = show c ++ show a ++ " := " ++ show x ++ "\n"

getLevel :: RTypeTerm -> Error Int
getLevel (Tp (RType n)) = return n
getLevel _ = fail "Type expected"

getPi :: RTypeTerm -> Error (RTypeTerm, Closure)
getPi (Tp (RPi a b)) = return (a, b)
getPi _ = fail "Function expected"

toList :: Ctx -> [(RTypeTerm, RTerm)]
toList EmptyCtx = []
toList (c :- x) = x : toList c

env :: Ctx -> Env
env c = map snd $ toList c

getVar :: [a] -> Int -> Error a
getVar [] _ = fail "Variable index out of range"
getVar (x : _) 0 = return x
getVar (_ : c) n | n > 0 = getVar c (n - 1)
                 | otherwise = fail "Negative variable index"

getType :: Ctx -> Int -> Error RTypeTerm
getType c n = fst <$> getVar (toList c) n

addDef :: Term -> Term -> StateT Ctx Error ()
addDef a x = do
  c <- get
  d <- lift $ checkDef c
  put (c :- d)
  where
    checkDef :: Ctx -> Error (RTypeTerm, RTerm)
    checkDef c = do
      _ <- typecheckType c a
      a' <- Tp <$> reduce (env c) a
      typecheck c a' x
      x' <- reduce (env c) x
      return (a', x')

newVar :: String -> RTypeTerm -> Ctx -> RTerm
newVar s a c = RIrreducible (IVar s (length (toList c))) a

pushVar :: String -> RTypeTerm -> Ctx -> Ctx
pushVar s a c = c :- (a, newVar s a c)

typecheck :: Ctx -> RTypeTerm -> Term -> Error ()
typecheck c a (Var _ n) = do
  a' <- getType c n
  unifyType c a a'
typecheck c a (App f x) = do
  a'' <- infer c f
  (a', (_, b, e)) <- getPi a''
  typecheck c a' x
  x' <- reduce (env c) x
  b' <- Tp <$> reduce (x' : e) b
  unifyType c a b'
typecheck c (Tp (RType n)) x = do
  m <- typecheckType c x
  if m == n then
    return ()
  else
    fail "Wrong universe level"
typecheck c (Tp (RPi a (s, b, e))) x = typecheckPi c a s b e x
typecheck _ (Tp (RIrreducible _ _)) _ = fail "Cannot typecheck against an irreducible type"
typecheck _ _ _ = fail "Cannot typecheck"

typecheckType :: Ctx -> Term -> Error Int
typecheckType c (Var _ n) = do
  a <- getType c n
  getLevel a
typecheckType _ (Type n) = return $ n + 1
typecheckType c (Pi s a b) = do
  n <- typecheckType c a
  a' <- Tp <$> reduce (env c) a
  m <- typecheckType (pushVar s a' c) b
  return $ max n m
typecheckType c (App f x) = do
  a' <- infer c f
  (a, (_, b, e)) <- getPi a'
  typecheck c a x
  x' <- reduce (env c) x
  b' <- Tp <$> reduce (x' : e) b
  getLevel b'
typecheckType _ _ = fail "Type expected"

typecheckPi :: Ctx -> RTypeTerm -> String -> Term -> Env -> Term -> Error ()
typecheckPi c a s b e (Lam s' x) = do
  b' <- Tp <$> reduce (newVar s a c : e) b
  typecheck (pushVar s' a c) b' x
typecheckPi _ _ _ _ _ (App _ _) = fail "Unreachable code"
typecheckPi _ _ _ _ _ _ = fail "Function expected"

infer :: Ctx -> Term -> Error RTypeTerm
infer c (Var _ n) = do
  a <- getType c n
  return a
infer _ (Type n) = return $ Tp $ RType (n + 1)
infer c (Pi s a b) = do
  a' <- infer c a
  n <- getLevel a'
  b' <- infer (pushVar s a' c) b
  m <- getLevel b'
  return $ Tp $ RType (max n m)
infer _ (Lam _ _) = fail "Cannot infer the type of a lambda"
infer c (App f x) = do
  a' <- infer c f
  (a, (_, b, e)) <- getPi a'
  typecheck c a x
  x' <- reduce (env c) x
  Tp <$> reduce (x' : e) b

reduce :: Env -> Term -> Error RTerm
reduce e (Var _ n) = getVar e n
reduce _ (Type n) = return $ RType n
reduce e (Pi s a b) = do
  a' <- Tp <$> reduce e a
  return $ RPi a' (s, b, e)
reduce e (Lam s x) = do
  return $ RLam (s, x, e)
reduce e (App f x) = do
  f' <- reduce e f
  x' <- reduce e x
  reduceApp f' x'

reduceApp :: RTerm -> RTerm -> Error RTerm
reduceApp (RIrreducible f (Tp (RPi a (_, b, e)))) x = do
  b' <- Tp <$> reduce (x : e) b
  return $ RIrreducible (IApp f x a) b'
reduceApp (RLam (_, f, e)) x = reduce (x : e) f
reduceApp _ _ = fail "Function expected"

unify :: Ctx -> RTypeTerm -> RTerm -> RTerm -> Error ()
unify c (Tp (RType _)) a b = unifyType c (Tp a) (Tp b)
unify c (Tp (RPi a (s, b, e))) f g = do
  let v = newVar s a c
  x <- reduceApp f v
  y <- reduceApp g v
  b' <- Tp <$> reduce (v : e) b
  unify (c :- (a, v)) b' x y
unify c _ (RIrreducible x _) (RIrreducible y _) = unifyIrreducible c x y
unify _ _ _ _ = fail "Cannot unify"

unifyType :: Ctx -> RTypeTerm -> RTypeTerm -> Error ()
unifyType c (Tp (RIrreducible x _)) (Tp (RIrreducible y _)) = unifyIrreducible c x y
unifyType _ (Tp (RType n)) (Tp (RType m)) | n == m = return ()
                                          | otherwise = fail "Wrong universe level"
unifyType c (Tp (RPi a (s, b, e))) (Tp (RPi a' (s', b', e'))) = do
  unifyType c a a'
  b'' <- Tp <$> reduce (newVar s a c : e) b
  b''' <- Tp <$> reduce (newVar s' a c : e') b'
  unifyType c b'' b'''
unifyType _ _ _ = fail "Cannot unify types"

unifyIrreducible :: Ctx -> Irreducible -> Irreducible -> Error ()
unifyIrreducible _ (IVar _ x) (IVar _ y) | x == y = return ()
                                         | otherwise = fail "Variables are not equal"
unifyIrreducible c (IApp f x a) (IApp g y b) = do
  unifyIrreducible c f g
  unifyType c a b
  unify c a x y
unifyIrreducible _ _ _ = fail "Cannot unify irreducibles"