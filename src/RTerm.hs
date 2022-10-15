module RTerm (RTerm(..), Irreducible(..), Ctx, addDef) where

import Control.Monad.State
import Error
import Term

data RTerm
  = RIrreducible Irreducible RTerm
  | RType Int
  | RPi RTerm Closure
  | RLam RTerm Closure
  deriving (Show)

data Irreducible
  = IVar Int
  | IApp Irreducible RTerm RTerm
  deriving (Show)

getLevel :: RTerm -> Error Int
getLevel (RType n) = return n
getLevel _ = fail "Type expected"

getPi :: RTerm -> Error (RTerm, Closure)
getPi (RPi a b) = return (a, b)
getPi _ = fail "Function expected"

type Ctx = [(RTerm, RTerm)]

getType :: Ctx -> Int -> Error RTerm
getType [] _ = fail "Variable index out of range"
getType ((a, _) : _) 0 = return a
getType (_ : c) n | n > 0 = getType c (n - 1)
                  | otherwise = fail "Negative variable index"

addDef :: Term -> Term -> StateT Ctx Error ()
addDef a x = do
  c <- get
  d <- lift $ checkDef c
  put $ d : c
  where
    checkDef :: Ctx -> Error (RTerm, RTerm)
    checkDef c = do
      _ <- typecheckType c a
      a' <- reduce (map snd c) a
      typecheck c a' x
      x' <- reduce (map snd c) x
      return (a', x')

typecheck :: Ctx -> RTerm -> Term -> Error ()
typecheck c a (Var n) = do
  a' <- getType c n
  unifyType (map fst c) a a'
typecheck c a (App f x) = do
  a'' <- infer c f
  (a', (b, e)) <- getPi a''
  typecheck c a' x
  x' <- reduce (map snd c) x
  b' <- reduce (x' : e) b
  unifyType (map fst c) a b'
typecheck c (RType n) x = do
  m <- typecheckType c x
  if m == n then
    return ()
  else
    fail "Wrong universe level"
typecheck c (RPi a (b, e)) x = typecheckPi c a b e x
typecheck _ (RIrreducible _ _) _ = fail "Cannot typecheck against an irreducible type"
typecheck _ _ _ = fail "Cannot typecheck"

typecheckType :: Ctx -> Term -> Error Int
typecheckType c (Var n) = do
  a <- getType c n
  getLevel a
typecheckType _ (Type n) = return $ n + 1
typecheckType c (Pi a b) = do
  n <- typecheckType c a
  a' <- reduce (map snd c) a
  m <- typecheckType ((a', RIrreducible (IVar (length c)) a') : c) b
  return $ max n m
typecheckType c (App f x) = do
  a' <- infer c f
  (a, (b, e)) <- getPi a'
  typecheck c a x
  x' <- reduce (map snd c) x
  b' <- reduce (x' : e) b
  getLevel b'
typecheckType _ _ = fail "Type expected"

typecheckPi :: Ctx -> RTerm -> Term -> REnv -> Term -> Error ()
typecheckPi c a b e (Lam a' x) = do
  a'' <- reduce (map snd c) a'
  unifyType (map snd c) a a''
  b' <- reduce (RIrreducible (IVar (length c)) a : e) b
  typecheck ((a, RIrreducible (IVar (length c)) a) : c) b' x
typecheckPi _ _ _ _ (App _ _) = fail "Unreachable code"
typecheckPi _ _ _ _ _ = fail "Function expected"

infer :: Ctx -> Term -> Error RTerm
infer c (Var n) = do
  a <- getType c n
  return a
infer _ (Type n) = return $ RType (n + 1)
infer c (Pi a b) = do
  a' <- infer c a
  n <- getLevel a'
  b' <- infer ((a', RIrreducible (IVar (length c)) a') : c) b
  m <- getLevel b'
  return $ RType (max n m)
infer _ (Lam _ _) = fail "Cannot infer the type of a lambda"
infer c (App f x) = do
  a' <- infer c f
  (a, (b, e)) <- getPi a'
  typecheck c a x
  x' <- reduce (map snd c) x
  reduce (x' : e) b

type REnv = [RTerm]

type Closure = (Term, REnv)

type RCtx = [RTerm]

getEnv :: REnv -> Int -> Error RTerm
getEnv [] _ = fail "Variable index out of range"
getEnv (x : _) 0 = return x
getEnv (_ : e) n | n > 0 = getEnv e (n - 1)
                 | otherwise = fail "Negative variable index"

reduce :: REnv -> Term -> Error RTerm
reduce e (Var n) = getEnv e n
reduce _ (Type n) = return $ RType n
reduce e (Pi a b) = do
  a' <- reduce e a
  return $ RPi a' (b, e)
reduce e (Lam a x) = do
  a' <- reduce e a
  return $ RLam a' (x, e)
reduce e (App f x) = do
  f' <- reduce e f
  x' <- reduce e x
  reduceApp f' x'

reduceApp :: RTerm -> RTerm -> Error RTerm
reduceApp (RIrreducible f (RPi a (b, e))) x = do
  b' <- reduce (x : e) b
  return $ RIrreducible (IApp f x a) b'
reduceApp (RLam _ (f, e)) x = reduce (x : e) f
reduceApp _ _ = fail "Function expected"

unify :: RCtx -> RTerm -> RTerm -> RTerm -> Error ()
unify c (RType _) a b = unifyType c a b
unify c (RPi a (b, e)) f g = do
  x <- reduceApp f (RIrreducible (IVar (length c)) a)
  y <- reduceApp g (RIrreducible (IVar (length c)) a)
  b' <- reduce (RIrreducible (IVar (length c)) a : e) b
  unify (a : c) b' x y
unify c _ (RIrreducible x _) (RIrreducible y _) = unifyIrreducible c x y
unify _ _ _ _ = fail "Cannot unify"

unifyType :: RCtx -> RTerm -> RTerm -> Error ()
unifyType c (RIrreducible x _) (RIrreducible y _) = unifyIrreducible c x y
unifyType _ (RType n) (RType m) | n == m = return ()
                                | otherwise = fail "Wrong universe level"
unifyType c (RPi a (b, e)) (RPi a' (b', e')) = do
  unifyType c a a'
  b'' <- reduce ((RIrreducible (IVar (length c)) a) : e) b
  b''' <- reduce ((RIrreducible (IVar (length c)) a) : e') b'
  unifyType c b'' b'''
unifyType _ _ _ = fail "Cannot unify types"

unifyIrreducible :: RCtx -> Irreducible -> Irreducible -> Error ()
unifyIrreducible _ (IVar x) (IVar y) | x == y = return ()
                                     | otherwise = fail "Variables are not equal"
unifyIrreducible c (IApp f x a) (IApp g y b) = do
  unifyIrreducible c f g
  unifyType c a b
  unify c a x y
unifyIrreducible _ _ _ = fail "Cannot unify irreducibles"