module Elaborate (module Goal, module Syntax, elaborate, elaborateType) where

import Control.Monad.Trans.Accum
import Error
import Goal
import Reduce
import Syntax
import Unify

elaborate :: MonadTrace m => Ctx -> RTypeTerm -> Preterm -> AccumT [Goal] m Term
elaborate _c _a _x = mapAccumT (trace ("\nElaborating " ++ show _x ++ " as " ++ show (quote _a))) $ elaborate' _c _a _x
  where
  elaborate' :: MonadTrace m => Ctx -> RTypeTerm -> Preterm -> AccumT [Goal] m Term
  elaborate' c a (Var s) = do
    (d, n) <- lookupVar c s
    unifyType c a (defType d)
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
  elaborateType' c (Var s) = do
    (d, n) <- lookupVar c s
    m <- getLevel (defType d)
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
infer c (Var s) = do
  (d, n) <- lookupVar c s
  return (TVar s n, defType d)
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