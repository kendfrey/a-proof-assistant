module Elaborate (module Goal, module Syntax, elaborate, elaborateType) where

import Control.Monad.Trans.Accum
import Data.Maybe
import Error
import Goal
import Reduce
import Syntax
import Unify

elaborate :: MonadTrace m => Ctx -> [String] -> RTypeTerm -> Preterm -> AccumT [Goal] m Term
elaborate _c _u _a _x = mapAccumT (trace ("\nElaborating " ++ show _x ++ " as " ++ show (quote _a))) $ elaborate' _c _u _a _x
  where
  elaborate' :: MonadTrace m => Ctx -> [String] -> RTypeTerm -> Preterm -> AccumT [Goal] m Term
  elaborate' c u a (Var s v) = do
    (d, n) <- lookupVar c s
    v' <- mapM (reduceLevel u) v
    a' <- substLevels v' (tpTerm (defType d)) (fromMaybe 0 (universeVars <$> defTopLevel d))
    unifyType c a (Tp a')
    return $ TVar s v' n
  elaborate' c _ a Hole = do
    n <- looks length
    add [Goal n c a]
    return $ THole n a
  elaborate' c u a (App f x) = do
    (f', a'') <- infer c u f
    (a', (_, b, e)) <- getPi a''
    x' <- elaborate c u a' x
    x'' <- reduce (env c) x'
    b' <- Tp <$> reduce ((x'', Nothing) : e) b
    unifyType c a b'
    return $ TApp f' x'
  elaborate' c u (Tp (RType n)) x = do
    (x', m) <- elaborateType c u x
    if m == n then
      return x'
    else
      fail "Wrong universe level"
  elaborate' c u (Tp (RPi a (s, b, e))) x = elaboratePi c u a s b e x
  elaborate' _ _ (Tp (RIrreducible _ _)) _ = fail "Cannot elaborate as an irreducible type"
  elaborate' _ _ _ _ = fail "Cannot elaborate"

elaborateType :: MonadTrace m => Ctx -> [String] -> Preterm -> AccumT [Goal] m (Term, RLevel)
elaborateType _c _u _a = trace ("\nElaborating " ++ show _a ++ " as a type") $ elaborateType' _c _u _a
  where
  elaborateType' :: MonadTrace m => Ctx -> [String] -> Preterm -> AccumT [Goal] m (Term, RLevel)
  elaborateType' c u (Var s v) = do
    (d, n) <- lookupVar c s
    v' <- mapM (reduceLevel u) v
    a <- substLevels v' (tpTerm (defType d)) (fromMaybe 0 (universeVars <$> defTopLevel d))
    m <- getLevel (Tp a)
    return (TVar s v' n, m)
  elaborateType' c u (Pi s a b) = do
    (a', n) <- elaborateType c u a
    a'' <- Tp <$> reduce (env c) a'
    (b', m) <- elaborateType (pushVar s a'' c) u b
    return (TPi s a' b', rlMax n m)
  elaborateType' c u (App f x) = do
    (f', a') <- infer c u f
    (a, (_, b, e)) <- getPi a'
    x' <- elaborate c u a x
    x'' <- reduce (env c) x'
    b' <- Tp <$> reduce ((x'', Nothing) : e) b
    n <- getLevel b'
    return (TApp f' x', n)
  elaborateType' _ _ _ = fail "Type expected"

elaboratePi :: MonadTrace m => Ctx -> [String] -> RTypeTerm -> String -> Term -> Env -> Preterm -> AccumT [Goal] m Term
elaboratePi c u a s b e (Lam s' x) = do
  b' <- Tp <$> reduce ((newVar s a c, Nothing) : e) b
  x' <- elaborate (pushVar s' a c) u b' x
  return $ TLam s' x'
elaboratePi _ _ _ _ _ _ (App _ _) = fail "Unreachable code"
elaboratePi _ _ _ _ _ _ _ = fail "Function expected"

infer :: MonadTrace m => Ctx -> [String] -> Preterm -> AccumT [Goal] m (Term, RTypeTerm)
infer c u (Var s v) = do
  (d, n) <- lookupVar c s
  v' <- mapM (reduceLevel u) v
  a <- substLevels v' (tpTerm (defType d)) (fromMaybe 0 (universeVars <$> defTopLevel d))
  return (TVar s v' n, Tp a)
infer _ _ Hole = fail "Cannot infer the type of a hole"
infer c u (Pi s a b) = do
  (a', a'') <- infer c u a
  n <- getLevel a''
  (b', b'') <- infer (pushVar s a'' c) u b
  m <- getLevel b''
  return (TPi s a' b', Tp (RType (rlMax n m)))
infer _ _ (Lam _ _) = fail "Cannot infer the type of a lambda"
infer c u (App f x) = do
  (f', a') <- infer c u f
  (a, (_, b, e)) <- getPi a'
  x' <- elaborate c u a x
  x'' <- reduce (env c) x'
  b' <- reduce ((x'', Nothing) : e) b
  return (TApp f' x', Tp b')