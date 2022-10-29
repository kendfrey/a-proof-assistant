module Reduce (module Syntax, reduce, reduceApp) where

import Error
import Syntax

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