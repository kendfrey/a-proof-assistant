module Reduce (module Syntax, reduce, reduceApp) where

import Data.Maybe
import Error
import Syntax

reduce :: MonadTrace m => Env -> Term -> m RTerm
reduce e (TVar _ u n) = do
  (x, v) <- getVar e n
  substLevels u x (fromMaybe 0 v)
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
reduce _ TEmpty = return REmpty
reduce e (TEmptyElim u a x) = do
  a' <- reduce e a
  x' <- reduce e x
  reduceEmptyElim u a' x'

reduceApp :: MonadTrace m => RTerm -> RTerm -> m RTerm
reduceApp (RIrreducible f (Tp (RPi a (_, b, e)))) x = do
  b' <- Tp <$> reduce ((x, Nothing) : e) b
  return $ RIrreducible (IApp f x a) b'
reduceApp (RLam (_, f, e)) x = reduce ((x, Nothing) : e) f
reduceApp _ _ = fail "Function expected"

reduceEmptyElim :: MonadTrace m => RLevel -> RTerm -> RTerm -> m RTerm
reduceEmptyElim u a x'@(RIrreducible x (Tp REmpty)) = do
  a' <- Tp <$> reduceApp a x'
  return $ RIrreducible (IEmptyElim u a x) a'
reduceEmptyElim _ _ _ = fail "Unexpected value of type Empty"