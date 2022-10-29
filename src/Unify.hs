module Unify (module Syntax, unifyType) where

import Error
import Reduce
import Syntax

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