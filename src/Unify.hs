module Unify (module Syntax, unifyType) where

import Error
import Reduce
import Syntax

unify :: MonadTrace m => Ctx -> RTypeTerm -> RTerm -> RTerm -> m ()
unify _c _a _x _y = trace ("\nUnifying " ++ show (quote _x) ++ " and " ++ show (quote _y)) $ unify' _c _a _x _y
  where
  unify' c (Tp (RType _)) a b = unifyType c (Tp a) (Tp b)
  unify' c (Tp (RPi a (s, b, e))) f g = do
    let v = newVar s a c
    x <- reduceApp f v
    y <- reduceApp g v
    b' <- Tp <$> reduce ((v, Nothing) : e) b
    unify (c |- Def s a v Nothing) b' x y
  unify' _ (Tp (REq _ _ _ _)) _ _ = return ()
  unify' _ (Tp REmpty) _ _ = return ()
  unify' _ (Tp RUnit) _ _ = return ()
  unify' _ (Tp RBool) RTrue RTrue = return ()
  unify' _ (Tp RBool) RFalse RFalse = return ()
  unify' c _ (RIrreducible x _) (RIrreducible y _) = unifyIrreducible c x y
  unify' _ _ _ _ = fail "Cannot unify"

unifyType :: MonadTrace m => Ctx -> RTypeTerm -> RTypeTerm -> m ()
unifyType _c _a _b = trace ("\nUnifying " ++ show (quote _a) ++ " and " ++ show (quote _b)) $ unifyType' _c _a _b
  where
  unifyType' c (Tp (RIrreducible x _)) (Tp (RIrreducible y _)) = unifyIrreducible c x y
  unifyType' _ (Tp (RType n)) (Tp (RType m)) | n == m = return ()
                                             | otherwise = fail ("Expected universe level " ++ show (quoteLevel n) ++ " but was " ++ show (quoteLevel m))
  unifyType' c (Tp (RPi a (s, b, e))) (Tp (RPi a' (s', b', e'))) = do
    unifyType c a a'
    b'' <- Tp <$> reduce ((newVar s a c, Nothing) : e) b
    b''' <- Tp <$> reduce ((newVar s' a c, Nothing) : e') b'
    unifyType c b'' b'''
  unifyType' c (Tp (REq _ a x y)) (Tp (REq _ b x' y')) = do
    unifyType c a b
    unify c a x x'
    unify c a y y'
  unifyType' _ (Tp REmpty) (Tp REmpty) = return ()
  unifyType' _ (Tp RUnit) (Tp RUnit) = return ()
  unifyType' _ (Tp RBool) (Tp RBool) = return ()
  unifyType' _ _ _ = fail "Cannot unify types"

unifyIrreducible :: MonadTrace m => Ctx -> Irreducible -> Irreducible -> m ()
unifyIrreducible _ (IVar _ u x) (IVar _ v y) | u /= v = fail "Variable level indices are not equal"
                                             | x == y = return ()
                                             | otherwise = fail "Variables are not equal"
unifyIrreducible _ (IMVar x) (IMVar y) | x == y = return ()
                                       | otherwise = fail "Metavariables are not equal"
unifyIrreducible c (IApp f x a) (IApp g y b) = do
  unifyIrreducible c f g
  unifyType c a b
  unify c a x y
unifyIrreducible c (IEqElim u _ a p r x y _) (IEqElim _ _ _ _ r' x' y' _) = do
  let ra = Tp (RPi a ("x", TApp (TApp (TApp (TVar "P" [] 1) (TVar "x" [] 0)) (TVar "x" [] 0)) (TRefl u (TVar "A" [] 2) (TVar "x" [] 0)), [(p, Nothing), (tpTerm a, Nothing)]))
  unify c ra r r'
  -- TODO: is this better?
  -- let z = newVar "!" a c
  -- r'' <- reduceApp r z
  -- r''' <- reduceApp r' z
  -- p' <- reduceApp p z`
  -- p'' <- reduceApp p' z
  -- p''' <- Tp <$> reduceApp p'' (RRefl u a z)
  -- unify (c |- Def "!" a z Nothing) p''' r'' r'''
  unify c a x x'
  unify c a y y'
unifyIrreducible _ (IEmptyElim _ _ _) (IEmptyElim _ _ _) = return ()
unifyIrreducible c (IBoolElim _ a t f x) (IBoolElim _ _ t' f' y) = do
  at <- Tp <$> reduceApp a RTrue
  unify c at t t'
  af <- Tp <$> reduceApp a RFalse
  unify c af f f'
  unifyIrreducible c x y
unifyIrreducible _ _ _ = fail "Cannot unify irreducibles"