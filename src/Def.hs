module Def (module Elaborate, module Syntax, addDef, defaultCtx) where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Accum
import Control.Monad.Trans.State
import Elaborate
import Error
import Reduce
import Syntax

defaultCtx :: Ctx
defaultCtx = Ctx []
  |- Def vType
    (Tp (RType (rlPlus (rlVar 0 "u") 1)))
    (RType (rlVar 0 "u"))
    (Just (TLDef 1 True))
  |- Def vEmpty
    (Tp (RType (rlLevel 0)))
    REmpty
    (Just (TLDef 0 True))
  |- Def vEmptyElim
    (Tp (RPi (Tp (RPi (Tp REmpty) ("_", TType (rlVar 0 "u"), []))) ("P", TPi "x" TEmpty (TApp (TVar "P" [] 1) (TVar "x" [] 0)), [])))
    (RLam ("P", TLam "x" (TEmptyElim (rlVar 0 "u") (TVar "P" [] 1) (TVar "x" [] 0)), []))
    (Just (TLDef 1 True))
  |- Def vUnit
    (Tp (RType (rlLevel 0)))
    RUnit
    (Just (TLDef 0 True))
  |- Def vStar
    (Tp RUnit)
    RStar
    (Just (TLDef 0 True))
  |- Def vUnitElim
    (Tp (RPi (Tp (RPi (Tp RUnit) ("_", TType (rlVar 0 "u"), []))) ("P", TPi "_" (TApp (TVar "P" [] 0) TStar) (TPi "x" TUnit (TApp (TVar "P" [] 2) (TVar "x" [] 0))), [])))
    (RLam ("P", TLam "s" (TLam "x" (TVar "s" [] 1)), []))
    (Just (TLDef 1 True))
  |- Def vBool
    (Tp (RType (rlLevel 0)))
    RBool
    (Just (TLDef 0 True))
  |- Def vTrue
    (Tp RBool)
    RTrue
    (Just (TLDef 0 True))
  |- Def vFalse
    (Tp RBool)
    RFalse
    (Just (TLDef 0 True))
  |- Def vBoolElim
    (Tp (RPi (Tp (RPi (Tp RBool) ("_", TType (rlVar 0 "u"), []))) ("P", TPi "_" (TApp (TVar "P" [] 0) TTrue) (TPi "_" (TApp (TVar "P" [] 1) TFalse) (TPi "x" TBool (TApp (TVar "P" [] 3) (TVar "x" [] 0)))), [])))
    (RLam ("P", TLam "t" (TLam "f" (TLam "x" (TBoolElim (rlVar 0 "u") (TVar "P" [] 3) (TVar "t" [] 2) (TVar "f" [] 1) (TVar "x" [] 0)))), []))
    (Just (TLDef 1 True))
  |- Def vEq
    (Tp (RPi (Tp (RType (rlVar 0 "u"))) ("A", TPi "x" (TVar "A" [] 0) (TPi "y" (TVar "A" [] 1) (TType (rlVar 0 "u"))), [])))
    (RLam ("A", TLam "x" (TLam "y" (TEq (rlVar 0 "u") (TVar "A" [] 2) (TVar "x" [] 1) (TVar "y" [] 0))), []))
    (Just (TLDef 1 True))
  |- Def vRefl
    (Tp (RPi (Tp (RType (rlVar 0 "u"))) ("A", TPi "x" (TVar "A" [] 0) (TEq (rlVar 0 "u") (TVar "A" [] 1) (TVar "x" [] 0) (TVar "x" [] 0)), [])))
    (RLam ("A", TLam "x" (TRefl (rlVar 0 "u") (TVar "A" [] 1) (TVar "x" [] 0)), []))
    (Just (TLDef 1 True))
  |- Def vEqElim
    (Tp (RPi (Tp (RType (rlVar 0 "u"))) ("A", TPi "P" (TPi "x" (TVar "A" [] 0) (TPi "y" (TVar "A" [] 1) (TPi "_" (TEq (rlVar 0 "u") (TVar "A" [] 2) (TVar "x" [] 1) (TVar "y" [] 0)) (TType (rlVar 1 "v"))))) (TPi "_" (TPi "x" (TVar "A" [] 1) (TApp (TApp (TApp (TVar "P" [] 1) (TVar "x" [] 0)) (TVar "x" [] 0)) (TRefl (rlVar 0 "u") (TVar "A" [] 2) (TVar "x" [] 0)))) (TPi "x" (TVar "A" [] 2) (TPi "y" (TVar "A" [] 3) (TPi "h" (TEq (rlVar 0 "u") (TVar "A" [] 4) (TVar "x" [] 1) (TVar "y" [] 0)) (TApp (TApp (TApp (TVar "P" [] 4) (TVar "x" [] 2)) (TVar "y" [] 1)) (TVar "h" [] 0)))))), [])))
    (RLam ("A", TLam "P" (TLam "r" (TLam "x" (TLam "y" (TLam "h" (TEqElim (rlVar 0 "u") (rlVar 1 "v") (TVar "A" [] 5) (TVar "P" [] 4) (TVar "r" [] 3) (TVar "x" [] 2) (TVar "y" [] 1) (TVar "h" [] 0)))))), []))
    (Just (TLDef 2 True))

addDef :: String -> [String] -> Preterm -> Preterm -> StateT Ctx (AccumT [Goal] Error) ()
addDef s u a x = mapStateT (mapAccumT (trace ("\nAdding a definition '" ++ s ++ "' with type " ++ show a ++ " and value " ++ show x))) $ do
  c <- get
  d <- lift $ checkDef c
  put (c |- d)
  where
    checkDef :: Ctx -> AccumT [Goal] Error Def
    checkDef c = do
      (a', _) <- elaborateType c u a
      a'' <- lift $ Tp <$> reduce (env c) a'
      x' <- elaborate c u a'' x
      x'' <- lift $ reduce (env c) x'
      return $ Def s a'' x'' (Just (TLDef (length u) False))