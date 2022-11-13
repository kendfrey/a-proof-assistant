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
  |- Def "Type"
    (Tp (RType (rlPlus (rlVar 0 "u") 1)))
    (RType (rlVar 0 "u")) (Just (TLDef 1 True))

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