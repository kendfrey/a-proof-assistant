module Goal (module Syntax, Goal(..)) where

import Data.List (intercalate)
import Syntax

data Goal = Goal Int Ctx RTypeTerm

instance Show Goal where
  show (Goal n c a) = "?" ++ show n ++ "\n" ++ showGoalCtx ++ "\n|- " ++ show (quote a)
    where
    showGoalCtx :: String
    showGoalCtx = intercalate "\n" . map showDef . reverse . filter defBound $ defs c
    showDef :: Def -> String
    showDef d = defName d ++ " : " ++ show (quote (defType d))