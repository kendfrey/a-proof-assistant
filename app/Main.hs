module Main (main) where

import Control.Monad.Trans.Accum
import Control.Monad.Trans.State
import Data.List (intercalate)
import Error
import Syntax

main :: IO ()
main = do
  putStrLn . mapError id (intercalate "\n\n" . map show) $ execAccumT (execStateT test $ Ctx []) []

test :: StateT Ctx (AccumT [Goal] Error) ()
test = do
  addDef "MyType1" (Type 1) (Type 0)
  addDef "MyType2" (Type 1) (Pi "A" (Type 0) (Type 0))
  addDef "typeId" (Pi "A" (Type 0) (Type 0)) (Lam "A" (Var "A" 0))
  addDef "id" (Pi "A" (Type 0) (Pi "x" (Var "A" 0) (Var "A" 1))) (Lam "A" (Lam "x" (Var "x" 0)))
  addDef "comp"
    (Pi "A" (Type 0) (Pi "B" (Type 0) (Pi "C" (Type 0) (Pi "f" (Pi "y" (Var "B" 1) (Var "C" 1)) (Pi "g" (Pi "x" (Var "A" 3) (Var "B" 3)) (Pi "x" (Var "A" 4) (Var "C" 3)))))))
    --(Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" (App (Var "f" 2) (App (Var "g" 1) (Var "x" 0)))))))))
    (Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" Hole))))))
  addDef "dup"
    (Pi "A" (Type 0) (Pi "B" (Type 0) (Pi "f" (Pi "x" (Var "A" 1) (Pi "y" (Var "A" 2) (Var "B" 2))) (Pi "x" (Var "A" 2) (Var "B" 2)))))
    --(Lam "A" (Lam "B" (Lam "f" (Lam "x" (App (App (Var "f" 1) (Var "x" 0)) (Var "x" 0))))))
    (Lam "A" (Lam "B" (Lam "f" (Lam "x" (App (App (Var "f" 1) Hole) Hole)))))
  addDef "familyId"
    (Pi "P" (Pi "A" (Type 0) (Type 0)) (Pi "A" (Type 0) (Pi "h" (App (Var "P" 1) (Var "A" 0)) (App (Var "P" 2) (Var "A" 1)))))
    (Lam "P" (Lam "A" (Lam "h" (Var "h" 0))))