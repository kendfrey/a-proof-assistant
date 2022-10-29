module Main (main) where

import Control.Monad.Trans.Accum
import Control.Monad.Trans.State
import Data.List (intercalate)
import Def
import Error

main :: IO ()
main = do
  putStrLn . mapError id (intercalate "\n\n" . map show) $ execAccumT (execStateT test $ Ctx []) []

test :: StateT Ctx (AccumT [Goal] Error) ()
test = do
  addDef "MyType1" (Type 1) (Type 0)
  addDef "MyType2" (Type 1) (Pi "A" (Type 0) (Type 0))
  addDef "typeId" (Pi "A" (Type 0) (Type 0)) (Lam "A" (Var "A"))
  addDef "id" (Pi "A" (Type 0) (Pi "x" (Var "A") (Var "A"))) (Lam "A" (Lam "x" (Var "x")))
  addDef "comp"
    (Pi "A" (Type 0) (Pi "B" (Type 0) (Pi "C" (Type 0) (Pi "f" (Pi "y" (Var "B") (Var "C")) (Pi "g" (Pi "x" (Var "A") (Var "B")) (Pi "x" (Var "A") (Var "C")))))))
    --(Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" (App (Var "f") (App (Var "g") (Var "x")))))))))
    (Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" Hole))))))
  addDef "dup"
    (Pi "A" (Type 0) (Pi "B" (Type 0) (Pi "f" (Pi "x" (Var "A") (Pi "y" (Var "A") (Var "B"))) (Pi "x" (Var "A") (Var "B")))))
    --(Lam "A" (Lam "B" (Lam "f" (Lam "x" (App (App (Var "f") (Var "x")) (Var "x"))))))
    (Lam "A" (Lam "B" (Lam "f" (Lam "x" (App (App (Var "f") Hole) Hole)))))
  addDef "familyId"
    (Pi "P" (Pi "A" (Type 0) (Type 0)) (Pi "A" (Type 0) (Pi "h" (App (Var "P") (Var "A")) (App (Var "P") (Var "A")))))
    (Lam "P" (Lam "A" (Lam "h" (Var "h"))))