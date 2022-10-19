module Main (main) where

import Control.Monad.State
import Error
import RTerm
import Term

main :: IO ()
main = do
  putStrLn . show $ execStateT test EmptyCtx

test :: StateT Ctx Error ()
test = do
  addDef (Type 1) (Type 0)
  addDef (Type 1) (Pi "A" (Type 0) (Type 0))
  addDef (Pi "A" (Type 0) (Type 0)) (Lam "A" (Var "A" 0))
  addDef (Pi "A" (Type 0) (Pi "x" (Var "A" 0) (Var "A" 1))) (Lam "A" (Lam "x" (Var "x" 0)))
  addDef
    (Pi "A" (Type 0) (Pi "B" (Type 0) (Pi "C" (Type 0) (Pi "f" (Pi "y" (Var "B" 1) (Var "C" 1)) (Pi "g" (Pi "x" (Var "A" 3) (Var "B" 3)) (Pi "x" (Var "A" 4) (Var "C" 3)))))))
    (Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" (App (Var "f" 2) (App (Var "g" 1) (Var "x" 0)))))))))
  addDef
    (Pi "A" (Type 0) (Pi "f" (Pi "x" (Var "A" 0) (Pi "y" (Var "A" 1) (Var "A" 2))) (Pi "x" (Var "A" 1) (Var "A" 2))))
    (Lam "A" (Lam "f" (Lam "x" (App (App (Var "f" 1) (Var "x" 0)) (Var "x" 0)))))
  addDef
    (Pi "P" (Pi "A" (Type 0) (Type 0)) (Pi "A" (Type 0) (Pi "h" (App (Var "P" 1) (Var "A" 0)) (App (Var "P" 2) (Var "A" 1)))))
    (Lam "P" (Lam "A" (Lam "h" (Var "h" 0))))