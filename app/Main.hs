module Main (main) where

import Control.Monad.State
import Error
import RTerm
import Term

main :: IO ()
main = do
  putStrLn . show $ execStateT test []

test :: StateT Ctx Error ()
test = do
  addDef (Type 1) (Type 0)
  addDef (Type 1) (Pi (Type 0) (Type 0))
  addDef (Pi (Type 0) (Type 0)) (Lam (Type 0) (Var 0))
  addDef (Pi (Type 0) (Pi (Var 0) (Var 1))) (Lam (Type 0) (Lam (Var 0) (Var 0)))
  addDef
    (Pi (Type 0) (Pi (Type 0) (Pi (Type 0) (Pi (Pi (Var 1) (Var 1)) (Pi (Pi (Var 3) (Var 3)) (Pi (Var 4) (Var 3)))))))
    (Lam (Type 0) (Lam (Type 0) (Lam (Type 0) (Lam (Pi (Var 1) (Var 1)) (Lam (Pi (Var 3) (Var 3)) (Lam (Var 4) (App (Var 2) (App (Var 1) (Var 0)))))))))
  addDef
    (Pi (Type 0) (Pi (Pi (Var 0) (Pi (Var 1) (Var 2))) (Pi (Var 1) (Var 2))))
    (Lam (Type 0) (Lam (Pi (Var 0) (Pi (Var 1) (Var 2))) (Lam (Var 1) (App (App (Var 1) (Var 0)) (Var 0)))))
  addDef
    (Pi (Pi (Type 0) (Type 0)) (Pi (Type 0) (Pi (App (Var 1) (Var 0)) (App (Var 2) (Var 1)))))
    (Lam (Pi (Type 0) (Type 0)) (Lam (Type 0) (Lam (App (Var 1) (Var 0)) (Var 0))))