module Main (main) where

import Control.Monad.Trans.Accum
import Control.Monad.Trans.State
import Data.List (intercalate)
import Def
import Error

main :: IO ()
main = do
  putStrLn . mapError id showState $ runAccumT (execStateT test $ Ctx []) []

showState :: (Ctx, [Goal]) -> String
showState (c, g) = show c ++ "\n\n" ++ intercalate "\n\n" (map show g)

test :: StateT Ctx (AccumT [Goal] Error) ()
test = do
  addDef "MyType1" [] (Type (Level 1)) (Type (Level 0))
  addDef "MyType2" [] (Type (Level 1)) (fun (Type (Level 0)) (Type (Level 0)))
  addDef "typeId" [] (fun (Type (Level 0)) (Type (Level 0))) (Lam "A" (var "A"))
  addDef "id" ["u"] (Pi "A" (Type (LVar "u")) (fun (var "A") (var "A"))) (lam (Lam "x" (var "x")))
  addDef "comp" ["u", "v", "w"]
    (Pi "A" (Type (LVar "u")) (Pi "B" (Type (LVar "v")) (Pi "C" (Type (LVar "w")) (fun (fun (var "B") (var "C")) (fun (fun (var "A") (var "B")) (fun (var "A") (var "C")))))))
    --(Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" (App (var "f") (App (var "g") (var "x")))))))))
    (Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" Hole))))))
  addDef "dup" ["u", "v"]
    (Pi "A" (Type (LVar "u")) (Pi "B" (Type (LVar "v")) (fun (fun (var "A") (fun (var "A") (var "B"))) (fun (var "A") (var "B")))))
    --(Lam "A" (Lam "B" (Lam "f" (Lam "x" (App (App (var "f") (var "x")) (var "x"))))))
    (Lam "A" (Lam "B" (Lam "f" (Lam "x" (App (App (var "f") Hole) Hole)))))
  addDef "familyId" ["u", "v"]
    (Pi "P" (fun (Type (LVar "u")) (Type (LVar "v"))) (Pi "A" (Type (LVar "u")) (fun (App (var "P") (var "A")) (App (var "P") (var "A")))))
    --(lam (lam (Lam "h" (var "h"))))
    --(Lam "p" (Lam "a" Hole))
    (Lam "P" (Lam "A" (App (Var "id" [LVar "v"]) (App (var "P") (var "A")))))