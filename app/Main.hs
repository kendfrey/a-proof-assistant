module Main (main) where

import Control.Monad.Trans.Accum
import Control.Monad.Trans.State
import Data.List (intercalate)
import Def
import Error

main :: IO ()
main = do
  putStrLn . mapError id showState $ runAccumT (execStateT test defaultCtx) []

showState :: (Ctx, [Goal]) -> String
showState (c, g) = show c ++ "\n\n" ++ intercalate "\n\n" (map show g)

test :: StateT Ctx (AccumT [Goal] Error) ()
test = do
  addDef "MyType1" [] (Var vType [Level 1]) (Var vType [Level 0])
  addDef "MyType2" [] (Var vType [Level 1]) (fun (Var vType [Level 0]) (Var vType [Level 0]))
  addDef "typeId" [] (fun (Var vType [Level 0]) (Var vType [Level 0])) (Lam "A" (var "A"))
  addDef "id" ["u"] (Pi "A" (Var vType [LVar "u"]) (fun (var "A") (var "A"))) (lam (Lam "x" (var "x")))
  addDef "comp" ["u", "v", "w"]
    (Pi "A" (Var vType [LVar "u"]) (Pi "B" (Var vType [LVar "v"]) (Pi "C" (Var vType [LVar "w"]) (fun (fun (var "B") (var "C")) (fun (fun (var "A") (var "B")) (fun (var "A") (var "C")))))))
    --(Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" (App (var "f") (App (var "g") (var "x")))))))))
    (Lam "A" (Lam "B" (Lam "C" (Lam "f" (Lam "g" (Lam "x" Hole))))))
  addDef "dup" ["u", "v"]
    (Pi "A" (Var vType [LVar "u"]) (Pi "B" (Var vType [LVar "v"]) (fun (fun (var "A") (fun (var "A") (var "B"))) (fun (var "A") (var "B")))))
    --(Lam "A" (Lam "B" (Lam "f" (Lam "x" (App (App (var "f") (var "x")) (var "x"))))))
    (Lam "A" (Lam "B" (Lam "f" (Lam "x" (App (App (var "f") Hole) Hole)))))
  addDef "familyId" ["u", "v"]
    (Pi "P" (fun (Var vType [LVar "u"]) (Var vType [LVar "v"])) (Pi "A" (Var vType [LVar "u"]) (fun (App (var "P") (var "A")) (App (var "P") (var "A")))))
    --(lam (lam (Lam "h" (var "h"))))
    --(Lam "p" (Lam "a" Hole))
    (Lam "P" (Lam "A" (App (Var "id" [LVar "v"]) (App (var "P") (var "A")))))
  addDef "absurd" ["u"]
    (Pi "A" (Var vType [LVar "u"]) (fun (var vEmpty) (var "A")))
    --(Lam "A" (Lam "x" Hole))
    (Lam "A" (Lam "x" (App (App (Var vEmptyElim [LVar "u"]) (lam (var "A"))) (var "x"))))
  addDef "absurd2" []
    (Pi "P" (fun (var vEmpty) (Var vType [Level 0])) (Pi "x" (var vEmpty) (Pi "y" (var vEmpty) (App (var "P") (var "x")))))
    (Lam "P" (Lam "x" (Lam "y" (App (App (Var vEmptyElim [Level 0]) (var "P")) (var "y")))))
  addDef "absurd'" []
    (Pi "x" (var vEmpty) (App (App (Var vEmptyElim [Level 1]) (lam (Var vType [Level 0]))) (var "x")))
    (Lam "x" (App (App (Var vEmptyElim [Level 0]) (App (Var vEmptyElim [Level 1]) (lam (Var vType [Level 0])))) Hole))