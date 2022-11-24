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
  addDef "fromUnit" ["u"]
    (Pi "A" (Var vType [LVar "u"]) (fun (fun (var vUnit) (var "A")) (var "A")))
    (Lam "A" (Lam "s" (App (var "s") (var vStar))))
  addDef "castUnit" ["u"]
    (Pi "P" (fun (var vUnit) (Var vType [LVar "u"])) (Pi "x" (var vUnit) (Pi "y" (var vUnit) (fun (App (var "P") (var "x")) (App (var "P") (var "y"))))))
    (Lam "P" (Lam "x" (Lam "y" (Lam "h" (var "h")))))
  addDef "if" ["u"]
    (Pi "A" (Var vType [LVar "u"]) (fun (var vBool) (fun (var "A") (fun (var "A") (var "A")))))
    (Lam "A" (Lam "b" (Lam "t" (Lam "f" (App (App (App (App (Var vBoolElim [LVar "u"]) (lam (var "A"))) (var "t")) (var "f")) (var "b"))))))
  addDef "star'" []
    (App (App (App (App (Var "if" [Level 1]) (Var vType [Level 0])) (var vTrue)) (var vUnit)) (var vEmpty))
    (var vStar)
  addDef "Bool.nc" []
    (fun (var vBool) (fun (var vBool) (Var vType [Level 0])))
    (Lam "x" (Lam "y" (App (App (App (App (Var "if" [Level 1]) (Var vType [Level 0])) (var "x")) (App (App (App (App (Var "if" [Level 1]) (Var vType [Level 0])) (var "y")) (var vUnit)) (var vEmpty))) (App (App (App (App (Var "if" [Level 1]) (Var vType [Level 0])) (var "y")) (var vEmpty)) (var vUnit)))))
  addDef "trueEqTrue" []
    (App (App (App (Var vEq [Level 0]) (var vBool)) (var vTrue)) (var vTrue))
    (App (App (Var vRefl [Level 0]) (var vBool)) (var vTrue))
  addDef "trueEqTrue'" []
    (App (App (var "Bool.nc") (var vTrue)) (var vTrue))
    (var vStar)
  addDef "trueNeFalse" []
    (fun (App (App (App (Var vEq [Level 0]) (var vBool)) (var vTrue)) (var vFalse)) (var vEmpty))
    --(Lam "h" (App (App (App (App (App (App (Var vEqElim [Level 0, Level 0]) (var vBool)) (Lam "x" (Lam "y" (lam (App (App (var "Bool.nc") (var "x")) (var "y")))))) Hole) (var vTrue)) (var vFalse)) (var "h")))
    --(App (App (App (App (App (Var vEqElim [Level 0, Level 0]) (var vBool)) (Lam "x" (Lam "y" (lam (App (App (var "Bool.nc") (var "x")) (var "y")))))) (App (App (App (Var vBoolElim [Level 0]) (Lam "x" (App (App (var "Bool.nc") (var "x")) (var "x")))) (var vStar)) (var vStar))) (var vTrue)) (var vFalse))
    (Lam "h" (App (App (App (App (App (App (Var vEqElim [Level 0, Level 0]) (var vBool)) (Lam "x" (Lam "y" (lam (App (App (var "Bool.nc") (var "x")) (var "y")))))) (App (App (App (Var vBoolElim [Level 0]) (Lam "x" (App (App (var "Bool.nc") (var "x")) (var "x")))) (var vStar)) (var vStar))) (var vTrue)) (var vFalse)) (var "h")))
  addDef "BoolElimEq" []
    (Pi "h" (App (App (App (Var vEq [Level 0]) (var vBool)) (var vTrue)) (var vTrue)) (App (App (App (Var vEq [Level 0]) (var vBool))
      (App (App (App (App (App (App (Var vEqElim [Level 0, Level 0]) (var vBool)) (lam (lam (lam (var vBool))))) (lam (var vTrue))) (var vTrue)) (var vTrue)) (var "h")))
      (App (App (App (App (App (App (Var vEqElim [Level 0, Level 0]) (var vBool)) (lam (lam (lam (var vBool))))) (lam (var vTrue))) (var vTrue)) (var vTrue)) (var "h"))))
    (Lam "h" (App (App (Var vRefl [Level 0]) (var vBool)) (App (App (App (App (App (App (Var vEqElim [Level 0, Level 0]) (var vBool)) (lam (lam (lam (var vBool))))) (lam (var vTrue))) (var vTrue)) (var vTrue)) (var "h"))))
  addDef "Eq.elim'" ["u", "v"]
    (Pi "A" (Var vType [LVar "u"]) (Pi "x" (var "A") (Pi "P" (Pi "y" (var "A") (Pi "h" (App (App (App (Var vEq [LVar "u"]) (var "A")) (var "x")) (var "y")) (Var vType [LVar "v"]))) (Pi "r" (App (App (var "P") (var "x")) (App (App (Var vRefl [LVar "u"]) (var "A")) (var "x"))) (Pi "y" (var "A") (Pi "h" (App (App (App (Var vEq [LVar "u"]) (var "A")) (var "x")) (var "y")) (App (App (var "P") (var "y")) (var "h"))))))))
    --(Lam "A" (Lam "x" (Lam "P" (Lam "r" (Lam "y" (Lam "h" Hole))))))
    (Lam "A" (Lam "x" (Lam "P" (Lam "r" (Lam "y" (Lam "h" (App (App (App (App (App (App (App (App (Var vEqElim [LVar "u", LMax (LVar "u") (LPlus (LVar "v") 1)]) (var "A")) (Lam "x" (Lam "y" (Lam "h" (Pi "P" (Pi "z" (var "A") (fun (App (App (App (Var vEq [LVar "u"]) (var "A")) (var "x")) (var "z")) (Var vType [LVar "v"]))) (fun (App (App (var "P") (var "x")) (App (App (Var vRefl [LVar "u"]) (var "A")) (var "x"))) (App (App (var "P") (var "y")) (var "h")))))))) (lam (lam (Lam "h" (var "h"))))) (var "x")) (var "y")) (var "h")) (var "P")) (var "r"))))))))
  addDef "trueNeFalse'" []
    (fun (App (App (App (Var vEq [Level 0]) (var vBool)) (var vTrue)) (var vFalse)) (var vEmpty))
    (Lam "h" (App (App (App (App (App (App (Var "Eq.elim'" [Level 0, Level 0]) (var vBool)) (var vTrue)) (Lam "y" (lam (App (App (App (App (Var "if" [Level 1]) (Var vType [Level 0])) (var "y")) (var vUnit)) (var vEmpty))))) (var vStar)) (var vFalse)) (var "h")))
  addDef "subst" ["u", "v"]
    (Pi "A" (Var vType [LVar "u"]) (Pi "P" (fun (var "A") (Var vType [LVar "v"])) (Pi "x" (var "A") (Pi "y" (var "A") (fun (App (App (App (Var vEq [LVar "u"]) (var "A")) (var "x")) (var "y")) (fun (App (var "P") (var "x")) (App (var "P") (var "y"))))))))
    --(Lam "A" (Lam "P" (Lam "x" (Lam "y" (Lam "h" (App (App (App (App (App (App (Var vEqElim [LVar "u", LVar "v"]) (var "A")) (Lam "x" (Lam "y" (lam (fun (App (var "P") (var "x")) (App (var "P") (var "y"))))))) (Lam "x" Hole)) (var "x")) (var "y")) (var "h")))))))
    (Lam "A" (Lam "P" (App (App (App (Var vEqElim [LVar "u", LVar "v"]) (var "A")) (Lam "x" (Lam "y" (lam (fun (App (var "P") (var "x")) (App (var "P") (var "y"))))))) (lam (Lam "h" (var "h"))))))