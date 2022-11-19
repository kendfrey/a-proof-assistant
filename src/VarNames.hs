module VarNames (
  vBool,
  vBoolElim,
  vEmpty,
  vEmptyElim,
  vFalse,
  vStar,
  vTrue,
  vType,
  vUnit,
  vUnitElim
  ) where

vBool :: String
vBool = "Bool"

vBoolElim :: String
vBoolElim = "Bool.elim"

vEmpty :: String
vEmpty = "Empty"

vEmptyElim :: String
vEmptyElim = "Empty.elim"

vFalse :: String
vFalse = "false"

vStar :: String
vStar = "star"

vTrue :: String
vTrue = "true"

vType :: String
vType = "Type"

vUnit :: String
vUnit = "Unit"

vUnitElim :: String
vUnitElim = "Unit.elim"