module VarNames (
  vBool,
  vBoolElim,
  vEmpty,
  vEmptyElim,
  vEq,
  vEqElim,
  vFalse,
  vRefl,
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

vEq :: String
vEq = "Eq"

vEqElim :: String
vEqElim = "Eq.elim"

vFalse :: String
vFalse = "false"

vRefl :: String
vRefl = "refl"

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