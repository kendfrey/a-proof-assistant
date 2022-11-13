module Level (Level(..), RLevel(..), quoteLevel, rlLevel, rlMax, rlPlus, rlVar, reduceLevel) where

import Data.Map (Map, elems, empty, singleton, unionWith)
import qualified Data.Map as M

data Level
  = Level Int
  | LVar String
  | LPlus Level Int
  | LMax Level Level

instance Show Level where
  show (Level n) = show n
  show (LVar s) = s
  show (LPlus l n) = show l ++ " + " ++ show n
  show (LMax l l') = "max(" ++ show l ++ ", " ++ show l' ++ ")"

data RLevel = RLevel { rlMinInt :: Int, rlVars :: Map Int (Int, String) }
  deriving (Eq)

rlLevel :: Int -> RLevel
rlLevel n = RLevel n empty

rlVar :: Int -> String -> RLevel
rlVar n s = RLevel 0 (singleton n (0, s))

rlPlus :: RLevel -> Int -> RLevel
rlPlus (RLevel m vs) n = RLevel (m + n) (M.map (\(n', s) -> (n' + n, s)) vs)

rlMax :: RLevel -> RLevel -> RLevel
rlMax (RLevel n vs) (RLevel n' vs') = RLevel (max n n') (unionWith (\(m, s) (m', _) -> (max m m', s)) vs vs')

lookupVar :: MonadFail m => [String] -> String -> m Int
lookupVar [] u = fail $ "Level " ++ u ++ " is not defined"
lookupVar (u : us) v | u == v = return 0
                     | otherwise = do
                         n <- lookupVar us v
                         return $ n + 1

reduceLevel :: MonadFail m => [String] -> Level -> m RLevel
reduceLevel _ (Level n) = return $ rlLevel n
reduceLevel u (LVar s) = do
  n <- lookupVar u s
  return $ rlVar n s
reduceLevel u (LPlus l n) = do
  l' <- reduceLevel u l
  return $ rlPlus l' n
reduceLevel u (LMax l l') = do
  l'' <- reduceLevel u l
  l''' <- reduceLevel u l'
  return $ rlMax l'' l'''

quoteLevel :: RLevel -> Level
quoteLevel (RLevel m vs) | null vs = Level m
                         | M.foldr (\(n, _) l -> max n l) 0 vs == m = foldr1 LMax . map quoteVar $ elems vs
                         | otherwise = M.foldr (\n l -> LMax n l) (Level m) . M.map quoteVar $ vs
  where
  quoteVar :: (Int, String) -> Level
  quoteVar (0, s) = LVar s
  quoteVar (n, s) = LPlus (LVar s) n