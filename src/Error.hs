{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Error (Error(..), mapError, MonadTrace, trace) where

import Control.Monad.Trans.Accum

newtype Error a = Error (Either String a) deriving (Functor, Applicative, Monad)

instance MonadFail Error where
  fail = Error . Left

instance Show a => Show (Error a) where
  show (Error (Right x)) = show x
  show (Error (Left x)) = "Error: " ++ x

mapError :: (String -> b) -> (a -> b) -> Error a -> b
mapError _ f (Error (Right x)) = f x
mapError f _ (Error (Left x)) = f x

class MonadFail m => MonadTrace m where
  trace :: String -> m a -> m a

instance (Monoid w, MonadTrace m) => MonadTrace (AccumT w m) where
  trace s = mapAccumT (trace s)

instance MonadTrace Error where
  trace s (Error (Left s')) = Error (Left (s' ++ s))
  trace _ x = x