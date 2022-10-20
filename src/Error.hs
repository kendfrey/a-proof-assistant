{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Error (Error(..), trace) where

newtype Error a = Error (Either String a) deriving (Functor, Applicative, Monad)

instance MonadFail Error where
  fail = Error . Left

instance Show a => Show (Error a) where
  show (Error (Right x)) = show x
  show (Error (Left x)) = "Error: " ++ x

trace :: String -> Error a -> Error a
trace s (Error (Left s')) = Error (Left (s' ++ s))
trace _ x = x