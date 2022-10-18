{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Error (Error(..)) where

newtype Error a = Error (Either String a) deriving (Functor, Applicative, Monad)

instance MonadFail Error where
  fail = Error . Left

instance Show a => Show (Error a) where
  show (Error (Right x)) = show x
  show (Error (Left x)) = "Error: " ++ show x