{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Error (Error(..)) where

newtype Error a = Error (Either String a) deriving (Functor, Applicative, Monad, Show)

instance MonadFail Error where
  fail = Error . Left