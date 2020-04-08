{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE OverloadedStrings   #-}

module Core.Expression where

-- import Prelude hiding (lookup)
-- import Data.Foldable
-- import Test.QuickCheck
--import Data.String


data Term v where
  Var  :: v                -> Term v
  Unit ::                     Term v
  Lam  :: v      -> Term v -> Term v
  App  :: Term v -> Term v -> Term v
  Ann  :: Term v -> Type v -> Term v

data Type v where
  TyUnit  ::                     Type v
  TyVar   :: v                -> Type v
  ExVar   :: v                -> Type v
  ForAll  :: v      -> Type v -> Type v
  TyArr   :: Type v -> Type v -> Type v

data MonoType v where
  MonoUnit :: MonoType v
  MonoVar  :: v -> MonoType v
  MonoArr  :: MonoType v -> MonoType v -> MonoType v

asTypeScheme :: MonoType v -> Type v
asTypeScheme = \case
  MonoUnit  -> TyUnit
  MonoVar v -> TyVar v
  MonoArr m1 m2 -> TyArr (asTypeScheme m1) (asTypeScheme m2)
  
