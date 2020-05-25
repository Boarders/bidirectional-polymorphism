{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}

module Core.Expression where

-- import Prelude hiding (lookup)
-- import Data.Foldable
-- import Test.QuickCheck
--import Data.String
import Data.Set (Set)
import qualified Data.Set as Set


data Term v where
  Var  :: v                -> Term v
  Unit ::                     Term v
  Lam  :: v      -> Term v -> Term v
  App  :: Term v -> Term v -> Term v
  Ann  :: Term v -> Type v -> Term v
  deriving stock (Eq, Ord, Show)

data Type v where
  TyUnit  ::                     Type v
  TyVar   :: v                -> Type v
  ExVar   :: v                -> Type v
  ForAll  :: v      -> Type v -> Type v
  TyArr   :: Type v -> Type v -> Type v
  deriving stock (Eq, Ord, Show)

data MonoType v where
  MonoUnit  :: MonoType v
  MonoVar   :: v -> MonoType v
  MonoExVar :: v -> MonoType v
  MonoArr   :: MonoType v -> MonoType v -> MonoType v
 deriving stock (Eq, Ord, Show)

substitute :: Eq v => v -> (Type v) -> (Type v) -> Type v
substitute var sub = \case
  TyUnit -> TyUnit
  TyVar v | v == var -> sub
  TyArr ty1 ty2 -> TyArr (substitute var sub ty1) (substitute var sub ty2)
  ex -> ex
                           

-- Note: Might be better to make MonoType constructor directly in Type?
isMonoType :: (Eq v) => Type v -> Bool
isMonoType TyUnit = True
isMonoType (TyVar _) = True
isMonoType (ExVar _) = True
isMonoType (ForAll _ _) = False
isMonoType (TyArr ty1 ty2) = isMonoType ty1 && isMonoType ty2

getMonoType :: Type v -> Maybe (MonoType v)
getMonoType (TyUnit)  = pure MonoUnit
getMonoType (TyVar v) = pure (MonoVar v)
getMonoType (ExVar v) = pure (MonoExVar v)
getMonoType (TyArr ty1 ty2) = do
  mon1 <- getMonoType ty1
  mon2 <- getMonoType ty2
  pure $ MonoArr mon1 mon2
getMonoType _ = Nothing


asTypeScheme :: MonoType v -> Type v
asTypeScheme = \case
  MonoUnit  -> TyUnit
  MonoVar v -> TyVar v
  MonoArr m1 m2 -> TyArr (asTypeScheme m1) (asTypeScheme m2)
  MonoExVar v -> ExVar v

subTyVar :: (Eq v) => v -> Type v -> Type v -> Type v
subTyVar _   _   TyUnit  = TyUnit
subTyVar var sub (TyVar v) | var == v = sub
subTyVar var sub (TyArr ty1 ty2) = TyArr (subTyVar var sub ty1) (subTyVar var sub ty2)
subTyVar var _    ty@(ForAll v _) | v == var = ty
subTyVar var sub (ForAll v ty) = ForAll v (subTyVar var sub ty)
subTyVar _    _  ty = ty

class FreeVars t v where
  fvs :: t -> Set v

instance Ord v => FreeVars (Type v) v where
  fvs = \case
    TyUnit  -> mempty
    TyVar v -> Set.singleton v
    ExVar v -> Set.singleton v
    ForAll v ty_v -> (fvs ty_v) `Set.difference` (Set.singleton v)
    TyArr  ty1 ty2 -> (fvs ty1) <> (fvs ty2)

hasFV :: Ord v => v -> Type v -> Bool
hasFV fv = (Set.member fv) . fvs
    


