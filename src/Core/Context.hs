{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE FlexibleContexts    #-}

module Core.Context where

import Core.Expression
import Control.Monad.Except
import Data.Monoid
import Control.Applicative

data Bwd a where
  Nil  :: Bwd a
  Snoc :: Bwd a -> a -> Bwd a
  deriving stock (Eq, Functor, Foldable)

data Zipper a where
  Zipper :: Bwd a -> a -> [a] -> Zipper a

infixl 5 :|>
pattern (:|>) :: Bwd a -> a -> Bwd a
pattern xs :|> x <- Snoc xs x
  where
    xs :|> x = Snoc xs x
{-# COMPLETE Nil, (:|>) #-}

  

data ConTerm v where
  ConTyVar  :: v -> ConTerm v
  ConTerm   :: v -> Type v -> ConTerm v
  ConExVar  :: v -> ConTerm v
  ConExDef  :: v -> MonoType v -> ConTerm v
  ScopeMark :: v -> ConTerm v

isVar :: Eq v => v -> ConTerm v -> Bool
isVar v (ConTyVar v') = v == v'
isVar v (ConExVar v') = v == v'
isVar v (ConExDef v' _) = v == v'
isVar _ _ = False

type Context v = Bwd (ConTerm v)
type ContextFocus v = Zipper (ConTerm v)

data ContextError v =
    VarUndefined v (Context v)


hasVar :: Eq v => v -> Context v -> Bool
hasVar v = getAny . foldMap (Any . isVar v)

checkVar :: (MonadError (ContextError v) m, Eq v, Alternative m) => Context v -> v -> m ()
checkVar ctxt v = do
  if (hasVar v ctxt)
    then
      pure ()
    else
      throwError (VarUndefined v ctxt)

isType :: (MonadError (ContextError v) m, Eq v, Alternative m) => Context v -> Type v -> m ()
isType ctxt (TyVar v) = checkVar ctxt v
isType ctxt (ExVar v) = checkVar ctxt v
isType _    TyUnit = pure ()
isType ctxt (ForAll a ty) = isType (ctxt :|> ConTyVar a) ty
isType ctxt (TyArr ty1 ty2) =
  do
    isType ctxt ty1
    isType ctxt ty2

    

    

