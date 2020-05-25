{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable    #-}

module Core.Context where

import Core.Expression (Type(..), MonoType)
import qualified Core.Expression as Exp
import Control.Monad.Except
import Data.Monoid
import Data.Foldable


-- |
-- A snoc list
data Bwd a where
  Nil  :: Bwd a
  Snoc :: Bwd a -> a -> Bwd a
  deriving stock (Eq, Functor, Foldable)

fromList :: [a] -> Bwd a
fromList = foldl' Snoc Nil

-- |
-- A list zipper for focusing on an elememt
data Zipper a where
  Zipper :: Bwd a -> a -> [a] -> Zipper a

infixl 5 :|>
pattern (:|>) :: Bwd a -> a -> Bwd a
pattern xs :|> x <- Snoc xs x
  where
    xs :|> x = Snoc xs x
{-# COMPLETE Nil, (:|>) #-}


-- |
-- The types of terms that can appear in contexts:
--   type variables, solved variables,
--   existential variables, solved existentials (instaniated at a monotype)
--   and scope markers for handling higher rank instantiation
data ConTerm v where
  ConTyVar  :: v -> ConTerm v
  ConTerm   :: v -> Type v -> ConTerm v
  ConExVar  :: v -> ConTerm v
  ConExDef  :: v -> MonoType v -> ConTerm v
  ScopeMark :: v -> ConTerm v
  deriving stock (Eq, Ord, Show)

-- |
-- Whether a context term is a variable
conVar :: ConTerm v -> Maybe v
conVar (ConTyVar v)   = Just v
conVar (ConExVar v)   = Just v
conVar _              = Nothing

-- |
-- Pattern for variable type.
pattern ConVar :: v -> ConTerm v
pattern ConVar v <- (conVar -> Just v)

{-# COMPLETE ConVar, ConTerm, ConExDef, ScopeMark #-}

-- |
-- Check If a given variable is equal to a context term variable
isVar :: Eq v => v -> ConTerm v -> Bool
isVar v (ConTyVar v')   = v == v'
isVar v (ConExVar v')   = v == v'
isVar v (ConExDef v' _) = v == v'
isVar _ _ = False

-- |
-- If a given variable is equal to a existential variable
isExVar :: Eq v => v -> ConTerm v -> Bool
isExVar v (ConExVar v')   = v == v'
isExVar _ _ = False

-- |
-- Get the solved type of an existential
hasType :: Eq v => v -> ConTerm v -> Maybe (MonoType v)
hasType v (ConExDef v' ty) | v == v' = Just ty
hasType _  _                         = Nothing


type Context v = Bwd (ConTerm v)
type ContextFocus v = Zipper (ConTerm v)

-- |
-- Errors one can have for well-formed context
data ContextError v =
    VarUndefined v (Context v)
  | NonWellFormedContext (ConTerm v) (Context v)

class VarError v err  where
  varErr :: v -> (Context v) ->  err

instance VarError v (ContextError v) where
  varErr = VarUndefined

fromFocus :: (Context v) -> ConTerm v -> [ConTerm v] -> Context v
fromFocus ctxt foc = foldl' Snoc (ctxt :|> foc)

fromFoci :: (Context v) -> [ConTerm v] -> [ConTerm v] -> Context v
fromFoci ctxt foci = foldl' Snoc (foldl' Snoc ctxt foci)
   

-- |
-- check if a variable is present in a context.
hasVar :: Eq v => v -> Context v -> Bool
hasVar v = getAny . foldMap (Any . isVar v)

-- |
-- check if a existential variable is present in a context.
hasExVar :: Eq v => v -> Context v -> Bool
hasExVar v = getAny . foldMap (Any . isExVar v)


-- |
-- Check if a term is present in a context.
hasConTerm :: Eq v => (ConTerm v) -> Context v -> Bool
hasConTerm conTerm = getAny . foldMap (Any . (== conTerm))


-- |
-- Get the type (in order) of an existentially solved variable
hasExDef :: Eq v => v -> Context v -> Maybe (MonoType v)
hasExDef v = getFirst . foldMap (First . hasType v)
                              

-- |
-- Error handler for variable not present in a context.
handleVar
  :: (MonadError err m)
  => Bool -> err -> m a -> m a
handleVar b err ma =
  if b then ma else throwError err


-- | Check variable is defined in context.
checkVar :: (MonadError e m, Eq v, VarError v e) => Context v -> v -> m ()
checkVar ctxt v = handleVar (hasVar v ctxt) (varErr v ctxt) (pure ())

-- | Check variable is defined in context.
checkExVar :: (MonadError e m, Eq v, VarError v e) => Context v -> v -> m ()
checkExVar ctxt v = handleVar (hasExVar v ctxt) (varErr v ctxt) (pure ())


isType
  :: (MonadError e m, Eq v, VarError v e)
  => Context v -> Type v -> m ()
isType ctxt (TyVar v) = checkVar ctxt v
isType ctxt (ExVar v) = checkVar ctxt v
isType _    TyUnit = pure ()
isType ctxt (ForAll a ty) = isType (ctxt :|> ConTyVar a) ty
isType ctxt (TyArr ty1 ty2) =
  do
    isType ctxt ty1
    isType ctxt ty2


-- |
-- Add a term to a context making sure it remains valid.
addToCon
  :: (Eq v, MonadError (ContextError v) m)
  => ConTerm v -> Context v -> m (Context v)
addToCon conTerm@(ConVar var) ctxt =
  do
    handleVar (not $ hasVar var ctxt) (NonWellFormedContext conTerm ctxt)
      do
        pure $ ctxt :|> conTerm
addToCon conTerm@(ConExDef var ty) ctxt =
  do
    handleVar (not $ hasVar var ctxt) (NonWellFormedContext conTerm ctxt)
      do
        isType ctxt (Exp.asTypeScheme ty)
        pure $ ctxt :|> conTerm
addToCon conTerm @(ConTerm  var ty) ctxt =
  do
    handleVar (not $ hasVar var ctxt) (NonWellFormedContext conTerm ctxt)
      do
        isType ctxt ty
        pure $ ctxt :|> conTerm
addToCon conTerm@(ScopeMark var  ) ctxt =
  do
    handleVar (not $ hasVar var ctxt) (NonWellFormedContext conTerm ctxt)
       do
         if (hasConTerm conTerm ctxt) then
           throwError (NonWellFormedContext conTerm ctxt)
         else
           pure $ ctxt :|> conTerm


applyContext :: (Eq v) => Context v -> Type v -> Type v
applyContext _       (TyVar v) = TyVar v
applyContext _       (TyUnit)  = TyUnit
applyContext ctxt ex@(ExVar v) =
  case hasExDef v ctxt of
    Just ty -> Exp.asTypeScheme ty
    Nothing -> ex
applyContext ctxt (ForAll a ty)   = ForAll a (applyContext ctxt ty)
applyContext ctxt (TyArr ty1 ty2) = TyArr (applyContext ctxt ty1) (applyContext ctxt ty2)
  

class Fresh v where
  fresh :: Context v -> v


removeTyVarSuffix :: Eq v => v -> Context v -> Context v
removeTyVarSuffix _ Nil = Nil
removeTyVarSuffix var (ctxt :|> ConTyVar v) | v == var = ctxt
removeTyVarSuffix var (ctxt :|> _) = removeTyVarSuffix var ctxt


splitExVar
  :: (Eq v, MonadError e m)
  => (v -> (Context v) -> e) -> v -> Context v -> m ((Context v), [ConTerm v])
splitExVar errHand var context = go var context []
  where
    go v Nil _ =  throwError (errHand v context)
    go v (c :|> ConExVar ex) rest | ex == v = pure (c, rest)
    go v (c :|> conTerm) rest = go v c (conTerm : rest)

removeScopeSuffix
  :: (Eq v, MonadError e m)
  => (v -> (Context v) -> e) -> v -> Context v -> m (Context v)
removeScopeSuffix errHand var context = go var context
  where
    go v Nil =  throwError (errHand v context)
    go v (c :|> ScopeMark ex)  | ex == v = pure c
    go v (c :|> _) = go v c


instantiateExVar
  :: (Eq v, MonadError (ContextError v) m)
  => Context v -> MonoType v -> m (Context v)
instantiateExVar = undefined
