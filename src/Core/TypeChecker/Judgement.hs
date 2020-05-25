{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns     #-}
module Core.TypeChecker.Judgement where

import Core.Context
import Core.Expression
import Control.Monad.Except
import Data.Tree

data JudgementError v =
    SubTypeError
  | InstantiateError
  | VarError v (Context v)
  | NotSubType (Type v) (Type v)
  | SubTypeOccursCheck v (Type v)
  | NoMatchingSubTypeRule (Type v) (Type v)
  | InstaniationRError (Type v) v
  | InstaniationLError v (Type v)
  | ScopeMarkError v (Context v)

instance VarError v (JudgementError v) where
  varErr = VarError


subtype
  :: (MonadError (JudgementError v) m , Eq v, Ord v, Fresh v)
  => Context v -> Type v -> Type v -> m (Context v)
subtype ctxt (TyVar a1) (TyVar a2) | a1 == a2 =
  do
 -- check if the variable is in the context
    handleVar (hasVar a1 ctxt) (VarError a1 ctxt)
      do
     -- if so return the context
        pure ctxt
          -- unit is a subtype of itself
subtype ctxt TyUnit TyUnit = pure ctxt
subtype ctxt (ExVar a1) (ExVar a2) | a1 == a2 =
  do
 -- check that the existential var is declard in the context
    handleVar (hasVar a1 ctxt) (VarError a1 ctxt)
      do
     -- if so return the context
        pure ctxt
subtype ctxt (TyArr a1 a2) (TyArr b1 b2) =
  do
              -- Due to contravariance we check b1 is a subtype of a1.
    srcOutput <- subtype ctxt b1 a1
 -- then we apply the context and check the substituted targets are subtypes
    subtype srcOutput (applyContext srcOutput a2) (applyContext srcOutput b2)
subtype ctxt (ForAll var subTy) superTy =
  do
    let
   -- Create a new existential variable with marker 
      newVar  = fresh ctxt
      newCtxt = ctxt :|> ScopeMark newVar :|> ConExVar newVar
   -- substitute the existential variable for the old scheme variable
      exSubTy = subTyVar var (ExVar newVar) subTy
 -- Get the output context with the new existential context
    exCtxt <- subtype newCtxt exSubTy superTy
 -- Now remove the scope after the new existential variable and return it.
    removeScopeSuffix (\v c -> ScopeMarkError v c) newVar exCtxt
subtype ctxt subTy (ForAll var superTy) =
  do
    let
      newCtxt = ctxt :|> (ConTyVar var)
 -- to check when something is a subtype of a type scheme
 -- we prove that it is a subtype generic in the type variable of the context
    tyCtxt <- subtype newCtxt subTy superTy
 -- Finally we remove whatever context we introduce for the type variable.
    pure . removeTyVarSuffix var $ tyCtxt
subtype ctxt (ExVar exA) superType =
  do
 -- Check the existential variable is defined in the context
    handleVar (hasVar exA ctxt) (VarError exA ctxt)
      do
     -- perform the occurs check, see if the super type has the variable we
     -- are trying to instantiate it at
        if hasFV exA superType then throwError (SubTypeOccursCheck exA superType)
        else
          do
         -- defer to the instantiate judgement to do work
            instantiateL ctxt exA superType
subtype ctxt subType (ExVar exA) =
  do
 -- identical to above.
    handleVar (hasVar exA ctxt) (VarError exA ctxt)
      do
        if hasFV exA subType then throwError (SubTypeOccursCheck exA subType)
        else
          do
            instantiateR ctxt subType exA
subtype _ ty1 ty2 = throwError (NoMatchingSubTypeRule ty1 ty2)

--
-- to do: check these rules are in the correct order
-- e.g. InstLReach is only valid if alpha beta are defined in the context
instantiateL
  :: (MonadError (JudgementError v) m, Fresh v, Eq v, Ord v)
  => Context v -> v -> Type v -> m (Context v)
-- InstLSolve: instantiate an existential subtype at a monotype
instantiateL ctxt exA ty@(getMonoType -> Just monoTy) =
  do
    handleVar (hasExVar exA ctxt) (VarError exA ctxt) (pure ())
    (prefix, suffix) <- splitExVar (\v c -> VarError v c) exA ctxt
    isType prefix ty
    let solvedCtxt = fromFocus prefix (ConExDef exA monoTy) suffix
    pure solvedCtxt
-- InstLReach: instantiate an existential supertype with a previously
-- an existential subtype variable
instantiateL ctxt exA (ExVar exB) =
  do
    handleVar (hasExVar exA ctxt) (VarError exA ctxt) (pure ()) 
    handleVar (hasExVar exB ctxt) (VarError exB ctxt) (pure ())   
    (prefix, suffix) <- splitExVar (\v c -> VarError v c) exB ctxt
    let solvedCtxt = fromFocus prefix (ConExDef exB (MonoExVar exA)) suffix
    pure solvedCtxt
instantiateL ctxt exA (TyArr a1 a2) =
-- InstLArr: instantiateL a existential subtype
-- at an arrow by introducing new existential variables
-- and then solving the lhs followed by rhs
  do
    handleVar (hasExVar exA ctxt) (VarError exA ctxt) (pure ())
    (prefix, suffix) <- splitExVar (\v c -> VarError v c) exA ctxt
    let
      exName1 = fresh ctxt
      exVar1  = ConExVar exName1      
      exName2 = fresh (ctxt :|> exVar1)
      exVar2  = ConExVar exName2
      foci    = [exVar1, exVar2, ConExDef exA (MonoArr (MonoExVar exName1) (MonoExVar exName2))]
      newCtxt = fromFoci prefix foci suffix
    leftSolved <- instantiateR newCtxt a1 exName1
    let newRHS = applyContext leftSolved a2
    instantiateL leftSolved exName2 newRHS
-- InstLAllR: instantiate a existential variable at a polymorphic
-- supertype
instantiateL ctxt exA (ForAll b ty_b) =
  do
    handleVar (hasExVar exA ctxt) (VarError exA ctxt) (pure ())
    exBCon <- instantiateL (ctxt :|> ConTyVar b) exA ty_b
    (prefix, _) <- splitExVar (\v c -> VarError v c) exA exBCon
    pure prefix
instantiateL _ var ty = throwError (InstaniationLError var ty)

instantiateR
  :: (MonadError (JudgementError v) m, Fresh v, Eq v, Ord v)
  => Context v -> Type v -> v -> m (Context v)
-- InstLAllR: instantitate an existential subtype at
-- a polymorphic supertype

-- InstRSolve: instantiateR an existential supertype at a monotype
instantiateR ctxt ty@(getMonoType -> Just monoTy) exA =
  do
    handleVar (hasExVar exA ctxt) (VarError exA ctxt) (pure ())
    (prefix, suffix) <- splitExVar (\v c -> VarError v c) exA ctxt
    isType prefix ty
    let solvedCtxt = fromFocus prefix (ConExDef exA monoTy) suffix
    pure solvedCtxt
-- InstRReach: instantiateR an existential supertype with a previously
-- an existential subtype variable
instantiateR ctxt (ExVar exB) exA =
  do
    handleVar (hasExVar exA ctxt) (VarError exA ctxt) (pure ()) 
    handleVar (hasExVar exB ctxt) (VarError exB ctxt) (pure ())   
    (prefix, suffix) <- splitExVar (\v c -> VarError v c) exB ctxt
    let solvedCtxt = fromFocus prefix (ConExDef exB (MonoExVar exA)) suffix
    pure solvedCtxt
-- InstRArr: instantiateR a existential supertype
-- at an arrow by introducing new existential variables
-- and then solving the lhs followed by rhs    
instantiateR ctxt (TyArr a1 a2) exA =
  do
    handleVar (hasExVar exA ctxt) (VarError exA ctxt) (pure ())
    (prefix, suffix) <- splitExVar (\v c -> VarError v c) exA ctxt
    let
      exName1 = fresh ctxt
      exVar1  = ConExVar exName1      
      exName2 = fresh (ctxt :|> exVar1)
      exVar2  = ConExVar exName2
      foci    = [exVar1, exVar2, ConExDef exA (MonoArr (MonoExVar exName1) (MonoExVar exName2))]
      newCtxt = fromFoci prefix foci suffix
    leftSolved <- instantiateL newCtxt exName1 a1
    let newRHS = applyContext leftSolved a2
    instantiateR leftSolved newRHS exName2
-- InstRAllR: instantitate an existential subtype at
-- a polymorphic supertype
instantiateR ctxt (ForAll b ty_b) exA =
  do
    handleVar (hasExVar exA ctxt) (VarError exA ctxt) (pure ())
    let
      exB      = fresh ctxt
      exVarB   = ExVar exB
      exContext = ctxt :|> ScopeMark exB :|> (ConExVar exB)
      instTy_b = substitute b exVarB ty_b
    exBCon <- instantiateR exContext instTy_b exA
    removeScopeSuffix (\v c -> ScopeMarkError v c) exA exBCon
instantiateR _ ty var = throwError (InstaniationRError ty var)



data JudgmentType v =
     -- input context   term     type    output context
    Check (Context v)   (Term v) (Type v) (Context v)
  | Infer (Context v)   (Term v) (Type v) (Context v)
  | Sub   (Context v)   (Term v) (Type v) (Context v)
  | Inst  (Context v)   (Term v) (Type v) (Context v)  
     -- input context   fun     arg     infer type  context   
  | App   (Context v)   (Term v) (Term v) (Type v)    (Context v)


type Judgment v = (JudgmentType v, String)

type JudgmentTree v = Tree (Judgment v)
